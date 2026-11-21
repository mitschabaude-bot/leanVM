"""The deployed guest's instance modules renamed into the salted guest's.

The guest's proof is stated over one compiled program: the modules that import its generated data
(`Statement/Data/`, `LeanVM/Guest/Data/`), directly or not, name that program, and the rest is
generic. The salted guest's counterparts of the first are the same text with the salted data in
place of the deployed: module `LeanVM.Guest.X` becomes `LeanVM.SaltedGuest.X` (`Statement.Data.Y`
becomes `LeanVM.SaltedGuest.Data.Y`, and a module importing `Statement.LeanVmGuest` also imports
`LeanVM.SaltedGuest.Program`, whose `guestProgram` is the salted program), its namespaces
`LeanVM.Guest…` become `LeanVM.SaltedGuest…` (each opening the generic namespaces it shadows, so
that the generic declarations stay in reach), an `open` of an instance namespace opens the salted
one, and a qualified name of an instance declaration is renamed with it. Inside
`LeanVM.SaltedGuest` a name resolves to the salted declaration before any opened one, so the
deployed declarations `Statement/LeanVmGuest.lean` brings (`LeanVM.Guest.guestProgram`, the
deployed `LeanVM.Guest.Data`) are not chosen.

  python3 -I scripts/salted-rename.py SRC_ROOT MODULE...

renames the deployed modules `MODULE...` (dotted names, read under `SRC_ROOT`, a directory laid out
as `lean_vm`) and writes them under `lean_vm/LeanVM/SaltedGuest/`. The instance modules are those
being written, those whose salted counterparts exist there already and the generated ones; an import
of any other deployed instance module is reported. `scripts/salted-guest-cert` uses it on the deployed-layout
output of `guest-cert --salted`.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

LEAN_VM = Path(__file__).resolve().parent.parent
# Deployed instance modules whose content is generic but for a part about the program or its data:
# the salted guest imports them as they are, and its hand-written module of the same name (a
# supplement) holds or imports the salted counterpart of that part.
SUPPLEMENTED = {"LeanVM.Guest.Exec", "LeanVM.Guest.Memory", "LeanVM.Guest.Pow"}
# Generic types' extensions that deployed instance modules declare, renamed for the salted guest
# (`Program.indexOf?` becomes `Program.saltedIndexOf?`) in the generic type's namespace, so that
# both guests' modules can be imported together.
EXTENSIONS = {"indexOf?": "saltedIndexOf?", "find?_of_indexOf?": "find?_of_saltedIndexOf?",
              "rsFit": "saltedRsFit", "locAtR": "saltedLocAtR", "winFits": "saltedWinFits"}
FORMAL = LEAN_VM.parent
SALTED = LEAN_VM / "LeanVM" / "SaltedGuest"
OLD, NEW = "LeanVM.Guest", "LeanVM.SaltedGuest"
IMPORT = re.compile(r"^((?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?)([\w.]+)", re.M)
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|public)\s+)*"
    r"(?:def|theorem|lemma|abbrev|structure|inductive|class|instance|opaque|axiom)\s+([^\s:({\[]+)",
    re.M)


def deployed_path(root: Path, module: str) -> Path:
    if module.startswith("Statement."):
        return FORMAL / (module.replace(".", "/") + ".lean")
    return root / (module.replace(".", "/") + ".lean")


def salted_name(module: str) -> str:
    if module.startswith("Statement.Data."):
        return f"{NEW}.Data." + module[len("Statement.Data."):]
    if module.startswith(OLD + "."):
        return NEW + module[len(OLD):]
    return NEW + module[len("LeanVM"):]


def deployed_name(module: str) -> str | None:
    """The deployed counterpart of a salted module, if it has one."""
    rest = module[len(NEW):]
    if rest.startswith(".Data.Bytecode"):
        return "Statement" + rest
    for name in (OLD + rest, "LeanVM" + rest):
        if deployed_path(LEAN_VM, name).exists():
            return name
    return None


def scan(text: str) -> tuple[set[str], set[str]]:
    """The namespaces a module declares (with their parents) and its declarations' full names."""
    spaces, decls, stack = set(), set(), []
    for line in text.splitlines():
        if m := re.match(r"^namespace\s+([\w.]+)", line):
            stack.append(m.group(1))
            parts = ".".join(stack).split(".")
            spaces.update(".".join(parts[:i]) for i in range(1, len(parts) + 1))
        elif m := re.match(r"^end\s+([\w.]+)\s*$", line):
            if stack and stack[-1] == m.group(1):
                stack.pop()
        elif m := DECL.match(line):
            name = m.group(1)
            decls.add(name[len("_root_."):] if name.startswith("_root_.") else ".".join(stack + [name]))
    return spaces, decls


def public_names(text: str) -> dict[str, set[str]]:
    """The undotted names of a module's public declarations, by namespace."""
    names: dict[str, set[str]] = {}
    stack: list[str] = []
    for line in text.splitlines():
        if m := re.match(r"^namespace\s+([\w.]+)", line):
            stack.append(m.group(1))
        elif m := re.match(r"^end\s+([\w.]+)\s*$", line):
            if stack and stack[-1] == m.group(1):
                stack.pop()
        elif (m := DECL.match(line)) and not re.search(r"\bprivate\b", line[:m.start(1)]):
            name = m.group(1)
            full = name[len("_root_."):] if name.startswith("_root_.") else ".".join(stack + [name])
            ns, _, short = full.rpartition(".")
            if ns and short and "." not in name.removeprefix("_root_."):
                names.setdefault(ns, set()).add(short)
    return names


def lean_modules():
    for root, base in ((LEAN_VM / "LeanVM", LEAN_VM), (FORMAL / "Statement", FORMAL)):
        for path in root.rglob("*.lean"):
            if ".lake" not in path.parts:
                yield ".".join(path.relative_to(base).with_suffix("").parts), path


def is_data(module: str) -> bool:
    return module.startswith("Statement.Data.") or module.startswith(f"{OLD}.Data.")


def is_generated(module: str) -> bool:
    """Written by the generators (`guest-export`, `guest-core`, `scripts/salted-guest-cert`)."""
    return is_data(module) or module == f"{OLD}.Checked" or module.startswith(f"{OLD}.Checked.")


def deployed_instance() -> set[str]:
    """Every deployed module that imports the deployed data or the deployed program
    (`Statement/LeanVmGuest.lean`), directly or not, but the statement's own modules."""
    imports = {m: [i for _, i in IMPORT.findall(p.read_text())] for m, p in lean_modules()
               if not m.startswith(NEW)}
    tainted: dict[str, bool] = {}

    def taint(m: str) -> bool:
        if m not in tainted:
            tainted[m] = False
            tainted[m] = is_data(m) or m == "Statement.LeanVmGuest" or any(taint(i) for i in imports.get(m, []))
        return tainted[m]

    return {m for m in imports if taint(m) and not (m.startswith("Statement.") and not is_data(m))}


def rename(src_root: Path, modules: list[str]) -> dict[Path, str]:
    """The salted modules of the deployed `modules` (read under `src_root`), by path."""
    existing = {".".join(("LeanVM", "SaltedGuest", *p.relative_to(SALTED).with_suffix("").parts))
                for p in SALTED.rglob("*.lean")}
    counterparts = ({d for d in (deployed_name(m) for m in existing) if d} | set(modules)) - SUPPLEMENTED
    every = deployed_instance()
    texts = {m: p.read_text() for m, p in lean_modules() if not m.startswith(NEW)}
    for m in modules:
        texts[m] = deployed_path(src_root, m).read_text()
    imports = {m: [i for _, i in IMPORT.findall(t)] for m, t in texts.items()}
    scanned = {m: scan(t) for m, t in texts.items()}
    supplements, supplement_names = {}, {}
    for m in SUPPLEMENTED:
        path = SALTED / (salted_name(m)[len(NEW) + 1:].replace(".", "/") + ".lean")
        text = path.read_text() if path.exists() else ""
        supplements[m] = {OLD + x[len(NEW):] for x in scan(text)[0] if x.startswith(NEW)}
        supplement_names[m] = {OLD + ns[len(NEW):]: n for ns, n in public_names(text).items() if ns.startswith(NEW)}
    names_of = {}
    inst_decls = set().union(*(scanned[m][1] for m in counterparts if m in scanned))
    inst_all = set().union(*(scanned[m][0] for m in counterparts if m in scanned), *supplements.values())

    def deployed_closure(m: str, seen: set[str]) -> None:
        stack = [m]
        while stack:
            x = stack.pop()
            if x not in seen:
                seen.add(x)
                stack += imports.get(x, [])

    def salted_env(m: str) -> tuple[set[str], set[str], dict[str, set[str]], dict[str, set[str]]]:
        """The salted copy of `m`'s environment: the instance namespaces (by their deployed names),
        those under their deployed names, the latter's public undotted names by namespace, and the
        supplements' (by their deployed namespaces)."""
        inst, gen, seen, stack = set(), set(), set(), [m]
        deployed: set[str] = set()
        supp: dict[str, set[str]] = {}
        while stack:
            x = stack.pop()
            if x in seen:
                continue
            seen.add(x)
            if x in SUPPLEMENTED:
                inst |= supplements[x]
                for ns, n in supplement_names[x].items():
                    supp.setdefault(ns, set()).update(n)
                deployed_closure(x, deployed)
            elif x in counterparts or is_generated(x):
                inst |= scanned[x][0] if x in scanned else set()
                stack += imports.get(x, [])
            else:
                deployed_closure(x, deployed)
        names: dict[str, set[str]] = {}
        for x in deployed:
            gen |= scanned[x][0] if x in scanned else set()
            if x not in names_of:
                names_of[x] = public_names(texts[x]) if x in texts else {}
            for ns, n in names_of[x].items():
                names.setdefault(ns, set()).update(n)
        return inst, gen, names, supp

    missing: set[str] = set()
    out = {}
    for module in modules:
        inst_spaces, gen_spaces, gen_names, supp_names = salted_env(module)
        path = SALTED / (salted_name(module)[len(NEW) + 1:].replace(".", "/") + ".lean")
        out[path] = transform(module, texts[module], counterparts, every, inst_spaces, inst_all, inst_decls,
                              gen_spaces, gen_names, supp_names, missing)
    if missing:
        sys.exit("deployed instance modules imported, without a salted counterpart: " + " ".join(sorted(missing)))
    return out


def transform(module: str, text: str, counterparts: set[str], every: set[str], inst_spaces: set[str],
              inst_all: set[str], inst_decls: set[str], gen_spaces: set[str], gen_names: dict[str, set[str]],
              supp_names: dict[str, set[str]], missing: set[str]) -> str:
    """`module`'s salted text: `inst_spaces` and `gen_spaces` are the instance namespaces (by their
    deployed names) and the deployed ones its imports declare, `gen_names` the latter's names and
    `supp_names` the supplements' by namespace, `inst_all` and `inst_decls` every instance
    namespace and declaration.

    The deployed text found a generic name through its namespace (`LeanVM.Guest.Check` inside
    `namespace LeanVM.Guest.Check`) before any opened namespace; the salted text opens that
    namespace, so every other opened namespace hides the names the deployed resolution would not
    have reached (`open … hiding …`), and an opened deployed namespace hides the names its salted
    supplement declares."""
    statement = False

    def imp(m):
        nonlocal statement
        name = m.group(2)
        if name == "Statement.LeanVmGuest":
            statement = True
        if name in counterparts or name in SUPPLEMENTED or is_generated(name):
            return m.group(1) + salted_name(name)
        if name in every:
            missing.add(name)
        return m.group(0)

    text = IMPORT.sub(imp, text)
    if statement:
        text = re.sub(r"^((?:public\s+)?import\s+Statement\.LeanVmGuest)$",
                      lambda m: m.group(1) + "\n" + m.group(1).replace("Statement.LeanVmGuest", f"{NEW}.Program"),
                      text, count=1, flags=re.M)
    text = re.sub(r"^(/-\n  )([\w.]+)", lambda m: m.group(1) + salted_name(module), text, count=1)

    chain: list[str] = []  # the shadowed namespaces of the current block, innermost first

    def hidden(name: str) -> list[str]:
        """What an open of the deployed namespace `name` hides."""
        mine = gen_names.get(name, set())
        inner = chain[:chain.index(name)] if name in chain else chain
        hide = set().union(*(gen_names.get(c, set()) for c in inner)) & mine
        if NEW + name[len(OLD):] in opened:
            hide |= supp_names.get(name, set()) & mine
        return sorted(hide)

    def open_clause(prefix: str, name: str, suffix: str) -> str:
        hide = hidden(name) if name == OLD or name.startswith(OLD + ".") else []
        return f"{prefix}{name}" + (" hiding " + " ".join(hide) if hide else "") + suffix

    def open_lines(prefix: str, names: list[str], suffix: str) -> list[str]:
        out = []
        for name in names:
            if name == OLD or name.startswith(OLD + "."):
                if name in inst_spaces:
                    out.append(NEW + name[len(OLD):])
                if name in gen_spaces:
                    out.append(name)
            else:
                out.append(name)
        out = list(dict.fromkeys(out))
        opened.update(out)
        plain = [n for n in out if not hidden_any(n)]
        lines = [f"{prefix}{' '.join(plain)}{suffix}"] if plain else []
        return lines + [open_clause(prefix, n, suffix) for n in out if hidden_any(n)]

    def hidden_any(name: str) -> bool:
        return (name == OLD or name.startswith(OLD + ".")) and bool(hidden(name))

    opened: set[str] = set()
    stack: list[str] = []  # the deployed namespaces of the open blocks, full names

    def enter() -> list[str]:
        nonlocal chain, opened
        full = stack[-1]
        parts = full.split(".")
        guest = full == OLD or full.startswith(OLD + ".")
        chain = [s for s in (".".join(parts[:i]) for i in range(len(parts), 1, -1))
                 if guest and (s == OLD or s.startswith(OLD + ".")) and s in gen_spaces]
        opened = set()
        return ([""] + open_lines("open ", chain[::-1], "")) if chain else []

    lines = []
    for line in text.split("\n"):
        if m := re.match(r"^namespace\s+([\w.]+)\s*$", line):
            name = m.group(1)
            outer = stack[-1] if stack else ""
            full = name if name.startswith("LeanVM.") or not outer else f"{outer}.{name}"
            stack.append(full)
            if name == OLD or name.startswith(OLD + "."):
                lines.append(f"namespace {NEW}{name[len(OLD):]}")
            else:
                lines.append(line)
            lines += enter()
            continue
        if m := re.match(r"^end\s+([\w.]+)\s*$", line):
            name = m.group(1)
            if stack:
                stack.pop()
            lines.append(f"end {NEW}{name[len(OLD):]}" if name == OLD or name.startswith(OLD + ".") else line)
            if stack:
                enter()
            else:
                chain, opened = [], set()
            continue
        if m := re.match(r"^(\s*open\s+)((?:[\w.]+\s*?)+?)(\s+in)?\s*$", line):
            lines += open_lines(m.group(1), m.group(2).split(), m.group(3) or "")
            continue
        lines.append(line)
    text = "\n".join(lines)

    def qualified(m):
        name = m.group(0)
        parts = name[len(OLD) + 1:].split(".")
        for i in range(len(parts), 0, -1):
            prefix = OLD + "." + ".".join(parts[:i])
            if prefix in inst_decls or (prefix in inst_all and prefix not in gen_spaces):
                return NEW + name[len(OLD):]
        return name

    text = re.sub(r"(?<![\w.])" + re.escape(OLD) + r"\.[\w.']+", qualified, text)
    for old, new in EXTENSIONS.items():
        # the declaration, in its generic type's namespace
        text = re.sub(r"^((?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|theorem)\s+)([\w.]+)\." + re.escape(old)
                      + r"(?=[\s:({])", lambda m: generic_extension(m, module, new), text, flags=re.M)
        text = re.sub(r"(?<![\w'?])" + re.escape(old) + r"(?![\w'?])", new, text)
    return text


def generic_extension(m: re.Match, module: str, new: str) -> str:
    """A generic type's extension, declared at the generic type's full name."""
    types = {"Program": "LeanVM.Guest.Core.Program", "Core.Program": "LeanVM.Guest.Core.Program",
             "Cert": "LeanVM.Guest.Check.Cert"}
    return f"{m.group(1)}_root_.{types[m.group(2)]}.{new}"


if __name__ == "__main__":
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    for path, text in rename(Path(sys.argv[1]), sys.argv[2:]).items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        print(path.relative_to(LEAN_VM))
