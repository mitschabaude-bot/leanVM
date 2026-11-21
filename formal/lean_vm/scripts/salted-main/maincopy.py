"""Copy the deployed `main` modules' declarations that rest on `MainFacts` to the salted ones.

  python3 maincopy.py OUT.lean HEADER.lean SKIP DEPLOYED.lean...

Keeps the declarations of the deployed files that mention `MainFacts`, `KidOk` or `MF`, or a kept
declaration (the others, which read no fact, are the deployed ones, used through `open`), renames
each kept declaration `N` to `NK`, `MainFacts C rd σ` to `MainFactsK C rd σ S key` and `KidOk C rd σ`
to `KidOkK C rd σ S`, `CalleesWC … (σ (.n 47))` to `CalleesWCK … (σ (.n 47)) key S`, and moves them to `LeanVM.SaltedGuest.B1.Main`. `SKIP` (comma-separated)
names declarations left out (ported by hand); a file given as `@FILE` is read for the kept names
only (copied by an earlier run), not emitted. Prints the kept names.
"""
import re
import sys

KEYWORDS = ("theorem ", "lemma ", "def ", "noncomputable def ", "structure ", "abbrev ",
            "noncomputable abbrev ", "instance ", "private theorem ", "@[")


def blocks(src):
    """Split into (kind, name, text): kind 'decl' or 'other'."""
    lines = src.split("\n")
    out = []
    inc = False  # inside a section that includes `MF`
    i = 0
    pending = []  # docstring / attribute / set_option lines before a declaration
    while i < len(lines):
        ln = lines[i]
        if ln.startswith("/--"):
            j = i
            while "-/" not in lines[j]:
                j += 1
            pending += lines[i:j + 1]
            i = j + 1
            continue
        if (ln.startswith(("set_option", "omit ", "include ")) and ln.rstrip().endswith(" in")):
            pending.append(ln)
            i += 1
            continue
        if ln.startswith(KEYWORDS) and not ln.startswith("@[expose]"):
            j = i + 1
            while j < len(lines) and (lines[j].startswith((" ", "\t")) or lines[j] == "" or
                                      lines[j].startswith("  ")):
                if lines[j] == "" and j + 1 < len(lines) and not lines[j + 1].startswith(" "):
                    break
                j += 1
            text = "\n".join(pending + lines[i:j])
            m = re.match(r"(?:@\[[^\]]*\]\s*)?(?:private |noncomputable )*(?:theorem|lemma|def|structure|abbrev|instance)\s+([^\s({:]+)", ln)
            omitted = any(p.startswith("omit MF") for p in pending)
            out.append(("decl", m.group(1) if m else None, text + ("\n-- uses MF" if inc and not omitted else "")))
            pending = []
            i = j
            continue
        if ln.startswith("/-!") or ln.startswith("/-"):
            j = i
            while "-/" not in lines[j]:
                j += 1
            out.append(("other", None, "\n".join(pending + lines[i:j + 1])))
            pending = []
            i = j + 1
            continue
        if ln.startswith("include MF"):
            inc = True
        if ln.startswith("end ") and ln != "end":
            inc = False
        out.append(("other", None, "\n".join(pending + [ln])))
        pending = []
        i += 1
    return out


def main():
    outp, doc, skip = sys.argv[1], open(sys.argv[2]).read(), set(filter(None, sys.argv[3].split(",")))
    allb = []
    names_only = []
    for f in sys.argv[4:]:
        emit = not f.startswith("@")
        src = open(f.lstrip("@")).read()
        start = src.index("namespace LeanVM.Guest.B1.Main")
        bs = blocks(src[start:])
        if emit:
            allb += bs
        else:
            names_only += [b for b in bs if b[0] == "decl"]
    decls = names_only + [b for b in allb if b[0] == "decl"]
    seed = re.compile(r"\bMainFacts\b|\bKidOk\b|\bMF\b|\bCalleesWC\b")
    kept = set()
    changed = True
    while changed:
        changed = False
        for _, n, t in decls:
            if n in kept or n is None:
                continue
            if seed.search(t) or any(re.search(r"(?<![\w.])%s(?![\w'])" % re.escape(k), t) for k in kept):
                kept.add(n)
                changed = True
    ren = sorted(kept, key=len, reverse=True)

    def rename(t):
        t = re.sub(r"\bMainFacts C rd σ\b", "MainFactsK C rd σ S key", t)
        t = re.sub(r"\bKidOk C rd σ\b", "KidOkK C rd σ S", t)
        t = t.replace("CalleesWC bytecode C rd (σ (.n 47))", "CalleesWCK bytecode C rd (σ (.n 47)) key S")
        for k in ren:
            t = re.sub(r"(?<![\w.])%s(?![\w'])" % re.escape(k), k + "K", t)
        return t

    body = []
    for kind, n, t in allb:
        if kind == "decl":
            if n in kept and n not in skip:
                body.append(rename(t.replace("\n-- uses MF", "")))
            continue
        if t.startswith("namespace LeanVM.Guest.B1.Main"):
            t = "namespace LeanVM.SaltedGuest.B1.Main"
        elif t.startswith("end LeanVM.Guest.B1.Main"):
            t = "end LeanVM.SaltedGuest.B1.Main"
        elif t.startswith("open LeanVM.Guest.B1.Digest LeanVM.Node"):
            t += "\nopen LeanVM.Guest.B1 LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted"
        elif t.startswith("variable {C : CallRel}"):
            t += "\n\nvariable {S : Digest} {key : E}"
        elif t.startswith("variable"):
            t = rename(t)
        elif t.startswith("/-!") and not t.startswith("/-! #") and "\n" not in t:
            pass
        elif t.startswith("/-!") or t.startswith("/-"):
            continue
        body.append(t)
    text = "\n".join(body)
    text = re.sub(r"\n{3,}", "\n\n", text)
    open(outp, "w").write(doc + "\n" + text.strip() + "\n")
    print(" ".join(sorted(kept)))


main()
