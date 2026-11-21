import LeanVM.SaltedGuest.Data.Bytecode
import LeanVM.SaltedGuest.Data.Source
import LeanVM.Guest.Code
import LeanVMTests.SaltedGuest.Manifest

/-!
# The salted guest's generated data against the Rust's manifest

`scripts/guest-export` writes the compiled salted guest (`LeanVM/SaltedGuest/Data/Bytecode*.lean`),
its source AST (`Data/Source.lean`) and what the Rust reports of it (`Manifest.lean`). Recomputed
here from the Lean data: the log size, the code length, the function count, the instructions of
each opcode, the source's placeholders' log size. That the assembled `guestProgram` is the
bytecode the Rust proves, every instruction, is `lake exe salted-node-diff` (the seed of the
manifest's salt against `Manifest.seed`).
-/

namespace LeanVMTests.SaltedGuest.Data

open LeanVM.Guest LeanVM.SaltedGuest.Data

/-- The opcode index of an instruction: `XOR`, `MUL`, `SET`, `DEREF`, `JUMP`, `KECCAK`. -/
def opIdx : OffsetInstruction → Nat
  | .xor .. => 0
  | .mul .. => 1
  | .set .. => 2
  | .deref .. => 3
  | .jump .. => 4
  | .keccak .. => 5

/-- The instructions of each opcode in the padded bytecode. -/
def opcodeCounts : List Nat :=
  let code := functions.flatMap (·.chunks.flatten)
  let pad := 2 ^ logSize - codeLen
  (List.range 6).map fun i ↦ (code.filter (opIdx · == i)).length + if i == 2 then pad else 0

#guard logSize = Manifest.logSize
#guard codeLen = Manifest.codeLen
#guard functions.length = Manifest.functionCount
#guard (functions.map (·.instructionCount)).sum = codeLen
#guard opcodeCounts = Manifest.opcodeCounts

/- The source's placeholders are those of the bytecode's size. -/
#guard bytecodeLog = logSize

/- The salted guest's source: its functions, `main` and the keyed hash's helpers among them. -/
#guard guest.funcs.any (·.name == "main")
#guard guest.funcs.any (·.name == "keyed_state")
#guard guest.funcs.any (·.name == "da_padding_root")

end LeanVMTests.SaltedGuest.Data
