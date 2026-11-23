/-
  LeanVM.Salted.ProgramCode

  The bit length of a program of leanVM's cost machine, for the recursion's statement.
-/

module

public import LeanVM.Cost.Machine
public import Mathlib.Data.Nat.Bits

/-!
# The bit length of a program

**The bit length** of a program of leanVM's cost machine (`MachineProgram.bits`) is the length
of its binary encoding `programCode`, in which every number of the program is written out: a
literal's numbers, tags, positions, field and function indices, the operations and the lengths of
lists. A number `n` is written as the count of its binary digits in unary, a zero, then the digits
(`natCode`, `2·⌊log₂ n⌋ + 3` bits for `n ≥ 1`); a term or a value as the number of its kind, then
its parts. A function index, in a call, a closure or a closure value, is written as its distance
from the index of the function whose body holds it, after a bit for the direction (`indexCode`);
the code starts with the count of functions. The machine's `MachineProgram.size` is not such a
length: it counts a tag or an index as one, whatever its value.
-/

namespace Recursion.Salted

open LeanVM LeanVM.Cost

@[expose] public section


/-- **The code of a number**: as many ones as it has binary digits, a zero, then its binary digits,
least significant first. -/
def natCode (n : ℕ) : List Bool := List.replicate n.bits.length true ++ false :: n.bits

/-- The number of a primitive operation. -/
def operationIndex : PrimitiveOperation → ℕ
  | .bitwiseAnd => 0 | .bitwiseOr => 1 | .bitwiseXor => 2 | .shiftLeft => 3 | .shiftRight => 4
  | .add => 5 | .truncatedSubtract => 6 | .equal => 7 | .lessThan => 8 | .multiply => 9
  | .divide => 10 | .modulo => 11 | .carrylessMultiply => 12 | .arraySize => 13 | .arrayGet => 14
  | .arraySet => 15 | .arrayPush => 16 | .arrayOfList => 17 | .arrayToList => 18
  | .arrayAppend => 19 | .arrayExtract => 20 | .arrayReplicate => 21

/-- **The code of a function index** `f` in the body of function `self`: a bit for the direction,
then the code of the distance from `self` to `f`. -/
def indexCode (self f : ℕ) : List Bool :=
  if self ≤ f then false :: natCode (f - self) else true :: natCode (self - f)

mutual

/-- **The code of a value** in the body of function `self`: its kind's number, then a number's
code, or a tag's code, or a function index's code (`indexCode`), the count of its parts and their
codes. -/
def valueCode (self : ℕ) : MachineValue → List Bool
  | .nat n => natCode 0 ++ natCode n
  | .constructor tag fields =>
    natCode 1 ++ natCode tag ++ natCode fields.length ++ valuesCode self fields
  | .array entries =>
    natCode 2 ++ natCode entries.toList.length ++ valuesCode self entries.toList
  | .closure f captured =>
    natCode 3 ++ indexCode self f ++ natCode captured.length ++ valuesCode self captured

/-- The codes of values, one after the other. -/
def valuesCode (self : ℕ) : List MachineValue → List Bool
  | [] => []
  | v :: vs => valueCode self v ++ valuesCode self vs

end

mutual

/-- **The code of a term** in the body of function `self`: its kind's number, then the codes of its
numbers and of its parts, a list of parts preceded by its length's code, a function index by
`indexCode`. -/
def termCode (self : ℕ) : Term → List Bool
  | .position i => natCode 0 ++ natCode i
  | .literal v => natCode 1 ++ valueCode self v
  | .primitive o ts =>
    natCode 2 ++ natCode (operationIndex o) ++ natCode ts.length ++ termsCode self ts
  | .constructor tag ts => natCode 3 ++ natCode tag ++ natCode ts.length ++ termsCode self ts
  | .field i t => natCode 4 ++ natCode i ++ termCode self t
  | .case t alts => natCode 5 ++ termCode self t ++ natCode alts.length ++ termsCode self alts
  | .letIn t b => natCode 6 ++ termCode self t ++ termCode self b
  | .call f ts => natCode 7 ++ indexCode self f ++ natCode ts.length ++ termsCode self ts
  | .closure f ts => natCode 8 ++ indexCode self f ++ natCode ts.length ++ termsCode self ts
  | .applyClosure t ts => natCode 9 ++ termCode self t ++ natCode ts.length ++ termsCode self ts

/-- The codes of terms, one after the other. -/
def termsCode (self : ℕ) : List Term → List Bool
  | [] => []
  | t :: ts => termCode self t ++ termsCode self ts

end

/-- **The codes of the bodies** of the functions `start`, `start + 1`, …, in order. -/
def bodiesCode : ℕ → List Term → List Bool
  | _, [] => []
  | start, t :: ts => termCode start t ++ bodiesCode (start + 1) ts

/-- **The code of a program**: the number of its functions, then their bodies' codes in order. -/
def programCode (program : MachineProgram) : List Bool :=
  natCode program.toList.length ++ bodiesCode 0 program.toList

/-- **The bit length of a program**: the length of its code, in which every number of the program
is written out in binary and every function index as its distance from the function that holds
it. -/
def _root_.LeanVM.Cost.MachineProgram.bits (program : MachineProgram) : ℕ :=
  (programCode program).length

end

end Recursion.Salted
