import Formalgo.Core.TDAlgorithm
import Formalgo.Core.WordRAM

/-!
# The transdichotomous (TD) word RAM
Programs for `w`-bit words are lifted to larger words by padding with `0`s. They can depend on
overflow, but not on words having exactly `w` bits.
-/

namespace Formalgo

/-- Pad an instruction for `w`-bit words to larger words. -/
def WordRAM.liftInstruction {w w' : ℕ} {Operation : Type*} (h : w ≤ w') :
    RAM.Instruction (BitVec w) (BitVec w) (RAM.Arithmetic (BitVec w) Operation) →
      RAM.Instruction (BitVec w') (BitVec w') (RAM.Arithmetic (BitVec w') Operation) :=
  .map (·.setWidth' h) (·.setWidth' h) (.map (·.setWidth' h))

/-- TD word RAM with a fixed list of operations. -/
def tdWordRAM (operations : List WordRAM.Operation) :
    TDMachine (fun w => RAM.Instruction (BitVec w) (BitVec w)
      (RAM.Arithmetic (BitVec w) {operation // operation ∈ operations})) BitVec BitVec where
  semantics w := (wordRAM w operations).semantics
  lift := WordRAM.liftInstruction

end Formalgo
