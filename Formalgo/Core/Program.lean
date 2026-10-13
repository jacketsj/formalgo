import Formalgo.Core.ControlFlow
import Formalgo.Core.Machine
import Formalgo.Core.Semantics

/-!
# Programs
-/

namespace Formalgo

/-- A program: control flow with an instruction for each valid PC value. -/
structure Program (PC Instruction Outcome : Type*) [Fintype PC] [Fintype Outcome]
    extends ControlFlow PC Outcome where
  /-- Instruction at a given PC value. -/
  instruction : PC → Instruction

/-- State of a running program. -/
structure Program.State (PC Address Value : Type*) where
  /-- Current PC value. -/
  pc : PC
  /-- Current tape. -/
  tape : Tape Address Value

/-- The machine running `program` with `semantics`. -/
def Program.machine {PC Instruction Outcome Address Value : Type*} [Fintype PC] [Fintype Outcome]
    (program : Program PC Instruction Outcome)
    (semantics : Semantics Instruction Outcome Address Value) :
    Machine (Program.State PC Address Value) where
  step state := match semantics.exec (program.instruction state.pc) state.tape with
    | (none, tape) => .halted ⟨state.pc, tape⟩
    | (some outcome, tape) => .running ⟨program.next state.pc outcome, tape⟩

end Formalgo
