import Formalgo.Core.ControlFlow

/-!
# Programs
-/

namespace Formalgo

/-- A program: control flow with an instruction for each valid PC value. -/
structure Program (PC Instruction Outcome : Type*) [Fintype PC] [Fintype Outcome]
    extends ControlFlow PC Outcome where
  /-- Instruction at a given PC value. -/
  instruction : PC → Instruction

/-- `program` with each instruction mapped by `f`. -/
def Program.map {PC Instruction Instruction' Outcome : Type*} [Fintype PC] [Fintype Outcome]
    (f : Instruction → Instruction') (program : Program PC Instruction Outcome) :
    Program PC Instruction' Outcome :=
  { program with instruction := fun pc => f (program.instruction pc) }

end Formalgo
