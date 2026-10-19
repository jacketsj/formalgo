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

end Formalgo
