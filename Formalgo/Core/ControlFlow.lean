import Mathlib.Data.Fintype.Defs

/-!
# Control flow
These can be used to represent program descriptions for complex machines.
This is equivalent to a semiautomaton.
-/

namespace Formalgo

/-- Control flow: program counter (PC) values, and transitions based on outcomes. -/
structure ControlFlow (PC Outcome : Type*) [Fintype PC] [Fintype Outcome] where
  /-- Initial PC value. -/
  init : PC
  /-- The next PC value, given the outcome of the current step. This encodes branching. -/
  next : PC → Outcome → PC

end Formalgo
