import Mathlib.Data.Fintype.Defs

/-!
# Control flow
These can be used to represent program descriptions for complex machines.
This is equivalent to a semiautomaton.
-/

namespace Formalgo

/-- Control flow: finitely many states, and transitions on finitely many outcomes. -/
structure ControlFlow (State Outcome : Type*) [Fintype State] [Fintype Outcome] where
  /-- Initial state. -/
  init : State
  /-- The next state, given the outcome of the current step. This encodes branching. -/
  next : State → Outcome → State

end Formalgo
