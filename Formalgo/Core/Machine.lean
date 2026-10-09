import Mathlib.Data.Nat.Notation

/-!
# Basic and generic machine definition
-/

namespace Formalgo

/-- The status of an execution along with the state (State) of the machine. -/
inductive Status (State : Type*) where
  /-- The computation continues from `state`. -/
  | running (state : State)
  /-- The computation completed in `state`. -/
  | halted (state : State)

/-- A machine with states `State`. -/
structure Machine (State : Type*) where
  /-- Perform one computation step. -/
  step : State → Status State

/-- Run `m` for `n` steps, or until it halts. -/
def Machine.run {State : Type*} (m : Machine State) : ℕ → State → Status State
  | 0, s => .running s
  | n + 1, s => match m.step s with
    | .running s' => m.run n s'
    | .halted s' => .halted s'

end Formalgo
