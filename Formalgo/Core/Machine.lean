import Mathlib.Data.Nat.Notation

/-!
# Basic and generic machine definition
-/

namespace Formalgo

/-- The status of an execution along with the state (σ) of the machine. -/
inductive Status (σ : Type*) where
  /-- The computation continues from `state`. -/
  | running (state : σ)
  /-- The computation completed in `state`. -/
  | halted (state : σ)

/-- A deterministic machine with states `σ`. -/
structure Machine (σ : Type*) where
  /-- Perform one computation step. -/
  step : σ → Status σ

/-- Run `m` for `n` steps, or until it halts. -/
def Machine.run {σ : Type*} (m : Machine σ) : ℕ → σ → Status σ
  | 0, s => .running s
  | n + 1, s => match m.step s with
    | .running s' => m.run n s'
    | .halted s' => .halted s'

end Formalgo
