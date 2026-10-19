import Mathlib.Tactic.TypeStar

/-!
# Input/output specifications
A problem, given by which outputs are valid for each input.
-/

namespace Formalgo

/-- An input/output specification. -/
structure IOSpec (Input Output : Type*) where
  /-- Whether an output is valid for an input. -/
  valid : Input → Output → Prop

end Formalgo
