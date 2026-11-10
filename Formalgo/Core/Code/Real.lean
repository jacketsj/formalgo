import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.NNReal.Defs
import Formalgo.Core.Code

/-!
# Codes for reals
Codes on tapes of real numbers.
-/

namespace Formalgo.Code

/-- A natural number is written as a single real. -/
noncomputable instance singleRealCell : Code ℕ ℝ where
  encode n := [n]
  decode stream := (⌊stream 0⌋₊, fun i => stream (i + 1))

/-- A nonnegative real is written as itself. -/
noncomputable instance nnreal : Code NNReal ℝ where
  encode r := [r]
  decode stream := ((stream 0).toNNReal, fun i => stream (i + 1))

end Formalgo.Code
