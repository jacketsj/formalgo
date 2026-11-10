import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.NNReal.Defs
import Formalgo.Core.Code
import Formalgo.Core.RAM

/-!
# The real RAM
A RAM whose words are real numbers, with a parametrized set of arithmetic operations from `+`,
`−`, `*`, `/` and `<`. The words that are natural numbers are the addresses.
-/

namespace Formalgo

/-- Arithmetic operations on reals. -/
inductive RealRAM.Operation where
  | add
  | sub
  | mul
  /-- Division; division by `0` gives `0`. -/
  | div
  /-- `1` if the left word is smaller, and `0` otherwise. -/
  | less

/-- Real RAM with a fixed list of arithmetic operations. -/
noncomputable def realRAM (operations : List RealRAM.Operation) :
    RAM (Address := ℕ) (Word := ℝ)
      (Extension := RAM.Arithmetic ℕ {operation // operation ∈ operations}) where
  toAddress? word := if (⌊word⌋₊ : ℝ) = word then some ⌊word⌋₊ else none
  extension := RAM.arithmetic fun
    | ⟨.add, _⟩ => (· + ·)
    | ⟨.sub, _⟩ => (· - ·)
    | ⟨.mul, _⟩ => (· * ·)
    | ⟨.div, _⟩ => (· / ·)
    | ⟨.less, _⟩ => fun left right => if left < right then 1 else 0

/-- A natural number is written as a single real. -/
noncomputable instance RealRAM.code : Code ℕ ℝ where
  encode n := [n]
  decode stream := (⌊stream 0⌋₊, fun i => stream (i + 1))

/-- A nonnegative real is written as itself. -/
noncomputable instance RealRAM.nnrealCode : Code NNReal ℝ where
  encode r := [r]
  decode stream := ((stream 0).toNNReal, fun i => stream (i + 1))

/-- Real RAM with `<`, `+` and `−`. -/
noncomputable def RealRAM.withAddSub := realRAM [.less, .add, .sub]

/-- Real RAM with `<`, `+`, `−`, `*` and `/`. -/
noncomputable def RealRAM.withDivision := realRAM [.less, .add, .sub, .mul, .div]

end Formalgo
