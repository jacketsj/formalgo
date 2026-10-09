import Formalgo.Core.RAM

/-!
# The integer RAM
A simple RAM whose words are unbounded integers,
with a parametrized set of arithmetic operations from `+`, `−`, `<`, and '*'.
-/

namespace Formalgo

/-- Arithmetic operations on integers. -/
inductive IntegerRAM.Operation where
  | add
  | sub
  | mul
  /-- Integer division, rounding toward zero as in C; division by `0` gives `0`. -/
  | div
  /-- `1` if the left word is smaller, and `0` otherwise. -/
  | less

/-- Integer RAM with a fixed list of arithmetic operations.
Its addresses are the nonnegative integers. -/
def integerRAM (operations : List IntegerRAM.Operation) :
    RAM (Address := ℕ) (Word := ℤ)
      (Extension := RAM.Arithmetic ℕ {operation // operation ∈ operations}) where
  toAddress? word := if 0 ≤ word then some word.toNat else none
  extension := RAM.arithmetic fun
    | ⟨.add, _⟩ => (· + ·)
    | ⟨.sub, _⟩ => (· - ·)
    | ⟨.mul, _⟩ => (· * ·)
    | ⟨.div, _⟩ => Int.tdiv
    | ⟨.less, _⟩ => fun left right => if left < right then 1 else 0

/-- Integer RAM with only `<`. -/
def IntegerRAM.comparison := integerRAM [.less]

/-- Integer RAM with `<`, `+` and `−`. -/
def IntegerRAM.withAddSub := integerRAM [.less, .add, .sub]

/-- Integer RAM with `<`, `+`, `−` and `*`. -/
def IntegerRAM.withMultiplication := integerRAM [.less, .add, .sub, .mul]

/-- Integer RAM with `<`, `+`, `−`, `*` and `/`. -/
def IntegerRAM.withDivision := integerRAM [.less, .add, .sub, .mul, .div]

end Formalgo
