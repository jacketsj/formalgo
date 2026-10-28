import Formalgo.Core.RAM

/-!
# The word RAM
A RAM whose words are natural numbers less than `2^w`, for any word size `w`.
Arithmetic wraps around modulo `2^w`.
-/

namespace Formalgo

/-- Operations on words. -/
inductive WordRAM.Operation where
  | add
  | sub
  | mul
  /-- Division, rounding down; division by `0` gives `0`. -/
  | div
  /-- Remainder; remainder by `0` gives the left word. -/
  | mod
  /-- `1` if the left word is smaller, and `0` otherwise. -/
  | less
  /-- Bitwise and. -/
  | and
  /-- Bitwise or. -/
  | or
  /-- Bitwise exclusive or. -/
  | xor
  /-- Shift the left word toward its high bits by the right word, filling with `0`s. -/
  | shiftLeft
  /-- Shift the left word toward its low bits by the right word, filling with `0`s. -/
  | shiftRight

/-- Word RAM with words of size `2^w`.
Each operation is reduced modulo `2^w`. -/
def wordRAM (w : ℕ) (operations : List WordRAM.Operation) :
    RAM (Address := ℕ) (Word := ℕ)
      (Extension := RAM.Arithmetic ℕ {operation // operation ∈ operations}) where
  toAddress? word := some word
  extension := RAM.arithmetic fun operation left right => (match operation with
    | ⟨.add, _⟩ => left + right
    | ⟨.sub, _⟩ => left + 2 ^ w - right % 2 ^ w
    | ⟨.mul, _⟩ => left * right
    | ⟨.div, _⟩ => left % 2 ^ w / (right % 2 ^ w)
    | ⟨.mod, _⟩ => left % 2 ^ w % (right % 2 ^ w)
    | ⟨.less, _⟩ => if left % 2 ^ w < right % 2 ^ w then 1 else 0
    | ⟨.and, _⟩ => left &&& right
    | ⟨.or, _⟩ => left ||| right
    | ⟨.xor, _⟩ => left ^^^ right
    | ⟨.shiftLeft, _⟩ => left <<< (right % 2 ^ w)
    | ⟨.shiftRight, _⟩ => (left % 2 ^ w) >>> (right % 2 ^ w)) % 2 ^ w

/-- Word RAM with every operation. -/
def WordRAM.standard (w : ℕ) :=
  wordRAM w [.add, .sub, .mul, .div, .mod, .less, .and, .or, .xor, .shiftLeft, .shiftRight]

end Formalgo
