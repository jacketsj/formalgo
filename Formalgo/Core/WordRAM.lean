import Formalgo.Core.RAM

/-!
# The word RAM
A RAM whose words are unsigned integers of `w` bits, for any word size `w`.
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

/-- Word RAM with words of `w` bits, and a fixed list of operations.
Its addresses are the words. -/
def wordRAM (w : ℕ) (operations : List WordRAM.Operation) :
    RAM (Address := BitVec w) (Word := BitVec w)
      (Extension := RAM.Arithmetic (BitVec w) {operation // operation ∈ operations}) where
  toAddress? word := some word
  extension := RAM.arithmetic fun
    | ⟨.add, _⟩ => (· + ·)
    | ⟨.sub, _⟩ => (· - ·)
    | ⟨.mul, _⟩ => (· * ·)
    | ⟨.div, _⟩ => (· / ·)
    | ⟨.mod, _⟩ => (· % ·)
    | ⟨.less, _⟩ => fun left right => if left < right then 1 else 0
    | ⟨.and, _⟩ => (· &&& ·)
    | ⟨.or, _⟩ => (· ||| ·)
    | ⟨.xor, _⟩ => (· ^^^ ·)
    | ⟨.shiftLeft, _⟩ => (· <<< ·)
    | ⟨.shiftRight, _⟩ => (· >>> ·)

/-- Word RAM with every operation. -/
def WordRAM.standard (w : ℕ) :=
  wordRAM w [.add, .sub, .mul, .div, .mod, .less, .and, .or, .xor, .shiftLeft, .shiftRight]

end Formalgo
