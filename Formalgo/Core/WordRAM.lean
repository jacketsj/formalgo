import Formalgo.Core.RAM

/-!
# The word RAM
A RAM whose words are unsigned integers of `w` bits.
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

/-- Word RAM with words of `w` bits. -/
def wordRAM (w : ℕ) {Address : Type} [DecidableEq Address] (toAddress? : BitVec w → Option Address)
    (operations : List WordRAM.Operation) :
    RAM (Address := Address) (Word := BitVec w)
      (Extension := RAM.Arithmetic Address {operation // operation ∈ operations}) where
  toAddress? := toAddress?
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
def WordRAM.standard (w : ℕ) {Address : Type} [DecidableEq Address]
    (toAddress? : BitVec w → Option Address) :=
  wordRAM w toAddress?
    [.add, .sub, .mul, .div, .mod, .less, .and, .or, .xor, .shiftLeft, .shiftRight]

end Formalgo
