import Mathlib.Data.Nat.Digits.Defs
import Formalgo.Core.Code
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

/-- A natural number is written as its number of digits in base `2 ^ w`, then its digits, least
significant first. -/
instance WordRAM.code (w : ℕ) : Code ℕ (BitVec w) where
  encode n := let digits := Nat.digits (2 ^ w) n
    .ofNat w digits.length :: digits.map (.ofNat w)
  decode stream :=
    let count := (stream 0).toNat
    (Nat.ofDigits (2 ^ w) ((List.range count).map fun i => (stream (i + 1)).toNat),
      fun i => stream (i + count + 1))

/-- Word RAM with every operation. -/
def WordRAM.standard (w : ℕ) :=
  wordRAM w [.add, .sub, .mul, .div, .mod, .less, .and, .or, .xor, .shiftLeft, .shiftRight]

end Formalgo
