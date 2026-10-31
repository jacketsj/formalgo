import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log
import Formalgo.Core.Algorithm

/-!
# Codes
Model-agnostic ways to write data as a sequence of values, and read it back.
-/

namespace Formalgo

/-- A way to write `α` as a sequence of values, and read it back from the start of a stream. -/
class Code (α Value : Type*) where
  /-- The values representing `a`. -/
  encode : α → List Value
  /-- The element at the start of a stream, and the rest of the stream. -/
  decode : (ℕ → Value) → α × (ℕ → Value)

namespace Code

variable {α β Value : Type*}

/-- A value is written as itself. -/
instance value : Code Value Value where
  encode value := [value]
  decode stream := (stream 0, fun i => stream (i + 1))

/-- A pair is written as its first component, then its second. -/
instance prod [Code α Value] [Code β Value] : Code (α × β) Value where
  encode pair := encode pair.1 ++ encode pair.2
  decode stream :=
    let (a, stream) : α × _ := decode stream
    let (b, stream) : β × _ := decode stream
    ((a, b), stream)

/-- Read `n` elements from the start of a stream. -/
def decodeMany [Code α Value] : ℕ → (ℕ → Value) → List α × (ℕ → Value)
  | 0, stream => ([], stream)
  | n + 1, stream =>
    let (a, stream) : α × _ := decode stream
    let (rest, stream) := decodeMany n stream
    (a :: rest, stream)

/-- A list is written as its length, then its elements. -/
instance list [Code ℕ Value] [Code α Value] : Code (List α) Value where
  encode list := encode list.length ++ list.flatMap encode
  decode stream :=
    let (n, stream) : ℕ × _ := decode stream
    decodeMany n stream

/-- A natural number is written in base `base`, least significant digit first. Each digit is
preceded by `true`, meaning "a digit follows", and the end by `false`. -/
@[reducible] noncomputable def digits (base : ℕ) [NeZero base] [Code Bool Value]
    [Code (Fin base) Value] : Code ℕ Value where
  encode n := ((List.range (Nat.log base n + 1)).flatMap
    fun i => encode true ++ encode (Fin.ofNat base (n / base ^ i))) ++ encode false
  decode stream :=
    -- The first `k` digits, each with the `true` before it, and the stream after them.
    let digits (k : ℕ) := decodeMany (α := Bool × Fin base) k stream
    -- Whether another digit follows the first `k`.
    let follows (k : ℕ) : Bool := (decode (α := Bool) (digits k).2).1
    -- The number of digits: the first `k` not followed by another digit.
    let count := open Classical in if h : ∃ k, follows k = false then Nat.find h else 0
    let (pairs, rest) := digits count
    let n := (pairs.map (·.2)).foldr (fun digit n => base * n + digit) 0
    -- Skip the final `false`.
    (n, (decode (α := Bool) rest).2)

/-- A natural number is written in binary, on any tape with a code for bits. -/
noncomputable instance (priority := low) nat [Code Bool Value] : Code ℕ Value :=
  letI : Code (Fin 2) Value :=
    ⟨fun digit => encode (digit = 1 : Bool), fun stream =>
      let (bit, stream) : Bool × _ := decode stream
      (if bit then 1 else 0, stream)⟩
  digits 2

/-- `nat`, specialized to integer tapes: a natural number is written as a single integer. -/
instance singleIntCell : Code ℕ ℤ where
  encode n := [n]
  decode stream := ((stream 0).toNat, fun i => stream (i + 1))

end Code

/-- The standard tape coding: the input is written from cell `0`, followed by blanks (`default`),
and the output is read from just after the input. -/
def TapeCoding.standard {Input Output Address Value : Type*} [Code Input Value] [Code Output Value]
    [NatCast Address] [DecidableEq Address] [Inhabited Value] :
    TapeCoding Input Output Address Value where
  encode input := (Code.encode input).zipIdx.foldr (fun (value, i) tape => tape.write i value)
    ⟨fun _ => default⟩
  decode tape := (Code.decode (Code.decode (α := Input) fun i => tape.read i).2).1

end Formalgo
