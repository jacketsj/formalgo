import Formalgo.Core.Code

/-!
# Transdichotomous (TD) algorithms
Programs for one word size, run at a word size selected from the input.
-/

namespace Formalgo

/-- A machine for each word size `w`. -/
structure TDMachine (Instruction Address Value : ℕ → Type*) where
  /-- The semantics with words of `w` bits. -/
  semantics (w : ℕ) : Semantics (Instruction w) Bool (Address w) (Value w)
  /-- Lift an instruction to a larger word size. -/
  lift {w w' : ℕ} : w ≤ w' → Instruction w → Instruction w'

/-- A TD algorithm. -/
structure TDAlgorithm (Instruction : ℕ → Type*) (PC Input Output : Type*) [Fintype PC] where
  /-- The word size of the program. -/
  width : ℕ
  /-- The program. -/
  program : Program PC (Instruction width) Bool
  /-- The word size, as a multiple of the bits of the input. -/
  scale : ℕ

namespace TDAlgorithm

variable {Instruction Address Value : ℕ → Type*} {PC Input Output : Type*} [Fintype PC]
  [Code Input ℕ] [∀ w, NatCast (Address w)] [∀ w, DecidableEq (Address w)]
  [∀ w, Inhabited (Value w)] [∀ w, Code ℕ (Value w)] [∀ w, Code Input (Value w)]
  [∀ w, Code Output (Value w)] (algorithm : TDAlgorithm Instruction PC Input Output)

/-- The word size for `input`. -/
def wordSize (input : Input) : ℕ :=
  let code : List ℕ := Code.encode input
  algorithm.width ⊔ algorithm.scale * (Nat.log 2 (code.foldr max code.length) + 1)

/-- `algorithm` with words of `w` bits, with `w` written before the input. -/
def atWordSize (machine : TDMachine Instruction Address Value) (w : ℕ) (h : algorithm.width ≤ w) :
    Algorithm PC (Instruction w) Bool (Address w) (Value w) (ℕ × Input) Output where
  program := algorithm.program.map (machine.lift h)
  tapeCoding := .standard

/-- A TD algorithm runs at the word size for each input. -/
instance : Runnable (TDAlgorithm Instruction PC Input Output) (TDMachine Instruction Address Value)
    Input Output (Σ w, Program.State PC (Address w) (Value w)) where
  run algorithm machine := {
    status input steps := let w := algorithm.wordSize input
      let atWordSize := algorithm.atWordSize machine w le_sup_left
      ((Runnable.run atWordSize (machine.semantics w)).status (w, input) steps).map (⟨w, ·⟩)
    output state := (TapeCoding.standard (Input := ℕ × Input)).decode state.2.tape }

end TDAlgorithm

/-- Some TD algorithm solves `spec` within `time input` steps on each input. -/
def TDMachine.SolvableWithin {Instruction Address Value : ℕ → Type*} {Input Output : Type*}
    [Code Input ℕ] [∀ w, NatCast (Address w)] [∀ w, DecidableEq (Address w)]
    [∀ w, Inhabited (Value w)] [∀ w, Code ℕ (Value w)] [∀ w, Code Input (Value w)]
    [∀ w, Code Output (Value w)] (machine : TDMachine Instruction Address Value)
    (spec : IOSpec Input Output) (time : Input → ℕ) : Prop :=
  ∃ (PC : Type) (_ : Fintype PC) (algorithm : TDAlgorithm Instruction PC Input Output),
    Solves algorithm machine spec ∧ ∀ input, HaltsWithin algorithm machine input (time input)

end Formalgo
