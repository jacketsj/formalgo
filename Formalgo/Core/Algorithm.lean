import Formalgo.Core.Code
import Formalgo.Core.Runnable

/-!
# Algorithms
A program, and a tape coding of inputs and outputs on the tape.
Semantics are given separately, so an algorithm can be run with different ones (e.g. word sizes).
-/

namespace Formalgo

/-- An algorithm: a program, and a tape coding of inputs and outputs. -/
structure Algorithm (PC Instruction Outcome Address Value Input Output : Type*) [Fintype PC]
    [Fintype Outcome] where
  /-- The program. -/
  program : Program PC Instruction Outcome
  /-- The tape coding of inputs and outputs. -/
  tapeCoding : TapeCoding Input Output Address Value

/-- An algorithm runs with semantics. -/
instance {PC Instruction Outcome Address Value Input Output : Type*} [Fintype PC]
    [Fintype Outcome] :
    Runnable (Algorithm PC Instruction Outcome Address Value Input Output)
      (Semantics Instruction Outcome Address Value) Input Output (Program.State PC Address Value)
    where
  run algorithm semantics := {
    status input steps := algorithm.program.run semantics steps
      ⟨algorithm.program.init, algorithm.tapeCoding.encode input⟩
    output state := algorithm.tapeCoding.decode state.tape }

/-- Some program solves `spec` within `time input` steps on each input, with the standard tape
coding. -/
def Semantics.SolvableWithin {Instruction Outcome Address Value Input Output : Type*}
    [Fintype Outcome] [NatCast Address] [DecidableEq Address] [Inhabited Value] [Code Input Value]
    [Code Output Value] (semantics : Semantics Instruction Outcome Address Value)
    (spec : IOSpec Input Output) (time : Input → ℕ) : Prop :=
  ∃ (PC : Type) (_ : Fintype PC) (program : Program PC Instruction Outcome),
    let algorithm : Algorithm PC Instruction Outcome Address Value Input Output :=
      ⟨program, .standard⟩
    Solves algorithm semantics spec ∧
      ∀ input, HaltsWithin algorithm semantics input (time input)

end Formalgo
