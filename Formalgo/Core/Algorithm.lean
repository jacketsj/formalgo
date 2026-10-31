import Formalgo.Core.Runnable

/-!
# Algorithms
A program, and a tape coding of inputs and outputs on the tape.
Semantics are given separately, so an algorithm can be run with different ones (e.g. word sizes).
-/

namespace Formalgo

/-- How inputs are written to a tape, and how outputs are read from it. -/
structure TapeCoding (Input Output Address Value : Type*) where
  /-- The tape holding an input. -/
  encode : Input → Tape Address Value
  /-- The output held by a tape. Note that the tape could also contain other things. -/
  decode : Tape Address Value → Output

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

end Formalgo
