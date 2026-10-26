import Formalgo.Core.IOSpec
import Formalgo.Core.Run

/-!
# Algorithms
A program, and a tape coding of inputs and outputs on the tape.
Semantics are given separately, so an algorithm can be run with different ones (e.g. word sizes).
Time and space bounds (per-input) are also defined
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

namespace Algorithm

/-- Run `algorithm` with `semantics` on `input` for `steps` steps. -/
def run {PC Instruction Outcome Address Value Input Output : Type*} [Fintype PC] [Fintype Outcome]
    (algorithm : Algorithm PC Instruction Outcome Address Value Input Output)
    (semantics : Semantics Instruction Outcome Address Value) (input : Input) (steps : ℕ) :
    Status (Program.State PC Address Value) :=
  algorithm.program.run semantics steps
    ⟨algorithm.program.init, algorithm.tapeCoding.encode input⟩

/-- `algorithm` with `semantics` halts on `input` with `output`. -/
def Outputs {PC Instruction Outcome Address Value Input Output : Type*} [Fintype PC]
    [Fintype Outcome] (algorithm : Algorithm PC Instruction Outcome Address Value Input Output)
    (semantics : Semantics Instruction Outcome Address Value) (input : Input) (output : Output) :
    Prop :=
  ∃ steps state, algorithm.run semantics input steps = .halted state ∧
    algorithm.tapeCoding.decode state.tape = output

/-- On every input, `algorithm` with `semantics` halts with a valid output. -/
def Solves {PC Instruction Outcome Address Value Input Output : Type*} [Fintype PC]
    [Fintype Outcome] (algorithm : Algorithm PC Instruction Outcome Address Value Input Output)
    (semantics : Semantics Instruction Outcome Address Value) (spec : IOSpec Input Output) :
    Prop :=
  ∀ input, ∃ output, algorithm.Outputs semantics input output ∧ spec.valid input output

/-- `algorithm` with `semantics` halts on `input` within `steps` steps. -/
def HaltsWithin {PC Instruction Outcome Address Value Input Output : Type*} [Fintype PC]
    [Fintype Outcome] (algorithm : Algorithm PC Instruction Outcome Address Value Input Output)
    (semantics : Semantics Instruction Outcome Address Value) (input : Input) (steps : ℕ) :
    Prop :=
  ∃ state, algorithm.run semantics input steps = .halted state

/-- Every tape of `algorithm` with `semantics` on `input` has size at most `bound`, where `size`
measures the space a tape uses. -/
def SpaceWithin {PC Instruction Outcome Address Value Input Output : Type*} [Fintype PC]
    [Fintype Outcome] (algorithm : Algorithm PC Instruction Outcome Address Value Input Output)
    (semantics : Semantics Instruction Outcome Address Value) (size : Tape Address Value → ℕ)
    (input : Input) (bound : ℕ) : Prop :=
  ∀ steps, match algorithm.run semantics input steps with
    | .running state | .halted state => size state.tape ≤ bound

end Algorithm

end Formalgo
