import Mathlib.Data.Nat.Notation
import Formalgo.Core.Program
import Formalgo.Core.Semantics

/-!
# Runs
-/

namespace Formalgo

/-- State of a running program. -/
structure Program.State (PC Address Value : Type*) where
  /-- Current PC value. -/
  pc : PC
  /-- Current tape. -/
  tape : Tape Address Value

/-- The status of a computation, with the current state. -/
inductive Status (State : Type*) where
  /-- The computation continues from `state`. -/
  | running (state : State)
  /-- The computation completed in `state`. -/
  | halted (state : State)

/-- Map the state of a status. -/
def Status.map {State State' : Type*} (f : State → State') : Status State → Status State'
  | .running state => .running (f state)
  | .halted state => .halted (f state)

/-- Execute one instruction of `program` with `semantics`. -/
def Program.step {PC Instruction Outcome Address Value : Type*} [Fintype PC] [Fintype Outcome]
    (program : Program PC Instruction Outcome)
    (semantics : Semantics Instruction Outcome Address Value)
    (state : Program.State PC Address Value) : Status (Program.State PC Address Value) :=
  match semantics.exec (program.instruction state.pc) state.tape with
  | (none, tape) => .halted ⟨state.pc, tape⟩
  | (some outcome, tape) => .running ⟨program.next state.pc outcome, tape⟩

/-- Run `program` with `semantics` for `steps` steps, or until it halts. -/
def Program.run {PC Instruction Outcome Address Value : Type*} [Fintype PC] [Fintype Outcome]
    (program : Program PC Instruction Outcome)
    (semantics : Semantics Instruction Outcome Address Value) :
    ℕ → Program.State PC Address Value → Status (Program.State PC Address Value)
  | 0, state => .running state
  | steps + 1, state => match program.step semantics state with
    | .running next => program.run semantics steps next
    | .halted final => .halted final

end Formalgo
