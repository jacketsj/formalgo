import Formalgo.Core.IOSpec
import Formalgo.Core.Run

/-!
# Runnable algorithms
Outputs, and time and space bounds (per-input), for any kind of algorithm that can be run.
-/

namespace Formalgo

/-- The status on each input after each number of steps, and the output of each state. -/
structure ExecutionTrace (Input Output State : Type*) where
  /-- The status on `input` after `steps` steps. -/
  status : Input → ℕ → Status State
  /-- The output of a state. -/
  output : State → Output

/-- Algorithms of type `A`, run with machines of type `Machine`. -/
class Runnable (A Machine : Type*) (Input Output State : outParam Type*) where
  /-- The execution trace of `algorithm` with `machine`. -/
  run (algorithm : A) (machine : Machine) : ExecutionTrace Input Output State

export Runnable (run)

variable {A Machine Input Output State : Type*} [Runnable A Machine Input Output State]

/-- `algorithm` with `machine` halts on `input` with `output`. -/
def Outputs (algorithm : A) (machine : Machine) (input : Input) (output : Output) : Prop :=
  ∃ steps state, (run algorithm machine).status input steps = .halted state ∧
    (run algorithm machine).output state = output

/-- `algorithm` with `machine` halts on every input with a valid output. -/
def Solves (algorithm : A) (machine : Machine) (spec : IOSpec Input Output) : Prop :=
  ∀ input, ∃ output, Outputs algorithm machine input output ∧ spec.valid input output

/-- `algorithm` with `machine` halts on `input` within `steps` steps. -/
def HaltsWithin (algorithm : A) (machine : Machine) (input : Input) (steps : ℕ) : Prop :=
  ∃ state, (run algorithm machine).status input steps = .halted state

/-- Every state of `algorithm` with `machine` on `input` has `size` at most `bound`. -/
def SpaceWithin (algorithm : A) (machine : Machine) (size : State → ℕ) (input : Input)
    (bound : ℕ) : Prop :=
  ∀ steps, match (run algorithm machine).status input steps with
    | .running state | .halted state => size state ≤ bound

end Formalgo
