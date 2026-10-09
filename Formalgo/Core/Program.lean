import Formalgo.Core.ControlFlow
import Formalgo.Core.Machine
import Formalgo.Core.Tape

/-!
# Instruction sets
This is an abstraction layer for different kinds of taped machines
-/

namespace Formalgo

/-- Valid instructions that can affect the tape. -/
structure InstructionSet (Instruction Outcome Index Value : Type*) where
  /-- Execute an instruction: its outcome (`none` halts) and the new tape.
  This explicitly does not provide the new PC (program counter) value. -/
  exec : Instruction → Tape Index Value → Option Outcome × Tape Index Value

namespace InstructionSet

/-- State of a running program. -/
structure State (PC Index Value : Type*) where
  /-- Current PC value. -/
  pc : PC
  /-- Current tape. -/
  tape : Tape Index Value

/-- A program for `instructionSet`: control flow with an instruction for each valid PC value. -/
structure Program {Instruction Outcome Index Value : Type*} [Fintype Outcome]
    (instructionSet : InstructionSet Instruction Outcome Index Value) (PC : Type*) [Fintype PC]
    extends ControlFlow PC Outcome where
  /-- Instruction at a given PC value. -/
  instruction : PC → Instruction

/-- The machine running `program`. -/
def Program.machine {Instruction Outcome Index Value : Type*} [Fintype Outcome]
    {instructionSet : InstructionSet Instruction Outcome Index Value}
    {PC : Type*} [Fintype PC] (program : Program instructionSet PC) :
    Machine (State PC Index Value) where
  step state := match instructionSet.exec (program.instruction state.pc) state.tape with
    | (none, tape) => .halted ⟨state.pc, tape⟩
    | (some outcome, tape) => .running ⟨program.next state.pc outcome, tape⟩

end InstructionSet

end Formalgo
