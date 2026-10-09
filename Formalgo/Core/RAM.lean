import Formalgo.Core.Program

/-!
# Generic random-access machine (RAM)
These are machines with instruction sets whose tape is a memory
`M[address]` of 'words' of a given type.
This generic RAM can be extended with additional instructions and specific types of Words
-/

namespace Formalgo

/-! ### Instructions -/

/-- RAM instructions, with additional instructions `Extension`. -/
inductive RAM.Instruction (Address Word : Type) (Extension : Type*) where
  /-- `M[destination] := value` -/
  | const (destination : Address) (value : Word)
  /-- `M[destination] := M[source]` -/
  | copy (destination source : Address)
  /-- `M[destination] := M[M[pointer]]`, testing that `M[pointer]` is an address. -/
  | load (destination pointer : Address)
  /-- `M[M[pointer]] := M[source]`, testing that `M[pointer]` is an address. -/
  | store (pointer source : Address)
  /-- Halt. -/
  | halt
  /-- An additional instruction (for instantiations of generic RAM). -/
  | extension (instruction : Extension)

/-! ### RAMs -/

/-- A RAM: which words are addresses, and the extended instruction set. -/
structure RAM (Address Word : Type) (Extension : Type*) where
  /-- The address a word denotes, if any. -/
  toAddress? : Word → Option Address
  /-- The additional instructions. -/
  extension : InstructionSet Extension Bool Address Word

namespace RAM

/-- The instruction set implementation of `ram`.
If a test has outcome `false`, nothing changes.
All non-test outcomes are `true`. -/
def instructionSet {Address Word : Type} {Extension : Type*} [DecidableEq Address]
    (ram : RAM Address Word Extension) :
    InstructionSet (Instruction Address Word Extension) Bool Address Word where
  exec instruction memory := match instruction with
    | .const destination value => (some true, memory.write destination value)
    | .copy destination source => (some true, memory.write destination (memory.read source))
    | .load destination pointer => match ram.toAddress? (memory.read pointer) with
      | some address => (some true, memory.write destination (memory.read address))
      | none => (some false, memory)
    | .store pointer source => match ram.toAddress? (memory.read pointer) with
      | some address => (some true, memory.write address (memory.read source))
      | none => (some false, memory)
    | .halt => (none, memory)
    | .extension instruction => ram.extension.exec instruction memory

/-- Macro for `ram` program. -/
abbrev Program {Address Word : Type} {Extension : Type*} [DecidableEq Address]
    (ram : RAM Address Word Extension) (PC : Type*) [Fintype PC] :=
  ram.instructionSet.Program PC

end RAM

end Formalgo
