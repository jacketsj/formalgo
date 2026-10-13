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

/-- A RAM: which words are addresses, and the semantics of its additional instructions. -/
structure RAM (Address Word : Type) (Extension : Type*) where
  /-- The address a word denotes, if any. -/
  toAddress? : Word → Option Address
  /-- The additional instructions. -/
  extension : Semantics Extension Bool Address Word

namespace RAM

/-- The semantics of `ram`.
If a test has outcome `false`, nothing changes.
All non-test outcomes are `true`. -/
def semantics {Address Word : Type} {Extension : Type*} [DecidableEq Address]
    (ram : RAM Address Word Extension) :
    Semantics (Instruction Address Word Extension) Bool Address Word where
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

/-- Macro for programs of a given RAM specialization. -/
abbrev Program {Address Word : Type} {Extension : Type*} (_ : RAM Address Word Extension)
    (PC : Type*) [Fintype PC] :=
  Formalgo.Program PC (Instruction Address Word Extension) Bool

/-! ### Arithmetic
Generic extension templates for arithmetic operations, independent of Word type
-/

/-- Arithmetic instructions, with binary operations `Operation`. -/
inductive Arithmetic (Address Operation : Type*) where
  /-- `M[destination] := operation M[left] M[right]` -/
  | apply (operation : Operation) (destination left right : Address)
  /-- Test `M[left] = M[right]`. -/
  | equal (left right : Address)

/-- Arithmetic instructions with generic `eval` implementation. -/
def arithmetic {Address Word Operation : Type*} [DecidableEq Address] [DecidableEq Word]
    (eval : Operation → Word → Word → Word) :
    Semantics (Arithmetic Address Operation) Bool Address Word where
  exec instruction memory := match instruction with
    | .apply operation destination left right =>
      (some true, memory.write destination (eval operation (memory.read left) (memory.read right)))
    | .equal left right => (some (memory.read left = memory.read right), memory)

end RAM

end Formalgo
