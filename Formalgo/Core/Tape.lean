import Mathlib.Tactic.TypeStar

/-!
# Tapes
These are more general than standard definitions of 'Tapes',
and can be used to represent arbitrary memory systems
-/

namespace Formalgo

/-- A memory with a cell for each address. -/
structure Tape (Address Value : Type*) where
  /-- The value at a given cell address. -/
  read : Address → Value

/-- Overwrite one cell. -/
def Tape.write {Address Value : Type*} [DecidableEq Address] (tape : Tape Address Value)
    (address : Address) (value : Value) : Tape Address Value :=
  ⟨fun i => if i = address then value else tape.read i⟩

end Formalgo
