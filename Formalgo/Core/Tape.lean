import Mathlib.Tactic.TypeStar

/-!
# Tapes
These are more general than standard defininitions of 'Tapes',
and can be used to represent arbitrary memory systems
-/

namespace Formalgo

/-- A memory with a cell for each address. -/
structure Tape (Address Value : Type*) where
  /-- The value at a given cell address. -/
  read : Address → Value

namespace Tape

variable {Address Value : Type*}

/-- Overwrite one cell. -/
def write [DecidableEq Address] (tape : Tape Address Value) (address : Address) (value : Value) :
    Tape Address Value :=
  ⟨fun i => if i = address then value else tape.read i⟩

end Tape

end Formalgo
