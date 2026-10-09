import Mathlib.Tactic.TypeStar

/-!
# Tapes
These are more general than standard defininitions of 'Tapes',
and can be used to represent arbitrary memory systems
-/

namespace Formalgo

/-- A memory with a cell for each index. -/
structure Tape (Index Value : Type*) where
  /-- The value at a given cell index. -/
  read : Index → Value

namespace Tape

variable {Index Value : Type*}

/-- Overwrite one cell. -/
def write [DecidableEq Index] (tape : Tape Index Value) (index : Index) (value : Value) :
    Tape Index Value :=
  ⟨fun i => if i = index then value else tape.read i⟩

end Tape

end Formalgo
