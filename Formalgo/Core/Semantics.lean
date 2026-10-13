import Formalgo.Core.Tape

/-!
# Semantics
-/

namespace Formalgo

/-- The effect of each instruction on the tape. -/
structure Semantics (Instruction Outcome Address Value : Type*) where
  /-- Execute an instruction: its outcome (`none` halts) and the new tape. -/
  exec : Instruction → Tape Address Value → Option Outcome × Tape Address Value

end Formalgo
