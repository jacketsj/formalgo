import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Formalgo.Core.TDWordRAM
import Formalgo.Core.Code
import Formalgo.Algorithms.Sorting.Statement

/-!
# Proof that a TD word RAM sorts in `O(n log n)` steps

LLM-generated; not checked by a human.

A small language of structured commands with exact costs, compiled to word RAM programs and
proved correct against the TD word RAM; a harness and input/output loops for list problems; and
bottom-up merge sort in that language, with its correctness and step bound.
-/

section

/-!
## Structured commands for the word RAM


Commands over a memory of natural numbers, compiled to word RAM programs. `Exec` gives their
meaning with exact costs, and `Exec.run` shows that compiled programs follow it.
-/

namespace Formalgo.LLMUnchecked

/-- The operations used. -/
abbrev ops : List WordRAM.Operation := [.less, .add, .sub]

/-- An operation used. -/
abbrev Op := {operation // operation ∈ ops}

/-- Instructions over natural numbers. -/
abbrev NInstr := RAM.Instruction ℕ ℕ (RAM.Arithmetic ℕ Op)

/-- Instructions with `w`-bit words. -/
abbrev WInstr (w : ℕ) := RAM.Instruction (BitVec w) (BitVec w) (RAM.Arithmetic (BitVec w) Op)

/-- An instruction over natural numbers, with `w`-bit words. -/
def NInstr.toWord (w : ℕ) (instruction : NInstr) : WInstr w :=
  instruction.map (BitVec.ofNat w) (BitVec.ofNat w) (RAM.Arithmetic.map (BitVec.ofNat w))

/-- A line of code: an instruction, and the next line for each outcome. -/
structure Line where
  /-- The instruction. -/
  instr : NInstr
  /-- The next line if the outcome is `true`. -/
  onTrue : ℕ
  /-- The next line if the outcome is `false`. -/
  onFalse : ℕ

/-- A memory of natural numbers. -/
abbrev Mem := ℕ → ℕ

/-- Structured commands. -/
inductive Cmd
  | const (d v : ℕ)
  | copy (d s : ℕ)
  | load (d p : ℕ)
  | store (p s : ℕ)
  | add (d l r : ℕ)
  | sub (d l r : ℕ)
  | less (d l r : ℕ)
  | seq (a b : Cmd)
  /-- If `M[l] = M[r]`. -/
  | ite (l r : ℕ) (t e : Cmd)
  /-- While `M[l] = M[r]`. -/
  | loop (l r : ℕ) (body : Cmd)

namespace Cmd

/-- Addition. -/
def addOp : Op := ⟨.add, by simp [ops]⟩
/-- Subtraction. -/
def subOp : Op := ⟨.sub, by simp [ops]⟩
/-- Comparison. -/
def lessOp : Op := ⟨.less, by simp [ops]⟩

/-- A line that jumps to `target`. -/
def jump (target : ℕ) : Line := ⟨.extension (.equal 0 0), target, target⟩

/-- The number of lines of a command. -/
def size : Cmd → ℕ
  | seq a b => a.size + b.size
  | ite _ _ t e => t.size + e.size + 2
  | loop _ _ body => body.size + 2
  | _ => 1

/-- The lines of a command starting at line `s`. -/
def compile : Cmd → ℕ → List Line
  | const d v, s => [⟨.const d v, s + 1, s + 1⟩]
  | copy d x, s => [⟨.copy d x, s + 1, s + 1⟩]
  | load d p, s => [⟨.load d p, s + 1, s + 1⟩]
  | store p x, s => [⟨.store p x, s + 1, s + 1⟩]
  | add d l r, s => [⟨.extension (.apply addOp d l r), s + 1, s + 1⟩]
  | sub d l r, s => [⟨.extension (.apply subOp d l r), s + 1, s + 1⟩]
  | less d l r, s => [⟨.extension (.apply lessOp d l r), s + 1, s + 1⟩]
  | seq a b, s => a.compile s ++ b.compile (s + a.size)
  | ite l r t e, s => ⟨.extension (.equal l r), s + 1, s + t.size + 2⟩ ::
      (t.compile (s + 1) ++ jump (s + t.size + e.size + 2) :: e.compile (s + t.size + 2))
  | loop l r body, s => ⟨.extension (.equal l r), s + 1, s + body.size + 2⟩ ::
      (body.compile (s + 1) ++ [jump s])

theorem length_compile (c : Cmd) (s : ℕ) : (c.compile s).length = c.size := by
  induction c generalizing s <;> simp_all [compile, size]; omega

/-- The lines of a closed program: the command, then `halt`. -/
def lines (c : Cmd) : List Line := c.compile 0 ++ [⟨.halt, 0, 0⟩]

theorem length_lines (c : Cmd) : c.lines.length = c.size + 1 := by
  simp [lines, length_compile]

end Cmd

/-! ### Programs -/

/-- The program running `lines` with `w`-bit words. -/
def linesProgram (w : ℕ) (lines : List Line) (h : 0 < lines.length) :
    Program (Fin lines.length) (WInstr w) Bool where
  init := ⟨0, h⟩
  next pc outcome :=
    ⟨(if outcome then lines[pc].onTrue else lines[pc].onFalse) % lines.length, Nat.mod_lt _ h⟩
  instruction pc := lines[pc].instr.toWord w

/-- The word RAM semantics with the operations used. -/
abbrev sem (w : ℕ) := (wordRAM w ops).semantics

/-- A memory of natural numbers agrees with a tape of `w`-bit words. -/
def Corr {w : ℕ} (m : Mem) (T : Tape (BitVec w) (BitVec w)) : Prop :=
  ∀ a : BitVec w, (T.read a).toNat = m a.toNat

/-- `ls` sits in `lines` from line `s`. -/
def At (lines : List Line) (s : ℕ) (ls : List Line) : Prop :=
  ∀ i < ls.length, lines[s + i]? = ls[i]?

/-- Big-step semantics of commands, with exact costs, for words below `B`. -/
inductive Exec (B : ℕ) : Cmd → Mem → ℕ → Mem → Prop
  | const {m d v} : d < B → v < B → Exec B (.const d v) m 1 (Function.update m d v)
  | copy {m d s} : d < B → s < B → Exec B (.copy d s) m 1 (Function.update m d (m s))
  | load {m d p} : d < B → p < B → Exec B (.load d p) m 1 (Function.update m d (m (m p)))
  | store {m p s} : p < B → s < B → Exec B (.store p s) m 1 (Function.update m (m p) (m s))
  | add {m d l r} : d < B → l < B → r < B → m l + m r < B →
      Exec B (.add d l r) m 1 (Function.update m d (m l + m r))
  | sub {m d l r} : d < B → l < B → r < B → m r ≤ m l →
      Exec B (.sub d l r) m 1 (Function.update m d (m l - m r))
  | less {m d l r} : d < B → l < B → r < B →
      Exec B (.less d l r) m 1 (Function.update m d (if m l < m r then 1 else 0))
  | seq {a b m k₁ m₁ k₂ m₂} : Exec B a m k₁ m₁ → Exec B b m₁ k₂ m₂ →
      Exec B (.seq a b) m (k₁ + k₂) m₂
  | iteTrue {l r t e m k m'} : l < B → r < B → m l = m r → Exec B t m k m' →
      Exec B (.ite l r t e) m (k + 2) m'
  | iteFalse {l r t e m k m'} : l < B → r < B → m l ≠ m r → Exec B e m k m' →
      Exec B (.ite l r t e) m (k + 1) m'
  | loopTrue {l r body m k₁ m₁ k₂ m₂} : l < B → r < B → m l = m r → Exec B body m k₁ m₁ →
      Exec B (.loop l r body) m₁ k₂ m₂ → Exec B (.loop l r body) m (k₁ + k₂ + 2) m₂
  | loopFalse {l r body m} : l < B → r < B → m l ≠ m r → Exec B (.loop l r body) m 1 m

/-! ### Runs -/

section Run

variable {PC Instruction Address Value : Type*} [Fintype PC]
  {program : Program PC Instruction Bool} {semantics : Semantics Instruction Bool Address Value}

theorem run_succ_of_step {k : ℕ} {state state' : Program.State PC Address Value}
    (h : program.step semantics state = .running state') :
    program.run semantics (k + 1) state = program.run semantics k state' := by
  simp [Program.run, h]

theorem run_add_of_running {a b : ℕ} {state state' : Program.State PC Address Value}
    (h : program.run semantics a state = .running state') :
    program.run semantics (a + b) state = program.run semantics b state' := by
  induction a generalizing state with
  | zero => simp_all [Program.run]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [Program.run] at h ⊢
    cases hs : program.step semantics state with
    | running next => rw [hs] at h; exact ih h
    | halted final => rw [hs] at h; simp at h

theorem run_halted_of_le {a b : ℕ} {state final : Program.State PC Address Value}
    (h : program.run semantics a state = .halted final) (hab : a ≤ b) :
    program.run semantics b state = .halted final := by
  induction a generalizing state b with
  | zero => simp [Program.run] at h
  | succ a ih =>
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    simp only [Program.run] at h ⊢
    cases hs : program.step semantics state with
    | running next => rw [hs] at h; exact ih h (by omega)
    | halted final' => rw [hs] at h; exact h

end Run

/-! ### Correspondence -/

section Corr

variable {w : ℕ} {m : Mem} {T : Tape (BitVec w) (BitVec w)}

theorem Corr.write (hT : Corr m T) {d v : ℕ} (hd : d < 2 ^ w) (x : BitVec w) (hx : x.toNat = v) :
    Corr (Function.update m d v) (T.write (BitVec.ofNat w d) x) := by
  intro a
  simp only [Tape.write, Function.update_apply]
  by_cases ha : a = BitVec.ofNat w d
  · subst ha; simp [hx, Nat.mod_eq_of_lt hd]
  · have : a.toNat ≠ d := by
      intro h; apply ha; apply BitVec.eq_of_toNat_eq; simp [h, Nat.mod_eq_of_lt hd]
    simp [ha, this, hT a]

theorem Corr.read (hT : Corr m T) {a : ℕ} (ha : a < 2 ^ w) :
    (T.read (BitVec.ofNat w a)).toNat = m a := by
  rw [hT]; simp [Nat.mod_eq_of_lt ha]

theorem Corr.lt (hT : Corr m T) {a : ℕ} (ha : a < 2 ^ w) : m a < 2 ^ w := by
  rw [← hT.read ha]; exact BitVec.isLt _

end Corr

/-! ### Compiled commands follow `Exec` -/

theorem At.append {lines : List Line} {s : ℕ} {a b : List Line} (h : At lines s (a ++ b)) :
    At lines s a ∧ At lines (s + a.length) b := by
  constructor
  · intro i hi
    have := h i (by simp; omega)
    rw [this, List.getElem?_append_left hi]
  · intro i hi
    have := h (a.length + i) (by simp; omega)
    rw [← Nat.add_assoc] at this
    rw [this, List.getElem?_append_right (by omega)]
    simp

theorem At.cons {lines : List Line} {s : ℕ} {x : Line} {b : List Line} (h : At lines s (x :: b)) :
    lines[s]? = some x ∧ At lines (s + 1) b := by
  constructor
  · simpa using h 0 (by simp)
  · intro i hi
    have := h (i + 1) (by simp; omega)
    rw [show s + (i + 1) = s + 1 + i by omega] at this
    simpa using this

section Exec

variable {w : ℕ} {lines : List Line} {hlines : 0 < lines.length}

/-- One step on a line holding a non-halting instruction. -/
theorem run_line {T T' : Tape (BitVec w) (BitVec w)} {pc : Fin lines.length} {line : Line}
    {s : ℕ} (hpc : pc.val = s) (hline : lines[s]? = some line) {outcome : Bool}
    (hexec : (sem w).exec (line.instr.toWord w) T = (some outcome, T')) {target : ℕ}
    (htarget : (if outcome then line.onTrue else line.onFalse) = target)
    (ht : target < lines.length) :
    (linesProgram w lines hlines).run (sem w) 1 ⟨pc, T⟩ = .running ⟨⟨target, ht⟩, T'⟩ := by
  subst hpc
  have hl : lines[pc.val] = line := by
    rw [List.getElem?_eq_getElem pc.isLt] at hline; exact Option.some.inj hline
  simp only [Program.run, Program.step, linesProgram, Fin.getElem_fin, hl, hexec]
  simp only [htarget, Nat.mod_eq_of_lt ht]

/-- One step on a line holding a primitive command. -/
theorem run_prim {T T' : Tape (BitVec w) (BitVec w)} {pc : Fin lines.length} {s : ℕ}
    {i : NInstr} (hpc : pc.val = s) (hline : lines[s]? = some ⟨i, s + 1, s + 1⟩)
    (hexec : (sem w).exec (i.toWord w) T = (some true, T')) (ht : s + 1 < lines.length) :
    (linesProgram w lines hlines).run (sem w) 1 ⟨pc, T⟩ = .running ⟨⟨s + 1, ht⟩, T'⟩ :=
  run_line hpc hline hexec (by simp) ht

theorem toNat_one_of_pos (hw : 0 < w) : (1 : BitVec w).toNat = 1 := BitVec.toNat_one hw

theorem exec_equal {T : Tape (BitVec w) (BitVec w)} {m : Mem} (hT : Corr m T) {l r : ℕ}
    (hl : l < 2 ^ w) (hr : r < 2 ^ w) :
    (sem w).exec ((Line.instr ⟨.extension (.equal l r), 0, 0⟩).toWord w) T =
      (some (decide (m l = m r)), T) := by
  simp [NInstr.toWord, RAM.Instruction.map, RAM.Arithmetic.map, RAM.semantics, wordRAM,
    RAM.arithmetic, BitVec.toNat_eq, hT.read hl, hT.read hr]

/-- A compiled command follows `Exec`. -/
theorem Exec.run (hw : 0 < w) {c : Cmd} {m : Mem} {k : ℕ} {m' : Mem}
    (hE : Exec (2 ^ w) c m k m') :
    ∀ {s : ℕ} (_hat : At lines s (c.compile s)) (hlen : s + c.size < lines.length)
      {T : Tape (BitVec w) (BitVec w)} (_hT : Corr m T) {pc : Fin lines.length} (_hpc : pc.val = s),
      ∃ T', (linesProgram w lines hlines).run (sem w) k ⟨pc, T⟩ =
        .running ⟨⟨s + c.size, hlen⟩, T'⟩ ∧ Corr m' T' := by
  have h2 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  induction hE with
  | @const m d v hd hv =>
    intro s hat hlen T hT pc hpc
    have hline := (hat.cons).1
    exact ⟨T.write (BitVec.ofNat w d) (BitVec.ofNat w v), run_prim hpc hline
      (by simp [NInstr.toWord, RAM.Instruction.map, RAM.semantics]) hlen,
      hT.write hd _ (by simp [Nat.mod_eq_of_lt hv])⟩
  | @copy m d x hd hx =>
    intro s hat hlen T hT pc hpc
    have hline := (hat.cons).1
    exact ⟨T.write (BitVec.ofNat w d) (T.read (BitVec.ofNat w x)), run_prim hpc hline
      (by simp [NInstr.toWord, RAM.Instruction.map, RAM.semantics]) hlen,
      hT.write hd _ (hT.read hx)⟩
  | @load m d p hd hp =>
    intro s hat hlen T hT pc hpc
    have hline := (hat.cons).1
    exact ⟨T.write (BitVec.ofNat w d) (T.read (T.read (BitVec.ofNat w p))), run_prim hpc hline
      (by simp [NInstr.toWord, RAM.Instruction.map, RAM.semantics, wordRAM]) hlen,
      hT.write hd _ (by rw [hT, hT.read hp])⟩
  | @store m p x hp hx =>
    intro s hat hlen T hT pc hpc
    have hline := (hat.cons).1
    refine ⟨T.write (T.read (BitVec.ofNat w p)) (T.read (BitVec.ofNat w x)), run_prim hpc hline
      (by simp [NInstr.toWord, RAM.Instruction.map, RAM.semantics, wordRAM]) hlen, ?_⟩
    have hmp := hT.read hp
    have hlt : m p < 2 ^ w := hT.lt hp
    have := hT.write hlt (T.read (BitVec.ofNat w x)) (hT.read hx)
    have he : BitVec.ofNat w (m p) = T.read (BitVec.ofNat w p) := by
      apply BitVec.eq_of_toNat_eq; simp [hmp, Nat.mod_eq_of_lt hlt]
    rwa [he] at this
  | @add m d l r hd hl hr hsum =>
    intro s hat hlen T hT pc hpc
    have hline := (hat.cons).1
    exact ⟨T.write (BitVec.ofNat w d) (T.read (BitVec.ofNat w l) + T.read (BitVec.ofNat w r)),
      run_prim hpc hline (by simp [NInstr.toWord, RAM.Instruction.map, RAM.Arithmetic.map,
      RAM.semantics, wordRAM, RAM.arithmetic, Cmd.addOp]) hlen,
      hT.write hd _ (by rw [BitVec.toNat_add, hT.read hl, hT.read hr, Nat.mod_eq_of_lt hsum])⟩
  | @sub m d l r hd hl hr hle =>
    intro s hat hlen T hT pc hpc
    have hline := (hat.cons).1
    refine ⟨T.write (BitVec.ofNat w d) (T.read (BitVec.ofNat w l) - T.read (BitVec.ofNat w r)),
      run_prim hpc hline (by simp [NInstr.toWord, RAM.Instruction.map, RAM.Arithmetic.map,
      RAM.semantics, wordRAM, RAM.arithmetic, Cmd.subOp]) hlen, hT.write hd _ ?_⟩
    have hl' := hT.lt hl
    rw [BitVec.toNat_sub, hT.read hl, hT.read hr,
      show 2 ^ w - m r + m l = (m l - m r) + 2 ^ w by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  | @less m d l r hd hl hr =>
    intro s hat hlen T hT pc hpc
    have hline := (hat.cons).1
    refine ⟨T.write (BitVec.ofNat w d)
      (if T.read (BitVec.ofNat w l) < T.read (BitVec.ofNat w r) then 1 else 0),
      run_prim hpc hline (by simp [NInstr.toWord, RAM.Instruction.map, RAM.Arithmetic.map,
      RAM.semantics, wordRAM, RAM.arithmetic, Cmd.lessOp]) hlen, hT.write hd _ ?_⟩
    simp only [BitVec.lt_def, hT.read hl, hT.read hr]
    split <;> simp [hw]
  | @seq a b m k₁ m₁ k₂ m₂ _ _ iha ihb =>
    intro s hat hlen T hT pc hpc
    obtain ⟨hata, hatb⟩ := At.append hat
    rw [Cmd.length_compile] at hatb
    simp only [Cmd.size] at hlen
    obtain ⟨T₁, h₁, hT₁⟩ := iha hata (by omega) hT hpc
    obtain ⟨T₂, h₂, hT₂⟩ := ihb hatb (by omega) hT₁ (pc := ⟨s + a.size, by omega⟩) rfl
    refine ⟨T₂, ?_, hT₂⟩
    rw [run_add_of_running h₁, h₂]
    simp [Cmd.size, Nat.add_assoc]
  | @iteTrue l r t e m k m' hl hr heq _ iht =>
    intro s hat hlen T hT pc hpc
    obtain ⟨htest, hrest⟩ := At.cons hat
    obtain ⟨hatt, hrest⟩ := At.append hrest
    obtain ⟨hjump, _⟩ := At.cons hrest
    rw [Cmd.length_compile] at hjump
    simp only [Cmd.size] at hlen
    have h0 := run_line (hlines := hlines) hpc htest (exec_equal hT hl hr) (target := s + 1)
      (by simp [heq]) (by omega)
    obtain ⟨T₁, h₁, hT₁⟩ := iht hatt (by omega) hT (pc := ⟨s + 1, by omega⟩) rfl
    have h₂ := run_line (hlines := hlines) (pc := ⟨s + 1 + t.size, by omega⟩) rfl hjump
      (exec_equal hT₁ (show 0 < 2 ^ w by omega) (show 0 < 2 ^ w by omega))
      (target := s + (t.size + e.size + 2)) (by simp [Cmd.jump]; omega) (by omega)
    refine ⟨T₁, ?_, hT₁⟩
    rw [show k + 2 = 1 + (k + 1) by omega, run_add_of_running h0, run_add_of_running h₁, h₂]
    rfl
  | @iteFalse l r t e m k m' hl hr hne _ ihe =>
    intro s hat hlen T hT pc hpc
    obtain ⟨htest, hrest⟩ := At.cons hat
    obtain ⟨_, hrest⟩ := At.append hrest
    obtain ⟨_, hate⟩ := At.cons hrest
    rw [Cmd.length_compile, show s + 1 + t.size + 1 = s + t.size + 2 by omega] at hate
    simp only [Cmd.size] at hlen
    have h0 := run_line (hlines := hlines) hpc htest (exec_equal hT hl hr) (target := s + t.size + 2)
      (by simp [hne]) (by omega)
    obtain ⟨T₁, h₁, hT₁⟩ := ihe hate (by omega) hT (pc := ⟨s + t.size + 2, by omega⟩) rfl
    refine ⟨T₁, ?_, hT₁⟩
    rw [show k + 1 = 1 + k by omega, run_add_of_running h0, h₁]
    simp [Cmd.size]; omega
  | @loopTrue l r body m k₁ m₁ k₂ m₂ hl hr heq _ _ ihb ihl =>
    intro s hat hlen T hT pc hpc
    have hat' := hat
    obtain ⟨htest, hrest⟩ := At.cons hat
    obtain ⟨hatb, hrest⟩ := At.append hrest
    obtain ⟨hjump, _⟩ := At.cons hrest
    rw [Cmd.length_compile] at hjump
    simp only [Cmd.size] at hlen
    have h0 := run_line (hlines := hlines) hpc htest (exec_equal hT hl hr) (target := s + 1)
      (by simp [heq]) (by omega)
    obtain ⟨T₁, h₁, hT₁⟩ := ihb hatb (by omega) hT (pc := ⟨s + 1, by omega⟩) rfl
    have h₂ := run_line (hlines := hlines) (pc := ⟨s + 1 + body.size, by omega⟩) rfl hjump
      (exec_equal hT₁ (show 0 < 2 ^ w by omega) (show 0 < 2 ^ w by omega))
      (target := s) (by simp [Cmd.jump]) (by omega)
    obtain ⟨T₂, h₃, hT₂⟩ := ihl hat' (by simpa [Cmd.size] using hlen) hT₁ (pc := ⟨s, by omega⟩) rfl
    refine ⟨T₂, ?_, hT₂⟩
    rw [show k₁ + k₂ + 2 = 1 + (k₁ + (1 + k₂)) by omega, run_add_of_running h0,
      run_add_of_running h₁, run_add_of_running h₂, h₃]
  | @loopFalse l r body m hl hr hne =>
    intro s hat hlen T hT pc hpc
    obtain ⟨htest, _⟩ := At.cons hat
    exact ⟨T, run_line (hlines := hlines) hpc htest (exec_equal hT hl hr)
      (by simp [hne, Cmd.size]; omega) hlen, hT⟩

end Exec

end Formalgo.LLMUnchecked

end

section

/-!
## Tapes of the word RAM


When every number fits in a word, the word RAM code of a value is its code over natural numbers
with each number `v` written as `[1, v, 0]`; decoding reads it back.
-/

namespace Formalgo.LLMUnchecked

open Code

/-- A number written as words: `[1, v, 0]`. -/
def triple (w v : ℕ) : List (BitVec w) := [1, BitVec.ofNat w v, 0]

/-- Numbers written as words. -/
def triples (w : ℕ) (l : List ℕ) : List (BitVec w) := l.flatMap (triple w)

@[simp] theorem length_triples (w : ℕ) (l : List ℕ) : (triples w l).length = 3 * l.length := by
  induction l <;> simp_all [triples, triple]; omega

/-! ### Decoding numbers in base `b` with markers -/

section Digits

variable {V : Type*} {b : ℕ} [cb : Code Bool V] [cf : Code (Fin b) V]
  {bit : V → Bool} {dig : V → Fin b}

theorem decode_pair (hb : ∀ s : ℕ → V, cb.decode s = (bit (s 0), fun i => s (i + 1)))
    (hf : ∀ s : ℕ → V, cf.decode s = (dig (s 0), fun i => s (i + 1))) (s : ℕ → V) :
    (Code.decode s : (Bool × Fin b) × (ℕ → V)) = ((bit (s 0), dig (s 1)), fun i => s (i + 2)) := by
  simp [Code.decode, hb, hf]

theorem decodeMany_pair (hb : ∀ s : ℕ → V, cb.decode s = (bit (s 0), fun i => s (i + 1)))
    (hf : ∀ s : ℕ → V, cf.decode s = (dig (s 0), fun i => s (i + 1))) (k : ℕ) (s : ℕ → V) :
    (Code.decodeMany (α := Bool × Fin b) k s).2 = fun i => s (i + 2 * k) := by
  induction k generalizing s with
  | zero => simp [Code.decodeMany]
  | succ k ih =>
    simp only [Code.decodeMany, decode_pair hb hf, ih]
    funext i; congr 1

theorem decode_digits_single [NeZero b] (hb : ∀ s : ℕ → V, cb.decode s = (bit (s 0), fun i => s (i + 1)))
    (hf : ∀ s : ℕ → V, cf.decode s = (dig (s 0), fun i => s (i + 1))) (s : ℕ → V)
    (h0 : bit (s 0) = true) (h2 : bit (s 2) = false) :
    (Code.digits b).decode s = ((dig (s 1)).val, fun i => s (i + 3)) := by
  have hstep : ∀ k, ((Code.decode (α := Bool) (Code.decodeMany (α := Bool × Fin b) k s).2).1) =
      bit (s (2 * k)) := by
    intro k; rw [decodeMany_pair hb hf, hb]; simp
  have hex : ∃ k, (Code.decode (α := Bool) (Code.decodeMany (α := Bool × Fin b) k s).2).1 =
      false := ⟨1, by rw [hstep]; simpa using h2⟩
  have hfind : Nat.find hex = 1 := by
    rw [Nat.find_eq_iff]
    refine ⟨by rw [hstep]; simpa using h2, fun n hn => ?_⟩
    obtain rfl : n = 0 := by omega
    rw [hstep]; simp [h0]
  unfold Code.digits
  simp only []
  rw [dif_pos hex, hfind]
  simp [Code.decodeMany, decode_pair hb hf, hb]

end Digits

/-! ### Numbers as words -/

section Word

variable {w : ℕ}

theorem one_ne_zero_bitVec (hw : 0 < w) : (1 : BitVec w) ≠ 0 := by
  intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_one hw] at this

theorem encode_nat_word (_hw : 0 < w) {v : ℕ} (hv : v < 2 ^ w) :
    (Code.encode v : List (BitVec w)) = triple w v := by
  have hlog : Nat.log (2 ^ w) v = 0 := Nat.log_eq_zero_iff.2 (.inl hv)
  simp [Code.encode, hlog, triple]

theorem decode_nat_word (hw : 0 < w) {v : ℕ} (hv : v < 2 ^ w) (s : ℕ → BitVec w)
    (h0 : s 0 = 1) (h1 : s 1 = BitVec.ofNat w v) (h2 : s 2 = 0) :
    (Code.decode s : ℕ × (ℕ → BitVec w)) = (v, fun i => s (i + 3)) := by
  have := decode_digits_single (V := BitVec w) (b := 2 ^ w)
    (cb := ⟨fun bit => [if bit then 1 else 0], fun stream => (stream 0 != 0, fun i => stream (i + 1))⟩)
    (cf := ⟨fun digit => [.ofFin digit], fun stream => ((stream 0).toFin, fun i => stream (i + 1))⟩)
    (bit := fun x => x != 0) (dig := BitVec.toFin) (fun _ => rfl) (fun _ => rfl) s
    (by simp [h0, Nat.pos_iff_ne_zero.1 hw]) (by simp [h2])
  refine this.trans ?_
  simp [h1, Nat.mod_eq_of_lt hv]

end Word

/-! ### Layout of codes -/

section Layout

variable {α β : Type*} [Code α ℕ] [∀ w, Code α (BitVec w)] [Code β ℕ] [∀ w, Code β (BitVec w)]

/-- The code of `x` over natural numbers. -/
def ncode (x : α) : List ℕ := Code.encode x

/-- The code of `x` with `w`-bit words. -/
def wcode (w : ℕ) (x : α) : List (BitVec w) := Code.encode x

theorem ncode_nat (v : ℕ) : ncode v = [v] := rfl
theorem ncode_prod (a : α) (b : β) : ncode (a, b) = ncode a ++ ncode b := rfl
theorem ncode_list (l : List α) : ncode l = l.length :: l.flatMap ncode := rfl
theorem wcode_prod (w : ℕ) (a : α) (b : β) : wcode w (a, b) = wcode w a ++ wcode w b := rfl
theorem wcode_list (w : ℕ) (l : List α) :
    wcode w l = wcode w l.length ++ l.flatMap (wcode w) := rfl

theorem decode_prod {V : Type*} [Code α V] [Code β V] (s : ℕ → V) :
    (Code.decode s : (α × β) × _) =
      (((Code.decode s : α × _).1, (Code.decode (Code.decode s : α × _).2 : β × _).1),
        (Code.decode (Code.decode s : α × _).2 : β × _).2) := rfl

theorem decode_list {V : Type*} [Code ℕ V] [Code α V] (s : ℕ → V) :
    (Code.decode s : List α × _) =
      Code.decodeMany (Code.decode s : ℕ × _).1 (Code.decode s : ℕ × _).2 := rfl

/-- Every number in the code of `x` is below `2 ^ w`. -/
def Fits (w : ℕ) (x : α) : Prop := ∀ v ∈ ncode x, v < 2 ^ w

/-- With `w`-bit words, `x` is written as its numbers, each as `[1, v, 0]`. -/
def Layout (x : α) : Prop := ∀ w, 0 < w → Fits w x → wcode w x = triples w (ncode x)

/-- `s` starts with `E`. -/
def StartsWith {V : Type*} (s : ℕ → V) (E : List V) : Prop := ∀ i (h : i < E.length), s i = E[i]

/-- Decoding a stream that starts with the word code of `x` gives `x`, and moves past it. -/
def ReadsBack (x : α) : Prop :=
  ∀ w, 0 < w → Fits w x → ∀ s : ℕ → BitVec w, StartsWith s (wcode w x) →
    (Code.decode s : α × _) = (x, fun i => s (i + (wcode w x).length))

/-- Decoding a stream that starts with the word code of `x` moves past it. -/
def Skips (x : α) : Prop :=
  ∀ w, 0 < w → Fits w x → ∀ s : ℕ → BitVec w, StartsWith s (wcode w x) →
    (Code.decode s : α × _).2 = fun i => s (i + (wcode w x).length)

theorem ReadsBack.skips {x : α} (h : ReadsBack x) : Skips x :=
  fun w hw hf s hs => by rw [h w hw hf s hs]

theorem triples_append (w : ℕ) (a b : List ℕ) : triples w (a ++ b) = triples w a ++ triples w b := by
  simp [triples]

theorem StartsWith.append_left {V : Type*} {s : ℕ → V} {a b : List V}
    (h : StartsWith s (a ++ b)) : StartsWith s a := fun i hi => by
  rw [h i (by simp; omega), List.getElem_append_left hi]

theorem StartsWith.append_right {V : Type*} {s : ℕ → V} {a b : List V}
    (h : StartsWith s (a ++ b)) : StartsWith (fun i => s (i + a.length)) b := fun i hi => by
  simp only
  rw [h (i + a.length) (by simp; omega), List.getElem_append_right (by omega)]
  simp

theorem fits_nat {w v : ℕ} : Fits w v ↔ v < 2 ^ w := by
  simp [Fits, ncode_nat]

theorem fits_prod {w : ℕ} {a : α} {b : β} : Fits w (a, b) ↔ Fits w a ∧ Fits w b := by
  simp [Fits, ncode_prod, or_imp, forall_and]

theorem fits_list {w : ℕ} {l : List α} :
    Fits w l ↔ l.length < 2 ^ w ∧ ∀ a ∈ l, Fits w a := by
  simp only [Fits, ncode_list, List.mem_cons, List.mem_flatMap]
  constructor
  · intro h
    exact ⟨h _ (.inl rfl), fun a ha v hv => h v (.inr ⟨a, ha, hv⟩)⟩
  · rintro ⟨hl, ha⟩ v (rfl | ⟨a, hmem, hv⟩)
    · exact hl
    · exact ha a hmem v hv

theorem layout_nat (v : ℕ) : Layout v := fun w hw hf => by
  rw [fits_nat] at hf
  rw [wcode, encode_nat_word hw hf, ncode_nat]
  simp [triples]

theorem Layout.prod {a : α} {b : β} (ha : Layout a) (hb : Layout b) : Layout (a, b) :=
  fun w hw hf => by
    rw [fits_prod] at hf
    rw [wcode_prod, ncode_prod, ha w hw hf.1, hb w hw hf.2, triples_append]

theorem layout_list {l : List α} (h : ∀ a ∈ l, Layout a) : Layout l := fun w hw hf => by
  rw [fits_list] at hf
  rw [wcode_list, ncode_list, layout_nat _ w hw (fits_nat.2 hf.1), ← List.singleton_append,
    triples_append, ncode_nat]
  congr 1
  induction l with
  | nil => simp [triples]
  | cons a l ih =>
    simp only [List.flatMap_cons, triples_append]
    rw [h a (by simp) w hw (hf.2 a (by simp))]
    congr 1
    exact ih (fun a ha => h a (by simp [ha])) ⟨by simp at hf; omega,
      fun a ha => hf.2 a (by simp [ha])⟩

theorem readsBack_nat (v : ℕ) : ReadsBack v := fun w hw hf s hs => by
  rw [fits_nat] at hf
  have hc : wcode w v = triple w v := encode_nat_word hw hf
  rw [hc] at hs ⊢
  exact decode_nat_word hw hf s (hs 0 (by simp [triple])) (hs 1 (by simp [triple]))
    (hs 2 (by simp [triple]))

theorem ReadsBack.prod {a : α} {b : β} (ha : ReadsBack a) (hb : ReadsBack b) :
    ReadsBack (a, b) := fun w hw hf s hs => by
  rw [fits_prod] at hf
  rw [wcode_prod] at hs ⊢
  have h₁ := ha w hw hf.1 s hs.append_left
  have h₂ := hb w hw hf.2 _ hs.append_right
  rw [decode_prod, h₁]; simp only; rw [h₂, List.length_append]
  refine Prod.ext rfl ?_; funext i; simp only; congr 1; omega

theorem Skips.prod {a : α} {b : β} (ha : Skips a) (hb : Skips b) :
    Skips (a, b) := fun w hw hf s hs => by
  rw [fits_prod] at hf
  rw [wcode_prod] at hs ⊢
  have h₁ := ha w hw hf.1 s hs.append_left
  have h₂ := hb w hw hf.2 _ hs.append_right
  rw [decode_prod, h₁, h₂, List.length_append]
  funext i; congr 1; omega

theorem readsBack_list {l : List α} (h : ∀ a ∈ l, ReadsBack a) : ReadsBack l :=
  fun w hw hf s hs => by
  rw [fits_list] at hf
  rw [wcode_list] at hs ⊢
  have h₁ := readsBack_nat l.length w hw (fits_nat.2 hf.1) s hs.append_left
  have key : ∀ (l : List α) (s : ℕ → BitVec w), (∀ a ∈ l, ReadsBack a) → (∀ a ∈ l, Fits w a) →
      StartsWith s (l.flatMap (wcode w)) →
      Code.decodeMany l.length s = (l, fun i => s (i + (l.flatMap (wcode w)).length)) := by
    intro l
    induction l with
    | nil => intro s _ _ _; simp [Code.decodeMany]
    | cons a l ih =>
      intro s hr hfi hs
      simp only [List.flatMap_cons] at hs
      have ha := hr a (by simp) w hw (hfi a (by simp)) s hs.append_left
      have hl := ih _ (fun b hb => hr b (by simp [hb])) (fun b hb => hfi b (by simp [hb]))
        hs.append_right
      simp only [List.length_cons, Code.decodeMany, ha, hl, List.flatMap_cons, List.length_append]
      congr 1; funext i; congr 1; omega
  rw [decode_list, h₁]
  simp only
  rw [key l _ h hf.2 hs.append_right, List.length_append]
  congr 1; funext i; congr 1; omega

end Layout

/-! ### The standard tape coding with words -/

section Standard

variable {w : ℕ}

theorem Tape.read_write {A V : Type*} [DecidableEq A] (t : Tape A V) (x : A) (v : V) (a : A) :
    (t.write x v).read a = if a = x then v else t.read a := rfl

theorem read_foldr_zipIdx (L : List (BitVec w)) (k : ℕ) (hk : k + L.length ≤ 2 ^ w)
    (a : BitVec w) :
    ((L.zipIdx k).foldr (fun (p : BitVec w × ℕ) tape => tape.write (p.2 : BitVec w) p.1)
      (⟨fun _ => default⟩ : Tape (BitVec w) (BitVec w))).read a =
      if k ≤ a.toNat then L.getD (a.toNat - k) default else default := by
  induction L generalizing k with
  | nil => simp
  | cons v L ih =>
    simp only [List.zipIdx_cons, List.foldr_cons]
    rw [Tape.read_write, ih (k + 1) (by simp at hk; omega)]
    have hk' : k < 2 ^ w := by simp at hk; omega
    by_cases ha : a = (k : BitVec w)
    · subst ha
      simp [BitVec.natCast_eq_ofNat, Nat.mod_eq_of_lt hk']
    · have : a.toNat ≠ k := by
        intro h; apply ha; apply BitVec.eq_of_toNat_eq
        simp [BitVec.natCast_eq_ofNat, h, Nat.mod_eq_of_lt hk']
      simp only [ha, if_false]
      by_cases hle : k + 1 ≤ a.toNat
      · rw [if_pos hle, if_pos (by omega),
          show a.toNat - k = (a.toNat - (k + 1)) + 1 by omega]
        simp
      · rw [if_neg hle, if_neg (by omega)]

theorem standard_encode_read {I O : Type*} [Code I (BitVec w)] [Code O (BitVec w)] (x : I)
    (hlen : (Code.encode x : List (BitVec w)).length ≤ 2 ^ w) (a : BitVec w) :
    ((TapeCoding.standard : TapeCoding I O (BitVec w) (BitVec w)).encode x).read a =
      (Code.encode x : List (BitVec w)).getD a.toNat default := by
  have := read_foldr_zipIdx (Code.encode x : List (BitVec w)) 0 (by simpa using hlen) a
  simpa [TapeCoding.standard] using this

theorem standard_decode {I O : Type*} [Code I ℕ] [∀ w, Code I (BitVec w)] [Code O ℕ]
    [∀ w, Code O (BitVec w)] (hw : 0 < w) {x : I} {y : O} (hx : Skips x) (hy : ReadsBack y)
    (hfx : Fits w x) (hfy : Fits w y) (T : Tape (BitVec w) (BitVec w))
    (hT : ∀ i (h : i < (wcode w x ++ wcode w y).length),
      T.read (BitVec.ofNat w i) = (wcode w x ++ wcode w y)[i]) :
    (TapeCoding.standard : TapeCoding I O (BitVec w) (BitVec w)).decode T = y := by
  have hs : StartsWith (fun i : ℕ => T.read (i : BitVec w)) (wcode w x ++ wcode w y) :=
    fun i hi => by simp only [BitVec.natCast_eq_ofNat]; exact hT i hi
  have h₁ := hx w hw hfx _ hs.append_left
  simp only [TapeCoding.standard]
  rw [h₁, hy w hw hfy _ hs.append_right]

end Standard

end Formalgo.LLMUnchecked

end

section

/-!
## Reasoning about commands


`eval` runs loop-free commands directly; loops are handled with an invariant and a measure.
-/

namespace Formalgo.LLMUnchecked

open Function

namespace Cmd

/-- Run a loop-free command for words below `B`, with its cost. -/
def eval (B : ℕ) : Cmd → Mem → Option (Mem × ℕ)
  | const d v, m => if d < B ∧ v < B then some (update m d v, 1) else none
  | copy d s, m => if d < B ∧ s < B then some (update m d (m s), 1) else none
  | load d p, m => if d < B ∧ p < B then some (update m d (m (m p)), 1) else none
  | store p s, m => if p < B ∧ s < B then some (update m (m p) (m s), 1) else none
  | add d l r, m =>
    if d < B ∧ l < B ∧ r < B ∧ m l + m r < B then some (update m d (m l + m r), 1) else none
  | sub d l r, m =>
    if d < B ∧ l < B ∧ r < B ∧ m r ≤ m l then some (update m d (m l - m r), 1) else none
  | less d l r, m =>
    if d < B ∧ l < B ∧ r < B then some (update m d (if m l < m r then 1 else 0), 1) else none
  | seq a b, m => match eval B a m with
    | some (m₁, k₁) => match eval B b m₁ with
      | some (m₂, k₂) => some (m₂, k₁ + k₂)
      | none => none
    | none => none
  | ite l r t e, m => if l < B ∧ r < B then
      if m l = m r then (match eval B t m with | some (m', k) => some (m', k + 2) | none => none)
      else (match eval B e m with | some (m', k) => some (m', k + 1) | none => none)
    else none
  | loop _ _ _, _ => none

theorem eval_sound {B : ℕ} {c : Cmd} {m m' : Mem} {k : ℕ} (h : eval B c m = some (m', k)) :
    Exec B c m k m' := by
  induction c generalizing m m' k with
  | const d v =>
    simp only [eval] at h; split at h
    · next hc => cases h; exact .const hc.1 hc.2
    · cases h
  | copy d s =>
    simp only [eval] at h; split at h
    · next hc => cases h; exact .copy hc.1 hc.2
    · cases h
  | load d p =>
    simp only [eval] at h; split at h
    · next hc => cases h; exact .load hc.1 hc.2
    · cases h
  | store p s =>
    simp only [eval] at h; split at h
    · next hc => cases h; exact .store hc.1 hc.2
    · cases h
  | add d l r =>
    simp only [eval] at h; split at h
    · next hc => cases h; exact .add hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    · cases h
  | sub d l r =>
    simp only [eval] at h; split at h
    · next hc => cases h; exact .sub hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    · cases h
  | less d l r =>
    simp only [eval] at h; split at h
    · next hc => cases h; exact .less hc.1 hc.2.1 hc.2.2
    · cases h
  | seq a b iha ihb =>
    simp only [eval] at h
    split at h
    · next m₁ k₁ h₁ =>
      split at h
      · next m₂ k₂ h₂ => cases h; exact .seq (iha h₁) (ihb h₂)
      · cases h
    · cases h
  | ite l r t e iht ihe =>
    simp only [eval] at h
    split at h
    · next hc =>
      split at h
      · next heq =>
        split at h
        · next m₁ k₁ h₁ => cases h; exact .iteTrue hc.1 hc.2 heq (iht h₁)
        · cases h
      · next hne =>
        split at h
        · next m₁ k₁ h₁ => cases h; exact .iteFalse hc.1 hc.2 hne (ihe h₁)
        · cases h
    · cases h
  | loop => simp [eval] at h

end Cmd

/-- A loop, from an invariant `P` on memories and costs so far, and a decreasing measure. -/
theorem Exec.loop_of {B l r : ℕ} {body : Cmd} (P : Mem → ℕ → Prop) (μ : Mem → ℕ)
    (Q : Mem → ℕ → Prop) (hl : l < B) (hr : r < B)
    (hstep : ∀ m s, P m s → m l = m r →
      ∃ m' k, Exec B body m k m' ∧ P m' (s + k + 2) ∧ μ m' < μ m)
    (hexit : ∀ m s, P m s → m l ≠ m r → Q m (s + 1)) :
    ∀ m s, P m s → ∃ m' k, Exec B (.loop l r body) m k m' ∧ Q m' (s + k) := by
  intro m
  induction hμ : μ m using Nat.strong_induction_on generalizing m with
  | _ n ih =>
    intro s hP
    by_cases heq : m l = m r
    · obtain ⟨m₁, k₁, hb, hP₁, hμ₁⟩ := hstep m s hP heq
      obtain ⟨m₂, k₂, hl₂, hQ⟩ := ih (μ m₁) (hμ ▸ hμ₁) m₁ rfl _ hP₁
      exact ⟨m₂, k₁ + k₂ + 2, .loopTrue hl hr heq hb hl₂, by
        rw [show s + (k₁ + k₂ + 2) = s + k₁ + 2 + k₂ by omega]; exact hQ⟩
    · exact ⟨m, 1, .loopFalse hl hr heq, hexit m s hP heq⟩

/-- Sequencing, with the cost of the second part depending on the first. -/
theorem Exec.seq_of {B : ℕ} {a b : Cmd} {m : Mem} (Q : Mem → ℕ → Prop)
    (ha : ∃ m₁ k₁, Exec B a m k₁ m₁ ∧ ∃ m₂ k₂, Exec B b m₁ k₂ m₂ ∧ Q m₂ (k₁ + k₂)) :
    ∃ m' k, Exec B (.seq a b) m k m' ∧ Q m' k := by
  obtain ⟨m₁, k₁, h₁, m₂, k₂, h₂, hQ⟩ := ha
  exact ⟨m₂, k₁ + k₂, .seq h₁ h₂, hQ⟩

end Formalgo.LLMUnchecked

end

section

/-!
## Registers over the input


The input starts at cell `0`, so a program first saves cells `[0, K)` to a buffer at `S`, uses
them as registers, and restores them at the end. Cell `1` holds `S`, cell `2` is scratch, and the
body reads and writes cells below `K` through the buffer.
-/

namespace Formalgo.LLMUnchecked

open Function

namespace Cmd

/-- Run commands in order, then set the scratch cell `2` to `0`. -/
def seqs : List Cmd → Cmd
  | [] => const 2 0
  | c :: cs => seq c (seqs cs)

/-- Save cell `j` to `S + j`, with `S` in cell `0`. -/
def saveOne (j : ℕ) : Cmd := seqs [const 2 j, add 2 0 2, store 2 j]

/-- Restore cell `j` from `S + j`, with `S` in cell `0`. -/
def restoreOne (j : ℕ) : Cmd := seqs [const 2 j, add 2 0 2, load j 2]

/-- The registers that are saved: `1` and `3, …, K - 1`. -/
def regs (K : ℕ) : List ℕ := 1 :: List.range' 3 (K - 3)

/-- Compute `S` into cell `0`, save the registers, run `body`, and restore them. -/
def harness (K : ℕ) (setS body : Cmd) : Cmd :=
  seqs [setS, seqs ((regs K).map saveOne), store 0 3, copy 1 0, body, copy 0 1,
    seqs ((regs K).reverse.map restoreOne), const 0 1]

end Cmd

open Cmd

theorem mem_regs {K j : ℕ} (hK : 3 ≤ K) : j ∈ regs K ↔ j < K ∧ j ≠ 0 ∧ j ≠ 2 := by
  simp only [regs, List.mem_cons, List.mem_range']
  constructor
  · rintro (rfl | ⟨i, hi, rfl⟩) <;> omega
  · intro h
    by_cases h1 : j = 1
    · exact .inl h1
    · exact .inr ⟨j - 3, by omega, by omega⟩

theorem length_regs {K : ℕ} (hK : 3 ≤ K) : (regs K).length = K - 2 := by
  simp [regs]; omega

theorem nodup_regs (K : ℕ) : (regs K).Nodup := by
  simp only [regs, List.nodup_cons, List.mem_range']
  exact ⟨by omega, List.nodup_range' ..⟩

/-- A sequence of commands with the given effects. -/
theorem exec_seqs_nil {B : ℕ} {m : Mem} (hB : 2 < B) : Exec B (seqs []) m 1 (update m 2 0) :=
  .const hB (by omega)

theorem exec_saveOne {B S j : ℕ} {m : Mem} (h0 : m 0 = S) (hj2 : j ≠ 2) (hjS : j < S)
    (h3 : 3 ≤ S) (hB : S + j < B) :
    ∃ m', Exec B (saveOne j) m 4 m' ∧ m' (S + j) = m j ∧ m' 2 = 0 ∧
      ∀ a, a ≠ 2 → a ≠ S + j → m' a = m a := by
  have h2B : 2 < B := by omega
  have e := Exec.seq (B := B) (m := m) (.const (d := 2) (v := j) h2B (by omega))
    (.seq (.add (d := 2) (l := 0) (r := 2) h2B (by omega) h2B (by simp [update_apply, h0]; omega))
      (.seq (.store (p := 2) (s := j) h2B (by omega)) (.const (d := 2) (v := 0) h2B (by omega))))
  refine ⟨_, e, ?_, ?_, ?_⟩
  · simp [update_apply, h0, hj2]; omega
  · simp
  · intro a ha hb; simp [update_apply, h0, ha, hb, hj2]

theorem exec_restoreOne {B S j : ℕ} {m : Mem} (h0 : m 0 = S) (hj2 : j ≠ 2) (hj0 : j ≠ 0)
    (hjS : j < S) (h3 : 3 ≤ S) (hB : S + j < B) :
    ∃ m', Exec B (restoreOne j) m 4 m' ∧ m' j = m (S + j) ∧ m' 2 = 0 ∧
      ∀ a, a ≠ 2 → a ≠ j → m' a = m a := by
  have h2B : 2 < B := by omega
  have e := Exec.seq (B := B) (m := m) (.const (d := 2) (v := j) h2B (by omega))
    (.seq (.add (d := 2) (l := 0) (r := 2) h2B (by omega) h2B (by simp [update_apply, h0]; omega))
      (.seq (.load (d := j) (p := 2) (by omega) h2B) (.const (d := 2) (v := 0) h2B (by omega))))
  refine ⟨_, e, ?_, ?_, ?_⟩
  · simp [update_apply, h0, hj2, show S + j ≠ 2 by omega]
  · simp
  · intro a ha hb; simp [update_apply, h0, ha, hb]

theorem exec_saveAll {B S : ℕ} (js : List ℕ) (hnd : js.Nodup) {m : Mem} (h0 : m 0 = S)
    (hjs : ∀ j ∈ js, j ≠ 0 ∧ j ≠ 2 ∧ j < S) (h3 : 3 ≤ S) (hB : ∀ j ∈ js, S + j < B)
    (h2B : 2 < B) :
    ∃ m', Exec B (seqs (js.map saveOne)) m (4 * js.length + 1) m' ∧ m' 0 = S ∧ m' 2 = 0 ∧
      (∀ j ∈ js, m' (S + j) = m j) ∧
      ∀ a, a ≠ 2 → (∀ j ∈ js, a ≠ S + j) → m' a = m a := by
  induction js generalizing m with
  | nil =>
    exact ⟨_, exec_seqs_nil h2B, by simp [update_apply, h0], by simp, by simp,
      fun a ha _ => by simp [update_apply, ha]⟩
  | cons j js ih =>
    obtain ⟨hj0, hj2, hjS⟩ := hjs j (by simp)
    obtain ⟨m₁, h₁, hm₁j, hm₁2, hm₁⟩ := exec_saveOne (B := B) h0 hj2 hjS h3 (hB j (by simp))
    have h0₁ : m₁ 0 = S := by rw [hm₁ 0 (by omega) (by omega), h0]
    obtain ⟨hjnot, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨m₂, h₂, h0₂, h2₂, hbuf, hrest⟩ := ih hnd' h0₁ (fun j hj => hjs j (by simp [hj]))
      (fun j hj => hB j (by simp [hj]))
    refine ⟨m₂, ?_, h0₂, h2₂, ?_, ?_⟩
    · have := Exec.seq h₁ h₂
      simpa [List.map_cons, seqs, show 4 + (4 * js.length + 1) = 4 * (js.length + 1) + 1 by omega]
        using this
    · intro j' hj'
      rcases List.mem_cons.1 hj' with rfl | hj'
      · rw [hrest _ (by omega) (fun j'' hj'' h => hjnot (by
          have : j' = j'' := by omega
          exact this ▸ hj'')), hm₁j]
      · have := hjs j' (by simp [hj'])
        rw [hbuf j' hj', hm₁ j' this.2.1 (by omega)]
    · intro a ha hne
      rw [hrest a ha (fun j' hj' => hne j' (by simp [hj'])),
        hm₁ a ha (hne j (by simp))]

theorem exec_restoreAll {B S : ℕ} (js : List ℕ) {m : Mem} (h0 : m 0 = S)
    (hjs : ∀ j ∈ js, j ≠ 0 ∧ j ≠ 2 ∧ j < S) (h3 : 3 ≤ S) (hB : ∀ j ∈ js, S + j < B)
    (h2B : 2 < B) :
    ∃ m', Exec B (seqs (js.map restoreOne)) m (4 * js.length + 1) m' ∧ m' 0 = S ∧ m' 2 = 0 ∧
      (∀ j ∈ js, m' j = m (S + j)) ∧
      ∀ a, a ≠ 2 → a ∉ js → m' a = m a := by
  induction js generalizing m with
  | nil =>
    exact ⟨_, exec_seqs_nil h2B, by simp [update_apply, h0], by simp, by simp,
      fun a ha _ => by simp [update_apply, ha]⟩
  | cons j js ih =>
    obtain ⟨hj0, hj2, hjS⟩ := hjs j (by simp)
    obtain ⟨m₁, h₁, hm₁j, hm₁2, hm₁⟩ := exec_restoreOne (B := B) h0 hj2 hj0 hjS h3 (hB j (by simp))
    have h0₁ : m₁ 0 = S := by rw [hm₁ 0 (by omega) (by omega), h0]
    obtain ⟨m₂, h₂, h0₂, h2₂, hreg, hrest⟩ := ih h0₁ (fun j hj => hjs j (by simp [hj]))
      (fun j hj => hB j (by simp [hj]))
    refine ⟨m₂, ?_, h0₂, h2₂, ?_, ?_⟩
    · have := Exec.seq h₁ h₂
      simpa [List.map_cons, seqs, show 4 + (4 * js.length + 1) = 4 * (js.length + 1) + 1 by omega]
        using this
    · intro j' hj'
      by_cases hin : j' ∈ js
      · rw [hreg j' hin, hm₁ _ (by omega) (by have := (hjs j' (by simp [hin])).2.2; omega)]
      · rcases List.mem_cons.1 hj' with rfl | hj'
        · rw [hrest j' (by omega) hin, hm₁j]
        · exact absurd hj' hin
    · intro a ha hne
      rw [hrest a ha (fun h => hne (by simp [h])), hm₁ a ha (fun h => hne (by simp [h]))]

/-- The harness: if the body leaves the final values in its cells from `K` and in the buffer, the
program leaves them in cells `[0, N)`. -/
theorem exec_harness {B K S N : ℕ} {setS body : Cmd} {m₀ m₁ : Mem} {k₀ : ℕ} (final : Mem)
    (T : ℕ) (hK : 4 ≤ K) (hKS : K ≤ S) (hNS : N ≤ S) (hB : S + K < B)
    (hset : Exec B setS m₀ k₀ m₁) (hm₁0 : m₁ 0 = S) (hm₁ : ∀ a, a ≠ 0 → a ≠ 2 → m₁ a = m₀ a)
    (h00 : m₀ 0 = 1) (h02 : m₀ 2 = 0) (h03 : m₀ 3 = 1) (hblank : ∀ a, S ≤ a → m₀ a = 0)
    (hf0 : final 0 = 1) (hf2 : final 2 = 0)
    (hbody : ∀ m, m 1 = S → (∀ j < K, m (S + j) = m₀ j) →
      (∀ a, 3 ≤ a → a < S ∨ S + K ≤ a → m a = m₀ a) →
      ∃ m' k, Exec B body m k m' ∧ k ≤ T ∧ m' 1 = S ∧
        (∀ j < K, j ≠ 0 → j ≠ 2 → m' (S + j) = final j) ∧
        ∀ a, K ≤ a → a < N → m' a = final a) :
    ∃ m' k, Exec B (harness K setS body) m₀ k m' ∧ k ≤ k₀ + T + 8 * K ∧
      ∀ i < N, m' i = final i := by
  have h3K : 3 ≤ K := by omega
  have h2B : 2 < B := by omega
  have hregs : ∀ j ∈ regs K, j ≠ 0 ∧ j ≠ 2 ∧ j < S := fun j hj => by
    have := (mem_regs h3K).1 hj; omega
  have hregsB : ∀ j ∈ regs K, S + j < B := fun j hj => by
    have := (mem_regs h3K).1 hj; omega
  -- Save.
  obtain ⟨m₂, hsave, h₂0, h₂2, h₂buf, h₂⟩ :=
    exec_saveAll (B := B) (regs K) (nodup_regs K) hm₁0 hregs (by omega) hregsB h2B
  have h₂3 : m₂ 3 = 1 := by
    rw [h₂ 3 (by omega) (fun j hj => by have := hregs j hj; omega), hm₁ 3 (by omega) (by omega),
      h03]
  -- `store 0 3`, then `copy 1 0`.
  have e₃ : Exec B (.store 0 3) m₂ 1 (update m₂ S 1) := by
    have := Exec.store (B := B) (m := m₂) (p := 0) (s := 3) (by omega) (by omega)
    rwa [h₂0, h₂3] at this
  set m₃ := update m₂ S 1
  have e₄ : Exec B (.copy 1 0) m₃ 1 (update m₃ 1 S) := by
    have := Exec.copy (B := B) (m := m₃) (d := 1) (s := 0) (by omega) (by omega)
    rwa [show m₃ 0 = S by simp [m₃, update_apply, h₂0]; omega] at this
  set m₄ := update m₃ 1 S
  -- The body.
  have hm₄buf : ∀ j < K, m₄ (S + j) = m₀ j := by
    intro j hj
    simp only [m₄, m₃, update_apply]
    rw [if_neg (by omega)]
    by_cases hj0 : j = 0
    · subst hj0; simp [h00]
    · rw [if_neg (by omega)]
      by_cases hj2 : j = 2
      · subst hj2
        rw [h₂ _ (by omega) (fun j hj => by have := hregs j hj; omega),
          hm₁ _ (by omega) (by omega), hblank _ (by omega), h02]
      · rw [h₂buf j ((mem_regs h3K).2 ⟨hj, hj0, hj2⟩), hm₁ j hj0 hj2]
  have hm₄rest : ∀ a, 3 ≤ a → a < S ∨ S + K ≤ a → m₄ a = m₀ a := by
    intro a ha hS
    simp only [m₄, m₃, update_apply]
    rw [if_neg (by omega), if_neg (by omega),
      h₂ a (by omega) (fun j hj => by have := (mem_regs h3K).1 hj; omega),
      hm₁ a (by omega) (by omega)]
  obtain ⟨m₅, k, hbe, hk, h₅1, h₅buf, h₅⟩ := hbody m₄ (by simp [m₄]) hm₄buf hm₄rest
  -- `copy 0 1`, then restore.
  have e₆ : Exec B (.copy 0 1) m₅ 1 (update m₅ 0 S) := by
    have := Exec.copy (B := B) (m := m₅) (d := 0) (s := 1) (by omega) (by omega)
    rwa [h₅1] at this
  have hregsr : ∀ j ∈ (regs K).reverse, j ≠ 0 ∧ j ≠ 2 ∧ j < S := fun j hj =>
    hregs j (List.mem_reverse.1 hj)
  obtain ⟨m₇, hrest, h₇0, h₇2, h₇reg, h₇⟩ :=
    exec_restoreAll (B := B) (regs K).reverse (m := update m₅ 0 S) (by simp) hregsr (by omega)
      (fun j hj => hregsB j (List.mem_reverse.1 hj)) h2B
  have e₈ : Exec B (.const 0 1) m₇ 1 (update m₇ 0 1) := .const (by omega) (by omega)
  have e₉ := exec_seqs_nil (B := B) (m := update m₇ 0 1) h2B
  refine ⟨_, _, .seq hset (.seq hsave (.seq e₃ (.seq e₄ (.seq hbe (.seq e₆ (.seq hrest
    (.seq e₈ e₉))))))), ?_, ?_⟩
  · simp only [List.length_reverse, length_regs h3K]
    omega
  · intro i hi
    simp only [update_apply]
    by_cases hi2 : i = 2
    · subst hi2; simp [hf2]
    · rw [if_neg hi2]
      by_cases hi0 : i = 0
      · subst hi0; simp [hf0]
      · rw [if_neg hi0]
        by_cases hiK : i < K
        · rw [h₇reg i (List.mem_reverse.2 ((mem_regs h3K).2 ⟨hiK, hi0, hi2⟩)), update_apply,
            if_neg (by omega), h₅buf i hiK hi0 hi2]
        · rw [h₇ i hi2 (fun h => by
            have := (mem_regs h3K).1 (List.mem_reverse.1 h); omega), update_apply,
            if_neg hi0, h₅ i (by omega) hi]

end Formalgo.LLMUnchecked

end

section

/-!
## Registers and virtual memory


Fixed registers, and the memory a body sees: cells below `nK` come from the buffer at `S`, so
that registers are separate from it.
-/

namespace Formalgo.LLMUnchecked

open Function Cmd

/-- The number of registers. -/
scoped notation "nK" => (32 : ℕ)
/-- Register holding `S`. -/
scoped notation "rS" => (1 : ℕ)
/-- Register holding `1`. -/
scoped notation "rOne" => (3 : ℕ)
/-- Register holding `nK`. -/
scoped notation "rK" => (5 : ℕ)
/-- Register for comparisons in `vaddr`. -/
scoped notation "rT" => (6 : ℕ)
/-- Register for physical addresses in `vaddr`. -/
scoped notation "rP" => (7 : ℕ)

/-- Close a goal about reads of updated memories by cases. -/
macro "memo" : tactic => `(tactic| first
  | omega
  | ((try simp (disch := omega) only [Function.update_self, Function.update_of_ne])
     first
       | omega
       | (split_ifs <;> omega)
       | (simp only [Function.update_apply]; split_ifs <;> omega)))

/-- `memo`, also rewriting with the given conditional equations. -/
macro "memo" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| first
  | omega
  | ((try simp (disch := omega) only [Function.update_self, Function.update_of_ne, $ts,*])
     first
       | omega
       | (split_ifs <;> omega)
       | (simp only [Function.update_apply]; split_ifs <;> omega)))

/-- The memory a body sees: the buffer in place of the registers, and `0` where it is. -/
def vm (S : ℕ) (m : Mem) (a : ℕ) : ℕ :=
  if a < nK then m (S + a) else if S ≤ a ∧ a < S + nK then 0 else m a

/-- The fixed registers hold their values. -/
def Regs (S : ℕ) (m : Mem) : Prop := m rS = S ∧ m rOne = 1 ∧ m rK = nK

theorem vm_high {S a : ℕ} {m : Mem} (hKS : nK ≤ S) (ha : S + nK ≤ a) : vm S m a = m a := by
  simp only [vm]; split_ifs <;> omega

theorem vm_update_reg {S r v : ℕ} {m : Mem} (hr : r < nK) (hS : nK ≤ S) :
    vm S (update m r v) = vm S m := by
  funext a; simp only [vm, update_apply]; split_ifs <;> first | rfl | omega

theorem vm_update_high {S p v : ℕ} {m : Mem} (hp : nK ≤ p) (hpS : p < S ∨ S + nK ≤ p) :
    vm S (update m p v) = update (vm S m) p v := by
  funext a
  by_cases ha : a = p
  · subst ha; simp only [vm, update_apply, if_pos rfl]; split_ifs <;> first | rfl | omega
  · simp only [vm, update_apply, ha, if_false]
    split_ifs <;> first | rfl | omega

theorem vm_update_buf {S j v : ℕ} {m : Mem} (hj : j < nK) :
    vm S (update m (S + j) v) = update (vm S m) j v := by
  funext a
  by_cases ha : a = j
  · subst ha; simp [vm, hj]
  · simp only [vm, update_apply, ha, if_false]
    split_ifs <;> first | rfl | omega

theorem Regs.update {S r v : ℕ} {m : Mem} (h : Regs S m) (hr : r ≠ rS ∧ r ≠ rOne ∧ r ≠ rK) :
    Regs S (Function.update m r v) := by
  obtain ⟨h1, h3, h5⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp [update_apply, *] <;> omega

/-- The physical address of virtual address `M[va]`, into `rP`. -/
def vaddr (va : ℕ) : Cmd := seq (less rT va rK) (ite rT rOne (add rP va rS) (copy rP va))

/-- `M[d] := vm[M[va]]`. -/
def vread (d va : ℕ) : Cmd := seq (vaddr va) (load d rP)

/-- `vm[M[va]] := M[src]`. -/
def vwrite (va src : ℕ) : Cmd := seq (vaddr va) (store rP src)

/-- The physical address of a virtual address. -/
def paddr (S a : ℕ) : ℕ := if a < nK then S + a else a

theorem exec_vaddr {B S va : ℕ} {m : Mem} (hR : Regs S m) (hva : va < nK) (hvaT : va ≠ rT)
    (hB : S + nK < B) :
    ∃ m' k, Exec B (vaddr va) m k m' ∧ k ≤ 4 ∧ m' rP = paddr S (m va) ∧
      ∀ a, a ≠ rT → a ≠ rP → m' a = m a := by
  obtain ⟨h1, h3, h5⟩ := hR
  have hl := Exec.less (B := B) (m := m) (d := rT) (l := va) (r := rK) (by omega) (by omega)
    (by omega)
  set m₁ := update m rT (if m va < m rK then 1 else 0)
  have h₁va : m₁ va = m va := by simp [m₁, update_apply, hvaT]
  have h₁1 : m₁ rS = S := by simp [m₁, update_apply, h1]
  have h₁3 : m₁ rOne = 1 := by simp [m₁, update_apply, h3]
  by_cases hlt : m va < nK
  · have e := Exec.iteTrue (B := B) (m := m₁) (l := rT) (r := rOne) (e := copy rP va)
      (by omega) (by omega) (by simp [m₁, update_apply, h3, h5, hlt])
      (.add (m := m₁) (d := rP) (l := va) (r := rS) (by omega) (by omega) (by omega)
        (by rw [h₁va, h₁1]; omega))
    refine ⟨_, _, .seq hl e, by omega, ?_, ?_⟩
    · simp [paddr, hlt, h₁va, h₁1, Nat.add_comm]
    · intro a ha hb; simp [m₁, update_apply, ha, hb]
  · have e := Exec.iteFalse (B := B) (m := m₁) (l := rT) (r := rOne) (t := add rP va rS)
      (by omega) (by omega) (by simp [m₁, update_apply, h3, h5, hlt])
      (.copy (m := m₁) (d := rP) (s := va) (by omega) (by omega))
    refine ⟨_, _, .seq hl e, by omega, ?_, ?_⟩
    · simp [paddr, hlt, h₁va]
    · intro a ha hb; simp [m₁, update_apply, ha, hb]

theorem vm_of_frame {S : ℕ} {m m' : Mem} (hKS : nK ≤ S)
    (h : ∀ a, a ≠ rT → a ≠ rP → m' a = m a) : vm S m' = vm S m := by
  funext a; simp only [vm]; split_ifs <;> first | rfl | exact h _ (by omega) (by omega)

theorem Regs.of_frame {S : ℕ} {m m' : Mem} (hR : Regs S m)
    (h : ∀ a, a ≠ rT → a ≠ rP → m' a = m a) : Regs S m' := by
  obtain ⟨a, b, c⟩ := hR
  exact ⟨by rw [h _ (by omega) (by omega), a], by rw [h _ (by omega) (by omega), b],
    by rw [h _ (by omega) (by omega), c]⟩

theorem paddr_read {S a : ℕ} {m m' : Mem} (hKS : nK ≤ S) (ha : a < S ∨ S + nK ≤ a)
    (h : ∀ a, a ≠ rT → a ≠ rP → m' a = m a) : m' (paddr S a) = vm S m a := by
  unfold paddr vm; split_ifs <;> first | omega | exact h _ (by omega) (by omega)

theorem exec_vread {B S d va : ℕ} {m : Mem} (hR : Regs S m) (hva : va < nK) (hvaT : va ≠ rT)
    (hd : d < nK) (hdR : d ≠ rS ∧ d ≠ rOne ∧ d ≠ rK) (hKS : nK ≤ S) (hB : S + nK < B)
    (hsrc : m va < S ∨ S + nK ≤ m va) :
    ∃ m' k, Exec B (vread d va) m k m' ∧ k ≤ 5 ∧ Regs S m' ∧ m' d = vm S m (m va) ∧
      vm S m' = vm S m ∧ ∀ a, a ≠ rT → a ≠ rP → a ≠ d → m' a = m a := by
  obtain ⟨m₁, k₁, e₁, hk₁, h₁P, h₁⟩ := exec_vaddr (B := B) hR hva hvaT hB
  have e₂ := Exec.load (B := B) (m := m₁) (d := d) (p := rP) (by omega) (by omega)
  refine ⟨_, _, .seq e₁ e₂, by omega, (hR.of_frame h₁).update hdR, ?_, ?_, ?_⟩
  · simp [h₁P, paddr_read hKS hsrc h₁]
  · rw [vm_update_reg hd hKS, vm_of_frame hKS h₁]
  · intro a ha hb hc; simp [update_apply, hc, h₁ a ha hb]

theorem exec_vwrite {B S va src : ℕ} {m : Mem} (hR : Regs S m) (hva : va < nK) (hvaT : va ≠ rT)
    (hsrcK : src < nK) (hsrc : src ≠ rT ∧ src ≠ rP) (hKS : nK ≤ S) (hB : S + nK < B)
    (hdst : m va < S ∨ S + nK ≤ m va) :
    ∃ m' k, Exec B (vwrite va src) m k m' ∧ k ≤ 5 ∧ Regs S m' ∧
      vm S m' = update (vm S m) (m va) (m src) ∧ ∀ a < nK, a ≠ rT → a ≠ rP → m' a = m a := by
  obtain ⟨m₁, k₁, e₁, hk₁, h₁P, h₁⟩ := exec_vaddr (B := B) hR hva hvaT hB
  have e₂ := Exec.store (B := B) (m := m₁) (p := rP) (s := src) (by omega) (by omega)
  have hsrc₁ : m₁ src = m src := h₁ _ hsrc.1 hsrc.2
  have hR₁ := hR.of_frame h₁
  refine ⟨_, _, .seq e₁ e₂, by omega, ?_, ?_, ?_⟩
  · obtain ⟨a, b, c⟩ := hR₁
    rw [h₁P]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [update_apply, paddr] <;> split_ifs <;> first
      | assumption | omega
  · rw [h₁P, hsrc₁]
    unfold paddr
    split_ifs with hlt
    · rw [vm_update_buf hlt, vm_of_frame hKS h₁]
    · rw [vm_update_high (by omega) hdst, vm_of_frame hKS h₁]
  · intro a ha hb hc
    rw [h₁P]; simp only [update_apply, paddr]
    split_ifs <;> first | omega | exact h₁ a hb hc

/-! ### Running commands, by continuations -/

/-- `c` runs from `m` to a memory and cost satisfying `Q`. -/
def Runs (B : ℕ) (c : Cmd) (m : Mem) (Q : Mem → ℕ → Prop) : Prop :=
  ∃ m' k, Exec B c m k m' ∧ Q m' k

namespace Runs

variable {B : ℕ} {m : Mem} {Q : Mem → ℕ → Prop}

theorem seq {a b : Cmd} (h : Runs B a m fun m₁ k₁ => Runs B b m₁ fun m₂ k₂ => Q m₂ (k₁ + k₂)) :
    Runs B (.seq a b) m Q := by
  obtain ⟨m₁, k₁, e₁, m₂, k₂, e₂, hQ⟩ := h
  exact ⟨m₂, k₁ + k₂, .seq e₁ e₂, hQ⟩

theorem seqs_cons {c : Cmd} {cs : List Cmd}
    (h : Runs B c m fun m₁ k₁ => Runs B (seqs cs) m₁ fun m₂ k₂ => Q m₂ (k₁ + k₂)) :
    Runs B (seqs (c :: cs)) m Q := seq h

theorem seqs_nil (hB : 2 < B) (h : Q (update m 2 0) 1) : Runs B (seqs []) m Q :=
  ⟨_, _, .const hB (by omega), h⟩

theorem const {d v : ℕ} (hd : d < B) (hv : v < B) (h : Q (update m d v) 1) :
    Runs B (.const d v) m Q := ⟨_, _, .const hd hv, h⟩

theorem copy {d s : ℕ} (hd : d < B) (hs : s < B) (h : Q (update m d (m s)) 1) :
    Runs B (.copy d s) m Q := ⟨_, _, .copy hd hs, h⟩

theorem load {d p : ℕ} (hd : d < B) (hp : p < B) (h : Q (update m d (m (m p))) 1) :
    Runs B (.load d p) m Q := ⟨_, _, .load hd hp, h⟩

theorem store {p s : ℕ} (hp : p < B) (hs : s < B) (h : Q (update m (m p) (m s)) 1) :
    Runs B (.store p s) m Q := ⟨_, _, .store hp hs, h⟩

theorem add {d l r : ℕ} (hd : d < B) (hl : l < B) (hr : r < B) (hlr : m l + m r < B)
    (h : Q (update m d (m l + m r)) 1) : Runs B (.add d l r) m Q :=
  ⟨_, _, .add hd hl hr hlr, h⟩

theorem sub {d l r : ℕ} (hd : d < B) (hl : l < B) (hr : r < B) (hlr : m r ≤ m l)
    (h : Q (update m d (m l - m r)) 1) : Runs B (.sub d l r) m Q :=
  ⟨_, _, .sub hd hl hr hlr, h⟩

theorem less {d l r : ℕ} (hd : d < B) (hl : l < B) (hr : r < B)
    (h : Q (update m d (if m l < m r then 1 else 0)) 1) : Runs B (.less d l r) m Q :=
  ⟨_, _, .less hd hl hr, h⟩

theorem ite {l r : ℕ} {t e : Cmd} (hl : l < B) (hr : r < B)
    (ht : m l = m r → Runs B t m fun m' k => Q m' (k + 2))
    (he : m l ≠ m r → Runs B e m fun m' k => Q m' (k + 1)) : Runs B (.ite l r t e) m Q := by
  by_cases h : m l = m r
  · obtain ⟨m', k, e', hQ⟩ := ht h; exact ⟨m', k + 2, .iteTrue hl hr h e', hQ⟩
  · obtain ⟨m', k, e', hQ⟩ := he h; exact ⟨m', k + 1, .iteFalse hl hr h e', hQ⟩

theorem loop {l r : ℕ} {body : Cmd} (P : Mem → ℕ → Prop) (μ : Mem → ℕ) (hl : l < B) (hr : r < B)
    (hstep : ∀ m s, P m s → m l = m r →
      Runs B body m fun m' k => P m' (s + k + 2) ∧ μ m' < μ m)
    (hexit : ∀ m s, P m s → m l ≠ m r → Q m (s + 1)) (h0 : P m 0) :
    Runs B (.loop l r body) m Q := by
  obtain ⟨m', k, e, hQ⟩ := Exec.loop_of P μ Q hl hr
    (fun m s hP heq => by
      obtain ⟨m', k, e, hP', hμ⟩ := hstep m s hP heq
      exact ⟨m', k, e, hP', hμ⟩) hexit m 0 h0
  exact ⟨m', k, e, by simpa using hQ⟩

theorem mono {c : Cmd} {Q' : Mem → ℕ → Prop} (h : Runs B c m Q) (hQ : ∀ m k, Q m k → Q' m k) :
    Runs B c m Q' := by
  obtain ⟨m', k, e, hq⟩ := h; exact ⟨m', k, e, hQ _ _ hq⟩

theorem vread {S d va : ℕ} (hR : Regs S m) (hva : va < nK) (hvaT : va ≠ rT) (hd : d < nK)
    (hdR : d ≠ rS ∧ d ≠ rOne ∧ d ≠ rK) (hKS : nK ≤ S) (hB : S + nK < B)
    (hsrc : m va < S ∨ S + nK ≤ m va)
    (h : ∀ m' k, k ≤ 5 → Regs S m' → m' d = vm S m (m va) → vm S m' = vm S m →
      (∀ a, a ≠ rT → a ≠ rP → a ≠ d → m' a = m a) → Q m' k) :
    Runs B (vread d va) m Q := by
  obtain ⟨m', k, e, hk, hR', hd', hvm, hfr⟩ := exec_vread hR hva hvaT hd hdR hKS hB hsrc
  exact ⟨m', k, e, h m' k hk hR' hd' hvm hfr⟩

theorem vwrite {S va src : ℕ} (hR : Regs S m) (hva : va < nK) (hvaT : va ≠ rT)
    (hsrcK : src < nK) (hsrc : src ≠ rT ∧ src ≠ rP) (hKS : nK ≤ S) (hB : S + nK < B)
    (hdst : m va < S ∨ S + nK ≤ m va)
    (h : ∀ m' k, k ≤ 5 → Regs S m' → vm S m' = update (vm S m) (m va) (m src) →
      (∀ a < nK, a ≠ rT → a ≠ rP → m' a = m a) → Q m' k) :
    Runs B (vwrite va src) m Q := by
  obtain ⟨m', k, e, hk, hR', hvm, hfr⟩ := exec_vwrite hR hva hvaT hsrcK hsrc hKS hB hdst
  exact ⟨m', k, e, h m' k hk hR' hvm hfr⟩

/-! Register commands, with the new memory kept abstract. -/

theorem constR {d v : ℕ} (hd : d < B) (hv : v < B)
    (h : ∀ m', m' d = v → (∀ a, a ≠ d → m' a = m a) → Q m' 1) : Runs B (.const d v) m Q :=
  const hd hv (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem copyR {d s : ℕ} (hd : d < B) (hs : s < B)
    (h : ∀ m', m' d = m s → (∀ a, a ≠ d → m' a = m a) → Q m' 1) : Runs B (.copy d s) m Q :=
  copy hd hs (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem loadR {d p : ℕ} (hd : d < B) (hp : p < B)
    (h : ∀ m', m' d = m (m p) → (∀ a, a ≠ d → m' a = m a) → Q m' 1) : Runs B (.load d p) m Q :=
  load hd hp (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem storeR {p s : ℕ} (hp : p < B) (hs : s < B)
    (h : ∀ m', m' (m p) = m s → (∀ a, a ≠ m p → m' a = m a) → Q m' 1) :
    Runs B (.store p s) m Q :=
  store hp hs (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem addR {d l r : ℕ} (hd : d < B) (hl : l < B) (hr : r < B) (hlr : m l + m r < B)
    (h : ∀ m', m' d = m l + m r → (∀ a, a ≠ d → m' a = m a) → Q m' 1) :
    Runs B (.add d l r) m Q :=
  add hd hl hr hlr (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem subR {d l r : ℕ} (hd : d < B) (hl : l < B) (hr : r < B) (hlr : m r ≤ m l)
    (h : ∀ m', m' d = m l - m r → (∀ a, a ≠ d → m' a = m a) → Q m' 1) :
    Runs B (.sub d l r) m Q :=
  sub hd hl hr hlr (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem lessR {d l r : ℕ} (hd : d < B) (hl : l < B) (hr : r < B)
    (h : ∀ m', m' d = (if m l < m r then 1 else 0) → (∀ a, a ≠ d → m' a = m a) → Q m' 1) :
    Runs B (.less d l r) m Q :=
  less hd hl hr (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem seqs_nilR (hB : 2 < B) (h : ∀ m', m' 2 = 0 → (∀ a, a ≠ 2 → m' a = m a) → Q m' 1) :
    Runs B (seqs []) m Q :=
  seqs_nil hB (h _ (by simp) fun a ha => by simp [update_apply, ha])

end Runs

theorem vm_of_reg {S d : ℕ} {m m' : Mem} (hd : d < nK) (hKS : nK ≤ S)
    (h : ∀ a, a ≠ d → m' a = m a) : vm S m' = vm S m := by
  funext a; simp only [vm]; split_ifs <;> first | rfl | exact h _ (by omega)

theorem Regs.of_reg {S d : ℕ} {m m' : Mem} (hR : Regs S m) (hd : d ≠ rS ∧ d ≠ rOne ∧ d ≠ rK)
    (h : ∀ a, a ≠ d → m' a = m a) : Regs S m' := by
  obtain ⟨a, b, c⟩ := hR
  exact ⟨by rw [h _ (by omega), a], by rw [h _ (by omega), b], by rw [h _ (by omega), c]⟩

theorem vm_of_store {S p v : ℕ} {m m' : Mem} (hp : nK ≤ p) (hpS : p < S ∨ S + nK ≤ p)
    (hv : m' p = v) (h : ∀ a, a ≠ p → m' a = m a) : vm S m' = update (vm S m) p v := by
  have : m' = update m p v := by
    funext a; by_cases ha : a = p
    · subst ha; simp [hv]
    · simp [update_apply, ha, h a ha]
  rw [this, vm_update_high hp hpS]

namespace Runs

variable {B : ℕ} {m : Mem} {Q : Mem → ℕ → Prop}

/-! Register commands, also keeping `vm`. -/

theorem constV {S d v : ℕ} (hKS : nK ≤ S) (hdK : d < nK) (hd : d < B) (hv : v < B)
    (h : ∀ m', m' d = v → (∀ a, a ≠ d → m' a = m a) → vm S m' = vm S m → Q m' 1) :
    Runs B (.const d v) m Q :=
  constR hd hv fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg hdK hKS h₂)

theorem copyV {S d s : ℕ} (hKS : nK ≤ S) (hdK : d < nK) (hd : d < B) (hs : s < B)
    (h : ∀ m', m' d = m s → (∀ a, a ≠ d → m' a = m a) → vm S m' = vm S m → Q m' 1) :
    Runs B (.copy d s) m Q :=
  copyR hd hs fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg hdK hKS h₂)

theorem loadV {S d p : ℕ} (hKS : nK ≤ S) (hdK : d < nK) (hd : d < B) (hp : p < B)
    (h : ∀ m', m' d = m (m p) → (∀ a, a ≠ d → m' a = m a) → vm S m' = vm S m → Q m' 1) :
    Runs B (.load d p) m Q :=
  loadR hd hp fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg hdK hKS h₂)

theorem addV {S d l r : ℕ} (hKS : nK ≤ S) (hdK : d < nK) (hd : d < B) (hl : l < B) (hr : r < B)
    (hlr : m l + m r < B)
    (h : ∀ m', m' d = m l + m r → (∀ a, a ≠ d → m' a = m a) → vm S m' = vm S m → Q m' 1) :
    Runs B (.add d l r) m Q :=
  addR hd hl hr hlr fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg hdK hKS h₂)

theorem subV {S d l r : ℕ} (hKS : nK ≤ S) (hdK : d < nK) (hd : d < B) (hl : l < B) (hr : r < B)
    (hlr : m r ≤ m l)
    (h : ∀ m', m' d = m l - m r → (∀ a, a ≠ d → m' a = m a) → vm S m' = vm S m → Q m' 1) :
    Runs B (.sub d l r) m Q :=
  subR hd hl hr hlr fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg hdK hKS h₂)

theorem lessV {S d l r : ℕ} (hKS : nK ≤ S) (hdK : d < nK) (hd : d < B) (hl : l < B)
    (hr : r < B)
    (h : ∀ m', m' d = (if m l < m r then 1 else 0) → (∀ a, a ≠ d → m' a = m a) →
      vm S m' = vm S m → Q m' 1) :
    Runs B (.less d l r) m Q :=
  lessR hd hl hr fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg hdK hKS h₂)

theorem seqs_nilV {S : ℕ} (hKS : nK ≤ S) (hB : 2 < B)
    (h : ∀ m', m' 2 = 0 → (∀ a, a ≠ 2 → m' a = m a) → vm S m' = vm S m → Q m' 1) :
    Runs B (seqs []) m Q :=
  seqs_nilR hB fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg (by omega) hKS h₂)

end Runs

/-- Solve a goal about register values, from the facts in context. -/
macro "rs" : tactic => `(tactic| first
  | omega
  | ((simp (disch := omega) only [*, Function.update_self, Function.update_of_ne]) <;> first
      | omega
      | (split_ifs <;> omega)))

/-- Run the next register command. -/
macro "rstep" : tactic => `(tactic| first
  | refine Runs.seqs_cons ?_
  | refine Runs.seq ?_
  | (refine Runs.seqs_nilV (by assumption) (by omega) ?_; intro _ _ _ _)
  | (refine Runs.constV (by assumption) (by omega) (by omega) (by omega) ?_; intro _ _ _ _)
  | (refine Runs.copyV (by assumption) (by omega) (by omega) (by omega) ?_; intro _ _ _ _)
  | (refine Runs.loadV (by assumption) (by omega) (by omega) (by omega) ?_; intro _ _ _ _)
  | (refine Runs.addV (by assumption) (by omega) (by omega) (by omega) (by omega) (by rs) ?_;
      intro _ _ _ _)
  | (refine Runs.subV (by assumption) (by omega) (by omega) (by omega) (by omega) (by rs) ?_;
      intro _ _ _ _)
  | (refine Runs.lessV (by assumption) (by omega) (by omega) (by omega) (by omega) ?_;
      intro _ _ _ _))

/-- Run the next register command, without tracking `vm`. -/
macro "rstepR" : tactic => `(tactic| first
  | refine Runs.seqs_cons ?_
  | refine Runs.seq ?_
  | (refine Runs.seqs_nilR (by omega) ?_; intro _ _ _)
  | (refine Runs.constR (by omega) (by omega) ?_; intro _ _ _)
  | (refine Runs.copyR (by omega) (by omega) ?_; intro _ _ _)
  | (refine Runs.loadR (by omega) (by omega) ?_; intro _ _ _)
  | (refine Runs.addR (by omega) (by omega) (by omega) (by rs) ?_; intro _ _ _)
  | (refine Runs.subR (by omega) (by omega) (by omega) (by rs) ?_; intro _ _ _)
  | (refine Runs.lessR (by omega) (by omega) (by omega) ?_; intro _ _ _))

/-- The harness, with the body described through `vm`. -/
theorem exec_harness_vm {B S N : ℕ} {setS body : Cmd} {m₀ m₁ : Mem} {k₀ : ℕ} (final : Mem)
    (T : ℕ) (hKS : nK ≤ S) (hNS : N ≤ S) (hB : S + nK < B)
    (hset : Exec B setS m₀ k₀ m₁) (hm₁0 : m₁ 0 = S) (hm₁ : ∀ a, a ≠ 0 → a ≠ 2 → m₁ a = m₀ a)
    (h00 : m₀ 0 = 1) (h02 : m₀ 2 = 0) (h03 : m₀ 3 = 1) (hblank : ∀ a, S ≤ a → m₀ a = 0)
    (hf0 : final 0 = 1) (hf2 : final 2 = 0)
    (hbody : ∀ m, m rS = S → (∀ a, vm S m a = m₀ a) → (∀ r, 3 ≤ r → r < nK → m r = m₀ r) →
      ∃ m' k, Exec B body m k m' ∧ k ≤ T ∧ m' rS = S ∧
        ∀ a < S, a ≠ 0 → a ≠ 2 → vm S m' a = final a) :
    ∃ m' k, Exec B (harness nK setS body) m₀ k m' ∧ k ≤ k₀ + T + 8 * nK ∧
      ∀ i < N, m' i = final i := by
  refine exec_harness final T (by omega) hKS hNS hB hset hm₁0 hm₁ h00 h02 h03 hblank hf0 hf2 ?_
  intro m hm1 hbuf hrest
  have hvm : ∀ a, vm S m a = m₀ a := by
    intro a; simp only [vm]
    split_ifs with h1 h2
    · exact hbuf a h1
    · exact (hblank a h2.1).symm
    · exact hrest a (by omega) (by omega)
  obtain ⟨m', k, e, hk, h1, hfin⟩ := hbody m hm1 hvm (fun r hr hr' => hrest r hr (by omega))
  refine ⟨m', k, e, hk, h1, ?_, ?_⟩
  · intro j hj hj0 hj2
    have := hfin j (by omega) hj0 hj2
    simpa [vm, hj] using this
  · intro a ha haN
    have := hfin a (by omega) (by omega) (by omega)
    simpa [vm, show ¬ a < 32 by omega, show ¬ (S ≤ a ∧ a < S + 32) by omega] using this

end Formalgo.LLMUnchecked

end

section

/-!
## Commands as TD word RAM algorithms


A command `c` is a TD word RAM algorithm. If `c` runs from the memory holding the word size and
the input, and leaves the input followed by the output, the algorithm outputs it.
-/

namespace Formalgo.LLMUnchecked

/-- The numbers in an instruction. -/
def NInstr.nums : NInstr → List ℕ
  | .const d v => [d, v]
  | .copy d s => [d, s]
  | .load d p => [d, p]
  | .store p s => [p, s]
  | .halt => []
  | .extension (.apply _ d l r) => [d, l, r]
  | .extension (.equal l r) => [l, r]

/-- Every number in the lines is below `2 ^ W`. -/
def Small (W : ℕ) (lines : List Line) : Prop := ∀ line ∈ lines, ∀ n ∈ line.instr.nums, n < 2 ^ W

instance (W : ℕ) (lines : List Line) : Decidable (Small W lines) := by
  unfold Small; infer_instance

theorem setWidth'_ofNat {W w : ℕ} (h : W ≤ w) {n : ℕ} (hn : n < 2 ^ W) :
    (BitVec.ofNat W n).setWidth' h = BitVec.ofNat w n := by
  apply BitVec.eq_of_toNat_eq
  have : n < 2 ^ w := lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) h)
  simp [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt this]

theorem lift_toWord {W w : ℕ} (h : W ≤ w) {i : NInstr} (hi : ∀ n ∈ i.nums, n < 2 ^ W) :
    WordRAM.liftInstruction h (i.toWord W) = i.toWord w := by
  cases i with
  | extension e =>
    cases e <;> simp_all [WordRAM.liftInstruction, NInstr.toWord, NInstr.nums, RAM.Instruction.map,
      RAM.Arithmetic.map, setWidth'_ofNat h]
  | _ => simp_all [WordRAM.liftInstruction, NInstr.toWord, NInstr.nums, RAM.Instruction.map,
      RAM.Arithmetic.map, setWidth'_ofNat h]

theorem lift_linesProgram {W w : ℕ} (h : W ≤ w) {lines : List Line} (hl : 0 < lines.length)
    (hsmall : Small W lines) :
    (linesProgram W lines hl).map (WordRAM.liftInstruction h) = linesProgram w lines hl := by
  simp only [Program.map, linesProgram]
  congr 1
  funext pc
  exact lift_toWord h (hsmall _ (List.getElem_mem _))

/-- Numbers written as `[1, v, 0]`, over natural numbers. -/
def tripleNat (l : List ℕ) : List ℕ := l.flatMap fun v => [1, v, 0]

@[simp] theorem length_tripleNat (l : List ℕ) : (tripleNat l).length = 3 * l.length := by
  induction l <;> simp_all [tripleNat]; omega

theorem tripleNat_append (a b : List ℕ) : tripleNat (a ++ b) = tripleNat a ++ tripleNat b := by
  simp [tripleNat]

theorem triples_getElem {w : ℕ} (hw : 0 < w) {l : List ℕ} (hl : ∀ v ∈ l, v < 2 ^ w) (i : ℕ)
    (hi : i < (triples w l).length) :
    ((triples w l)[i]).toNat = (tripleNat l).getD i 0 := by
  induction l generalizing i with
  | nil => simp at hi
  | cons v l ih =>
    have hv := hl v (by simp)
    simp only [triples, List.flatMap_cons, triple] at hi ⊢
    rcases i with _ | _ | _ | i
    · simp [tripleNat, BitVec.toNat_one hw]
    · simp [tripleNat, Nat.mod_eq_of_lt hv]
    · simp [tripleNat]
    · have := ih (fun v hv => hl v (by simp [hv])) i (by simp [triples] at hi ⊢; omega)
      simpa [triples, tripleNat] using this

/-- The memory holding the word size and the input. -/
def initMem {Input : Type*} [Code Input ℕ] (w : ℕ) (x : Input) : Mem :=
  fun a => (tripleNat (ncode (w, x))).getD a 0

/-- The TD word RAM algorithm running `c`, written for `W`-bit words. -/
def cmdAlgorithm (Input Output : Type*) (c : Cmd) (W scale : ℕ) :
    TDAlgorithm (fun w => WInstr w) (Fin c.lines.length) Input Output where
  width := W
  program := linesProgram W c.lines (by simp [Cmd.length_lines])
  scale := scale

/-- The largest of the length and the numbers of a code. -/
def codeMax (l : List ℕ) : ℕ := l.foldr max l.length

theorem le_foldr_max_init (l : List ℕ) (a : ℕ) : a ≤ l.foldr max a := by
  induction l <;> simp_all [le_max_of_le_right]

theorem le_foldr_max {l : List ℕ} {a v : ℕ} (hv : v ∈ l) : v ≤ l.foldr max a := by
  induction l with
  | nil => simp at hv
  | cons b l ih =>
    rcases List.mem_cons.1 hv with rfl | hv
    · simp
    · simp [ih hv]

theorem length_le_codeMax (l : List ℕ) : l.length ≤ codeMax l := le_foldr_max_init _ _

theorem le_codeMax {l : List ℕ} {v : ℕ} (hv : v ∈ l) : v ≤ codeMax l := le_foldr_max hv

theorem wordSize_spec {Input Output : Type*} [Code Input ℕ] (c : Cmd) (W scale : ℕ) (x : Input) :
    W ≤ (cmdAlgorithm Input Output c W scale).wordSize x ∧
      (codeMax (ncode x) + 1) ^ scale ≤ 2 ^ (cmdAlgorithm Input Output c W scale).wordSize x := by
  refine ⟨le_sup_left, ?_⟩
  set M := codeMax (ncode x)
  have h1 : M + 1 ≤ 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self (by omega) M
  calc (M + 1) ^ scale ≤ (2 ^ (Nat.log 2 M + 1)) ^ scale := Nat.pow_le_pow_left h1 _
    _ = 2 ^ (scale * (Nat.log 2 M + 1)) := by rw [← Nat.pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ (cmdAlgorithm Input Output c W scale).wordSize x :=
      Nat.pow_le_pow_right (by omega) le_sup_right

section Glue

variable {Input Output : Type*} [Code Input ℕ] [∀ w, Code Input (BitVec w)] [Code Output ℕ]
  [∀ w, Code Output (BitVec w)]

theorem run_halt {w : ℕ} {lines : List Line} {hl : 0 < lines.length} {pc : Fin lines.length}
    (hpc : lines[pc.val]? = some ⟨.halt, 0, 0⟩) (T : Tape (BitVec w) (BitVec w)) :
    (linesProgram w lines hl).run (sem w) 1 ⟨pc, T⟩ = .halted ⟨pc, T⟩ := by
  have : lines[pc.val] = ⟨.halt, 0, 0⟩ := by
    rw [List.getElem?_eq_getElem pc.isLt] at hpc; exact Option.some.inj hpc
  simp [Program.run, Program.step, linesProgram, this, NInstr.toWord, RAM.Instruction.map,
    RAM.semantics]

/-- A command that leaves the input followed by the output gives a TD algorithm with that output,
halting within one more step. -/
theorem outputs_of_exec (c : Cmd) {W scale : ℕ} (hsmall : Small W c.lines) (x : Input)
    (y : Output) (hx : Layout x) (hxs : Skips x) (hy : Layout y) (hyr : ReadsBack y)
    (hw : 0 < (cmdAlgorithm Input Output c W scale).wordSize x)
    (hfit : Fits ((cmdAlgorithm Input Output c W scale).wordSize x) x)
    (hfity : Fits ((cmdAlgorithm Input Output c W scale).wordSize x) y)
    (hlen : 3 * ((ncode ((cmdAlgorithm Input Output c W scale).wordSize x, x)).length +
      (ncode y).length) ≤ 2 ^ (cmdAlgorithm Input Output c W scale).wordSize x)
    {k : ℕ} {m' : Mem}
    (hE : Exec (2 ^ (cmdAlgorithm Input Output c W scale).wordSize x) c
      (initMem ((cmdAlgorithm Input Output c W scale).wordSize x) x) k m')
    (hout : ∀ i < 3 * ((ncode ((cmdAlgorithm Input Output c W scale).wordSize x, x)).length +
      (ncode y).length),
      m' i = (tripleNat (ncode ((cmdAlgorithm Input Output c W scale).wordSize x, x) ++
        ncode y)).getD i 0) :
    Outputs (cmdAlgorithm Input Output c W scale) (tdWordRAM ops) x y ∧
      HaltsWithin (cmdAlgorithm Input Output c W scale) (tdWordRAM ops) x (k + 1) := by
  set A := cmdAlgorithm Input Output c W scale
  set w := A.wordSize x with hwdef
  have hlpos : 0 < c.lines.length := by simp [Cmd.length_lines]
  have hWw : W ≤ w := le_sup_left
  -- Facts about `(w, x)`.
  have hfwx : Fits w (w, x) := fits_prod.2 ⟨fits_nat.2 (Nat.lt_two_pow_self), hfit⟩
  have hlay : Layout (w, x) := (layout_nat w).prod hx
  have hskip : Skips (w, x) := (readsBack_nat w).skips.prod hxs
  have hwx : wcode w (w, x) = triples w (ncode (w, x)) := hlay w hw hfwx
  have hwy : wcode w y = triples w (ncode y) := hy w hw hfity
  -- The start.
  set T₀ := (TapeCoding.standard : TapeCoding (ℕ × Input) Output (BitVec w) (BitVec w)).encode
    (w, x)
  have hT₀ : Corr (initMem w x) T₀ := by
    intro a
    have hlen' : (wcode w (w, x)).length ≤ 2 ^ w := by
      rw [hwx, length_triples]; omega
    rw [standard_encode_read (w, x) hlen' a]
    simp only [initMem]
    change ((wcode w (w, x)).getD a.toNat default).toNat = _
    by_cases ha : a.toNat < (wcode w (w, x)).length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some]
      have := triples_getElem hw hfwx a.toNat (by rwa [← hwx])
      rw [← this]
      congr 1
      exact List.getElem_of_eq hwx ha
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rw [hwx, length_triples] at ha
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
  -- The run.
  have hprog : (A.atWordSize (tdWordRAM ops) w le_sup_left).program =
      linesProgram w c.lines hlpos := lift_linesProgram hWw hlpos hsmall
  obtain ⟨T', hrun, hT'⟩ := Exec.run (lines := c.lines) (hlines := hlpos) hw hE (s := 0)
    (fun i hi => by simp [Cmd.lines, List.getElem?_append_left (by rwa [Cmd.length_compile] at hi)])
    (by simp [Cmd.length_lines]) hT₀ (pc := ⟨0, hlpos⟩) rfl
  have hhalt := run_halt (hl := hlpos) (pc := ⟨0 + c.size, by simp [Cmd.length_lines]⟩)
    (by simp [Cmd.lines, List.getElem?_append_right, Cmd.length_compile]) T'
  have hfull : (linesProgram w c.lines hlpos).run (sem w) (k + 1) ⟨⟨0, hlpos⟩, T₀⟩ =
      .halted ⟨⟨0 + c.size, by simp [Cmd.length_lines]⟩, T'⟩ := by
    rw [run_add_of_running hrun, hhalt]
  have hstatus : (Runnable.run A (tdWordRAM ops)).status x (k + 1) =
      .halted ⟨w, ⟨⟨0 + c.size, by simp [Cmd.length_lines]⟩, T'⟩⟩ := by
    show Status.map _ ((Runnable.run (A.atWordSize (tdWordRAM ops) w le_sup_left)
      ((tdWordRAM ops).semantics w)).status (w, x) (k + 1)) = _
    simp only [Runnable.run, hprog]
    change Status.map _ ((linesProgram w c.lines hlpos).run (sem w) (k + 1) ⟨⟨0, hlpos⟩, T₀⟩) = _
    rw [hfull]; rfl
  refine ⟨⟨k + 1, _, hstatus, ?_⟩, ⟨_, hstatus⟩⟩
  -- The output.
  show (TapeCoding.standard : TapeCoding (ℕ × Input) Output (BitVec w) (BitVec w)).decode T' = y
  apply standard_decode hw hskip hyr hfwx hfity T'
  intro i hi
  have hi' : i < 3 * ((ncode (w, x)).length + (ncode y).length) := by
    simp [hwx, hwy] at hi; omega
  apply BitVec.eq_of_toNat_eq
  have hall : ∀ v ∈ ncode (w, x) ++ ncode y, v < 2 ^ w := by
    intro v hv; rcases List.mem_append.1 hv with h | h
    · exact hfwx v h
    · exact hfity v h
  have heq : wcode w (w, x) ++ wcode w y = triples w (ncode (w, x) ++ ncode y) := by
    rw [hwx, hwy, triples_append]
  rw [hT', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hout i hi', List.getElem_of_eq heq,
    triples_getElem hw hall]

/-- `outputs_of_exec`, with the word size named. -/
theorem outputs_of_exec' (c : Cmd) {W scale : ℕ} (hsmall : Small W c.lines) (x : Input)
    (y : Output) (hx : Layout x) (hxs : Skips x) (hy : Layout y) (hyr : ReadsBack y) {w : ℕ}
    (hwdef : (cmdAlgorithm Input Output c W scale).wordSize x = w) (hw : 0 < w)
    (hfit : Fits w x) (hfity : Fits w y)
    (hlen : 3 * ((ncode (w, x)).length + (ncode y).length) ≤ 2 ^ w) {k : ℕ} {m' : Mem}
    (hE : Exec (2 ^ w) c (initMem w x) k m')
    (hout : ∀ i < 3 * ((ncode (w, x)).length + (ncode y).length),
      m' i = (tripleNat (ncode (w, x) ++ ncode y)).getD i 0) :
    Outputs (cmdAlgorithm Input Output c W scale) (tdWordRAM ops) x y ∧
      HaltsWithin (cmdAlgorithm Input Output c W scale) (tdWordRAM ops) x (k + 1) := by
  subst hwdef
  exact outputs_of_exec c hsmall x y hx hxs hy hyr hw hfit hfity hlen hE hout

theorem map_halted {α β : Type*} {f : α → β} {s : Status α} {b : β} (h : s.map f = .halted b) :
    ∃ a, s = .halted a := by
  cases s with
  | running a => simp [Status.map] at h
  | halted a => exact ⟨a, rfl⟩

theorem status_halted_mono {PC I A V In Out : Type*} [Fintype PC]
    {alg : Algorithm PC I Bool A V In Out} {sem : Semantics I Bool A V} {x : In} {a b : ℕ}
    {st : Program.State PC A V} (h : (Runnable.run alg sem).status x a = .halted st)
    (hab : a ≤ b) : (Runnable.run alg sem).status x b = .halted st :=
  run_halted_of_le (program := alg.program) (semantics := sem) h hab

theorem haltsWithin_mono (c : Cmd) {W scale : ℕ} {x : Input} {a b : ℕ}
    (h : HaltsWithin (cmdAlgorithm Input Output c W scale) (tdWordRAM ops) x a) (hab : a ≤ b) :
    HaltsWithin (cmdAlgorithm Input Output c W scale) (tdWordRAM ops) x b := by
  obtain ⟨st, hst⟩ := h
  obtain ⟨st', hst'⟩ := map_halted hst
  refine ⟨⟨_, st'⟩, ?_⟩
  show Status.map _ ((Runnable.run _ _).status _ b) = _
  rw [status_halted_mono hst' hab]
  rfl

end Glue

end Formalgo.LLMUnchecked

end

section

/-!
## Lists of numbers in and out


For an input list `x` of length `n`, the tape holds `w`, `n` and `x` as triples in cells
`[0, L)`, `L = 3 (n + 2)`, and the output list goes in `[L, N)`, `N = 6 n + 9`. Programs copy `x`
into an array at `A = S + nK`, transform it, and write it out.
-/

namespace Formalgo.LLMUnchecked

open Function Cmd

/-! ### Triples -/

theorem getD_append_right' (a b : List ℕ) (i : ℕ) : (a ++ b).getD (a.length + i) 0 = b.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem getD_append_left' (a b : List ℕ) {i : ℕ} (hi : i < a.length) :
    (a ++ b).getD i 0 = a.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_le' (l : List ℕ) {i : ℕ} (hi : l.length ≤ i) : l.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem tripleNat_cons (v : ℕ) (l : List ℕ) : tripleNat (v :: l) = 1 :: v :: 0 :: tripleNat l := by
  simp [tripleNat]

theorem getD_cons3 (a b c : ℕ) (t : List ℕ) (i : ℕ) :
    (a :: b :: c :: t).getD (i + 3) 0 = t.getD i 0 := by
  simp [List.getD_eq_getElem?_getD]

theorem tripleNat_getD_cons (v : ℕ) (l : List ℕ) (k : ℕ) :
    (tripleNat (v :: l)).getD k 0 =
      if k = 0 then 1 else if k = 1 then v else if k = 2 then 0 else (tripleNat l).getD (k - 3) 0 := by
  rw [tripleNat_cons]
  rcases k with _ | _ | _ | k <;> simp [List.getD_eq_getElem?_getD]

theorem tripleNat_getD_mul (l : List ℕ) (i : ℕ) :
    (tripleNat l).getD (3 * i) 0 = if i < l.length then 1 else 0 := by
  induction l generalizing i with
  | nil => simp [tripleNat]
  | cons v l ih =>
    rcases i with _ | i
    · simp [tripleNat_cons]
    · rw [tripleNat_cons, show 3 * (i + 1) = 3 * i + 3 by omega, getD_cons3, ih]
      simp

theorem tripleNat_getD_mul_one (l : List ℕ) (i : ℕ) :
    (tripleNat l).getD (3 * i + 1) 0 = if h : i < l.length then l[i] else 0 := by
  induction l generalizing i with
  | nil => simp [tripleNat]
  | cons v l ih =>
    rcases i with _ | i
    · simp [tripleNat_cons]
    · rw [tripleNat_cons, show 3 * (i + 1) + 1 = 3 * i + 1 + 3 by omega, getD_cons3, ih]
      simp

theorem tripleNat_getD_mul_two (l : List ℕ) (i : ℕ) :
    (tripleNat l).getD (3 * i + 2) 0 = 0 := by
  induction l generalizing i with
  | nil => simp [tripleNat]
  | cons v l ih =>
    rcases i with _ | i
    · simp [tripleNat_cons]
    · rw [tripleNat_cons, show 3 * (i + 1) + 2 = 3 * i + 2 + 3 by omega, getD_cons3, ih]

theorem tripleNat_getD_append_right (a b : List ℕ) (i : ℕ) :
    (tripleNat (a ++ b)).getD (3 * a.length + i) 0 = (tripleNat b).getD i 0 := by
  rw [tripleNat_append, show 3 * a.length = (tripleNat a).length by simp, getD_append_right']

theorem tripleNat_getD_append_left (a b : List ℕ) {i : ℕ} (hi : i < 3 * a.length) :
    (tripleNat (a ++ b)).getD i 0 = (tripleNat a).getD i 0 := by
  rw [tripleNat_append, getD_append_left' _ _ (by simpa using hi)]

theorem tripleNat_getD_of_le (l : List ℕ) {i : ℕ} (hi : 3 * l.length ≤ i) :
    (tripleNat l).getD i 0 = 0 :=
  getD_of_le' _ (by simpa using hi)

/-! ### The input -/

section Input

variable {w : ℕ} {x : List ℕ}

theorem ncode_list_nat (x : List ℕ) : ncode x = x.length :: x := by
  rw [ncode_list]; congr 1
  induction x with
  | nil => rfl
  | cons v x ih => rw [List.flatMap_cons, ih, ncode_nat]; rfl

theorem ncode_input (w : ℕ) (x : List ℕ) : ncode (w, x) = w :: x.length :: x := by
  rw [ncode_prod, ncode_nat, ncode_list_nat]; rfl

theorem initMem_list (a : ℕ) :
    initMem w x a = (tripleNat (w :: x.length :: x)).getD a 0 := by
  simp [initMem, ncode_input]

theorem initMem_0 : initMem w x 0 = 1 := by
  simpa [initMem_list] using tripleNat_getD_mul (w :: x.length :: x) 0

theorem initMem_1 : initMem w x 1 = w := by
  simpa [initMem_list] using tripleNat_getD_mul_one (w :: x.length :: x) 0

theorem initMem_2 : initMem w x 2 = 0 := by
  simpa [initMem_list] using tripleNat_getD_mul_two (w :: x.length :: x) 0

theorem initMem_3 : initMem w x 3 = 1 := by
  simpa [initMem_list] using tripleNat_getD_mul (w :: x.length :: x) 1

theorem initMem_4 : initMem w x 4 = x.length := by
  simpa [initMem_list] using tripleNat_getD_mul_one (w :: x.length :: x) 1

theorem initMem_elem {i : ℕ} (hi : i < x.length) : initMem w x (3 * i + 7) = x[i] := by
  have := tripleNat_getD_mul_one (w :: x.length :: x) (i + 2)
  rw [show 3 * (i + 2) + 1 = 3 * i + 7 by omega] at this
  simpa [initMem_list, hi] using this

theorem initMem_high {a : ℕ} (ha : 3 * (x.length + 2) ≤ a) : initMem w x a = 0 := by
  rw [initMem_list, tripleNat_getD_of_le _ (by simpa using ha)]

end Input

/-! ### Computing `S` -/

/-- `S = 6 n + 9 + nK`, into cell `0`. -/
def listSetS : Cmd := seqs [add 0 4 4, add 0 0 4, add 0 0 0, const 2 41, add 0 0 2]

theorem exec_listSetS {B n : ℕ} {m : Mem} (h4 : m 4 = n) (hB : 6 * n + 41 < B) :
    ∃ m', Exec B listSetS m 6 m' ∧ m' 0 = 6 * n + 41 ∧ ∀ a, a ≠ 0 → a ≠ 2 → m' a = m a := by
  have e := Exec.seq (B := B) (m := m) (.add (d := 0) (l := 4) (r := 4) (by omega) (by omega)
    (by omega) (by rw [h4]; omega))
    (.seq (.add (d := 0) (l := 0) (r := 4) (by omega) (by omega) (by omega)
      (by simp [update_apply, h4]; omega))
    (.seq (.add (d := 0) (l := 0) (r := 0) (by omega) (by omega) (by omega)
      (by simp [update_apply, h4]; omega))
    (.seq (.const (d := 2) (v := 41) (by omega) (by omega))
    (.seq (.add (d := 0) (l := 0) (r := 2) (by omega) (by omega) (by omega)
      (by simp [update_apply, h4]; omega))
    (.const (d := 2) (v := 0) (by omega) (by omega))))))
  refine ⟨_, e, ?_, ?_⟩
  · simp [update_apply, h4]; omega
  · intro a ha hb; simp [update_apply, ha, hb]

/-! ### Loading the input into the array at `A` -/

/-- One step of loading: `A[i] := vm[va]`, `i += 1`, `va += 3`. -/
def loadBody : Cmd := seqs [vread 14 12, add 13 9 11, store 13 14, add 11 11 3, add 12 12 16,
  less 15 11 4]

/-- Load `x` into `A[0, n)`. -/
def loadLoop : Cmd := seqs [const 11 0, const 12 7, less 15 11 4, loop 15 3 loadBody]

/-- The registers fixed throughout a list program. -/
def ListRegs (S n A : ℕ) (m : Mem) : Prop :=
  Regs S m ∧ m 4 = n ∧ m 8 = 0 ∧ m 9 = A ∧ m 10 = A + n ∧ m 16 = 3

theorem ListRegs.update {S n A r v : ℕ} {m : Mem} (h : ListRegs S n A m)
    (hr : r ≠ 1 ∧ r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 8 ∧ r ≠ 9 ∧ r ≠ 10 ∧ r ≠ 16) :
    ListRegs S n A (Function.update m r v) := by
  obtain ⟨hR, h4, h8, h9, h10, h16⟩ := h
  refine ⟨hR.update ⟨hr.1, hr.2.1, hr.2.2.2.1⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [update_apply, *] <;> omega

theorem ListRegs.of_frame {S n A : ℕ} {m m' : Mem} (h : ListRegs S n A m)
    (hf : ∀ a, a ≠ rT → a ≠ rP → a ≠ 14 → m' a = m a) : ListRegs S n A m' := by
  obtain ⟨⟨h1, h3, h5⟩, h4, h8, h9, h10, h16⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hf _ (by omega) (by omega) (by omega)] <;>
    assumption

set_option maxHeartbeats 1000000 in
theorem exec_loadLoop {B S n A : ℕ} {m : Mem} {x : List ℕ} (hn : x.length = n)
    (hR : ListRegs S n A m) (hKS : nK ≤ S) (hA : A = S + nK) (hB : A + n + nK < B)
    (hx : ∀ j < n, vm S m (3 * j + 7) = x[j]!) (hxB : ∀ j < n, x[j]! < B)
    (hxS : 3 * n + 7 < S) :
    ∃ m' k, Exec B loadLoop m k m' ∧ k ≤ 13 * n + 8 ∧ ListRegs S n A m' ∧
      (∀ j < n, vm S m' (A + j) = x[j]!) ∧
      ∀ a, (a < A ∨ A + n ≤ a) → vm S m' a = vm S m a := by
  -- The loop invariant, with `i` iterations done.
  let P : Mem → ℕ → Prop := fun m' s => ∃ i ≤ n, ListRegs S n A m' ∧ m' 11 = i ∧
    m' 12 = 3 * i + 7 ∧ m' 15 = (if i < n then 1 else 0) ∧
    (∀ j < i, vm S m' (A + j) = x[j]!) ∧
    (∀ a, (a < A ∨ A + i ≤ a) → vm S m' a = vm S m a) ∧ s ≤ 13 * i + 3
  let Q : Mem → ℕ → Prop := fun m' s => ListRegs S n A m' ∧
    (∀ j < n, vm S m' (A + j) = x[j]!) ∧
    (∀ a, (a < A ∨ A + n ≤ a) → vm S m' a = vm S m a) ∧ s ≤ 13 * n + 4
  have hloop := Exec.loop_of (B := B) (l := 15) (r := 3) (body := loadBody) P
    (fun m' => n - m' 11) Q (by omega) (by omega)
    (by
      rintro m' s ⟨i, hi, hR', h11, h12, h15, hA', hfr, hs⟩ heq
      obtain ⟨⟨h'1, h'3, h'5⟩, h'4, h'8, h'9, h'10, h'16⟩ := id hR'
      have hlt : i < n := by
        by_contra h; simp [h15, h'3, h] at heq
      obtain ⟨m₁, k₁, e₁, hk₁, hR₁, h₁14, hvm₁, hfr₁⟩ :=
        exec_vread (B := B) (d := 14) (va := 12) hR'.1 (by omega) (by omega) (by omega)
          (by omega) hKS (by omega) (by rw [h12]; omega)
      have hLR₁ : ListRegs S n A m₁ := hR'.of_frame (fun a h1 h2 h3 => hfr₁ a h1 h2 h3)
      have h₁11 : m₁ 11 = i := by rw [hfr₁ 11 (by omega) (by omega) (by omega), h11]
      have h₁12 : m₁ 12 = 3 * i + 7 := by rw [hfr₁ 12 (by omega) (by omega) (by omega), h12]
      have hval : m₁ 14 = x[i]! := by
        rw [h₁14, h12, hfr (3 * i + 7) (.inl (by omega)), hx i hlt]
      obtain ⟨⟨h₁1, h₁3, h₁5⟩, h₁4, h₁8, h₁9, h₁10, h₁16⟩ := id hLR₁
      -- `A[i] := M[14]`, `i += 1`, `va += 3`, compare, and the final `const 2 0`.
      have e := Exec.seq e₁
        (.seq (.add (m := m₁) (d := 13) (l := 9) (r := 11) (by omega) (by omega) (by omega)
          (by omega))
        (.seq (.store (p := 13) (s := 14) (by omega) (by omega))
        (.seq (.add (d := 11) (l := 11) (r := 3) (by omega) (by omega) (by omega) (by memo))
        (.seq (.add (d := 12) (l := 12) (r := 16) (by omega) (by omega) (by omega) (by memo))
        (.seq (.less (d := 15) (l := 11) (r := 4) (by omega) (by omega) (by omega))
          (.const (d := 2) (v := 0) (by omega) (by omega)))))))
      have hvm : ∀ v₁₁ v₁₂ v₁₅ a, vm S (update (update (update (update (update (update m₁ 13
          (m₁ 9 + m₁ 11)) (update m₁ 13 (m₁ 9 + m₁ 11) 13) (update m₁ 13 (m₁ 9 + m₁ 11) 14))
          11 v₁₁) 12 v₁₂) 15 v₁₅) 2 0) a = update (vm S m') (A + i) (x[i]!) a := by
        intro v₁₁ v₁₂ v₁₅ a
        simp (disch := omega) only [Function.update_self, Function.update_of_ne, vm_update_reg,
          vm_update_high]
        rw [hvm₁, h₁9, h₁11, hval]
      refine ⟨_, _, e, ⟨i + 1, by omega, ?_, by memo, by memo, by memo, ?_, ?_, ?_⟩, by memo⟩
      · refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> memo
      · intro j hj
        rw [hvm, update_apply]
        split_ifs with h
        · have : j = i := by omega
          subst this; rfl
        · exact hA' j (by omega)
      · intro a ha
        rw [hvm, update_apply, if_neg (by omega)]
        exact hfr a (by omega)
      · omega)
    (by
      rintro m' s ⟨i, hi, hR', h11, h12, h15, hA', hfr, hs⟩ hne
      have hin : i = n := by
        by_contra h
        obtain ⟨⟨_, h'3, _⟩, _⟩ := hR'
        exact hne (by rw [h15, h'3, if_pos (by omega)])
      subst hin
      exact ⟨hR', hA', hfr, by omega⟩)
  obtain ⟨⟨h1, h3, h5⟩, h4, h8, h9, h10, h16⟩ := id hR
  -- The start: `i := 0`, `va := 7`, compare.
  have c₁ := Exec.const (B := B) (m := m) (d := 11) (v := 0) (by omega) (by omega)
  have c₂ := Exec.const (B := B) (m := update m 11 0) (d := 12) (v := 7) (by omega) (by omega)
  have c₃ := Exec.less (B := B) (m := update (update m 11 0) 12 7) (d := 15) (l := 11) (r := 4)
    (by omega) (by omega) (by omega)
  set m₀ := update (update (update m 11 0) 12 7) 15
      (if update (update m 11 0) 12 7 11 < update (update m 11 0) 12 7 4 then 1 else 0) with hm₀
  have hvm₀ : ∀ a, vm S m₀ a = vm S m a := by
    intro a; simp (disch := omega) only [m₀, vm_update_reg]
  have hP₀ : P m₀ 3 := by
    refine ⟨0, by omega, ?_, by simp [m₀], by simp [m₀], ?_, by simp, ?_,
      by omega⟩
    · refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> (simp only [m₀]; memo)
    · simp only [m₀, update_apply]; split_ifs <;> omega
    · intro a _; rw [hvm₀]
  obtain ⟨m₂, k₂, e₂, hR₂, hA₂, hfr₂, hk₂⟩ := hloop m₀ 3 hP₀
  have e₃ := Exec.const (B := B) (m := m₂) (d := 2) (v := 0) (by omega) (by omega)
  refine ⟨_, _, .seq c₁ (.seq c₂ (.seq c₃ (.seq e₂ e₃))), by omega, hR₂.update (by omega), ?_, ?_⟩
  · intro j hj; rw [vm_update_reg (by omega) hKS]; exact hA₂ j hj
  · intro a ha; rw [vm_update_reg (by omega) hKS]; exact hfr₂ a ha

/-! ### Writing the array at `A` out -/

/-- Set `L = 3 n + 6`, write `[1, n, 0]` at `L`, and start the loop. -/
def emitHead : Cmd := seqs [add 17 4 4, add 17 17 4, const 14 6, add 17 17 14, copy 12 17,
  vwrite 12 3, add 12 12 3, vwrite 12 4, add 12 12 3, vwrite 12 8, add 12 12 3, const 11 0,
  less 15 11 4]

/-- Write `[1, A[i], 0]` at `va`. -/
def emitBody : Cmd := seqs [vwrite 12 3, add 12 12 3, add 13 9 11, load 14 13, vwrite 12 14,
  add 12 12 3, vwrite 12 8, add 12 12 3, add 11 11 3, less 15 11 4]

/-- Write `n` and `A[0, n)` as triples from `L = 3 n + 6`. -/
def emitLoop : Cmd := seq emitHead (loop 15 3 emitBody)

set_option maxHeartbeats 1000000 in
theorem exec_emitLoop {B S n A : ℕ} {m : Mem} {ys : List ℕ} (hn : ys.length = n)
    (hR : ListRegs S n A m) (hKS : nK ≤ S) (hA : A = S + nK) (hB : A + n + nK < B)
    (hys : ∀ j < n, vm S m (A + j) = ys[j]!) (hyB : ∀ j < n, ys[j]! < B)
    (hNS : 6 * n + 9 ≤ S) :
    ∃ m' k, Exec B emitLoop m k m' ∧ k ≤ 30 * n + 60 ∧ ListRegs S n A m' ∧
      (∀ a, 3 * n + 6 ≤ a → a < 6 * n + 9 →
        vm S m' a = (tripleNat (n :: ys)).getD (a - (3 * n + 6)) 0) ∧
      ∀ a, (a < 3 * n + 6 ∨ 6 * n + 9 ≤ a) → vm S m' a = vm S m a := by
  obtain ⟨⟨h1, h3, h5⟩, h4, h8, h9, h10, h16⟩ := id hR
  suffices h : Runs B emitLoop m fun m' k => ListRegs S n A m' ∧
      (∀ a, 3 * n + 6 ≤ a → a < 6 * n + 9 →
        vm S m' a = (tripleNat (n :: ys)).getD (a - (3 * n + 6)) 0) ∧
      (∀ a, (a < 3 * n + 6 ∨ 6 * n + 9 ≤ a) → vm S m' a = vm S m a) ∧ k ≤ 30 * n + 60 by
    obtain ⟨m', k, e, hq1, hq2, hq3, hq4⟩ := h; exact ⟨m', k, e, hq4, hq1, hq2, hq3⟩
  rstep
  -- The head.
  rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep
  refine Runs.vwrite (S := S) ⟨by rs, by rs, by rs⟩ (by omega) (by omega) (by omega) (by omega)
    hKS (by omega) (by rs) ?_
  intro m₆ k₆ hk₆ hR₆ hvm₆ hfr₆
  rstep; rstep; rstep
  refine Runs.vwrite (S := S) ⟨by rs, by rs, by rs⟩ (by omega) (by omega) (by omega) (by omega)
    hKS (by omega) (by rs) ?_
  intro m₈ k₈ hk₈ hR₈ hvm₈ hfr₈
  rstep; rstep; rstep
  refine Runs.vwrite (S := S) ⟨by rs, by rs, by rs⟩ (by omega) (by omega) (by omega) (by omega)
    hKS (by omega) (by rs) ?_
  intro m₁₀ k₁₀ hk₁₀ hR₁₀ hvm₁₀ hfr₁₀
  rstep; rstep; rstep; rstep; rstep; rstep; rstep
  -- The loop invariant, with `i` triples written after the first.
  let P : Mem → ℕ → Prop := fun m' s => ∃ i ≤ n, ListRegs S n A m' ∧ m' 11 = i ∧
    m' 12 = 3 * n + 9 + 3 * i ∧ m' 15 = (if i < n then 1 else 0) ∧
    (∀ a, 3 * n + 6 ≤ a → a < 3 * n + 9 + 3 * i →
      vm S m' a = (tripleNat (n :: ys)).getD (a - (3 * n + 6)) 0) ∧
    (∀ a, (a < 3 * n + 6 ∨ 3 * n + 9 + 3 * i ≤ a) → vm S m' a = vm S m a) ∧ s ≤ 30 * i
  refine Runs.loop P (fun m' => n - m' 11) (by omega) (by omega) ?_ ?_ ?_
  · -- One iteration.
    rintro m' s ⟨i, hi, hR', h11, h12, h15, hdone, hfr, hs⟩ heq
    obtain ⟨⟨h'1, h'3, h'5⟩, h'4, h'8, h'9, h'10, h'16⟩ := id hR'
    have hlt : i < n := by by_contra h; simp [h15, h'3, h] at heq
    rstep
    refine Runs.vwrite (S := S) ⟨by rs, by rs, by rs⟩ (by omega) (by omega) (by omega)
      (by omega) hKS (by omega) (by rs) ?_
    intro m₁ k₁ hk₁ hR₁ hvm₁ hfr₁
    rstep; rstep; rstep; rstep; rstep; rstep; rstep
    refine Runs.vwrite (S := S) ⟨by rs, by rs, by rs⟩ (by omega) (by omega) (by omega)
      (by omega) hKS (by omega) (by rs) ?_
    intro m₅ k₅ hk₅ hR₅ hvm₅ hfr₅
    rstep; rstep; rstep
    refine Runs.vwrite (S := S) ⟨by rs, by rs, by rs⟩ (by omega) (by omega) (by omega)
      (by omega) hKS (by omega) (by rs) ?_
    intro m₇ k₇ hk₇ hR₇ hvm₇ hfr₇
    rstep; rstep; rstep; rstep; rstep; rstep; rstep
    have hval : m₁ (A + i) = ys[i]! := by
      have h := congrFun hvm₁ (A + i)
      rw [vm_high hKS (by omega), update_apply, if_neg (by rw [h12]; omega),
        hfr _ (.inr (by omega)), hys i hlt] at h
      exact h
    refine ⟨⟨i + 1, by omega, ⟨⟨by rs, by rs, by rs⟩, by rs, by rs, by rs, by rs, by rs⟩, by rs,
      by rs, by rs, ?_, ?_, by omega⟩, by rs⟩
    · intro a ha1 ha2
      simp (disch := omega) only [*]
      simp only [update_apply]
      split_ifs with e₂ e₁ e₀
      · subst e₂
        rw [show 3 * n + 9 + 3 * i + 1 + 1 - (3 * n + 6) = 3 * (i + 1) + 2 by omega,
          tripleNat_getD_mul_two]
      · subst e₁
        rw [show 3 * n + 9 + 3 * i + 1 - (3 * n + 6) = 3 * (i + 1) + 1 by omega,
          tripleNat_getD_mul_one]
        have := hval; rw [hA] at this
        simpa [hn, hlt] using this
      · subst e₀
        rw [show 3 * n + 9 + 3 * i - (3 * n + 6) = 3 * (i + 1) by omega, tripleNat_getD_mul]
        simp [hn, hlt]
      · exact hdone a ha1 (by omega)
    · intro a ha
      simp (disch := omega) only [*]
      simp only [update_apply]
      split_ifs <;> first | omega | exact hfr a (by omega)
  · -- The exit.
    rintro m' s ⟨i, hi, hR', h11, h12, h15, hdone, hfr, hs⟩ hne
    have hin : i = n := by
      by_contra h
      obtain ⟨⟨_, h'3, _⟩, _⟩ := hR'
      exact hne (by rw [h15, h'3, if_pos (by omega)])
    subst hin
    exact ⟨hR', fun a ha1 ha2 => hdone a ha1 (by omega), fun a ha => hfr a (by omega), by omega⟩
  · -- The start.
    refine ⟨0, by omega, ⟨⟨by rs, by rs, by rs⟩, by rs, by rs, by rs, by rs, by rs⟩, by rs, by rs,
      by rs, ?_, ?_, by omega⟩
    · intro a ha1 ha2
      simp (disch := omega) only [*]
      simp only [update_apply, tripleNat_getD_cons]
      split_ifs <;> first | rfl | omega
    · intro a ha
      simp (disch := omega) only [*]
      simp only [update_apply]
      split_ifs <;> first | rfl | omega

end Formalgo.LLMUnchecked

end

section

/-!
## Algorithms on lists of numbers


A list program loads its input into the array at `A`, runs a core on it, and writes the array out.
If the core computes a permutation `f x` of the array, the program is a TD word RAM algorithm for
`f`.
-/

namespace Formalgo.LLMUnchecked

open Function Cmd

/-- `core` turns the list `x` in the array at `A` into `f x` within `t n` steps, leaving the fixed
registers and the memory below `A` alone. -/
def CoreSpec (core : Cmd) (f : List ℕ → List ℕ) (t : ℕ → ℕ) : Prop :=
  ∀ (B S A : ℕ) (m : Mem) (x : List ℕ), ListRegs S x.length A m → nK ≤ S → A = S + nK →
    A + 2 * x.length + nK < B → (∀ v ∈ x, v < B) →
    (∀ j < x.length, vm S m (A + j) = x[j]!) →
    Runs B core m fun m' k => ListRegs S x.length A m' ∧
      (∀ j < x.length, vm S m' (A + j) = (f x)[j]!) ∧ (∀ a < A, vm S m' a = vm S m a) ∧
      k ≤ t x.length

/-- Set the fixed registers, load the input, run `core`, and write the array out. -/
def listBody (core : Cmd) : Cmd :=
  seqs [const 3 1, const 5 32, const 8 0, const 16 3, add 9 1 5, add 10 9 4, loadLoop, core,
    emitLoop]

/-- The list program running `core`. -/
def listProgram (core : Cmd) : Cmd := harness nK listSetS (listBody core)

theorem getElem!_eq_getElem {x : List ℕ} {j : ℕ} (hj : j < x.length) : x[j]! = x[j] := by
  simp [hj]

set_option maxHeartbeats 1000000 in
theorem listBody_runs {core : Cmd} {f : List ℕ → List ℕ} {t : ℕ → ℕ} (hcore : CoreSpec core f t)
    (hf : ∀ x, (f x).Perm x) {B S w : ℕ} {x : List ℕ} (hS : S = 6 * x.length + 41)
    (hB : 8 * x.length + 105 < B) (hxB : ∀ v ∈ x, v < B) {m : Mem} (h1 : m rS = S)
    (hvm : ∀ a, vm S m a = initMem w x a) (hreg : ∀ r, 3 ≤ r → r < nK → m r = initMem w x r) :
    Runs B (listBody core) m fun m' k => m' rS = S ∧
      (∀ a < S, a ≠ 0 → a ≠ 2 →
        vm S m' a = (tripleNat (ncode (w, x) ++ ncode (f x))).getD a 0) ∧
      k ≤ t x.length + 43 * x.length + 80 := by
  set n := x.length with hn
  have hKS : nK ≤ S := by omega
  have h4 : m 4 = n := by rw [hreg 4 (by omega) (by omega), initMem_4]
  clear hreg
  rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep
  rstep
  rename_i m₁ hm₁ hf₁ hv₁ m₂ hm₂ hf₂ hv₂ m₃ hm₃ hf₃ hv₃ m₄ hm₄ hf₄ hv₄ m₅ hm₅ hf₅ hv₅ m₆ hm₆ hf₆ hv₆
  have hR₆ : ListRegs S n (S + nK) m₆ := ⟨⟨by rs, by rs, by rs⟩, by rs, by rs, by rs, by rs, by rs⟩
  have hvm₆ : vm S m₆ = vm S m := by rw [hv₆, hv₅, hv₄, hv₃, hv₂, hv₁]
  -- Load.
  obtain ⟨m₇, k₇, e₇, hk₇, hR₇, hA₇, hfr₇⟩ := exec_loadLoop (B := B) (x := x) rfl hR₆ hKS rfl
    (by omega) (fun j hj => by rw [hvm₆, hvm, show 3 * j + 7 = 3 * j + 7 from rfl,
      initMem_elem hj, getElem!_eq_getElem hj])
    (fun j hj => by rw [getElem!_eq_getElem hj]; exact hxB _ (List.getElem_mem hj)) (by omega)
  refine ⟨m₇, k₇, e₇, ?_⟩
  rstep
  -- The core.
  refine Runs.mono (hcore B S (S + nK) m₇ x hR₇ hKS rfl (by omega) hxB hA₇) ?_
  rintro m₈ k₈ ⟨hR₈, hA₈, hfr₈, hk₈⟩
  have hk₈' : k₈ ≤ t n := hk₈
  rstep
  -- Write out.
  have hfn : (f x).length = n := (hf x).length_eq
  have hfB : ∀ j < n, (f x)[j]! < B := by
    intro j hj
    rw [getElem!_eq_getElem (by omega)]
    exact hxB _ ((hf x).subset (List.getElem_mem _))
  obtain ⟨m₉, k₉, e₉, hk₉, hR₉, hout₉, hfr₉⟩ := exec_emitLoop (B := B) (ys := f x) hfn hR₈ hKS rfl
    (by omega) hA₈ hfB (by omega)
  refine ⟨m₉, k₉, e₉, ?_⟩
  refine Runs.seqs_nilV hKS (by omega) ?_
  intro m₁₀ hm₁₀ hf₁₀ hv₁₀
  refine ⟨by rw [hf₁₀ _ (by omega)]; exact hR₉.1.1, ?_, by omega⟩
  intro a ha ha0 ha2
  rw [hv₁₀, ncode_input, ncode_list_nat, hfn]
  by_cases hL : a < 3 * n + 6
  · -- The input, unchanged.
    rw [hfr₉ a (.inl hL), hfr₈ a (by omega), hfr₇ a (.inl (by omega)), hvm₆, hvm, initMem_list,
      show w :: n :: x ++ n :: f x = (w :: n :: x) ++ (n :: f x) from rfl,
      tripleNat_getD_append_left _ _ (by simp; omega)]
  · by_cases hN : a < 6 * n + 9
    · -- The output.
      rw [hout₉ a (by omega) hN,
        show w :: n :: x ++ n :: f x = (w :: n :: x) ++ (n :: f x) from rfl,
        show a = 3 * (w :: n :: x).length + (a - (3 * n + 6)) by simp; omega,
        tripleNat_getD_append_right]
      congr 1; simp; omega
    · -- Blank.
      rw [hfr₉ a (.inr (by omega)), hfr₈ a (by omega), hfr₇ a (.inl (by omega)), hvm₆, hvm,
        initMem_high (by omega), tripleNat_getD_of_le _ (by simp [hfn]; omega)]

theorem cube_gt {n : ℕ} (h : 19 ≤ n) : 8 * n + 105 < (n + 2) ^ 3 := by
  have h1 : 21 * 21 ≤ (n + 2) * (n + 2) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : 21 * 21 * (n + 2) ≤ (n + 2) * (n + 2) * (n + 2) := Nat.mul_le_mul_right _ h1
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_one]
  omega

set_option maxHeartbeats 1000000 in
/-- A list program for a core computing a permutation `f x` outputs `f x`. -/
theorem list_outputs {core : Cmd} {f : List ℕ → List ℕ} {t : ℕ → ℕ} (hcore : CoreSpec core f t)
    (hf : ∀ x, (f x).Perm x) {W scale : ℕ} (hW : 8 ≤ W) (hscale : 3 ≤ scale)
    (hsmall : Small W (listProgram core).lines) (x : List ℕ) :
    Outputs (cmdAlgorithm (List ℕ) (List ℕ) (listProgram core) W scale) (tdWordRAM ops) x (f x) ∧
      HaltsWithin (cmdAlgorithm (List ℕ) (List ℕ) (listProgram core) W scale) (tdWordRAM ops) x
        (t x.length + 43 * x.length + 400) := by
  obtain ⟨hWw, hpow⟩ := wordSize_spec (Output := List ℕ) (listProgram core) W scale x
  generalize hwdef : (cmdAlgorithm (List ℕ) (List ℕ) (listProgram core) W scale).wordSize x = w
    at hWw hpow
  have hncode : ncode x = x.length :: x := ncode_list_nat x
  have hnM : x.length + 1 ≤ codeMax (ncode x) := by
    have := length_le_codeMax (ncode x)
    rw [show (ncode x).length = x.length + 1 by rw [hncode]; rfl] at this
    exact this
  have hxM : ∀ v ∈ x, v ≤ codeMax (ncode x) :=
    fun v hv => le_codeMax (by rw [hncode]; exact .tail _ hv)
  have hM1 : codeMax (ncode x) + 1 ≤ 2 ^ w := le_trans (Nat.le_self_pow (by omega) _) hpow
  have h256 : 256 ≤ 2 ^ w :=
    le_trans (show 256 ≤ 2 ^ 8 by decide) (Nat.pow_le_pow_right (by omega) (le_trans hW hWw))
  have hB : 8 * x.length + 105 < 2 ^ w := by
    by_cases hn19 : x.length < 19
    · omega
    · have h3 : (x.length + 2) ^ 3 ≤ (codeMax (ncode x) + 1) ^ 3 :=
        Nat.pow_le_pow_left (by omega) _
      have h3' : (codeMax (ncode x) + 1) ^ 3 ≤ (codeMax (ncode x) + 1) ^ scale :=
        Nat.pow_le_pow_right (by omega) hscale
      have := cube_gt (n := x.length) (by omega)
      omega
  have hxB : ∀ v ∈ x, v < 2 ^ w := fun v hv => by have := hxM v hv; omega
  have hw : 0 < w := by omega
  have hfn : (f x).length = x.length := (hf x).length_eq
  -- Fits and layouts.
  have hfit : Fits w x := fits_list.2 ⟨by omega, fun a ha => fits_nat.2 (hxB a ha)⟩
  have hfity : Fits w (f x) := fits_list.2 ⟨by omega,
    fun a ha => fits_nat.2 (hxB a ((hf x).subset ha))⟩
  have hlenc : 3 * ((ncode (w, x)).length + (ncode (f x)).length) = 6 * x.length + 9 := by
    rw [ncode_input, ncode_list_nat]; simp [hfn]; omega
  -- The run.
  obtain ⟨m₁, hset, hm₁0, hm₁⟩ := exec_listSetS (B := 2 ^ w) (initMem_4 (w := w) (x := x))
    (by omega)
  obtain ⟨m', k, hE, hk, hout⟩ := exec_harness_vm (B := 2 ^ w) (S := 6 * x.length + 41)
    (N := 6 * x.length + 9)
    (fun a => (tripleNat (ncode (w, x) ++ ncode (f x))).getD a 0)
    (t x.length + 43 * x.length + 80)
    (by omega) (by omega) (by omega) hset hm₁0 hm₁ initMem_0 initMem_2 initMem_3
    (fun a ha => initMem_high (by omega))
    (by rw [ncode_input]; simpa using tripleNat_getD_mul (w :: x.length :: x ++ ncode (f x)) 0)
    (by simpa using tripleNat_getD_mul_two (ncode (w, x) ++ ncode (f x)) 0)
    (fun m hm1 hvm hreg => by
      obtain ⟨m', k, e, h1, hfin, hk⟩ := listBody_runs hcore hf (w := w) (x := x) rfl hB hxB hm1
        hvm hreg
      exact ⟨m', k, e, hk, h1, hfin⟩)
  have := outputs_of_exec' (listProgram core) hsmall x (f x)
    (layout_list fun a _ => layout_nat a) (readsBack_list fun a _ => readsBack_nat a).skips
    (layout_list fun a _ => layout_nat a) (readsBack_list fun a _ => readsBack_nat a) hwdef hw
    hfit hfity (by rw [hlenc]; omega) hE (fun i hi => hout i (by omega))
  exact ⟨this.1, haltsWithin_mono _ this.2 (by omega)⟩

/-- A list program for a core computing `f`, within a time bound. -/
theorem solvableWithin_list {core : Cmd} {f : List ℕ → List ℕ} {t : ℕ → ℕ}
    (hcore : CoreSpec core f t) (hf : ∀ x, (f x).Perm x) {W scale : ℕ} (hW : 8 ≤ W)
    (hscale : 3 ≤ scale) (hsmall : Small W (listProgram core).lines)
    (spec : IOSpec (List ℕ) (List ℕ)) (hspec : ∀ x, spec.valid x (f x)) (time : List ℕ → ℕ)
    (htime : ∀ x, t x.length + 43 * x.length + 400 ≤ time x) :
    (tdWordRAM ops).SolvableWithin spec time :=
  ⟨_, inferInstance, cmdAlgorithm (List ℕ) (List ℕ) (listProgram core) W scale,
    fun x => ⟨f x, (list_outputs hcore hf hW hscale hsmall x).1, hspec x⟩,
    fun x => haltsWithin_mono _ (list_outputs hcore hf hW hscale hsmall x).2 (htime x)⟩

end Formalgo.LLMUnchecked

end

section

/-!
## Merge sort


Bottom-up merge sort of the array at `A` (register `9`), with scratch array `A + n` (register
`10`).

| register | content         | register | content                 |
|----------|-----------------|----------|-------------------------|
| 18       | source array    | 25       | end of left run         |
| 19       | destination     | 26       | `q`, read in right run  |
| 20       | run width `w`   | 27       | end of right run        |
| 21       | `i`, start      | 28       | `k`, write position     |
| 22       | `mid`           | 29       | end of output           |
| 23       | `hi`            | 30, 31   | `M[p]`, `M[q]`          |
| 24       | `p`, read left  | 11–15    | conditions, temporaries |
-/

namespace Formalgo.Algorithms.Sorting.MergeSort

open LLMUnchecked Cmd

/-- No operation. -/
def nop : Cmd := const 2 0

/-- Take the left element: `M[k] := M[p]`, `p += 1`, `k += 1`. -/
def takeLeft : Cmd := seqs [load 30 24, store 28 30, add 24 24 3, add 28 28 3]

/-- Take the right element: `M[k] := M[q]`, `q += 1`, `k += 1`. -/
def takeRight : Cmd := seqs [load 31 26, store 28 31, add 26 26 3, add 28 28 3]

/-- One merge step. -/
def mergeBody : Cmd := seqs [less 13 24 25,
  ite 13 3
    (seqs [less 14 26 27,
      ite 14 3 (seqs [load 30 24, load 31 26, less 15 31 30, ite 15 3 takeRight takeLeft])
        takeLeft])
    takeRight,
  less 12 28 29]

/-- Merge the runs at `i`, then move to the next pair. -/
def pairBody : Cmd := seqs [add 22 21 20, less 12 22 4, ite 12 3 nop (copy 22 4),
  add 23 22 20, less 12 23 4, ite 12 3 nop (copy 23 4),
  add 24 18 21, add 25 18 22, copy 26 25, add 27 18 23, add 28 19 21, add 29 19 23,
  less 12 28 29, loop 12 3 mergeBody, copy 21 23, less 11 21 4]

/-- One pass: merge all pairs of runs, swap the arrays, and double the width. -/
def passBody : Cmd := seqs [const 21 0, less 11 21 4, loop 11 3 pairBody,
  copy 13 18, copy 18 19, copy 19 13, add 20 20 20, less 11 20 4]

/-- Copy the source array back to `A`. -/
def copyBody : Cmd := seqs [add 13 18 21, load 30 13, add 14 9 21, store 14 30, add 21 21 3,
  less 11 21 4]

/-- Merge sort of the array at `A`. -/
def core : Cmd := seqs [copy 18 9, copy 19 10, const 20 1, less 11 20 4, loop 11 3 passBody,
  ite 18 9 nop (seqs [const 21 0, less 11 21 4, loop 11 3 copyBody])]

end Formalgo.Algorithms.Sorting.MergeSort

end

section

/-!
## Merge passes on lists

-/

namespace Formalgo.Algorithms.Sorting.MergeSort

/-! ### Merge passes on lists -/

section MergePass

variable {α : Type*} (le : α → α → Bool)

/-- Merge each pair of consecutive runs of width `w`. -/
def mergePass (w : ℕ) (l : List α) : List α :=
  if _ : 0 < w ∧ l ≠ [] then
    (l.take w).merge ((l.drop w).take w) le ++ mergePass w (l.drop (2 * w))
  else l
termination_by l.length
decreasing_by
  obtain ⟨_hw, hl⟩ := ‹0 < w ∧ l ≠ []›
  have := List.length_pos_of_ne_nil hl
  simp only [List.length_drop]
  omega

/-- `passes j l` performs the passes with widths `1, 2, …, 2 ^ (j - 1)`. -/
def passes : ℕ → List α → List α
  | 0, l => l
  | j + 1, l => mergePass le (2 ^ j) (passes j l)

/-- Every run `l[jw, (j+1)w)` of width `w` is sorted. -/
def RunsSorted (w : ℕ) (l : List α) : Prop :=
  ∀ j, ((l.drop (j * w)).take w).Pairwise (le · ·)

variable {le}

theorem mergePass_of_ne_nil {w : ℕ} {l : List α} (hw : 0 < w) (hl : l ≠ []) :
    mergePass le w l =
      (l.take w).merge ((l.drop w).take w) le ++ mergePass le w (l.drop (2 * w)) := by
  rw [mergePass, dif_pos ⟨hw, hl⟩]

@[simp] theorem mergePass_nil (w : ℕ) : mergePass le w [] = [] := by
  rw [mergePass]; simp

theorem mergePass_perm (w : ℕ) (l : List α) : (mergePass le w l).Perm l := by
  induction l using mergePass.induct w with
  | case1 l h ih =>
    rw [mergePass_of_ne_nil h.1 h.2]
    refine ((List.merge_perm_append le).append ih).trans (List.Perm.of_eq ?_)
    rw [List.append_assoc, Nat.two_mul, ← List.drop_drop, List.take_append_drop,
      List.take_append_drop]
  | case2 l h => rw [mergePass, dif_neg h]

theorem length_mergePass (w : ℕ) (l : List α) : (mergePass le w l).length = l.length :=
  (mergePass_perm w l).length_eq

theorem length_merge_runs (w : ℕ) (l : List α) :
    ((l.take w).merge ((l.drop w).take w) le).length = min (2 * w) l.length := by
  simp; omega

/-- The first merged run of a pass. -/
theorem take_mergePass {w : ℕ} (hw : 0 < w) (l : List α) :
    (mergePass le w l).take (2 * w) = (l.take w).merge ((l.drop w).take w) le := by
  by_cases hl : l = []
  · simp [hl]
  have hM := length_merge_runs (le := le) w l
  rw [mergePass_of_ne_nil hw hl, List.take_append, List.take_of_length_le (by omega)]
  by_cases h : 2 * w ≤ l.length
  · rw [hM, Nat.min_eq_left h, Nat.sub_self, List.take_zero, List.append_nil]
  · rw [List.drop_eq_nil_of_le (as := l) (i := 2 * w) (by omega), mergePass_nil, List.take_nil,
      List.append_nil]

/-- The rest of a pass is a pass on the rest. -/
theorem drop_mergePass {w : ℕ} (hw : 0 < w) (l : List α) :
    (mergePass le w l).drop (2 * w) = mergePass le w (l.drop (2 * w)) := by
  by_cases hl : l = []
  · simp [hl]
  have hM := length_merge_runs (le := le) w l
  rw [mergePass_of_ne_nil hw hl, List.drop_append, List.drop_eq_nil_of_le (by omega),
    List.nil_append]
  by_cases h : 2 * w ≤ l.length
  · rw [hM, Nat.min_eq_left h, Nat.sub_self, List.drop_zero]
  · rw [List.drop_eq_nil_of_le (as := l) (i := 2 * w) (by omega)]; simp

theorem drop_mergePass_mul {w : ℕ} (hw : 0 < w) (l : List α) (j : ℕ) :
    (mergePass le w l).drop (j * (2 * w)) = mergePass le w (l.drop (j * (2 * w))) := by
  induction j generalizing l with
  | zero => simp
  | succ j ih => rw [Nat.succ_mul, ← List.drop_drop, ← List.drop_drop, ih, drop_mergePass hw]

theorem runsSorted_one (l : List α) : RunsSorted le 1 l := fun j => by
  cases l.drop (j * 1) <;> simp

/-- A pass with width `w` turns sorted runs of width `w` into sorted runs of width `2 w`. -/
theorem RunsSorted.mergePass (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) {w : ℕ} (hw : 0 < w) {l : List α} (h : RunsSorted le w l) :
    RunsSorted le (2 * w) (mergePass le w l) := fun j => by
  rw [drop_mergePass_mul hw, take_mergePass hw]
  refine List.pairwise_merge trans total _ _ ?_ ?_
  · simpa [Nat.mul_assoc, Nat.mul_left_comm] using h (2 * j)
  · simpa [List.drop_drop, Nat.mul_assoc, Nat.mul_left_comm, Nat.add_mul, Nat.mul_add]
      using h (2 * j + 1)

theorem RunsSorted.pairwise {w : ℕ} {l : List α} (h : RunsSorted le w l) (hl : l.length ≤ w) :
    l.Pairwise (le · ·) := by
  simpa [List.take_of_length_le hl] using h 0

theorem passes_perm (j : ℕ) (l : List α) : (passes le j l).Perm l := by
  induction j with
  | zero => rfl
  | succ j ih => exact (mergePass_perm _ _).trans ih

theorem runsSorted_passes (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (j : ℕ) (l : List α) :
    RunsSorted le (2 ^ j) (passes le j l) := by
  induction j with
  | zero => exact runsSorted_one l
  | succ j ih =>
    simpa [passes, Nat.pow_succ, Nat.mul_comm] using
      ih.mergePass trans total (Nat.two_pow_pos j)

/-! Steps of a merge. -/

theorem merge_nil' (l : List α) : l.merge [] le = l := by
  cases l <;> simp [List.merge]

/-- Merging the rest, after taking the left element. -/
theorem merge_drop_left {P Q : List α} {x y : ℕ}
    (h : (P.merge Q le).drop (x + y) = (P.drop x).merge (Q.drop y) le) (hx : x < P.length)
    (hyle : y ≤ Q.length) (hy : ∀ hyQ : y < Q.length, le P[x] (Q[y]'hyQ)) :
    (P.merge Q le).drop (x + y + 1) = (P.drop (x + 1)).merge (Q.drop y) le ∧
      ∃ h', (P.merge Q le)[x + y]'h' = P[x] := by
  have hlen : x + y < (P.merge Q le).length := by rw [List.length_merge]; omega
  rw [List.drop_eq_getElem_cons hlen, List.drop_eq_getElem_cons hx] at h
  by_cases hyQ : y < Q.length
  · rw [List.drop_eq_getElem_cons hyQ, List.cons_merge_cons, if_pos (hy hyQ),
      ← List.drop_eq_getElem_cons hyQ] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    exact ⟨h2, hlen, h1⟩
  · rw [List.drop_eq_nil_of_le (as := Q) (i := y) (by omega), merge_nil'] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    refine ⟨?_, hlen, h1⟩
    rw [List.drop_eq_nil_of_le (as := Q) (i := y) (by omega), merge_nil', h2]

/-- Merging the rest, after taking the right element. -/
theorem merge_drop_right {P Q : List α} {x y : ℕ}
    (h : (P.merge Q le).drop (x + y) = (P.drop x).merge (Q.drop y) le) (hy : y < Q.length)
    (hxle : x ≤ P.length) (hx : ∀ hxP : x < P.length, le (P[x]'hxP) Q[y] = false) :
    (P.merge Q le).drop (x + y + 1) = (P.drop x).merge (Q.drop (y + 1)) le ∧
      ∃ h', (P.merge Q le)[x + y]'h' = Q[y] := by
  have hlen : x + y < (P.merge Q le).length := by rw [List.length_merge]; omega
  rw [List.drop_eq_getElem_cons hlen, List.drop_eq_getElem_cons hy] at h
  by_cases hxP : x < P.length
  · rw [List.drop_eq_getElem_cons hxP, List.cons_merge_cons, if_neg (by simp [hx hxP]),
      ← List.drop_eq_getElem_cons hxP] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    exact ⟨h2, hlen, h1⟩
  · rw [List.drop_eq_nil_of_le (as := P) (i := x) (by omega), List.nil_merge] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    refine ⟨?_, hlen, h1⟩
    rw [List.drop_eq_nil_of_le (as := P) (i := x) (by omega), List.nil_merge, h2]

end MergePass

end Formalgo.Algorithms.Sorting.MergeSort

end

section

/-!
## Merging two runs on the machine

-/

namespace Formalgo.Algorithms.Sorting.MergeSort

/-! ### Merging on the machine -/

open LLMUnchecked Cmd Function

/-- `M[b + j] = l[j]`. -/
def Arr (m : Mem) (b : ℕ) (l : List ℕ) : Prop := ∀ j (h : j < l.length), m (b + j) = l[j]

/-- The order on numbers, as a `Bool`. -/
def nle (a b : ℕ) : Bool := decide (a ≤ b)

/-- The registers the merge loop changes. -/
def mergeRegs : List ℕ := [2, 12, 13, 14, 15, 24, 26, 28, 30, 31]

/-- The merge loop invariant: `x` elements of `P` and `y` of `Q` taken. -/
def MergeInv (P Q : List ℕ) (p₀ q₀ k₀ : ℕ) (m m' : Mem) (s : ℕ) : Prop :=
  ∃ x y, x ≤ P.length ∧ y ≤ Q.length ∧
    (P.merge Q nle).drop (x + y) = (P.drop x).merge (Q.drop y) nle ∧
    m' 24 = p₀ + x ∧ m' 25 = p₀ + P.length ∧ m' 26 = q₀ + y ∧ m' 27 = q₀ + Q.length ∧
    m' 28 = k₀ + x + y ∧ m' 29 = k₀ + (P.length + Q.length) ∧ m' 3 = 1 ∧
    m' 12 = (if x + y < P.length + Q.length then 1 else 0) ∧
    (∀ j < x + y, m' (k₀ + j) = (P.merge Q nle).getD j 0) ∧
    (∀ a, a ∉ mergeRegs → (a < k₀ ∨ k₀ + (P.length + Q.length) ≤ a) → m' a = m a) ∧
    s ≤ 24 * (x + y)

theorem lt_of_cond {m : Mem} {r a b : ℕ} (h : m r = if a < b then 1 else 0) (hc : m r = m 3)
    (h3 : m 3 = 1) : a < b := by
  by_contra hab
  have := h.symm.trans hc
  rw [if_neg hab, h3] at this
  exact absurd this (by decide)

theorem not_lt_of_cond {m : Mem} {r a b : ℕ} (h : m r = if a < b then 1 else 0)
    (hc : m r ≠ m 3) (h3 : m 3 = 1) : ¬ a < b := by
  intro hab; rw [if_pos hab] at h; exact hc (h.trans h3.symm)

theorem mem_mergeRegs {a : ℕ} : a ∈ mergeRegs ↔
    a = 2 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 24 ∨ a = 26 ∨ a = 28 ∨ a = 30 ∨ a = 31 := by
  simp [mergeRegs]

theorem takeLeft_spec {B p d : ℕ} {m : Mem} {Q : Mem → ℕ → Prop} (h3 : m 3 = 1) (h24 : m 24 = p)
    (h28 : m 28 = d) (h32 : 32 ≤ d) (hB : p + 1 < B ∧ d + 1 < B)
    (h : ∀ m', m' 24 = p + 1 → m' 28 = d + 1 → m' d = m p →
      (∀ a, a ≠ 2 → a ≠ 24 → a ≠ 28 → a ≠ 30 → a ≠ d → m' a = m a) → Q m' 5) :
    Runs B takeLeft m Q := by
  rstepR; rstepR; rstepR
  refine Runs.storeR (by omega) (by omega) ?_
  intro m₂ hst hfst
  rename_i m₁ h₁ hf₁
  have hd : m₁ 28 = d := by rs
  rw [hd] at hst hfst
  rstepR; rstepR; rstepR; rstepR; rstepR
  rename_i m₃ h₃ hf₃ m₄ h₄ hf₄ m₅ h₅ hf₅
  refine h m₅ (by rs) (by rs) ?_ ?_
  · rw [hf₅ _ (by omega), hf₄ _ (by omega), hf₃ _ (by omega), hst]; rs
  · intro a h2 hp h28' hv had
    rw [hf₅ _ (by omega), hf₄ _ (by omega), hf₃ _ (by omega), hfst _ had, hf₁ _ (by omega)]

theorem takeRight_spec {B q d : ℕ} {m : Mem} {Q : Mem → ℕ → Prop} (h3 : m 3 = 1)
    (h26 : m 26 = q) (h28 : m 28 = d) (h32 : 32 ≤ d) (hB : q + 1 < B ∧ d + 1 < B)
    (h : ∀ m', m' 26 = q + 1 → m' 28 = d + 1 → m' d = m q →
      (∀ a, a ≠ 2 → a ≠ 26 → a ≠ 28 → a ≠ 31 → a ≠ d → m' a = m a) → Q m' 5) :
    Runs B takeRight m Q := by
  rstepR; rstepR; rstepR
  refine Runs.storeR (by omega) (by omega) ?_
  intro m₂ hst hfst
  rename_i m₁ h₁ hf₁
  have hd : m₁ 28 = d := by rs
  rw [hd] at hst hfst
  rstepR; rstepR; rstepR; rstepR; rstepR
  rename_i m₃ h₃ hf₃ m₄ h₄ hf₄ m₅ h₅ hf₅
  refine h m₅ (by rs) (by rs) ?_ ?_
  · rw [hf₅ _ (by omega), hf₄ _ (by omega), hf₃ _ (by omega), hst]; rs
  · intro a h2 hp h28' hv had
    rw [hf₅ _ (by omega), hf₄ _ (by omega), hf₃ _ (by omega), hfst _ had, hf₁ _ (by omega)]

theorem MergeInv.left {B : ℕ} {P Q : List ℕ} {p₀ q₀ k₀ : ℕ} {m m' : Mem} {s x y : ℕ}
    (hx : x ≤ P.length) (hy : y ≤ Q.length)
    (hdrop : (P.merge Q nle).drop (x + y) = (P.drop x).merge (Q.drop y) nle)
    (h'24 : m' 24 = p₀ + x) (h'25 : m' 25 = p₀ + P.length) (h'26 : m' 26 = q₀ + y)
    (h'27 : m' 27 = q₀ + Q.length) (h'28 : m' 28 = k₀ + x + y)
    (h'29 : m' 29 = k₀ + (P.length + Q.length)) (h'3 : m' 3 = 1)
    (hdst : ∀ j < x + y, m' (k₀ + j) = (P.merge Q nle).getD j 0)
    (hfr : ∀ a, a ∉ mergeRegs → (a < k₀ ∨ k₀ + (P.length + Q.length) ≤ a) → m' a = m a)
    (hs : s ≤ 24 * (x + y)) (hk32 : 32 ≤ k₀) :
    ∀ (hxP : x < P.length) (_ : ∀ hyQ : y < Q.length, nle P[x] (Q[y]'hyQ))
    (mF : Mem) (k : ℕ), mF 24 = p₀ + x + 1 → mF 25 = m' 25 → mF 26 = m' 26 →
    mF 27 = m' 27 → mF 28 = k₀ + x + y + 1 → mF 29 = m' 29 → mF 3 = 1 →
    mF 12 = (if k₀ + x + y + 1 < k₀ + (P.length + Q.length) then 1 else 0) →
    mF (k₀ + x + y) = P[x] → (∀ a, a ∉ mergeRegs → a ≠ k₀ + x + y → mF a = m' a) →
    k ≤ 22 → MergeInv P Q p₀ q₀ k₀ m mF (s + k + 2) ∧
      k₀ + (P.length + Q.length) - mF 28 < k₀ + (P.length + Q.length) - m' 28 := by
  intro hxP hle mF k f24 f25 f26 f27 f28 f29 f3 f12 fd ffr hk
  obtain ⟨hd', hlen, hval⟩ := merge_drop_left hdrop hxP hy hle
  refine ⟨⟨x + 1, y, by omega, hy, by rw [Nat.add_right_comm]; exact hd', by omega,
    by rw [f25, h'25], by rw [f26, h'26], by rw [f27, h'27], by omega, by rw [f29, h'29], f3,
    by rw [f12]; split_ifs <;> omega, fun j hj => ?_, fun a ha ha' => ?_, by omega⟩, by omega⟩
  · by_cases hjx : j = x + y
    · subst hjx
      rw [← Nat.add_assoc, fd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen,
        Option.getD_some, hval]
    · rw [ffr _ (by rw [mem_mergeRegs]; omega) (by omega), hdst j (by omega)]
  · rw [ffr a ha (by omega), hfr a ha ha']

theorem MergeInv.right {B : ℕ} {P Q : List ℕ} {p₀ q₀ k₀ : ℕ} {m m' : Mem} {s x y : ℕ}
    (hx : x ≤ P.length) (hy : y ≤ Q.length)
    (hdrop : (P.merge Q nle).drop (x + y) = (P.drop x).merge (Q.drop y) nle)
    (h'24 : m' 24 = p₀ + x) (h'25 : m' 25 = p₀ + P.length) (h'26 : m' 26 = q₀ + y)
    (h'27 : m' 27 = q₀ + Q.length) (h'28 : m' 28 = k₀ + x + y)
    (h'29 : m' 29 = k₀ + (P.length + Q.length)) (h'3 : m' 3 = 1)
    (hdst : ∀ j < x + y, m' (k₀ + j) = (P.merge Q nle).getD j 0)
    (hfr : ∀ a, a ∉ mergeRegs → (a < k₀ ∨ k₀ + (P.length + Q.length) ≤ a) → m' a = m a)
    (hs : s ≤ 24 * (x + y)) (hk32 : 32 ≤ k₀) :
    ∀ (hyQ : y < Q.length) (_ : ∀ hxP : x < P.length, nle (P[x]'hxP) Q[y] = false)
    (mF : Mem) (k : ℕ), mF 24 = m' 24 → mF 25 = m' 25 → mF 26 = q₀ + y + 1 →
    mF 27 = m' 27 → mF 28 = k₀ + x + y + 1 → mF 29 = m' 29 → mF 3 = 1 →
    mF 12 = (if k₀ + x + y + 1 < k₀ + (P.length + Q.length) then 1 else 0) →
    mF (k₀ + x + y) = Q[y] → (∀ a, a ∉ mergeRegs → a ≠ k₀ + x + y → mF a = m' a) →
    k ≤ 22 → MergeInv P Q p₀ q₀ k₀ m mF (s + k + 2) ∧
      k₀ + (P.length + Q.length) - mF 28 < k₀ + (P.length + Q.length) - m' 28 := by
  intro hyQ hle mF k f24 f25 f26 f27 f28 f29 f3 f12 fd ffr hk
  obtain ⟨hd', hlen, hval⟩ := merge_drop_right hdrop hyQ hx hle
  refine ⟨⟨x, y + 1, hx, by omega, by rw [← Nat.add_assoc]; exact hd', by rw [f24, h'24],
    by rw [f25, h'25], by omega, by rw [f27, h'27], by omega, by rw [f29, h'29], f3,
    by rw [f12]; split_ifs <;> omega, fun j hj => ?_, fun a ha ha' => ?_, by omega⟩, by omega⟩
  · by_cases hjx : j = x + y
    · subst hjx
      rw [← Nat.add_assoc, fd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen,
        Option.getD_some, hval]
    · rw [ffr _ (by rw [mem_mergeRegs]; omega) (by omega), hdst j (by omega)]
  · rw [ffr a ha (by omega), hfr a ha ha']

set_option maxHeartbeats 4000000 in
/-- One step of the merge loop. -/
theorem merge_step {B : ℕ} {P Q : List ℕ} {p₀ q₀ k₀ : ℕ} {m m' : Mem} {s x y : ℕ}
    (hx : x ≤ P.length) (hy : y ≤ Q.length)
    (hdrop : (P.merge Q nle).drop (x + y) = (P.drop x).merge (Q.drop y) nle)
    (h'24 : m' 24 = p₀ + x) (h'25 : m' 25 = p₀ + P.length) (h'26 : m' 26 = q₀ + y)
    (h'27 : m' 27 = q₀ + Q.length) (h'28 : m' 28 = k₀ + x + y)
    (h'29 : m' 29 = k₀ + (P.length + Q.length)) (h'3 : m' 3 = 1)
    (hdst : ∀ j < x + y, m' (k₀ + j) = (P.merge Q nle).getD j 0)
    (hfr : ∀ a, a ∉ mergeRegs → (a < k₀ ∨ k₀ + (P.length + Q.length) ≤ a) → m' a = m a)
    (hs : s ≤ 24 * (x + y))
    (hP : Arr m p₀ P) (hQ : Arr m q₀ Q)
    (hdP : k₀ + P.length + Q.length ≤ p₀ ∨ p₀ + P.length ≤ k₀)
    (hdQ : k₀ + P.length + Q.length ≤ q₀ ∨ q₀ + Q.length ≤ k₀)
    (h32 : 32 ≤ p₀ ∧ 32 ≤ q₀ ∧ 32 ≤ k₀)
    (hB : k₀ + P.length + Q.length < B ∧ p₀ + P.length < B ∧ q₀ + Q.length < B)
    (hvP : ∀ v ∈ P, v < B) (hvQ : ∀ v ∈ Q, v < B) (hlt : x + y < P.length + Q.length) :
    Runs B mergeBody m' fun m'' k => MergeInv P Q p₀ q₀ k₀ m m'' (s + k + 2) ∧
      k₀ + (P.length + Q.length) - m'' 28 < k₀ + (P.length + Q.length) - m' 28 := by
  have hPv : ∀ j (hj : j < P.length), m' (p₀ + j) = P[j] := fun j hj => by
    rw [hfr _ (by rw [mem_mergeRegs]; omega) (by omega)]; exact hP j hj
  have hQv : ∀ j (hj : j < Q.length), m' (q₀ + j) = Q[j] := fun j hj => by
    rw [hfr _ (by rw [mem_mergeRegs]; omega) (by omega)]; exact hQ j hj
  have finL := MergeInv.left (B := B) hx hy hdrop h'24 h'25 h'26 h'27 h'28 h'29 h'3 hdst hfr hs
    h32.2.2
  have finR := MergeInv.right (B := B) hx hy hdrop h'24 h'25 h'26 h'27 h'28 h'29 h'3 hdst hfr hs
    h32.2.2
  clear hdst hfr hdrop
  have hvP' : ∀ j (hj : j < P.length), P[j] < B := fun j hj => hvP _ (List.getElem_mem hj)
  have hvQ' : ∀ j (hj : j < Q.length), Q[j] < B := fun j hj => hvQ _ (List.getElem_mem hj)
  rstepR; rstepR; rstepR
  rename_i m₁ h₁ hf₁
  have h₁3 : m₁ 3 = 1 := by rw [hf₁ 3 (by omega)]; exact h'3
  refine Runs.ite (by omega) (by omega) (fun hc1 => ?_) (fun hc1 => ?_)
  · have hxP : x < P.length := by
      have := lt_of_cond h₁ hc1 h₁3; rw [h'24, h'25] at this; omega
    rstepR; rstepR; rstepR
    rename_i m₂ h₂ hf₂
    have h₂3 : m₂ 3 = 1 := by rw [hf₂ 3 (by omega)]; exact h₁3
    have h₂26 : m₂ 26 = q₀ + y := by rw [hf₂ 26 (by omega), hf₁ 26 (by omega), h'26]
    refine Runs.ite (by omega) (by omega) (fun hc2 => ?_) (fun hc2 => ?_)
    · have hyQ : y < Q.length := by
        have := lt_of_cond h₂ hc2 h₂3
        rw [hf₁ 26 (by omega), hf₁ 27 (by omega), h'26, h'27] at this; omega
      rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR
      rename_i m₃ h₃ hf₃ m₄ h₄ hf₄ m₅ h₅ hf₅
      have ha : m₃ 30 = P[x] := by
        rw [h₃, hf₂ 24 (by omega), hf₁ 24 (by omega), h'24, hf₂ _ (by omega),
          hf₁ _ (by omega), hPv x hxP]
      have hb : m₄ 31 = Q[y] := by
        rw [h₄, hf₃ 26 (by omega), h₂26, hf₃ _ (by omega), hf₂ _ (by omega), hf₁ _ (by omega),
          hQv y hyQ]
      have h₅3 : m₅ 3 = 1 := by rs
      refine Runs.ite (by omega) (by omega) (fun hc3 => ?_) (fun hc3 => ?_)
      · have hlt' : Q[y] < P[x] := by
          have := lt_of_cond h₅ hc3 h₅3
          rw [hb, hf₄ 30 (by omega), ha] at this
          exact this
        refine takeRight_spec (q := q₀ + y) (d := k₀ + x + y) h₅3 (by rs) (by rs) (by omega)
          (by omega) ?_
        intro mT hT26 hT28 hTd hTf
        repeat rstepR
        refine finR hyQ (fun _ => by simp [nle]; omega) _ _ (by rs) (by rs) (by rs) (by rs)
          (by rs) (by rs) (by rs) (by rs) (by rs) ?_ (by omega)
        intro a ha hne; rw [mem_mergeRegs] at ha; rs
      · have hle' : P[x] ≤ Q[y] := by
          have := not_lt_of_cond h₅ hc3 h₅3
          rw [hb, hf₄ 30 (by omega), ha] at this
          omega
        refine takeLeft_spec (p := p₀ + x) (d := k₀ + x + y) h₅3 (by rs) (by rs) (by omega)
          (by omega) ?_
        intro mT hT24 hT28 hTd hTf
        repeat rstepR
        refine finL hxP (fun _ => by simp [nle]; omega) _ _ (by rs) (by rs) (by rs) (by rs)
          (by rs) (by rs) (by rs) (by rs) (by rs) ?_ (by omega)
        intro a ha hne; rw [mem_mergeRegs] at ha; rs
    · have hyQ : ¬ y < Q.length := by
        have := not_lt_of_cond h₂ hc2 h₂3
        rw [hf₁ 26 (by omega), hf₁ 27 (by omega), h'26, h'27] at this; omega
      refine takeLeft_spec (p := p₀ + x) (d := k₀ + x + y) h₂3 (by rs) (by rs) (by omega)
        (by omega) ?_
      intro mT hT24 hT28 hTd hTf
      repeat rstepR
      refine finL hxP (fun h => absurd h hyQ) _ _ (by rs) (by rs) (by rs) (by rs)
        (by rs) (by rs) (by rs) (by rs) (by rs) ?_ (by omega)
      intro a ha hne; rw [mem_mergeRegs] at ha; rs
  · have hxP : ¬ x < P.length := by
      have := not_lt_of_cond h₁ hc1 h₁3; rw [h'24, h'25] at this; omega
    have hyQ : y < Q.length := by omega
    refine takeRight_spec (q := q₀ + y) (d := k₀ + x + y) h₁3 (by rs) (by rs) (by omega)
      (by omega) ?_
    intro mT hT26 hT28 hTd hTf
    repeat rstepR
    refine finR hyQ (fun h => absurd h hxP) _ _ (by rs) (by rs) (by rs) (by rs)
      (by rs) (by rs) (by rs) (by rs) (by rs) ?_ (by omega)
    intro a ha hne; rw [mem_mergeRegs] at ha; rs
set_option maxHeartbeats 1000000 in
theorem merge_loop {B : ℕ} {P Q : List ℕ} {p₀ q₀ k₀ : ℕ} {m : Mem} (h3 : m 3 = 1)
    (h24 : m 24 = p₀) (h25 : m 25 = p₀ + P.length) (h26 : m 26 = q₀)
    (h27 : m 27 = q₀ + Q.length) (h28 : m 28 = k₀) (h29 : m 29 = k₀ + P.length + Q.length)
    (h12 : m 12 = if k₀ < k₀ + P.length + Q.length then 1 else 0)
    (hP : Arr m p₀ P) (hQ : Arr m q₀ Q)
    (hdP : k₀ + P.length + Q.length ≤ p₀ ∨ p₀ + P.length ≤ k₀)
    (hdQ : k₀ + P.length + Q.length ≤ q₀ ∨ q₀ + Q.length ≤ k₀)
    (h32 : 32 ≤ p₀ ∧ 32 ≤ q₀ ∧ 32 ≤ k₀)
    (hB : k₀ + P.length + Q.length < B ∧ p₀ + P.length < B ∧ q₀ + Q.length < B)
    (hvP : ∀ v ∈ P, v < B) (hvQ : ∀ v ∈ Q, v < B) :
    Runs B (.loop 12 3 mergeBody) m fun m' s =>
      m' 24 = p₀ + P.length ∧ m' 26 = q₀ + Q.length ∧
      m' 28 = k₀ + P.length + Q.length ∧ Arr m' k₀ (P.merge Q nle) ∧
      (∀ a, a ∉ mergeRegs → (a < k₀ ∨ k₀ + P.length + Q.length ≤ a) → m' a = m a) ∧
      s ≤ 24 * (P.length + Q.length) + 1 := by
  refine Runs.loop (MergeInv P Q p₀ q₀ k₀ m) (fun m' => k₀ + (P.length + Q.length) - m' 28)
    (by omega) (by omega) ?_ ?_ ?_
  · rintro m' s ⟨x, y, hx, hy, hdrop, h'24, h'25, h'26, h'27, h'28, h'29, h'3, h'12, hdst, hfr,
      hs⟩ heq
    have hlt : x + y < P.length + Q.length := by
      by_contra h; rw [h'12, h'3, if_neg h] at heq; exact absurd heq (by decide)
    exact merge_step hx hy hdrop h'24 h'25 h'26 h'27 h'28 h'29 h'3 hdst hfr hs hP hQ hdP hdQ h32
      hB hvP hvQ hlt
  · rintro m' s ⟨x, y, hx, hy, hdrop, h'24, h'25, h'26, h'27, h'28, h'29, h'3, h'12, hdst, hfr,
      hs⟩ hne
    have hxy : x + y = P.length + Q.length := by
      by_contra h; exact hne (by rw [h'12, h'3, if_pos (by omega)])
    have hxP : x = P.length := by
      by_contra h
      have := List.length_merge nle (P.drop x) (Q.drop y)
      rw [← hdrop] at this; simp at this; omega
    refine ⟨by omega, by omega, by omega, fun j hj => ?_, fun a ha ha' => hfr a ha (by omega),
      by omega⟩
    rw [List.length_merge] at hj
    rw [hdst j (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
  · refine ⟨0, 0, by omega, by omega, by simp, by simp [h24], h25, by simp [h26], h27,
      by simp [h28], by rw [h29]; omega, h3, by rw [h12]; split_ifs <;> omega, fun j hj => by omega,
      fun a _ _ => rfl, by omega⟩

end Formalgo.Algorithms.Sorting.MergeSort

end

section

/-!
## Merging all pairs of runs on the machine

-/

namespace Formalgo.Algorithms.Sorting.MergeSort

open LLMUnchecked Cmd Function

/-- `rs`, trying `decide` before `omega` on side conditions. -/
local macro "rsd" : tactic => `(tactic| first
  | omega
  | ((simp (disch := first | decide | omega) only [*, Function.update_self,
      Function.update_of_ne]) <;> first
      | omega
      | (split_ifs <;> omega)))

/-! ### Merging all pairs of runs -/

theorem not_mem_mergeRegs_of_ge {a : ℕ} (h : 32 ≤ a) : a ∉ mergeRegs := by
  rw [mem_mergeRegs]; omega

theorem not_mem_mergeRegs {r : ℕ} (h2 : r ≠ 2) (h12 : r ≠ 12) (h13 : r ≠ 13) (h14 : r ≠ 14)
    (h15 : r ≠ 15) (h24 : r ≠ 24) (h26 : r ≠ 26) (h28 : r ≠ 28) (h30 : r ≠ 30) (h31 : r ≠ 31) :
    r ∉ mergeRegs := by
  rw [mem_mergeRegs]; omega

/-- `mid := min(mid, n)`, through a comparison already in register `12`. -/
theorem ite_min {B d : ℕ} {m : Mem} {Q : Mem → ℕ → Prop} (h3 : m 3 = 1)
    (h12 : m 12 = if m d < m 4 then 1 else 0) (hdB : d < B) (h12B : 12 < B) (hd2 : d ≠ 2)
    (h : ∀ m' k, m' d = min (m d) (m 4) → (∀ a, a ≠ 2 → a ≠ d → m' a = m a) → k ≤ 3 →
      Q m' k) : Runs B (.ite 12 3 nop (.copy d 4)) m Q := by
  refine Runs.ite (by omega) (by omega) (fun hc => ?_) (fun hc => ?_)
  · have hlt := lt_of_cond h12 hc h3
    refine Runs.constR (by omega) (by omega) fun m' h2 hf => h m' 3 ?_ (fun a ha _ => hf a ha) le_rfl
    rw [hf d hd2]; omega
  · have hlt := not_lt_of_cond h12 hc h3
    refine Runs.copyR (by omega) (by omega) fun m' hd hf => h m' 2 ?_ (fun a _ ha => hf a ha)
      (by omega)
    rw [hd]; omega

/-- The fixed registers of a list program are unchanged. -/
def KeepL (m m' : Mem) : Prop :=
  m' 1 = m 1 ∧ m' 3 = m 3 ∧ m' 4 = m 4 ∧ m' 5 = m 5 ∧ m' 8 = m 8 ∧ m' 9 = m 9 ∧ m' 10 = m 10 ∧
    m' 16 = m 16

/-- The merged runs at a multiple of `2 w`. -/
theorem merge_runs_eq {w j : ℕ} (hw : 0 < w) (L : List ℕ) :
    ((L.drop (j * (2 * w))).take w).merge (((L.drop (j * (2 * w))).drop w).take w) nle =
      ((mergePass nle w L).drop (j * (2 * w))).take (2 * w) := by
  rw [drop_mergePass_mul hw, take_mergePass hw]

/-- The pair loop invariant: the runs before `i` merged. -/
def PairInv (L : List ℕ) (src dst w : ℕ) (m m' : Mem) (s : ℕ) : Prop :=
  ∃ i ≤ L.length, (i = L.length ∨ ∃ j, i = j * (2 * w)) ∧ m' 21 = i ∧
    m' 11 = (if i < L.length then 1 else 0) ∧ KeepL m m' ∧ m' 18 = src ∧ m' 19 = dst ∧
    m' 20 = w ∧ (∀ j < i, m' (dst + j) = (mergePass nle w L).getD j 0) ∧
    (∀ a, 32 ≤ a → (a < dst ∨ dst + L.length ≤ a) → m' a = m a) ∧ s ≤ 60 * i

theorem PairInv.mono {L : List ℕ} {src dst w : ℕ} {m m' : Mem} {s s' : ℕ}
    (h : PairInv L src dst w m m' s) (hs : s' ≤ s) : PairInv L src dst w m m' s' := by
  obtain ⟨i, hi, a, b, c, d, e, f, g, h₁, h₂, h₃⟩ := h
  exact ⟨i, hi, a, b, c, d, e, f, g, h₁, h₂, by omega⟩

set_option maxHeartbeats 4000000 in
/-- Merge the runs at `i` and move to `hi`, from just before the merge loop. -/
theorem pair_tail {B src dst w i j : ℕ} {L : List ℕ} {m mA : Mem} (hw : 0 < w)
    (hwn : w < L.length) (hlt : i < L.length) (hj : j * (2 * w) = i)
    (hdisj : dst + L.length ≤ src ∨ src + L.length ≤ dst) (h32 : 32 ≤ src ∧ 32 ≤ dst)
    (hB : src + L.length < B ∧ dst + L.length < B ∧ 2 * L.length < B) (hv : ∀ v ∈ L, v < B)
    (a3 : mA 3 = 1) (a4 : mA 4 = L.length) (a18 : mA 18 = src) (a19 : mA 19 = dst)
    (a20 : mA 20 = w) (a23 : mA 23 = min (min (i + w) L.length + w) L.length)
    (a24 : mA 24 = src + i) (a25 : mA 25 = src + min (i + w) L.length)
    (a26 : mA 26 = src + min (i + w) L.length)
    (a27 : mA 27 = src + min (min (i + w) L.length + w) L.length) (a28 : mA 28 = dst + i)
    (a29 : mA 29 = dst + min (min (i + w) L.length + w) L.length)
    (a12 : mA 12 = if dst + i < dst + min (min (i + w) L.length + w) L.length then 1 else 0)
    (ak : KeepL m mA) (asrc : ∀ t (ht : t < L.length), mA (src + t) = L[t])
    (adst : ∀ t < i, mA (dst + t) = (mergePass nle w L).getD t 0)
    (afr : ∀ a, 32 ≤ a → (a < dst ∨ dst + L.length ≤ a) → mA a = m a) :
    Runs B (seqs [.loop 12 3 mergeBody, copy 21 23, less 11 21 4]) mA fun m'' k =>
      k ≤ 24 * (min (min (i + w) L.length + w) L.length - i) + 5 ∧
      m'' 21 = min (min (i + w) L.length + w) L.length ∧
      ∀ s', s' ≤ 60 * min (min (i + w) L.length + w) L.length → PairInv L src dst w m m'' s' := by
  have hPlen : ((L.drop i).take w).length = min (i + w) L.length - i := by simp; omega
  have hQlen : (((L.drop i).drop w).take w).length =
      min (min (i + w) L.length + w) L.length - min (i + w) L.length := by simp; omega
  have hdP : dst + i + ((L.drop i).take w).length + (((L.drop i).drop w).take w).length ≤
      src + i ∨ src + i + ((L.drop i).take w).length ≤ dst + i := by
    rw [hPlen, hQlen]; clear * - hdisj hlt hw; omega
  have hdQ : dst + i + ((L.drop i).take w).length + (((L.drop i).drop w).take w).length ≤
      src + min (i + w) L.length ∨
      src + min (i + w) L.length + (((L.drop i).drop w).take w).length ≤ dst + i := by
    rw [hPlen, hQlen]; clear * - hdisj hlt hw; omega
  have h32' : 32 ≤ src + i ∧ 32 ≤ src + min (i + w) L.length ∧ 32 ≤ dst + i := by
    clear * - h32; omega
  have hB' : dst + i + ((L.drop i).take w).length + (((L.drop i).drop w).take w).length < B ∧
      src + i + ((L.drop i).take w).length < B ∧
      src + min (i + w) L.length + (((L.drop i).drop w).take w).length < B := by
    rw [hPlen, hQlen]; clear * - hB hlt hw hwn; omega
  have c25 : mA 25 = src + i + ((L.drop i).take w).length := by
    rw [a25, hPlen]; clear * - hlt; omega
  have c27 : mA 27 = src + min (i + w) L.length + (((L.drop i).drop w).take w).length := by
    rw [a27, hQlen]; clear * - hlt; omega
  have c29 : mA 29 = dst + i + ((L.drop i).take w).length +
      (((L.drop i).drop w).take w).length := by
    rw [a29, hPlen, hQlen]; clear * - hlt; omega
  have c12 : mA 12 = if dst + i < dst + i + ((L.drop i).take w).length +
      (((L.drop i).drop w).take w).length then 1 else 0 := by
    rw [a12, hPlen, hQlen]; clear * - hlt; split_ifs <;> omega
  refine Runs.seqs_cons (Runs.mono (merge_loop (B := B) (P := (L.drop i).take w)
    (Q := ((L.drop i).drop w).take w) (p₀ := src + i) (q₀ := src + min (i + w) L.length)
    (k₀ := dst + i) a3 a24 c25 a26 c27 a28 c29 c12 ?_ ?_
    hdP hdQ h32' hB'
    (fun v h => hv v (List.mem_of_mem_drop (List.mem_of_mem_take h)))
    (fun v h => hv v (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take h)))))
    ?_)
  · intro t ht
    rw [List.getElem_take, List.getElem_drop, show src + i + t = src + (i + t) by omega]
    exact asrc _ _
  · intro t ht
    rw [hQlen] at ht
    rw [List.getElem_take, List.getElem_drop, List.getElem_drop,
      show src + min (i + w) L.length + t = src + (i + (w + t)) by omega]
    exact asrc _ _
  rintro m₁₄ s₁₄ ⟨g24, g26, g28, harr, hfr14, hs14⟩
  clear c25 c27 c29 c12 hdP hdQ h32' hB' a24 a25 a26 a27 a28 a29 a12 g24 g26 g28
  have gr : ∀ r, r < 32 → r ≠ 2 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 24 → r ≠ 26 →
      r ≠ 28 → r ≠ 30 → r ≠ 31 → m₁₄ r = mA r := by
    intro r hr h2 h12 h13 h14 h15 h24 h26 h28 h30 h31
    exact hfr14 r (not_mem_mergeRegs h2 h12 h13 h14 h15 h24 h26 h28 h30 h31)
      (.inl (by clear * - hr h32; omega))
  have gp : ∀ a, 32 ≤ a → (a < dst + i ∨ dst + i + ((L.drop i).take w).length +
      (((L.drop i).drop w).take w).length ≤ a) → m₁₄ a = mA a := fun a ha ha' =>
    hfr14 a (not_mem_mergeRegs_of_ge ha) ha'
  have hmr := merge_runs_eq (j := j) hw L
  rw [hj] at hmr
  have hlenM : ((L.drop i).take w).length + (((L.drop i).drop w).take w).length =
      min (min (i + w) L.length + w) L.length - i := by rw [hPlen, hQlen]; omega
  have hdst14 : ∀ t < min (min (i + w) L.length + w) L.length,
      m₁₄ (dst + t) = (mergePass nle w L).getD t 0 := by
    intro t ht
    by_cases hti : t < i
    · rw [gp _ (by clear * - h32; omega) (.inl (by clear * - hti; omega)), adst t hti]
    · have hidx : t - i < ((L.drop i).take w |>.merge (((L.drop i).drop w).take w) nle).length :=
        by rw [List.length_merge, hlenM]; clear * - ht hti; omega
      rw [show dst + t = dst + i + (t - i) by omega, harr (t - i) hidx, List.getElem_of_eq hmr,
        List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [length_mergePass]; clear * - ht; omega), Option.getD_some]
      congr 1; clear * - hti; omega
  have hfr' : ∀ a, 32 ≤ a → (a < dst ∨ dst + L.length ≤ a) → m₁₄ a = m a := by
    intro a ha ha'
    rw [gp a ha (by rw [Nat.add_assoc (dst + i), hlenM]; clear * - ha' hlt; omega),
      afr a ha ha']
  obtain ⟨k1, k3, k4, k5, k8, k9, k10, k16⟩ := ak
  have b3 : m₁₄ 3 = 1 := by rw [gr 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a3]
  have b4 : m₁₄ 4 = L.length := by rw [gr 4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a4]
  have b23 : m₁₄ 23 = min (min (i + w) L.length + w) L.length := by
    rw [gr 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), a23]
  have b1 : m₁₄ 1 = mA 1 := gr 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have b5 : m₁₄ 5 = mA 5 := gr 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have b8 : m₁₄ 8 = mA 8 := gr 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have b9 : m₁₄ 9 = mA 9 := gr 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have b10 : m₁₄ 10 = mA 10 := gr 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have b16 : m₁₄ 16 = mA 16 := gr 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have b18 : m₁₄ 18 = mA 18 := gr 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have b19 : m₁₄ 19 = mA 19 := gr 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have b20 : m₁₄ 20 = mA 20 := gr 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  clear hfr14 harr adst afr asrc hmr hv gp gr
  rstepR; rstepR; rstepR; rstepR; rstepR
  rename_i m₁₅ h₁₅ hf₁₅ m₁₆ h₁₆ hf₁₆ m₁₇ h₁₇ hf₁₇
  refine ⟨by rw [hlenM] at hs14; omega, by rsd, fun s' hs' => ⟨min (min (i + w) L.length + w)
    L.length, by omega, ?_, by rsd, by rsd, ⟨by rsd, by rsd, by rsd, by rsd, by rsd, by rsd, by rsd, by rsd⟩,
    by rsd, by rsd, by rsd, fun t ht => by rsd, fun a ha ha' => by rsd, hs'⟩⟩
  by_cases h : min (min (i + w) L.length + w) L.length < L.length
  · exact .inr ⟨j + 1, by rw [Nat.succ_mul]; omega⟩
  · exact .inl (by omega)

set_option maxHeartbeats 4000000 in
/-- One step of the pair loop. -/
theorem pair_step {B src dst w i j s : ℕ} {L : List ℕ} {m m' : Mem} (hw : 0 < w)
    (hwn : w < L.length) (hlt : i < L.length) (hj : j * (2 * w) = i)
    (hdisj : dst + L.length ≤ src ∨ src + L.length ≤ dst) (h32 : 32 ≤ src ∧ 32 ≤ dst)
    (hB : src + L.length < B ∧ dst + L.length < B ∧ 2 * L.length < B) (hv : ∀ v ∈ L, v < B)
    (hsrc : Arr m src L) (h'21 : m' 21 = i) (hk : KeepL m m') (h3 : m 3 = 1)
    (h4 : m 4 = L.length) (h'18 : m' 18 = src) (h'19 : m' 19 = dst) (h'20 : m' 20 = w)
    (hdst : ∀ t < i, m' (dst + t) = (mergePass nle w L).getD t 0)
    (hfr : ∀ a, 32 ≤ a → (a < dst ∨ dst + L.length ≤ a) → m' a = m a) (hs : s ≤ 60 * i) :
    Runs B pairBody m' fun m'' k => PairInv L src dst w m m'' (s + k + 2) ∧
      L.length - m'' 21 < L.length - m' 21 := by
  obtain ⟨k1, k3, k4, k5, k8, k9, k10, k16⟩ := id hk
  have hsrc2 : ∀ t (ht : t < L.length), m (src + t) = L[t] := hsrc
  clear hsrc
  -- `mid := min(i + w, n)`.
  rstepR; rstepR; rstepR; rstepR; rstepR
  rename_i m₁ h₁ hf₁ m₂ h₂ hf₂
  refine ite_min (by rsd) (by rsd) (by omega) (by omega) (by omega) ?_
  intro m₃ k₃ h₃ hf₃ hk₃
  -- `hi := min(mid + w, n)`.
  rstepR; rstepR; rstepR; rstepR; rstepR
  rename_i m₄ h₄ hf₄ m₅ h₅ hf₅
  refine ite_min (by rsd) (by rsd) (by omega) (by omega) (by omega) ?_
  intro m₆ k₆ h₆ hf₆ hk₆
  -- Set up the merge.
  rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR
  rstepR; rstepR
  rename_i m₇ h₇ hf₇ m₈ h₈ hf₈ m₉ h₉ hf₉ m₁₀ h₁₀ hf₁₀ m₁₁ h₁₁ hf₁₁ m₁₂ h₁₂ hf₁₂ m₁₃ h₁₃ hf₁₃
  refine Runs.mono (pair_tail (B := B) (src := src) (dst := dst) (w := w) (L := L) (m := m)
    (mA := m₁₃) (i := i) (j := j) hw hwn hlt hj hdisj h32 hB hv (by rsd) (by rsd)
    (by rsd) (by rsd) (by rsd) (by rsd) (by rsd) (by rsd) (by rsd) (by rsd) (by rsd) (by rsd)
    (by rsd) ⟨by rsd, by rsd, by rsd, by rsd, by rsd, by rsd, by rsd, by rsd⟩
    (fun t ht => by rsd) (fun t ht => by rsd) (fun a ha ha' => by rsd)) ?_
  rintro m'' k ⟨hk', h21'', hinv⟩
  refine ⟨hinv _ ?_, by rw [h21'', h'21]; clear * - hlt hw; omega⟩
  clear * - hs hk' hk₃ hk₆ hlt hw
  omega

set_option maxHeartbeats 1000000 in
theorem pair_loop {B src dst w : ℕ} {L : List ℕ} {m : Mem} (h3 : m 3 = 1)
    (h4 : m 4 = L.length) (h18 : m 18 = src) (h19 : m 19 = dst) (h20 : m 20 = w)
    (h21 : m 21 = 0) (h11 : m 11 = if 0 < L.length then 1 else 0) (hw : 0 < w)
    (hwn : w < L.length) (hsrc : Arr m src L)
    (hdisj : dst + L.length ≤ src ∨ src + L.length ≤ dst)
    (h32 : 32 ≤ src ∧ 32 ≤ dst)
    (hB : src + L.length < B ∧ dst + L.length < B ∧ 2 * L.length < B)
    (hv : ∀ v ∈ L, v < B) :
    Runs B (.loop 11 3 pairBody) m fun m' s => Arr m' dst (mergePass nle w L) ∧ KeepL m m' ∧
      m' 18 = src ∧ m' 19 = dst ∧ m' 20 = w ∧
      (∀ a, 32 ≤ a → (a < dst ∨ dst + L.length ≤ a) → m' a = m a) ∧ s ≤ 60 * L.length + 1 := by
  refine Runs.loop (PairInv L src dst w m) (fun m' => L.length - m' 21) (by omega) (by omega)
    ?_ ?_ ?_
  · rintro m' s ⟨i, hi, hij, h'21, h'11, hk, h'18, h'19, h'20, hdst, hfr, hs⟩ heq
    have hlt : i < L.length := lt_of_cond h'11 heq (by rw [hk.2.1, h3])
    obtain ⟨j, hj⟩ : ∃ j, j * (2 * w) = i := (hij.resolve_left (by omega)).imp fun _ h => h.symm
    exact pair_step hw hwn hlt hj hdisj h32 hB hv hsrc h'21 hk h3 h4 h'18 h'19 h'20 hdst hfr hs
  · rintro m' s ⟨i, hi, hij, h'21, h'11, hk, h'18, h'19, h'20, hdst, hfr, hs⟩ hne
    have hin : i = L.length := by
      by_contra h; exact hne (by rw [h'11, hk.2.1, h3, if_pos (by omega)])
    subst hin
    refine ⟨fun j hj => ?_, hk, h'18, h'19, h'20, hfr, by omega⟩
    rw [length_mergePass] at hj
    rw [hdst j hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
  · exact ⟨0, by omega, .inr ⟨0, by simp⟩, h21, h11, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      h18, h19, h20, fun j hj => by omega, fun a _ _ => rfl, by omega⟩

end Formalgo.Algorithms.Sorting.MergeSort

end

section

/-!
## Merge passes on the machine

-/

namespace Formalgo.Algorithms.Sorting.MergeSort

open LLMUnchecked Cmd Function

/-- `rs`, trying `decide` before `omega` on side conditions. -/
local macro "rsd" : tactic => `(tactic| first
  | omega
  | ((simp (disch := first | decide | omega) only [*, Function.update_self,
      Function.update_of_ne]) <;> first
      | omega
      | (split_ifs <;> omega)))

/-- The pass loop invariant: `jp` passes done, the result at `src`. -/
def PassInv (x : List ℕ) (A : ℕ) (m m' : Mem) (s : ℕ) : Prop :=
  ∃ jp src dst, (jp = 0 ∨ 2 ^ (jp - 1) < x.length) ∧
    ((src = A ∧ dst = A + x.length) ∨ (src = A + x.length ∧ dst = A)) ∧
    m' 18 = src ∧ m' 19 = dst ∧ m' 20 = 2 ^ jp ∧
    m' 11 = (if 2 ^ jp < x.length then 1 else 0) ∧
    (∀ t (ht : t < (passes nle jp x).length), m' (src + t) = (passes nle jp x)[t]) ∧
    KeepL m m' ∧ (∀ a, 32 ≤ a → (a < A ∨ A + 2 * x.length ≤ a) → m' a = m a) ∧
    s ≤ jp * (60 * x.length + 20)

theorem length_passes (j : ℕ) (x : List ℕ) : (passes nle j x).length = x.length :=
  (passes_perm j x).length_eq

set_option maxHeartbeats 4000000 in
/-- One pass. -/
theorem pass_step {B A jp src dst s : ℕ} {x : List ℕ} {m m' : Mem} (h3 : m 3 = 1)
    (h4 : m 4 = x.length) (hA : 32 ≤ A) (hB : A + 2 * x.length + 32 < B) (hv : ∀ v ∈ x, v < B)
    (hsd : (src = A ∧ dst = A + x.length) ∨ (src = A + x.length ∧ dst = A))
    (h18 : m' 18 = src) (h19 : m' 19 = dst) (h20 : m' 20 = 2 ^ jp)
    (hsrc : ∀ t (ht : t < (passes nle jp x).length), m' (src + t) = (passes nle jp x)[t])
    (hk : KeepL m m') (hfr : ∀ a, 32 ≤ a → (a < A ∨ A + 2 * x.length ≤ a) → m' a = m a)
    (hs : s ≤ jp * (60 * x.length + 20)) (hlt : 2 ^ jp < x.length) :
    Runs B passBody m' fun m'' k => PassInv x A m m'' (s + k + 2) ∧
      x.length - m'' 20 < x.length - m' 20 := by
  obtain ⟨k1, k3, k4, k5, k8, k9, k10, k16⟩ := id hk
  have hpos : 0 < 2 ^ jp := Nat.two_pow_pos jp
  have hvp : ∀ v ∈ passes nle jp x, v < B := fun v h => hv v ((passes_perm jp x).subset h)
  rstepR; rstepR; rstepR; rstepR; rstepR
  rename_i m₁ h₁ hf₁ m₂ h₂ hf₂
  refine Runs.mono (pair_loop (B := B) (src := src) (dst := dst) (w := 2 ^ jp)
    (L := passes nle jp x) (m := m₂) (by rsd) (by rw [length_passes]; rsd) (by rsd) (by rsd)
    (by rsd) (by rsd) (by rw [length_passes]; rsd) hpos (by rw [length_passes]; exact hlt)
    (by intro t ht; rw [hf₂ _ (by clear * - hsd hA; omega), hf₁ _ (by clear * - hsd hA; omega)]; exact hsrc t ht)
    (by rw [length_passes]; clear * - hsd; omega) (by clear * - hsd hA; omega)
    (by rw [length_passes]; clear * - hsd hB; omega) hvp) ?_
  rintro m₃ s₃ ⟨harr, hk₃, h₃18, h₃19, h₃20, hfr₃, hs₃⟩
  obtain ⟨l1, l3, l4, l5, l8, l9, l10, l16⟩ := hk₃
  rw [length_passes] at hfr₃ hs₃
  clear hsrc hvp
  rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR
  rename_i m₄ h₄ hf₄ m₅ h₅ hf₅ m₆ h₆ hf₆ m₇ h₇ hf₇ m₈ h₈ hf₈ m₉ h₉ hf₉
  refine ⟨⟨jp + 1, dst, src, .inr (by simpa using hlt), by clear * - hsd; omega, by rsd, by rsd,
    by rw [Nat.pow_succ]; rsd, by rw [Nat.pow_succ]; rsd, fun t ht => ?_,
    ⟨by rsd, by rsd, by rsd, by rsd, by rsd, by rsd, by rsd, by rsd⟩, fun a ha ha' => ?_, ?_⟩, ?_⟩
  · have := harr t (by rw [length_mergePass]; rwa [length_passes] at ht ⊢)
    rw [hf₉ _ (by clear * - hsd hA; omega), hf₈ _ (by clear * - hsd hA; omega),
      hf₇ _ (by clear * - hsd hA; omega), hf₆ _ (by clear * - hsd hA; omega),
      hf₅ _ (by clear * - hsd hA; omega), hf₄ _ (by clear * - hsd hA; omega), this]
    rfl
  · rw [hf₉ _ (by omega), hf₈ _ (by omega), hf₇ _ (by omega), hf₆ _ (by omega),
      hf₅ _ (by omega), hf₄ _ (by omega), hfr₃ a ha (by clear * - hsd ha'; omega),
      hf₂ _ (by omega), hf₁ _ (by omega), hfr a ha ha']
  · clear * - hs hs₃
    rw [Nat.succ_mul]; omega
  · rw [hf₉ 20 (by decide), hf₈ 20 (by decide), h₇, hf₆ 20 (by decide), hf₅ 20 (by decide),
      hf₄ 20 (by decide), h₃20, h20]
    clear * - hlt hpos; omega

/-- After the passes, `jp` is the number of passes needed. -/
theorem jp_eq_clog {jp n : ℕ} (h0 : jp = 0 ∨ 2 ^ (jp - 1) < n) (h1 : ¬ 2 ^ jp < n) :
    jp = Nat.clog 2 n := by
  apply le_antisymm
  · rcases h0 with rfl | h0
    · exact Nat.zero_le _
    · by_contra h
      have h2 : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by decide) n
      have h3 : 2 ^ Nat.clog 2 n ≤ 2 ^ (jp - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  · exact Nat.clog_le_of_le_pow (by omega)

set_option maxHeartbeats 1000000 in
theorem pass_loop {B A : ℕ} {x : List ℕ} {m m₀ : Mem} (h3 : m 3 = 1) (h4 : m 4 = x.length)
    (hA : 32 ≤ A) (hB : A + 2 * x.length + 32 < B) (hv : ∀ v ∈ x, v < B)
    (h0 : PassInv x A m m₀ 0) :
    Runs B (.loop 11 3 passBody) m₀ fun m' s => ∃ src, (src = A ∨ src = A + x.length) ∧
      m' 18 = src ∧
      (∀ t (ht : t < (passes nle (Nat.clog 2 x.length) x).length),
        m' (src + t) = (passes nle (Nat.clog 2 x.length) x)[t]) ∧
      KeepL m m' ∧ (∀ a, 32 ≤ a → (a < A ∨ A + 2 * x.length ≤ a) → m' a = m a) ∧
      s ≤ Nat.clog 2 x.length * (60 * x.length + 20) + 1 := by
  refine Runs.loop (PassInv x A m) (fun m' => x.length - m' 20) (by omega) (by omega) ?_ ?_ h0
  · rintro m' s ⟨jp, src, dst, hjp, hsd, h18, h19, h20, h11, hsrc, hk, hfr, hs⟩ heq
    have hlt : 2 ^ jp < x.length := lt_of_cond h11 heq (by rw [hk.2.1, h3])
    exact pass_step h3 h4 hA hB hv hsd h18 h19 h20 hsrc hk hfr hs hlt
  · rintro m' s ⟨jp, src, dst, hjp, hsd, h18, h19, h20, h11, hsrc, hk, hfr, hs⟩ hne
    have hge : ¬ 2 ^ jp < x.length := fun h => hne (by rw [h11, hk.2.1, h3, if_pos h])
    obtain rfl := jp_eq_clog hjp hge
    exact ⟨src, by omega, h18, hsrc, hk, hfr, by omega⟩

/-- The copy loop invariant: `l[0, i)` copied from `src` to `A`. -/
def CopyInv (l : List ℕ) (src A : ℕ) (m m' : Mem) (s : ℕ) : Prop :=
  ∃ i ≤ l.length, m' 21 = i ∧ m' 11 = (if i < l.length then 1 else 0) ∧ m' 18 = src ∧
    KeepL m m' ∧ (∀ t (ht : t < l.length), m' (src + t) = l[t]) ∧
    (∀ t < i, m' (A + t) = l.getD t 0) ∧
    (∀ a, 32 ≤ a → (a < A ∨ A + l.length ≤ a) → m' a = m a) ∧ s ≤ 9 * i

set_option maxHeartbeats 1000000 in
theorem copy_loop {B A src : ℕ} {l : List ℕ} {m m₀ : Mem} (h3 : m 3 = 1) (h4 : m 4 = l.length)
    (h9 : m 9 = A) (hA : 32 ≤ A) (hsrc : src = A + l.length) (hB : A + 2 * l.length + 32 < B)
    (h0 : CopyInv l src A m m₀ 0) :
    Runs B (.loop 11 3 copyBody) m₀ fun m' s => (∀ t < l.length, m' (A + t) = l.getD t 0) ∧
      KeepL m m' ∧ (∀ a, 32 ≤ a → (a < A ∨ A + l.length ≤ a) → m' a = m a) ∧
      s ≤ 9 * l.length + 1 := by
  refine Runs.loop (CopyInv l src A m) (fun m' => l.length - m' 21) (by omega) (by omega) ?_ ?_ h0
  · rintro m' s ⟨i, hi, h21, h11, h18, hk, hsr, hdst, hfr, hs⟩ heq
    obtain ⟨k1, k3, k4, k5, k8, k9, k10, k16⟩ := id hk
    have hlt : i < l.length := lt_of_cond h11 heq (by rw [k3, h3])
    rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR
    refine Runs.storeR (p := 14) (s := 30) (by omega) (by omega) ?_
    intro m₄ hst hfst
    rename_i m₁ h₁ hf₁ m₂ h₂ hf₂ m₃ h₃ hf₃
    have ha : m₃ 14 = A + i := by rsd
    have hval : m₃ 30 = l[i] := by
      rw [hf₃ 30 (by decide), h₂, h₁, h18, h21, hf₁ _ (by omega), hsr i hlt]
    rw [ha, hval] at hst; rw [ha] at hfst
    rstepR; rstepR; rstepR; rstepR; rstepR
    rename_i m₅ h₅ hf₅ m₆ h₆ hf₆ m₇ h₇ hf₇
    refine ⟨⟨i + 1, by omega, by rsd, by rsd, by rsd,
      ⟨by rsd, by rsd, by rsd, by rsd, by rsd, by rsd, by rsd, by rsd⟩, fun t ht => ?_,
      fun t ht => ?_, fun a ha ha' => ?_, by omega⟩, by rsd⟩
    · rw [hf₇ _ (by omega), hf₆ _ (by omega), hf₅ _ (by omega), hfst _ (by omega),
        hf₃ _ (by omega), hf₂ _ (by omega), hf₁ _ (by omega), hsr t ht]
    · rw [hf₇ _ (by omega), hf₆ _ (by omega), hf₅ _ (by omega)]
      by_cases hti : t = i
      · subst hti; rw [hst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
      · rw [hfst _ (by omega), hf₃ _ (by omega), hf₂ _ (by omega), hf₁ _ (by omega),
          hdst t (by omega)]
    · rw [hf₇ _ (by omega), hf₆ _ (by omega), hf₅ _ (by omega), hfst _ (by omega),
        hf₃ _ (by omega), hf₂ _ (by omega), hf₁ _ (by omega), hfr a ha ha']
  · rintro m' s ⟨i, hi, h21, h11, h18, hk, hsr, hdst, hfr, hs⟩ hne
    have hin : i = l.length := by
      by_contra h; exact hne (by rw [h11, hk.2.1, h3, if_pos (by omega)])
    subst hin
    exact ⟨hdst, hk, hfr, by omega⟩

end Formalgo.Algorithms.Sorting.MergeSort

end

section

/-!
## The sorting theorem

-/

namespace Formalgo.Algorithms.Sorting.MergeSort

open LLMUnchecked Cmd Function

/-- `rs`, trying `decide` before `omega` on side conditions. -/
local macro "rsd" : tactic => `(tactic| first
  | omega
  | ((simp (disch := first | decide | omega) only [*, Function.update_self,
      Function.update_of_ne]) <;> first
      | omega
      | (split_ifs <;> omega)))

/-- The list merge sort computes. -/
def sortList (x : List ℕ) : List ℕ := passes nle (Nat.clog 2 x.length) x

/-- The steps the merge sort core takes on a list of length `n`. -/
def coreTime (n : ℕ) : ℕ := Nat.clog 2 n * (60 * n + 20) + 9 * n + 40

theorem vm_eq_below {S A n : ℕ} {m m' : Mem} (hKS : nK ≤ S) (hA : A = S + nK)
    (hfr : ∀ a, 32 ≤ a → (a < A ∨ A + 2 * n ≤ a) → m' a = m a) :
    ∀ a < A, vm S m' a = vm S m a := by
  intro a ha; unfold vm; split_ifs <;> first | rfl | exact hfr _ (by omega) (by omega)

set_option maxHeartbeats 2000000 in
theorem core_spec : CoreSpec core sortList coreTime := by
  intro B S A m x hR hKS hA hB hv hx
  subst hA
  obtain ⟨⟨h1, h3, h5⟩, h4, h8, h9, h10, h16⟩ := hR
  have hx' : ∀ t (ht : t < (passes nle 0 x).length), m (S + 32 + t) = (passes nle 0 x)[t] := by
    intro t ht
    have ht' : t < x.length := ht
    have := hx t ht
    rw [vm_high hKS (by omega)] at this
    rw [this]; simp [passes, ht']
  clear hx
  rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR; rstepR
  rename_i m₁ g₁ f₁ m₂ g₂ f₂ m₃ g₃ f₃ m₄ g₄ f₄
  refine Runs.mono (pass_loop (B := B) (A := S + 32) (x := x) (m := m) (m₀ := m₄) h3 h4
    (by omega) (by omega) hv ⟨0, S + 32, S + 32 + x.length, .inl rfl, .inl ⟨rfl, rfl⟩, by rsd,
      by rsd, by rsd, by rsd, fun t ht => by rsd,
      ⟨by rsd, by rsd, by rsd, by rsd, by rsd, by rsd, by rsd, by rsd⟩,
      fun a ha ha' => by rsd, by simp⟩) ?_
  rintro m₅ s₅ ⟨src, hsrc, h18, harr, ⟨k1, k3, k4, k5, k8, k9, k10, k16⟩, hfr, hs⟩
  have hlen : (sortList x).length = x.length := length_passes _ x
  have hsl : ∀ j (hj : j < x.length), (sortList x)[j]! =
      (passes nle (Nat.clog 2 x.length) x)[j]'(by rw [length_passes]; exact hj) := by
    intro j hj; simp [sortList, hj, length_passes]
  clear hx' g₁ f₁ g₂ f₂ g₃ f₃ g₄ f₄
  rstepR
  refine Runs.ite (by omega) (by omega) (fun hc => ?_) (fun hc => ?_)
  · have hsA : src = S + 32 := by rw [← h18, hc, k9, h9]
    subst hsA
    rstepR; rstepR
    rename_i m₆ g₆ f₆ m₇ g₇ f₇
    refine ⟨⟨⟨by rsd, by rsd, by rsd⟩, by rsd, by rsd, by rsd, by rsd, by rsd⟩, fun j hj => ?_,
      fun a ha => ?_, ?_⟩
    · rw [vm_high hKS (by omega), f₇ _ (by omega), f₆ _ (by omega), harr j (by
        rw [length_passes]; exact hj), hsl j hj]
    · refine vm_eq_below (n := x.length) (m := m) (m' := m₇) hKS rfl (fun b hb hb' => ?_) a ha
      rw [f₇ _ (by omega), f₆ _ (by omega), hfr b hb hb']
    · simp only [coreTime]; clear * - hs; omega
  · have hsA : src = S + 32 + x.length := by
      rcases hsrc with h | h
      · exact absurd (by rw [h18, k9, h9, h]) hc
      · exact h
    subst hsA
    rstepR; rstepR; rstepR; rstepR; rstepR
    rename_i m₆ g₆ f₆ m₇ g₇ f₇
    refine Runs.mono (copy_loop (B := B) (A := S + 32) (src := S + 32 + x.length)
      (l := sortList x) (m := m₇) (m₀ := m₇) (by rsd) (by rw [hlen]; rsd) (by rsd) (by omega)
      (by rw [hlen]) (by rw [hlen]; omega)
      ⟨0, by omega, by rsd, by rw [hlen]; rsd, by rsd, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        fun t ht => by rw [f₇ _ (by omega), f₆ _ (by omega)]; exact harr t ht,
        fun t ht => by omega, fun a _ _ => rfl, le_rfl⟩) ?_
    rintro m₈ s₈ ⟨hA8, ⟨l1, l3, l4, l5, l8, l9, l10, l16⟩, hfr8, hs8⟩
    rw [hlen] at hfr8 hs8 hA8
    rstepR; rstepR
    rename_i m₉ g₉ f₉ m₁₀ g₁₀ f₁₀
    refine ⟨⟨⟨by rsd, by rsd, by rsd⟩, by rsd, by rsd, by rsd, by rsd, by rsd⟩, fun j hj => ?_,
      fun a ha => ?_, ?_⟩
    · rw [vm_high hKS (by omega), f₁₀ _ (by omega), f₉ _ (by omega), hA8 j hj,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hj)]
      simp [hj, hlen]
    · refine vm_eq_below (n := x.length) (m := m) (m' := m₁₀) hKS rfl (fun b hb hb' => ?_) a ha
      rw [f₁₀ _ (by omega), f₉ _ (by omega), hfr8 b hb (by omega), f₇ _ (by omega),
        f₆ _ (by omega), hfr b hb hb']
    · simp only [coreTime]; clear * - hs hs8; omega

theorem sortList_valid (x : List ℕ) : sorting.valid x (sortList x) := by
  refine ⟨passes_perm _ x, ?_⟩
  have h := (runsSorted_passes (le := nle) (fun a b c h₁ h₂ => by simp [nle] at *; omega)
    (fun a b => by simp [nle]; omega) (Nat.clog 2 x.length) x).pairwise
    (by rw [length_passes]; exact Nat.le_pow_clog (by decide) _)
  exact h.imp fun h => by simpa [nle] using h

theorem time_bound (n : ℕ) : coreTime n + 43 * n + 400 ≤ 500 * n * Nat.log 2 n + 500 := by
  unfold coreTime
  by_cases hn : n ≤ 1
  · have : Nat.clog 2 n = 0 := Nat.le_zero.1 (Nat.clog_le_of_le_pow (by simpa using hn))
    rw [this]; omega
  · have hL : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) (by simpa using (by omega : 2 ≤ n))
    have hC : Nat.clog 2 n ≤ Nat.log 2 n + 1 :=
      Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide) n).le
    have h1 : Nat.clog 2 n * (60 * n + 20) ≤ (Nat.log 2 n + 1) * (60 * n + 20) :=
      Nat.mul_le_mul_right _ hC
    have h2 : (Nat.log 2 n + 1) * (60 * n + 20) =
        60 * (n * Nat.log 2 n) + 20 * Nat.log 2 n + 60 * n + 20 := by ring
    have h3 : n ≤ n * Nat.log 2 n := Nat.le_mul_of_pos_right n hL
    have h4 : Nat.log 2 n ≤ n * Nat.log 2 n := Nat.le_mul_of_pos_left _ (by omega)
    have h5 : 500 * n * Nat.log 2 n = 500 * (n * Nat.log 2 n) := Nat.mul_assoc _ _ _
    omega

theorem small_core : Small 8 (listProgram core).lines := by decide +kernel

/-- A TD word RAM with `<`, `+` and `−` sorts in `O(n log n)` steps. -/
theorem sortsInNLogN : SortsInNLogN :=
  ⟨500, solvableWithin_list (W := 8) (scale := 3) core_spec (fun x => passes_perm _ x)
    (by omega) (by omega) small_core sorting sortList_valid _
    (fun x => time_bound x.length)⟩

end Formalgo.Algorithms.Sorting.MergeSort

end
