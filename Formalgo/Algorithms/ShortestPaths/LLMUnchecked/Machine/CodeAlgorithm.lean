import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Machine.CodeIO

/-!
# Algorithms on codes

LLM-generated; not checked by a human.

A code program loads the code of its input into the array at `A`, runs a core that writes the
code of the output into an array at `Z`, and writes it out.
-/

namespace Formalgo.LLMUnchecked

open Function Cmd

/-- `rs`, trying `decide` before `omega` on side conditions. -/
local macro "rsd" : tactic => `(tactic| first
  | omega
  | ((simp (disch := first | decide | omega) only [*, Function.update_self,
      Function.update_of_ne]) <;> first
      | omega
      | (split_ifs <;> omega)))

variable {I O : Type*} [Code I ℕ] [∀ w, Code I (BitVec w)] [Code O ℕ] [∀ w, Code O (BitVec w)]

/-- `core` turns the code of `x` at `A` into the code of `f x` at `Z = M[10]` (length in `M[17]`),
within `t x` steps, below `A + need x`. -/
def CodeSpec (core : Cmd) (f : I → O) (t need : I → ℕ) : Prop :=
  ∀ (B S A : ℕ) (m : Mem) (x : I), CodeRegs S (ncode x).length A m → nK ≤ S → A = S + nK →
    A + need x < B → (∀ v ∈ ncode x, v < B) →
    (∀ j < (ncode x).length, vm S m (A + j) = (ncode x)[j]!) →
    (∀ a, A + (ncode x).length ≤ a → vm S m a = 0) →
    Runs B core m fun m' k => CodeRegs S (ncode x).length A m' ∧ A ≤ m' 10 ∧
      m' 10 + (ncode (f x)).length ≤ A + need x ∧ m' 17 = (ncode (f x)).length ∧
      (∀ j < (ncode (f x)).length, vm S m' (m' 10 + j) = (ncode (f x))[j]!) ∧
      (∀ v ∈ ncode (f x), v < B) ∧ (∀ a < A, vm S m' a = vm S m a) ∧ k ≤ t x

/-- `lenC` sets register `4` to the length of the code, from the registers holding the input. -/
def LenSpec (lenC : Cmd) (_ : I → O) : Prop :=
  ∀ (B S w : ℕ) (m : Mem) (x : I), nK ≤ S → S + nK < B → 3 * ((ncode x).length + 1) ≤ S →
    Regs S m →
    (∀ r, 4 ≤ r → r < nK → r ≠ 5 → r ≠ 8 → r ≠ 9 → r ≠ 16 → m r = initMem w x r) →
    Runs B lenC m fun m' k => m' 4 = (ncode x).length ∧
      (∀ r, r ≠ 2 → r ≠ 4 → m' r = m r) ∧ vm S m' = vm S m ∧ k ≤ 10

/-- `setS` puts `Sf x` in cell `0`, using only cells `0` and `2`. -/
def SetSSpec (setS : Cmd) (Sf : I → ℕ) : Prop :=
  ∀ (B w : ℕ) (x : I), Sf x + nK < B → ∃ m₁ k₀, Exec B setS (initMem w x) k₀ m₁ ∧
    m₁ 0 = Sf x ∧ (∀ a, a ≠ 0 → a ≠ 2 → m₁ a = initMem w x a) ∧ k₀ ≤ 20

/-- Set the fixed registers, compute `ℓ`, load the input, run `core`, and write the output. -/
def codeBody (lenC core : Cmd) : Cmd :=
  seqs [const 3 1, const 5 32, const 8 0, const 16 3, add 9 1 5, lenC, loadCode, core, emitCode]

/-- The code program. -/
def codeProgram (setS lenC core : Cmd) : Cmd := harness nK setS (codeBody lenC core)

theorem getElem!_eq_getElem' {l : List ℕ} {j : ℕ} (hj : j < l.length) : l[j]! = l[j] := by
  simp [hj]

theorem ncode_input' (w : ℕ) (x : I) : ncode (w, x) = w :: ncode x := by
  rw [ncode_prod, ncode_nat]; rfl

theorem initMem_code (w : ℕ) (x : I) (a : ℕ) :
    initMem w x a = (tripleNat (w :: ncode x)).getD a 0 := by
  simp [initMem, ncode_input']

theorem initMem_code_elem {w : ℕ} {x : I} {j : ℕ} (hj : j < (ncode x).length) :
    initMem w x (3 * j + 4) = (ncode x)[j]! := by
  have := tripleNat_getD_mul_one (w :: ncode x) (j + 1)
  rw [show 3 * (j + 1) + 1 = 3 * j + 4 by omega] at this
  rw [initMem_code, this]
  simp [hj]

theorem initMem_code_high {w : ℕ} {x : I} {a : ℕ} (ha : 3 * ((ncode x).length + 1) ≤ a) :
    initMem w x a = 0 := by
  rw [initMem_code, tripleNat_getD_of_le _ (by simpa using ha)]

set_option maxHeartbeats 1000000 in
theorem codeBody_runs {lenC core : Cmd} {f : I → O} {t need : I → ℕ}
    (hcore : CodeSpec core f t need) (hlen : LenSpec lenC f) {B S w : ℕ} {x : I}
    (hNS : 3 * ((ncode x).length + 1) + 3 * (ncode (f x)).length + nK ≤ S)
    (hneed : (ncode x).length + nK ≤ need x) (hB : S + nK + need x < B) (hxB : ∀ v ∈ ncode x, v < B) {m : Mem} (h1 : m rS = S)
    (hvm : ∀ a, vm S m a = initMem w x a) (hreg : ∀ r, 3 ≤ r → r < nK → m r = initMem w x r) :
    Runs B (codeBody lenC core) m fun m' k => m' rS = S ∧
      (∀ a < S, a ≠ 0 → a ≠ 2 →
        vm S m' a = (tripleNat (ncode (w, x) ++ ncode (f x))).getD a 0) ∧
      (∀ v ∈ ncode (f x), v < B) ∧
      k ≤ t x + 13 * (ncode x).length + 25 * (ncode (f x)).length + 40 := by
  have hKS : nK ≤ S := by omega
  rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep
  rename_i m₁ g₁ f₁ v₁ m₂ g₂ f₂ v₂ m₃ g₃ f₃ v₃ m₄ g₄ f₄ v₄ m₅ g₅ f₅ v₅
  -- `ℓ`.
  refine Runs.mono (hlen B S w m₅ x hKS (by omega) (by omega) ⟨by rsd, by rsd, by rsd⟩
    (fun r hr hr' h5 h8 h9 h16 => by
      rw [f₅ r (by omega), f₄ r (by omega), f₃ r (by omega), f₂ r (by omega), f₁ r (by omega),
        hreg r (by omega) hr'])) ?_
  rintro m₆ k₆ ⟨g₆, f₆, v₆, hk₆⟩
  have hR₆ : CodeRegs S (ncode x).length (S + nK) m₆ :=
    ⟨⟨by rsd, by rsd, by rsd⟩, g₆, by rsd, by rsd, by rsd⟩
  have hvm₆ : vm S m₆ = vm S m := by rw [v₆, v₅, v₄, v₃, v₂, v₁]
  clear f₁ f₂ f₃ f₄ f₅ f₆ g₁ g₂ g₃ g₄ g₅ hreg
  -- Load.
  rstep
  refine Runs.mono (exec_loadCode (B := B) (c := ncode x) rfl hR₆ hKS rfl (by omega)
    (fun j hj => by rw [hvm₆, hvm, initMem_code_elem hj])
    (fun j hj => by rw [getElem!_eq_getElem' hj]; exact hxB _ (List.getElem_mem hj)) (by omega)) ?_
  rintro m₇ k₇ ⟨hR₇, hA₇, hfr₇, hk₇⟩
  -- The core.
  rstep
  refine Runs.mono (hcore B S (S + nK) m₇ x hR₇ hKS rfl (by omega) hxB hA₇
    (fun a ha => by rw [hfr₇ a (.inr ha), hvm₆, hvm, initMem_code_high (by omega)])) ?_
  rintro m₈ k₈ ⟨hR₈, hZ₈, hZB₈, h17₈, hz₈, hzB₈, hfr₈, hk₈⟩
  -- Write out.
  rstep
  refine Runs.mono (exec_emitCode (B := B) (z := ncode (f x)) rfl hR₈ rfl h17₈ hKS (by omega)
    (by omega) hz₈ (fun j hj => by rw [getElem!_eq_getElem' hj]; exact hzB₈ _ (List.getElem_mem hj))
    (by omega)) ?_
  rintro m₉ k₉ ⟨hR₉, hout₉, hfr₉, hk₉⟩
  refine Runs.seqs_nilV hKS (by omega) ?_
  intro m₁₀ hm₁₀ hf₁₀ hv₁₀
  refine ⟨by rw [hf₁₀ _ (by omega)]; exact hR₉.1.1, ?_, hzB₈, by omega⟩
  intro a ha ha0 ha2
  rw [hv₁₀, ncode_input']
  by_cases hL : a < 3 * ((ncode x).length + 1)
  · -- The input, unchanged.
    rw [hfr₉ a (.inl (by omega)), hfr₈ a (by omega), hfr₇ a (.inl (by omega)), hvm₆, hvm,
      initMem_code, show w :: ncode x ++ ncode (f x) = (w :: ncode x) ++ ncode (f x) from rfl,
      tripleNat_getD_append_left _ _ (by simp; omega)]
  · by_cases hN : a < 3 * ((ncode x).length + 1) + 3 * (ncode (f x)).length
    · -- The output.
      rw [hout₉ a (by omega) (by omega),
        show w :: ncode x ++ ncode (f x) = (w :: ncode x) ++ ncode (f x) from rfl,
        show a = 3 * (w :: ncode x).length + (a - (3 * (ncode x).length + 3)) by simp; omega,
        tripleNat_getD_append_right]
      congr 1; simp; omega
    · -- Blank.
      rw [hfr₉ a (.inr (by omega)), hfr₈ a (by omega), hfr₇ a (.inl (by omega)), hvm₆, hvm,
        initMem_code_high (by omega), tripleNat_getD_of_le _ (by simp; omega)]

set_option maxHeartbeats 1000000 in
/-- A code program for a core computing `f` outputs `f x`. -/
theorem code_outputs {setS lenC core : Cmd} {f : I → O} {t need Sf : I → ℕ}
    (hcore : CodeSpec core f t need) (hlen : LenSpec lenC f) (hset : SetSSpec setS Sf)
    (hlay : ∀ x : I, Layout x) (hskip : ∀ x : I, Skips x) (hlayO : ∀ y : O, Layout y)
    (hread : ∀ y : O, ReadsBack y) (hne : ∀ x : I, ncode x ≠ []) {W scale : ℕ} (hW : 1 ≤ W)
    (hscale : 1 ≤ scale) (hsmall : Small W (codeProgram setS lenC core).lines) (x : I)
    (hS : 3 * ((ncode x).length + 1) + 3 * (ncode (f x)).length + nK ≤ Sf x)
    (hneed : (ncode x).length + nK ≤ need x)
    (hbig : ∀ w, W ≤ w → (codeMax (ncode x) + 1) ^ scale ≤ 2 ^ w → Sf x + nK + need x < 2 ^ w)
    (hfy : ∀ v ∈ ncode (f x), v < (codeMax (ncode x) + 1) ^ scale) :
    Outputs (cmdAlgorithm I O (codeProgram setS lenC core) W scale) (tdWordRAM ops) x (f x) ∧
      HaltsWithin (cmdAlgorithm I O (codeProgram setS lenC core) W scale) (tdWordRAM ops) x
        (t x + 13 * (ncode x).length + 25 * (ncode (f x)).length + 330) := by
  obtain ⟨hWw, hpow⟩ := wordSize_spec (Output := O) (codeProgram setS lenC core) W scale x
  generalize hwdef : (cmdAlgorithm I O (codeProgram setS lenC core) W scale).wordSize x = w
    at hWw hpow
  have hBw := hbig w hWw hpow
  have hM1 : codeMax (ncode x) + 1 ≤ 2 ^ w := le_trans (Nat.le_self_pow (by omega) _) hpow
  have hxB : ∀ v ∈ ncode x, v < 2 ^ w := fun v hv => by have := le_codeMax hv; omega
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h; omega
    · exact h
  have hc : (ncode x).length ≠ 0 := by simpa using hne x
  -- The run.
  obtain ⟨m₁, k₀, hset', hm₁0, hm₁, hk₀⟩ := hset (2 ^ w) w x (by omega)
  have h00 : initMem w x 0 = 1 := by
    rw [initMem_code]; simpa using tripleNat_getD_mul (w :: ncode x) 0
  have h02 : initMem w x 2 = 0 := by
    rw [initMem_code]; simpa using tripleNat_getD_mul_two (w :: ncode x) 0
  have h03 : initMem w x 3 = 1 := by
    rw [initMem_code]
    have := tripleNat_getD_mul (w :: ncode x) 1
    simp only [Nat.mul_one, List.length_cons] at this
    rw [this, if_pos (by omega)]
  obtain ⟨m', k, hE, hk, hout⟩ := exec_harness_vm (B := 2 ^ w) (S := Sf x)
    (N := 3 * ((ncode x).length + 1) + 3 * (ncode (f x)).length)
    (fun a => (tripleNat (ncode (w, x) ++ ncode (f x))).getD a 0)
    (t x + 13 * (ncode x).length + 25 * (ncode (f x)).length + 40)
    (by omega) (by omega) (by omega) hset' hm₁0 hm₁ h00 h02 h03
    (fun a ha => initMem_code_high (by omega))
    (by rw [ncode_input']; simpa using tripleNat_getD_mul (w :: ncode x ++ ncode (f x)) 0)
    (by simpa using tripleNat_getD_mul_two (ncode (w, x) ++ ncode (f x)) 0)
    (fun m hm1 hvm hreg => by
      obtain ⟨m', k, e, h1, hfin, _, hk⟩ := codeBody_runs (f := f) hcore hlen (w := w) (x := x)
        hS hneed hBw hxB hm1 hvm hreg
      exact ⟨m', k, e, hk, h1, hfin⟩)
  -- The output values fit: rerun the body for its value bound.
  have hfity : Fits w (f x) := fun v hv => lt_of_lt_of_le (hfy v hv) hpow
  have hlenc : 3 * ((ncode (w, x)).length + (ncode (f x)).length) =
      3 * ((ncode x).length + 1) + 3 * (ncode (f x)).length := by
    rw [ncode_input']; simp; omega
  have := outputs_of_exec' (codeProgram setS lenC core) hsmall x (f x) (hlay x) (hskip x)
    (hlayO (f x)) (hread (f x)) hwdef hw hxB hfity (by rw [hlenc]; omega) hE
    (fun i hi => hout i (by omega))
  exact ⟨this.1, haltsWithin_mono _ this.2 (by omega)⟩

/-- A code program for a core computing `f`, within a time bound. -/
theorem solvableWithin_code {setS lenC core : Cmd} {f : I → O} {t need Sf : I → ℕ}
    (hcore : CodeSpec core f t need) (hlen : LenSpec lenC f) (hset : SetSSpec setS Sf)
    (hlay : ∀ x : I, Layout x) (hskip : ∀ x : I, Skips x) (hlayO : ∀ y : O, Layout y)
    (hread : ∀ y : O, ReadsBack y) (hne : ∀ x : I, ncode x ≠ []) {W scale : ℕ} (hW : 1 ≤ W)
    (hscale : 1 ≤ scale) (hsmall : Small W (codeProgram setS lenC core).lines)
    (hS : ∀ x, 3 * ((ncode x).length + 1) + 3 * (ncode (f x)).length + nK ≤ Sf x)
    (hneed : ∀ x, (ncode x).length + nK ≤ need x)
    (hbig : ∀ x w, W ≤ w → (codeMax (ncode x) + 1) ^ scale ≤ 2 ^ w →
      Sf x + nK + need x < 2 ^ w)
    (hfy : ∀ x, ∀ v ∈ ncode (f x), v < (codeMax (ncode x) + 1) ^ scale)
    (spec : IOSpec I O) (hspec : ∀ x, spec.valid x (f x)) (time : I → ℕ)
    (htime : ∀ x, t x + 13 * (ncode x).length + 25 * (ncode (f x)).length + 330 ≤ time x) :
    (tdWordRAM ops).SolvableWithin spec time :=
  ⟨_, inferInstance, cmdAlgorithm I O (codeProgram setS lenC core) W scale,
    fun x => ⟨f x, (code_outputs hcore hlen hset hlay hskip hlayO hread hne hW hscale hsmall x
      (hS x) (hneed x) (hbig x) (hfy x)).1, hspec x⟩,
    fun x => haltsWithin_mono _ (code_outputs hcore hlen hset hlay hskip hlayO hread hne hW hscale
      hsmall x (hS x) (hneed x) (hbig x) (hfy x)).2 (htime x)⟩

end Formalgo.LLMUnchecked
