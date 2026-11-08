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

/-- `lenC` sets register `4` to the length of the code, reading the tape. -/
def LenSpec (lenC : Cmd) (_ : I → O) : Prop :=
  ∀ (B S w : ℕ) (m : Mem) (x : I), nK ≤ S → S + nK < B → 3 * ((ncode x).length + 1) < S →
    Regs S m →
    (∀ r, 4 ≤ r → r < nK → r ≠ 5 → r ≠ 8 → r ≠ 9 → r ≠ 16 → m r = initMem w x r) →
    (∀ a, vm S m a = initMem w x a) →
    Runs B lenC m fun m' k => m' 4 = (ncode x).length ∧
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 6 → r ≠ 7 → r ≠ 12 → r ≠ 13 → r ≠ 14 → m' r = m r) ∧
      vm S m' = vm S m ∧ k ≤ 10 * (ncode x).length + 20

/-- `setS` puts `Sf x` in cell `0`, using only cells `0` and `2`. -/
def SetSSpec (setS : Cmd) (Sf : I → ℕ) : Prop :=
  ∀ (B w : ℕ) (x : I), ncode x ≠ [] → Sf x + nK < B → ∃ m₁ k₀, Exec B setS (initMem w x) k₀ m₁ ∧
    m₁ 0 = Sf x ∧ (∀ a, a ≠ 0 → a ≠ 2 → m₁ a = initMem w x a) ∧ k₀ ≤ 10 * (ncode x).length + 20

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
      k ≤ t x + 23 * (ncode x).length + 25 * (ncode (f x)).length + 50 := by
  have hKS : nK ≤ S := by omega
  rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep
  rename_i m₁ g₁ f₁ v₁ m₂ g₂ f₂ v₂ m₃ g₃ f₃ v₃ m₄ g₄ f₄ v₄ m₅ g₅ f₅ v₅
  -- `ℓ`.
  refine Runs.mono (hlen B S w m₅ x hKS (by omega) (by omega) ⟨by rsd, by rsd, by rsd⟩
    (fun r hr hr' h5 h8 h9 h16 => by
      rw [f₅ r (by omega), f₄ r (by omega), f₃ r (by omega), f₂ r (by omega), f₁ r (by omega),
        hreg r (by omega) hr']) (fun a => by rw [v₅, v₄, v₃, v₂, v₁, hvm])) ?_
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
        (t x + 33 * (ncode x).length + 25 * (ncode (f x)).length + 340) := by
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
  obtain ⟨m₁, k₀, hset', hm₁0, hm₁, hk₀⟩ := hset (2 ^ w) w x (hne x) (by omega)
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
    (t x + 23 * (ncode x).length + 25 * (ncode (f x)).length + 50)
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

/-- Count the code values, reading the markers `vm[3 j + 3]` from `j = 0` until one is not `1`. -/
def lenScan : Cmd := seqs [const 4 0, const 12 3, const 13 3, vread 14 12,
  loop 14 3 (seqs [add 4 4 3, add 12 12 13, vread 14 12])]

set_option maxHeartbeats 1000000 in
theorem lenScan_spec (f : I → O) : LenSpec lenScan f := by
  intro B S w m x hKS hB hS hR _ hvm
  have hflag : ∀ j, j ≤ (ncode x).length →
      vm S m (3 * j + 3) = if j < (ncode x).length then 1 else 0 := by
    intro j _
    rw [hvm, initMem_code, show 3 * j + 3 = 3 * (j + 1) by omega, tripleNat_getD_mul]
    simp
  generalize (ncode x).length = ℓ at hflag hS ⊢
  obtain ⟨h1, h3, h5⟩ := id hR
  let P : Mem → ℕ → Prop := fun m' s => ∃ j ≤ ℓ, Regs S m' ∧ m' 4 = j ∧ m' 12 = 3 * j + 3 ∧
    m' 13 = 3 ∧ m' 14 = (if j < ℓ then 1 else 0) ∧
    (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 6 → r ≠ 7 → r ≠ 12 → r ≠ 13 → r ≠ 14 → m' r = m r) ∧
    vm S m' = vm S m ∧ s ≤ 10 * j + 8
  rstep; rstep; rstep; rstep; rstep; rstep
  rename_i m₁ g₁ f₁ v₁ m₂ g₂ f₂ v₂ m₃ g₃ f₃ v₃
  have e3 : m₃ 12 = 3 * 0 + 3 := by rsd
  rstep
  refine Runs.vread (S := S) (d := 14) (va := 12) ⟨by rsd, by rsd, by rsd⟩ (by omega) (by omega)
    (by omega) (by omega) hKS (by omega) (.inl (by rw [e3]; omega)) ?_
  intro m₄ k₄ hk₄ hR₄ hv₄ hvm₄ hfr₄
  rstep
  refine Runs.mono (Q := fun m' k => m' 4 = ℓ ∧
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 6 → r ≠ 7 → r ≠ 12 → r ≠ 13 → r ≠ 14 → m' r = m r) ∧
      vm S m' = vm S m ∧ k ≤ 10 * ℓ + 9)
    (Runs.loop P (fun m' => ℓ - m' 4) (by omega) (by omega) ?_ ?_ ?_) ?_
  · rintro m' s ⟨j, hj, hR', h4, h12, h13, h14, hfr, hvm', hs⟩ heq
    obtain ⟨r1, r3, r5⟩ := id hR'
    have hlt : j < ℓ := by
      by_contra h
      rw [h14, if_neg h, r3] at heq
      exact absurd heq (by decide)
    rstep; rstep; rstep; rstep
    rename_i m₅ g₅ f₅ v₅ m₆ g₆ f₆ v₆
    have e4 : m₆ 4 = j + 1 := by rw [f₆ 4 (by decide), g₅, h4, r3]
    have e12 : m₆ 12 = 3 * (j + 1) + 3 := by
      rw [g₆, f₅ 12 (by decide), f₅ 13 (by decide), h12, h13]; omega
    rstep
    refine Runs.vread (S := S) (d := 14) (va := 12) ⟨by rsd, by rsd, by rsd⟩ (by omega)
      (by omega) (by omega) (by omega) hKS (by omega) (.inl (by rw [e12]; omega)) ?_
    intro m₇ k₇ hk₇ hR₇ hv₇ hvm₇ hfr₇
    refine Runs.seqs_nilV hKS (by omega) ?_
    intro m₈ g₈ f₈ v₈
    have e4' : m₈ 4 = j + 1 := by
      rw [f₈ 4 (by decide), hfr₇ 4 (by decide) (by decide) (by decide), e4]
    refine ⟨⟨j + 1, by omega, ⟨by rsd, by rsd, by rsd⟩, e4', ?_, ?_, ?_,
      fun r a b c d e f g => ?_, ?_, by omega⟩, by rw [e4', h4]; omega⟩
    · rw [f₈ 12 (by decide), hfr₇ 12 (by decide) (by decide) (by decide), e12]
    · rw [f₈ 13 (by decide), hfr₇ 13 (by decide) (by decide) (by decide), f₆ 13 (by decide),
        f₅ 13 (by decide), h13]
    · rw [f₈ 14 (by decide), hv₇, e12, v₆, v₅, hvm', hflag (j + 1) (by omega)]
    · rw [f₈ r a, hfr₇ r c d g, f₆ r e, f₅ r b, hfr r a b c d e f g]
    · rw [v₈, hvm₇, v₆, v₅, hvm']
  · rintro m' s ⟨j, hj, hR', h4, h12, h13, h14, hfr, hvm', hs⟩ hne
    have hjl : j = ℓ := by
      by_contra h
      exact hne (by rw [h14, if_pos (by omega), hR'.2.1])
    subst hjl
    exact ⟨h4, hfr, hvm', by omega⟩
  · refine ⟨0, by omega, hR₄, ?_, ?_, ?_, ?_, fun r a b c d e f g => ?_, ?_, by omega⟩
    · rw [hfr₄ 4 (by decide) (by decide) (by decide)]; rsd
    · rw [hfr₄ 12 (by decide) (by decide) (by decide), e3]
    · rw [hfr₄ 13 (by decide) (by decide) (by decide)]; rsd
    · rw [hv₄, e3, v₃, v₂, v₁, hflag 0 (by omega)]
    · rw [hfr₄ r c d g]; rsd
    · rw [hvm₄, v₃, v₂, v₁]
  · rintro m' k ⟨h4, hfr, hvm', hk⟩
    rstep
    rename_i m₉ g₉ f₉ v₉
    exact ⟨by rsd, fun r a b c d e f g => by rw [f₉ r a]; exact hfr r a b c d e f g,
      by rw [v₉, hvm'], by omega⟩

/-- `M[0] := 6 ℓ + 70`, where `ℓ` is the length of the code: read the markers `M[3 j + 3]` from
`j = 0` until one is not `1`. -/
def setScan : Cmd := seq (const 0 3) (seq (load 2 0) (seq (loop 2 3 (seq (const 2 3)
  (seq (add 0 0 2) (load 2 0)))) (seq (add 0 0 0) (seq (const 2 64) (add 0 0 2)))))

set_option maxHeartbeats 1000000 in
theorem setScan_spec : SetSSpec (I := I) setScan fun x => 6 * (ncode x).length + 70 := by
  intro B w x hne hB
  beta_reduce at hB ⊢
  have hflag : ∀ j, j ≤ (ncode x).length →
      initMem w x (3 * j + 3) = if j < (ncode x).length then 1 else 0 := by
    intro j _
    rw [initMem_code, show 3 * j + 3 = 3 * (j + 1) by omega, tripleNat_getD_mul]
    simp
  have hl : 0 < (ncode x).length := List.length_pos_of_ne_nil hne
  generalize initMem w x = m₀ at hflag ⊢
  generalize (ncode x).length = ℓ at hflag hl hB ⊢
  have h3 : m₀ 3 = 1 := by have := hflag 0 (by omega); rwa [if_pos hl] at this
  suffices h : Runs B setScan m₀ fun m' k => m' 0 = 6 * ℓ + 70 ∧
      (∀ a, a ≠ 0 → a ≠ 2 → m' a = m₀ a) ∧ k ≤ 10 * ℓ + 20 by
    obtain ⟨m', k, e, h1, h2, h3⟩ := h
    exact ⟨m', k, e, h1, h2, h3⟩
  refine Runs.seq (Runs.constR (by omega) (by omega) fun m₁ g₁ f₁ => ?_)
  refine Runs.seq (Runs.loadR (by omega) (by omega) fun m₂ g₂ f₂ => ?_)
  have e20 : m₂ 0 = 3 := by rw [f₂ 0 (by decide), g₁]
  have e22 : m₂ 2 = 1 := by rw [g₂, g₁, f₁ 3 (by decide), h3]
  refine Runs.seq (Runs.loop (fun m s => ∃ j ≤ ℓ, m 0 = 3 * j + 3 ∧
      m 2 = (if j < ℓ then 1 else 0) ∧ (∀ a, a ≠ 0 → a ≠ 2 → m a = m₀ a) ∧ s ≤ 5 * j)
    (fun m => 3 * ℓ + 3 - m 0) (by omega) (by omega) ?_ ?_
    ⟨0, by omega, e20, by rw [e22, if_pos hl], fun a h0 h2 => by rw [f₂ a h2, f₁ a h0], le_rfl⟩)
  · rintro m s ⟨j, hj, h0, h2, hfr, hs⟩ heq
    have hjl : j < ℓ := by
      by_contra h
      rw [h2, if_neg h, hfr 3 (by decide) (by decide), h3] at heq
      exact absurd heq (by decide)
    refine Runs.seq (Runs.constR (by omega) (by omega) fun m₃ g₃ f₃ => ?_)
    refine Runs.seq (Runs.addR (by omega) (by omega) (by omega)
      (by rw [f₃ 0 (by decide), g₃, h0]; omega) fun m₄ g₄ f₄ => ?_)
    have e40 : m₄ 0 = 3 * (j + 1) + 3 := by rw [g₄, f₃ 0 (by decide), g₃, h0]; omega
    refine Runs.loadR (by omega) (by omega) fun m₅ g₅ f₅ => ?_
    refine ⟨⟨j + 1, by omega, by rw [f₅ 0 (by decide), e40], ?_, fun a h0 h2 => ?_, by omega⟩,
      by rw [f₅ 0 (by decide), e40, h0]; omega⟩
    · rw [g₅, e40, f₄ _ (by omega), f₃ _ (by omega), hfr _ (by omega) (by omega),
        hflag (j + 1) (by omega)]
    · rw [f₅ a h2, f₄ a h0, f₃ a h2, hfr a h0 h2]
  · rintro m s ⟨j, hj, h0, h2, hfr, hs⟩ hne
    have hjl : j = ℓ := by
      by_contra h
      exact hne (by rw [h2, if_pos (by omega), hfr 3 (by decide) (by decide), h3])
    subst hjl
    refine Runs.seq (Runs.addR (by omega) (by omega) (by omega) (by rw [h0]; omega)
      fun m₆ g₆ f₆ => ?_)
    refine Runs.seq (Runs.constR (by omega) (by omega) fun m₇ g₇ f₇ => ?_)
    refine Runs.addR (by omega) (by omega) (by omega)
      (by rw [f₇ 0 (by decide), g₆, g₇, h0]; omega) fun m₈ g₈ f₈ => ?_
    refine ⟨by rw [g₈, f₇ 0 (by decide), g₆, g₇, h0]; omega, fun a h0' h2' => ?_, by omega⟩
    rw [f₈ a h0', f₇ a h2', f₆ a h0', hfr a h0' h2']

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
    (htime : ∀ x, t x + 33 * (ncode x).length + 25 * (ncode (f x)).length + 340 ≤ time x) :
    (tdWordRAM ops).SolvableWithin spec time :=
  ⟨_, inferInstance, cmdAlgorithm I O (codeProgram setS lenC core) W scale,
    fun x => ⟨f x, (code_outputs hcore hlen hset hlay hskip hlayO hread hne hW hscale hsmall x
      (hS x) (hneed x) (hbig x) (hfy x)).1, hspec x⟩,
    fun x => haltsWithin_mono _ (code_outputs hcore hlen hset hlay hskip hlayO hread hne hW hscale
      hsmall x (hS x) (hneed x) (hbig x) (hfy x)).2 (htime x)⟩

end Formalgo.LLMUnchecked
