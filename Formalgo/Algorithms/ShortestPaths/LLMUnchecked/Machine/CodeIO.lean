import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Machine.ListIO

/-!
# Codes in and out

LLM-generated; not checked by a human.

For an input whose code over natural numbers is `c` (length `ℓ`), the tape holds `w` and `c` as
triples in cells `[0, L)`, `L = 3 (ℓ + 1)`. Programs copy `c` into an array at `A = S + nK`, compute
the output code `z` (length `μ`) into an array at `Z`, and write it out from `L`.
-/

namespace Formalgo.Algorithms.ShortestPaths.LLMUnchecked

open Function Cmd

/-- `rs`, trying `decide` before `omega` on side conditions. -/
local macro "rsd" : tactic => `(tactic| first
  | omega
  | ((simp (disch := first | decide | omega) only [*, Function.update_self,
      Function.update_of_ne]) <;> first
      | omega
      | (split_ifs <;> omega)))

/-- The registers fixed throughout a code program: `S`, `1`, `ℓ`, `nK`, `0`, `A`, `3`. -/
def CodeRegs (S ℓ A : ℕ) (m : Mem) : Prop :=
  Regs S m ∧ m 4 = ℓ ∧ m 8 = 0 ∧ m 9 = A ∧ m 16 = 3

/-- Load the code `c` into `A[0, ℓ)`. -/
def loadCode : Cmd := seqs [const 11 0, const 12 4, less 15 11 4, loop 15 3 loadBody]

theorem exec_loadCode {B S ℓ A : ℕ} {m : Mem} {c : List ℕ} (hc : c.length = ℓ)
    (hR : CodeRegs S ℓ A m) (hKS : nK ≤ S) (hA : A = S + nK) (hB : A + ℓ + nK < B)
    (hx : ∀ j < ℓ, vm S m (3 * j + 4) = c[j]!) (hcB : ∀ j < ℓ, c[j]! < B)
    (hxS : 3 * ℓ + 4 < S) :
    Runs B loadCode m fun m' k => CodeRegs S ℓ A m' ∧ (∀ j < ℓ, vm S m' (A + j) = c[j]!) ∧
      (∀ a, (a < A ∨ A + ℓ ≤ a) → vm S m' a = vm S m a) ∧ k ≤ 13 * ℓ + 8 := by
  obtain ⟨⟨h1, h3, h5⟩, h4, h8, h9, h16⟩ := id hR
  let P : Mem → ℕ → Prop := fun m' s => ∃ i ≤ ℓ, CodeRegs S ℓ A m' ∧ m' 11 = i ∧
    m' 12 = 3 * i + 4 ∧ m' 15 = (if i < ℓ then 1 else 0) ∧
    (∀ j < i, vm S m' (A + j) = c[j]!) ∧
    (∀ a, (a < A ∨ A + i ≤ a) → vm S m' a = vm S m a) ∧ s ≤ 13 * i + 3
  rstep; rstep; rstep; rstep; rstep; rstep; rstep
  rename_i m₁ g₁ f₁ v₁ m₂ g₂ f₂ v₂ m₃ g₃ f₃ v₃
  refine Runs.mono (Q := fun m' k => CodeRegs S ℓ A m' ∧ (∀ j < ℓ, vm S m' (A + j) = c[j]!) ∧
      (∀ a, (a < A ∨ A + ℓ ≤ a) → vm S m' a = vm S m a) ∧ k ≤ 13 * ℓ + 4)
    (Runs.loop P (fun m' => ℓ - m' 11) (by omega) (by omega) ?_ ?_ ?_) ?_
  · rintro m' s ⟨i, hi, ⟨⟨r1, r3, r5⟩, r4, r8, r9, r16⟩, h11, h12, h15, hdone, hfr, hs⟩ heq
    have hlt : i < ℓ := by by_contra h; simp [h15, r3, h] at heq
    rstep
    refine Runs.vread (S := S) (d := 14) (va := 12) ⟨r1, r3, r5⟩ (by omega) (by omega) (by omega)
      (by omega) hKS (by omega) (by rw [h12]; omega) ?_
    intro m₄ k₄ hk₄ hR₄ hv₄ hvm₄ hfr₄
    have hval : m₄ 14 = c[i]! := by
      rw [hv₄, h12, hfr _ (.inl (by omega)), hx i hlt]
    rstep; rstep; rstep
    refine Runs.storeR (p := 13) (s := 14) (by omega) (by omega) ?_
    intro m₆ hst hfst
    rename_i m₅ g₅ f₅ v₅
    have ha : m₅ 13 = A + i := by rsd
    rw [ha] at hst hfst
    rstep; rstep; rstep; rstep; rstep; rstep; rstep
    rename_i m₇ g₇ f₇ v₇ m₈ g₈ f₈ v₈ m₉ g₉ f₉ v₉ m₁₀ g₁₀ f₁₀ v₁₀
    have hvm₆ : vm S m₆ = update (vm S m₅) (A + i) (c[i]!) := by
      rw [vm_of_store (by omega) (.inr (by omega)) (by rw [hst, f₅ 14 (by decide), hval]) hfst]
    refine ⟨⟨i + 1, by omega, ⟨⟨by rsd, by rsd, by rsd⟩, by rsd, by rsd, by rsd, by rsd⟩, by rsd,
      by rsd, by rsd, fun j hj => ?_, fun a ha' => ?_, by omega⟩, by rsd⟩
    · rw [v₁₀, v₉, v₈, v₇, hvm₆, v₅, hvm₄, update_apply]
      split_ifs with h
      · obtain rfl : j = i := by omega
        rfl
      · exact hdone j (by omega)
    · rw [v₁₀, v₉, v₈, v₇, hvm₆, v₅, hvm₄, update_apply, if_neg (by omega)]
      exact hfr a (by omega)
  · rintro m' s ⟨i, hi, hR', h11, h12, h15, hdone, hfr, hs⟩ hne
    have hin : i = ℓ := by
      by_contra h
      exact hne (by rw [h15, hR'.1.2.1, if_pos (by omega)])
    subst hin
    exact ⟨hR', hdone, hfr, by omega⟩
  · refine ⟨0, by omega, ⟨⟨by rsd, by rsd, by rsd⟩, by rsd, by rsd, by rsd, by rsd⟩, by rsd, by rsd,
      by rsd, fun j hj => by omega, fun a _ => by rw [v₃, v₂, v₁], by omega⟩
  · rintro m' k ⟨⟨⟨r1, r3, r5⟩, r4, r8, r9, r16⟩, hd, hfr, hk⟩
    rstep
    rename_i m₄ g₄ f₄ v₄
    refine ⟨⟨⟨by rsd, by rsd, by rsd⟩, by rsd, by rsd, by rsd, by rsd⟩,
      fun j hj => by rw [v₄]; exact hd j hj,
      fun a ha => by rw [v₄]; exact hfr a ha, by omega⟩

/-- Write `[1, Z[i], 0]` at `va`. -/
def emitBodyC : Cmd := seqs [vwrite 12 3, add 12 12 3, add 13 10 11, load 14 13, vwrite 12 14,
  add 12 12 3, vwrite 12 8, add 12 12 3, add 11 11 3, less 15 11 17]

/-- Write `Z[0, μ)` as triples from `L = 3 (ℓ + 1)`. -/
def emitCode : Cmd := seqs [add 18 4 4, add 18 18 4, add 18 18 16, copy 12 18, const 11 0,
  less 15 11 17, loop 15 3 emitBodyC]

theorem exec_emitCode {B S ℓ A Z μ : ℕ} {m : Mem} {z : List ℕ} (hz : z.length = μ)
    (hR : CodeRegs S ℓ A m) (h10 : m 10 = Z) (h17 : m 17 = μ) (hKS : nK ≤ S)
    (hZ : S + nK ≤ Z) (hB : Z + μ < B) (hzv : ∀ j < μ, vm S m (Z + j) = z[j]!)
    (hzB : ∀ j < μ, z[j]! < B) (hNS : 3 * ℓ + 3 + 3 * μ ≤ S) :
    Runs B emitCode m fun m' k => CodeRegs S ℓ A m' ∧
      (∀ a, 3 * ℓ + 3 ≤ a → a < 3 * ℓ + 3 + 3 * μ →
        vm S m' a = (tripleNat z).getD (a - (3 * ℓ + 3)) 0) ∧
      (∀ a, (a < 3 * ℓ + 3 ∨ 3 * ℓ + 3 + 3 * μ ≤ a) → vm S m' a = vm S m a) ∧
      k ≤ 25 * μ + 10 := by
  obtain ⟨⟨h1, h3, h5⟩, h4, h8, h9, h16⟩ := id hR
  have hT0 : ∀ i < μ, (tripleNat z).getD (3 * i) 0 = 1 := by
    intro i hi; rw [tripleNat_getD_mul]; simp [hz, hi]
  have hT1 : ∀ i (hi : i < μ), (tripleNat z).getD (3 * i + 1) 0 = z[i]! := by
    intro i hi; rw [tripleNat_getD_mul_one]; simp [hz, hi]
  have hT2 : ∀ i, (tripleNat z).getD (3 * i + 2) 0 = 0 := fun i => tripleNat_getD_mul_two z i
  let P : Mem → ℕ → Prop := fun m' s => ∃ i ≤ μ, CodeRegs S ℓ A m' ∧ m' 10 = Z ∧ m' 17 = μ ∧
    m' 11 = i ∧ m' 12 = 3 * ℓ + 3 + 3 * i ∧ m' 15 = (if i < μ then 1 else 0) ∧
    (∀ a, 3 * ℓ + 3 ≤ a → a < 3 * ℓ + 3 + 3 * i →
      vm S m' a = (tripleNat z).getD (a - (3 * ℓ + 3)) 0) ∧
    (∀ a, (a < 3 * ℓ + 3 ∨ 3 * ℓ + 3 + 3 * i ≤ a) → vm S m' a = vm S m a) ∧ s ≤ 25 * i
  rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep
  rename_i m₁ g₁ f₁ v₁ m₂ g₂ f₂ v₂ m₃ g₃ f₃ v₃ m₄ g₄ f₄ v₄ m₅ g₅ f₅ v₅ m₆ g₆ f₆ v₆
  refine Runs.mono (Q := fun m' k => CodeRegs S ℓ A m' ∧
      (∀ a, 3 * ℓ + 3 ≤ a → a < 3 * ℓ + 3 + 3 * μ →
        vm S m' a = (tripleNat z).getD (a - (3 * ℓ + 3)) 0) ∧
      (∀ a, (a < 3 * ℓ + 3 ∨ 3 * ℓ + 3 + 3 * μ ≤ a) → vm S m' a = vm S m a) ∧ k ≤ 25 * μ + 1)
    (Runs.loop P (fun m' => μ - m' 11) (by omega) (by omega) ?_ ?_ ?_) ?_
  · rintro m' s ⟨i, hi, ⟨⟨r1, r3, r5⟩, r4, r8, r9, r16⟩, r10, r17, h11, h12, h15, hdone, hfr, hs⟩
      heq
    have hlt : i < μ := by by_contra h; simp [h15, r3, h] at heq
    have hval : m' (Z + i) = z[i]! := by
      rw [← hzv i hlt, ← hfr _ (.inr (by omega)), vm_high hKS (by omega)]
    rstep
    refine Runs.vwrite (S := S) ⟨r1, r3, r5⟩ (by omega) (by omega) (by omega) (by omega) hKS
      (by omega) (by omega) ?_
    intro m₇ k₇ hk₇ hR₇ hvm₇ hfr₇
    rstep; rstep; rstep; rstep; rstep; rstep; rstep
    rename_i m₈ g₈ f₈ v₈ m₉ g₉ f₉ v₉ m₁₀ g₁₀ f₁₀ v₁₀
    have hadr : m₈ 10 + m₈ 11 = Z + i := by rsd
    have hv10 : m₁₀ 14 = z[i]! := by
      rw [g₁₀, g₉, hadr, f₉ _ (by omega), f₈ _ (by omega), ← vm_high hKS (by omega) (m := m₇),
        hvm₇, update_apply, if_neg (by rw [h12]; omega), vm_high hKS (by omega)]
      exact hval
    refine Runs.vwrite (S := S) ⟨by rsd, by rsd, by rsd⟩ (by omega) (by omega) (by omega)
      (by omega) hKS (by omega) (by rsd) ?_
    intro m₁₁ k₁₁ hk₁₁ hR₁₁ hvm₁₁ hfr₁₁
    rstep; rstep; rstep
    refine Runs.vwrite (S := S) ⟨by rsd, by rsd, by rsd⟩ (by omega) (by omega) (by omega)
      (by omega) hKS (by omega) (by rsd) ?_
    intro m₁₃ k₁₃ hk₁₃ hR₁₃ hvm₁₃ hfr₁₃
    rstep; rstep; rstep; rstep; rstep; rstep; rstep
    rename_i m₁₂ g₁₂ f₁₂ v₁₂ m₁₄ g₁₄ f₁₄ v₁₄ m₁₅ g₁₅ f₁₅ v₁₅ m₁₆ g₁₆ f₁₆ v₁₆ m₁₇ g₁₇ f₁₇ v₁₇
    have a7 : m' 12 = 3 * ℓ + 3 + 3 * i := h12
    have a11 : m₁₀ 12 = 3 * ℓ + 3 + 3 * i + 1 := by rsd
    have a13 : m₁₂ 12 = 3 * ℓ + 3 + 3 * i + 2 := by rsd
    have hv : ∀ a, vm S m₁₇ a = update (update (update (vm S m') (3 * ℓ + 3 + 3 * i) 1)
        (3 * ℓ + 3 + 3 * i + 1) (z[i]!)) (3 * ℓ + 3 + 3 * i + 2) 0 a := by
      intro a
      rw [v₁₇, v₁₆, v₁₅, v₁₄, hvm₁₃, v₁₂, hvm₁₁, v₁₀, v₉, v₈, hvm₇, a7, a11, a13, hv10,
        show m₁₂ 8 = 0 by rsd, show m' 3 = 1 from r3]
    refine ⟨⟨i + 1, by omega, ⟨⟨by rsd, by rsd, by rsd⟩, by rsd, by rsd, by rsd, by rsd⟩, by rsd,
      by rsd, by rsd, by rsd, by rsd, fun a ha1 ha2 => ?_, fun a ha => ?_, by omega⟩, by rsd⟩
    · rw [hv]
      simp only [update_apply]
      split_ifs with e₂ e₁ e₀
      · rw [e₂, show 3 * ℓ + 3 + 3 * i + 2 - (3 * ℓ + 3) = 3 * i + 2 by omega, hT2]
      · rw [e₁, show 3 * ℓ + 3 + 3 * i + 1 - (3 * ℓ + 3) = 3 * i + 1 by omega, hT1 i hlt]
      · rw [e₀, show 3 * ℓ + 3 + 3 * i - (3 * ℓ + 3) = 3 * i by omega, hT0 i hlt]
      · exact hdone a ha1 (by omega)
    · rw [hv]
      simp only [update_apply]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact hfr a (by omega)
  · rintro m' s ⟨i, hi, hR', r10, r17, h11, h12, h15, hdone, hfr, hs⟩ hne
    have hin : i = μ := by
      by_contra h
      exact hne (by rw [h15, hR'.1.2.1, if_pos (by omega)])
    subst hin
    exact ⟨hR', hdone, hfr, by omega⟩
  · refine ⟨0, by omega, ⟨⟨by rsd, by rsd, by rsd⟩, by rsd, by rsd, by rsd, by rsd⟩, by rsd, by rsd,
      by rsd, by rsd, by rsd, fun a ha1 ha2 => by omega,
      fun a _ => by rw [v₆, v₅, v₄, v₃, v₂, v₁], by omega⟩
  · rintro m' k ⟨⟨⟨r1, r3, r5⟩, r4, r8, r9, r16⟩, hd, hfr, hk⟩
    rstep
    rename_i m₇ g₇ f₇ v₇
    refine ⟨⟨⟨by rsd, by rsd, by rsd⟩, by rsd, by rsd, by rsd, by rsd⟩,
      fun a ha1 ha2 => by rw [v₇]; exact hd a ha1 ha2, fun a ha => by rw [v₇]; exact hfr a ha,
      by omega⟩

end Formalgo.Algorithms.ShortestPaths.LLMUnchecked
