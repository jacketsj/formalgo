import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunMain

/-!
# Running the output loop

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {m : Mem} {B : ℕ} {t : St}

/-- The registers the output loop uses. -/
def TO (a : ℕ) : Prop :=
  a = 2 ∨ a = 6 ∨ a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 17

theorem TO_tmp {a : ℕ} (h : TO a) : Tmp a := by
  simp only [TO] at h; simp only [Tmp]; omega

/-- Changes outside the heap and the fixed registers keep `Rep`. -/
theorem Rep.keep {σ : St} {m' : Mem} (h : Rep L σ m) (hm : ∀ a, ¬Tmp a → a < 32 → m' a = m a)
    (hd : ∀ a, L.Dyn a → m' a = m a) : Rep L σ m' := by
  have hr : ∀ a, ¬Tmp a → a < 32 → m' a = m a := hm
  refine ⟨h.H32, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk i hi => ?_, fun v hv j hj => ?_⟩
  · rw [hr _ (breg_not_tmp hk) (breg_lt k hk)]; exact h.base k hk
  · rw [hr 27 (by simp [Tmp]) (by omega)]; exact h.n
  · rw [hr 28 (by simp [Tmp]) (by omega)]; exact h.D
  · rw [hr 29 (by simp [Tmp]) (by omega)]; exact h.hmin
  · rw [hr 3 (by simp [Tmp]) (by omega)]; exact h.one
  · rw [hr 8 (by simp [Tmp]) (by omega)]; exact h.zero
  · rw [hr 16 (by simp [Tmp]) (by omega)]; exact h.three
  · rw [hd _ (dyn_arr hk hi)]; exact h.arr k hk i hi
  · rw [hd _ (dyn_ch hv hj)]; exact h.ch v hv j hj

/-- Write the output of vertex `v`, and move on. -/
theorem outBody_spec (hR : Rep L t m) {v : ℕ} (h11 : m 11 = v) (h1 : 1 ≤ v) (hv : v ≤ L.n)
    (hB : L.top < B) :
    Runs B outBody m fun m' k => Rep L t m' ∧ m' 11 = v + 1 ∧
      m' 12 = (if L.n < v + 1 then 1 else 0) ∧ m' (L.H + 9 * L.R + v) = outVal t v ∧
      (∀ a, a < 32 → ¬TO a → m' a = m a) ∧
      (∀ a, 32 ≤ a → a ≠ L.H + 9 * L.R + v → m' a = m a) ∧ k ≤ 14 := by
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have b1 : m 11 ≤ L.bnd 1 := by rw [h11]; simp [Lay.bnd]; omega
  have one := hR.one
  unfold outBody
  refine Runs.seqs_cons (Runs.mono (rd_spec hR (k := 1) (d := 13) (i := 11) (by omega) b1
    (by omega) (by omega) (by omega) hB) fun m₁ c₁ ⟨g₁, f₁, hc₁⟩ => ?_)
  rw [h11] at g₁
  replace g₁ : m₁ 13 = t.stat v := g₁
  have R₁ := hR.regs2 (r₁ := 2) (r₂ := 13) (by simp [Tmp]) (by simp [Tmp]) (by omega) (by omega) f₁
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [R₁.one]; omega) fun m₂ g₂ f₂ => ?_)
  rw [R₁.one] at g₂
  have R₂ := R₁.regs1 (r := 6) (by simp [Tmp]) (by omega) f₂
  have e11 : m₂ 11 = v := by rw [f₂ 11 (by omega), f₁ 11 (by omega) (by omega), h11]
  have e13 : m₂ 13 = t.stat v := by rw [f₂ 13 (by omega), g₁]
  -- The value: `key` for a settled vertex, or `0`.
  have hval : Runs B (ite 13 6 (seqs [rd 14 0 11]) (const 14 0)) m₂ fun m₃ c =>
      m₃ 14 = outVal t v ∧ (∀ a, a ≠ 2 → a ≠ 14 → m₃ a = m₂ a) ∧ c ≤ 6 := by
    refine Runs.ite (by omega) (by omega) (fun hs => ?_) (fun hs => ?_)
    · rw [e13, g₂] at hs
      have hs' : t.stat v = 2 := hs
      refine Runs.seqs_cons (Runs.mono (rd_spec R₂ (k := 0) (d := 14) (i := 11) (by omega)
        (by rw [e11]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
        fun m₃ c₃ ⟨g₃, f₃, hc₃⟩ => ?_)
      rw [e11] at g₃
      replace g₃ : m₃ 14 = t.key v := g₃
      refine Runs.seqs_nilR (by omega) fun m₅ g₅ f₅ => ?_
      refine ⟨?_, fun a h2 h14 => ?_, by omega⟩
      · rw [f₅ 14 (by omega), g₃]; simp [outVal, hs']
      · rw [f₅ a h2, f₃ a h2 h14]
    · rw [e13, g₂] at hs
      have hs' : t.stat v ≠ 2 := hs
      refine Runs.constR (by omega) (by omega) fun m₃ g₃ f₃ => ?_
      exact ⟨by rw [g₃]; simp [outVal, hs'], fun a _ h14 => f₃ a h14, by omega⟩
  refine Runs.seqs_cons (Runs.mono hval fun m₃ c₃ ⟨g₃, f₃, hc₃⟩ => ?_)
  have R₃ := R₂.regs2 (r₁ := 2) (r₂ := 14) (by simp [Tmp]) (by simp [Tmp]) (by omega) (by omega) f₃
  have e₃ : m₃ 11 = v := by rw [f₃ 11 (by omega) (by omega), e11]
  have b₃ : m₃ 10 = L.H + 9 * L.R := R₃.base 9 (by omega)
  have hvR : v < L.R := by omega
  -- Store it.
  have hbr : breg 9 = 10 := rfl
  refine Runs.seqs_cons (Runs.seq (Runs.addR (by omega) (by rw [hbr]; omega) (by omega)
    (by rw [hbr, b₃, e₃]; omega) fun m₄ g₄ f₄ => Runs.store (by omega) (by omega) ?_))
  have ad : m₄ 2 = L.H + 9 * L.R + v := by rw [g₄, hbr, b₃, e₃]
  rw [ad, f₄ 14 (by omega)]
  set m₅ := update m₄ (L.H + 9 * L.R + v) (m₃ 14) with hm₅
  have f₅ : ∀ a, a ≠ L.H + 9 * L.R + v → m₅ a = m₄ a := fun a ha => update_of_ne ha _ _
  have s₅ : m₅ (L.H + 9 * L.R + v) = m₃ 14 := update_self _ _ _
  have lo : ∀ a, a < 32 → a ≠ L.H + 9 * L.R + v := fun a ha => by omega
  have r₅ : ∀ a, a < 32 → a ≠ 2 → m₅ a = m₃ a := fun a ha h2 => by
    rw [f₅ a (lo a ha), f₄ a h2]
  have hCH := CH_ge (L := L)
  have R₅ : Rep L t m₅ := R₃.keep (fun a ha h32 => r₅ a h32 fun e => ha (by simp [Tmp, e]))
    (fun a hd => by
      have hne : a ≠ L.H + 9 * L.R + v := fun e => by unfold Lay.Dyn Lay.top at hd; omega
      have h2 : a ≠ 2 := fun e => by unfold Lay.Dyn Lay.top at hd; omega
      rw [f₅ a hne, f₄ a h2])
  have e11' : m₅ 11 = v := by rw [r₅ 11 (by omega) (by omega), e₃]
  have o₅ : m₅ 3 = 1 := R₅.one
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [e11', o₅]; omega) fun m₆ g₆ f₆ => ?_)
  rw [e11', o₅] at g₆
  have R₆ := R₅.regs1 (r := 11) (by simp [Tmp]) (by omega) f₆
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₇ g₇ f₇ => ?_)
  have n₆ : m₆ 27 = L.n := R₆.n
  rw [n₆, g₆] at g₇
  refine Runs.seqs_nilR (by omega) fun m₈ g₈ f₈ => ?_
  have hi : ∀ a, 32 ≤ a → m₈ a = m₅ a := fun a ha => by
    rw [f₈ a (by omega), f₇ a (by omega), f₆ a (by omega)]
  refine ⟨((R₆.regs1 (r := 12) (by simp [Tmp]) (by omega) f₇).regs1 (r := 2) (by simp [Tmp])
    (by omega) f₈), ?_, ?_, ?_, fun a ha hT => ?_, fun a ha hne => ?_, by omega⟩
  · rw [f₈ 11 (by omega), f₇ 11 (by omega), g₆]
  · rw [f₈ 12 (by omega), g₇]
  · rw [hi _ (by omega), s₅, g₃]
  · simp only [TO, not_or] at hT
    obtain ⟨t2, t6, t11, t12, t13, t14, t17⟩ := hT
    rw [f₈ a t2, f₇ a t12, f₆ a t11, r₅ a ha t2, f₃ a t2 t14, f₂ a t6, f₁ a t2 t13]
  · rw [hi a ha, f₅ a hne, f₄ a (by omega), f₃ a (by omega) (by omega), f₂ a (by omega),
      f₁ a (by omega) (by omega)]

/-- The output: `n`, then each vertex's value. -/
theorem output_run (hR : Rep L t m) (hB : L.top < B) :
    Runs B output m fun m' k => Rep L t m' ∧ m' 17 = L.n + 1 ∧ m' (L.H + 9 * L.R) = L.n ∧
      (∀ v, 1 ≤ v → v ≤ L.n → m' (L.H + 9 * L.R + v) = outVal t v) ∧
      (∀ a, a < 32 → ¬TO a → m' a = m a) ∧
      (∀ a, 32 ≤ a → (a < L.H + 9 * L.R ∨ L.H + 10 * L.R ≤ a) → m' a = m a) ∧
      k ≤ 17 * L.n + 12 := by
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have b₀ : m 10 = L.H + 9 * L.R := hR.base 9 (by omega)
  have n₀ : m 27 = L.n := hR.n
  have tmp12 : Tmp 12 := by simp [Tmp]
  unfold output
  refine Runs.seqs_cons (Runs.storeR (by omega) (by omega) fun m₁ g₁ f₁ => ?_)
  rw [b₀, n₀] at g₁
  have hne : ∀ a, a < 32 → a ≠ L.H + 9 * L.R := fun a ha => by omega
  have hCH := CH_ge (L := L)
  have R₁ : Rep L t m₁ := hR.keep (fun a _ h32 => f₁ a (by rw [b₀]; exact hne a h32))
    (fun a hd => f₁ a (by rw [b₀]; intro e; unfold Lay.Dyn Lay.top at hd; omega))
  refine Runs.seqs_cons (Runs.constR (by omega) (by omega) fun m₂ g₂ f₂ => ?_)
  have R₂ := R₁.regs1 (r := 11) (by simp [Tmp]) (by omega) f₂
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₃ g₃ f₃ => ?_)
  have R₃ := R₂.regs1 (r := 12) (by simp [Tmp]) (by omega) f₃
  have n₂ : m₂ 27 = L.n := R₂.n
  rw [n₂, g₂] at g₃
  -- The loop: vertices below `v` are written.
  let P : Mem → ℕ → Prop := fun m' c => ∃ v, 1 ≤ v ∧ v ≤ L.n + 1 ∧ Rep L t m' ∧ m' 11 = v ∧
    m' 12 = (if L.n < v then 1 else 0) ∧ m' (L.H + 9 * L.R) = L.n ∧
    (∀ j, 1 ≤ j → j < v → m' (L.H + 9 * L.R + j) = outVal t j) ∧
    (∀ a, a < 32 → ¬TO a → m' a = m a) ∧
    (∀ a, 32 ≤ a → (a < L.H + 9 * L.R ∨ L.H + 10 * L.R ≤ a) → m' a = m a) ∧
    c ≤ 16 * (v - 1)
  have lo₃ : ∀ a, a < 32 → ¬TO a → m₃ a = m a := fun a ha hT => by
    simp only [TO, not_or] at hT
    obtain ⟨t2, t6, t11, t12, t13, t14, t17⟩ := hT
    rw [f₃ a t12, f₂ a t11, f₁ a (by rw [b₀]; exact hne a ha)]
  have hi₃ : ∀ a, 32 ≤ a → (a < L.H + 9 * L.R ∨ L.H + 10 * L.R ≤ a) → m₃ a = m a :=
    fun a ha hr => by
      have hRp : 0 < L.R := by omega
      rw [f₃ a (by omega), f₂ a (by omega), f₁ a (by rw [b₀]; omega)]
  have o₃ : m₃ (L.H + 9 * L.R) = L.n := by rw [f₃ _ (by omega), f₂ _ (by omega), g₁]
  refine Runs.seqs_cons (Runs.loop P (fun m' => L.n + 1 - m' 11) (by omega) (by omega) ?_ ?_
    ⟨1, le_refl _, by omega, R₃, by rw [f₃ 11 (by omega), g₂], by rw [g₃], o₃,
      fun j h1 h2 => by omega, lo₃, hi₃, by omega⟩)
  · rintro m' c ⟨v, h1, hv, Rv, e11, e12, e0, hdone, hlo, hhi, hc⟩ heq
    have hvn : v ≤ L.n := by
      rw [e12, Rv.zero] at heq
      by_contra hn; simp [show L.n < v by omega] at heq
    refine Runs.mono (outBody_spec Rv e11 h1 hvn hB)
      fun m₄ k ⟨R₄, a11, a12, a0, alo, ahi, hk'⟩ => ⟨⟨v + 1, by omega, by omega, R₄, a11, a12, ?_,
        fun j h1' h2 => ?_, fun a ha hT => ?_, fun a ha hr => ?_, ?_⟩, ?_⟩
    · rw [ahi _ (by omega) (by omega), e0]
    · rcases Nat.lt_or_ge j v with hj | hj
      · rw [ahi _ (by omega) (by omega), hdone j h1' hj]
      · have : j = v := by omega
        subst this; exact a0
    · rw [alo a ha hT, hlo a ha hT]
    · have hRp : 0 < L.R := by omega
      rw [ahi a ha (by omega), hhi a ha hr]
    · simp only [Nat.add_sub_cancel]
      have : 16 * v = 16 * (v - 1) + 16 := by omega
      omega
    · rw [a11, e11]; omega
  · rintro m' c ⟨v, h1, hv, Rv, e11, e12, e0, hdone, hlo, hhi, hc⟩ heq
    have hvn : v = L.n + 1 := by
      rw [e12, Rv.zero] at heq
      by_contra hn
      exact heq (by rw [if_neg (by omega)])
    subst hvn
    have n' : m' 27 = L.n := Rv.n
    have o' : m' 3 = 1 := Rv.one
    refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
      (by rw [n', o']; omega) fun m₄ g₄ f₄ => ?_)
    rw [n', o'] at g₄
    refine Runs.seqs_nilR (by omega) fun m₅ g₅ f₅ => ?_
    have hH' : ∀ a, 32 ≤ a → m₅ a = m' a := fun a ha => by
      rw [f₅ a (by omega), f₄ a (by omega)]
    refine ⟨(Rv.regs1 (r := 17) (by simp [Tmp]) (by omega) f₄).regs1 (r := 2) (by simp [Tmp])
      (by omega) f₅, by rw [f₅ 17 (by omega), g₄], by rw [hH' _ (by omega), e0],
      fun j h1' h2 => by rw [hH' _ (by omega), hdone j h1' (by omega)],
      fun a ha hT => ?_, fun a ha hr => by rw [hH' a ha, hhi a ha hr], ?_⟩
    · have t2 : a ≠ 2 := fun e => hT (by simp [TO, e])
      have t17 : a ≠ 17 := fun e => hT (by simp [TO, e])
      rw [f₅ a t2, f₄ a t17, hlo a ha hT]
    · simp only [Nat.add_sub_cancel] at hc
      have : 16 * L.n ≤ 17 * L.n := by omega
      omega

end Formalgo.Algorithms.ShortestPaths
