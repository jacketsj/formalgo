import Formalgo.Algorithms.Sorting.LLMUnchecked.PairLoop

/-!
# Merge passes on the machine

LLM-generated; not checked by a human.
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
    by rw [pow_succ]; rsd, by rw [pow_succ]; rsd, fun t ht => ?_,
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
