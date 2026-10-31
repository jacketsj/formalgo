import Formalgo.Algorithms.Sorting.Statement
import Formalgo.Algorithms.Sorting.LLMUnchecked.Algorithm

/-!
# Proof that merge sort sorts in `O(n log n)` steps

LLM-generated; not checked by a human.
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

set_option maxHeartbeats 4000000 in
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
    have hPv : ∀ j (hj : j < P.length), m' (p₀ + j) = P[j] := fun j hj => by
      rw [hfr _ (by rw [mem_mergeRegs]; omega) (by omega)]; exact hP j hj
    have hQv : ∀ j (hj : j < Q.length), m' (q₀ + j) = Q[j] := fun j hj => by
      rw [hfr _ (by rw [mem_mergeRegs]; omega) (by omega)]; exact hQ j hj
    -- Finishing an iteration that took the left element.
    have finL : ∀ (hxP : x < P.length) (_ : ∀ hyQ : y < Q.length, nle P[x] (Q[y]'hyQ))
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
    -- Finishing an iteration that took the right element.
    have finR : ∀ (hyQ : y < Q.length) (_ : ∀ hxP : x < P.length, nle (P[x]'hxP) Q[y] = false)
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
