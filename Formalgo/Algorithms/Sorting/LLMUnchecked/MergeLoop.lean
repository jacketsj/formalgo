import Formalgo.Algorithms.Sorting.LLMUnchecked.MergeList

/-!
# Merging two runs on the machine

LLM-generated; not checked by a human.
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
