import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Machine.CodeAlgorithm

/-!
# Converting adjacency lists to the edge list

LLM-generated; not checked by a human.

The input code is `n, n`, then for each vertex `u` its degree and its neighbours, then the rest `t`.
`conv` writes, right after it, `n, E`, the pairs `u, v` with `u < v` in that order, then `t`.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Function

/-- `rs`, trying `decide` before `omega` on side conditions. -/
local macro "rsd" : tactic => `(tactic| first
  | omega
  | ((simp (disch := first | decide | omega) only [*, Function.update_self,
      Function.update_of_ne]) <;> first
      | omega
      | (split_ifs <;> omega)))

/-- The list `c` is in memory from `A`. -/
def MemAt (m : Mem) (A : ℕ) (c : List ℕ) : Prop := ∀ j (h : j < c.length), m (A + j) = c[j]

theorem MemAt.left {m : Mem} {A : ℕ} {c d : List ℕ} (h : MemAt m A
    (c ++ d)) : MemAt m A c := fun j hj => by
  have := h j (by simp; omega)
  rwa [List.getElem_append_left hj] at this

theorem MemAt.right {m : Mem} {A : ℕ} {c d : List ℕ} (h : MemAt m A (c ++ d)) :
    MemAt m (A + c.length) d := fun j hj => by
  have := h (c.length + j) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [Nat.add_assoc] using this

theorem MemAt.head {m : Mem} {A a : ℕ} {c : List ℕ} (h : MemAt m A (a :: c)) : m A = a :=
  h 0 (Nat.succ_pos _)

theorem MemAt.tail {m : Mem} {A a : ℕ} {c : List ℕ} (h : MemAt m A (a :: c)) : MemAt m (A + 1) c :=
  fun j hj => by
    have := h (j + 1) (by simp; omega)
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

/-! ### Lists -/

/-- A block: a degree, then the neighbours. -/
def blk (b : List ℕ) : List ℕ := b.length :: b

/-- `u, v` for each `v` in `b` above `u`. -/
def pairsAbove (u : ℕ) (b : List ℕ) : List ℕ := (b.filter fun v => u < v).flatMap fun v => [u, v]

/-- The pairs of the blocks `bs`, numbered from `u`. -/
def emitAll : List (List ℕ) → ℕ → List ℕ
  | [], _ => []
  | b :: bs, u => pairsAbove u b ++ emitAll bs (u + 1)

theorem emitAll_append (l₁ l₂ : List (List ℕ)) (u : ℕ) :
    emitAll (l₁ ++ l₂) u = emitAll l₁ u ++ emitAll l₂ (u + l₁.length) := by
  induction l₁ generalizing u with
  | nil => simp [emitAll]
  | cons b l ih =>
    simp only [List.cons_append, emitAll, ih, List.append_assoc, List.length_cons]
    congr 3; omega

theorem emitAll_take_succ {bs : List (List ℕ)} {i : ℕ} (h : i < bs.length) :
    emitAll (bs.take (i + 1)) 0 = emitAll (bs.take i) 0 ++ pairsAbove i bs[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, emitAll_append]
  simp [emitAll, Nat.min_eq_left h.le]

theorem pairsAbove_take_succ {u : ℕ} {b : List ℕ} {k : ℕ} (h : k < b.length) :
    pairsAbove u (b.take (k + 1)) =
      pairsAbove u (b.take k) ++ (if u < b[k] then [u, b[k]] else []) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some]
  unfold pairsAbove
  rw [List.filter_append, List.flatMap_append]
  split_ifs with hu <;> simp [hu]

theorem flatMap_take_succ {bs : List (List ℕ)} {i : ℕ} (h : i < bs.length) :
    (bs.take (i + 1)).flatMap blk = (bs.take i).flatMap blk ++ blk bs[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.flatMap_append]
  simp

theorem flatMap_split (bs : List (List ℕ)) {i : ℕ} (h : i < bs.length) :
    bs.flatMap blk = (bs.take i).flatMap blk ++ (blk bs[i] ++ (bs.drop (i + 1)).flatMap blk) := by
  conv_lhs => rw [← List.take_append_drop i bs, List.drop_eq_getElem_cons h, List.flatMap_append,
    List.flatMap_cons]

theorem MemAt.snoc {m m' : Mem} {Q : ℕ} {W : List ℕ} {v : ℕ} (h : MemAt m Q W)
    (hv : m' (Q + W.length) = v) (hf : ∀ a, a ≠ Q + W.length → m' a = m a) :
    MemAt m' Q (W ++ [v]) := fun j hj => by
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_ge j W.length with hj' | hj'
  · rw [hf _ (by omega), h j hj', List.getElem_append_left hj']
  · obtain rfl : j = W.length := by omega
    simp [hv]

theorem MemAt.frame {m m' : Mem} {Q : ℕ} {W : List ℕ} (h : MemAt m Q W)
    (hf : ∀ j < W.length, m' (Q + j) = m (Q + j)) : MemAt m' Q W := fun j hj => by
  rw [hf j hj, h j hj]

theorem MemAt.cons {m : Mem} {A a : ℕ} {c : List ℕ} (h0 : m A = a) (h : MemAt m (A + 1) c) :
    MemAt m A (a :: c) := fun j hj => by
  rcases j with _ | j
  · simpa using h0
  · rw [List.getElem_cons_succ, show A + (j + 1) = A + 1 + j by omega]
    exact h j (by simp at hj; omega)

theorem MemAt.append {m : Mem} {A : ℕ} {c d : List ℕ} (h1 : MemAt m A c)
    (h2 : MemAt m (A + c.length) d) : MemAt m A (c ++ d) := fun j hj => by
  rcases Nat.lt_or_ge j c.length with h | h
  · rw [List.getElem_append_left h]; exact h1 j h
  · rw [List.getElem_append_right h]
    have := h2 (j - c.length) (by simp at hj; omega)
    rwa [show A + c.length + (j - c.length) = A + j by omega] at this

/-! ### The program -/

/-- Write the pair `u, v`. -/
def emitP : Cmd := seqs [store 11 14, add 11 11 3, store 11 21, add 11 11 3]

/-- One neighbour `v` of `u`: if `u < v`, write `u, v`. -/
def innerBody : Cmd :=
  seqs [load 21 13, less 22 14 21, ite 22 3 emitP (seqs []), add 13 13 3, add 19 19 3,
    less 20 19 18]

/-- One vertex: its degree, then its neighbours. -/
def outerBody : Cmd :=
  seqs [load 18 13, add 13 13 3, const 19 0, less 20 19 18, loop 20 3 innerBody, add 14 14 3,
    less 17 14 15]

/-- Copy one cell. -/
def copyBody : Cmd := seqs [load 21 13, store 11 21, add 13 13 3, add 11 11 3, add 19 19 3,
  less 20 19 25]

/-- Write the edge-list code after the input, and point registers `9` and `4` at it. -/
def conv : Cmd :=
  seqs [add 10 9 4, const 12 2, add 11 10 12, add 13 9 12, const 14 0, load 15 9, less 17 14 15,
    loop 17 3 outerBody, store 10 15, load 23 13, add 24 10 3, store 24 23, add 25 23 12,
    const 19 0, less 20 19 25, loop 20 3 copyBody, copy 9 10, add 4 25 25, add 4 4 25,
    sub 4 4 12]

/-! ### One vertex -/

/-- The registers fixed while converting. -/
def CvRegs (S ℓ A n : ℕ) (m : Mem) : Prop :=
  CodeRegs S ℓ A m ∧ m 10 = A + ℓ ∧ m 12 = 2 ∧ m 15 = n

theorem CvRegs.of {S ℓ A n : ℕ} {m m' : Mem} (h : CvRegs S ℓ A n m)
    (hf : ∀ r, r < 17 → r ≠ 2 → r ≠ 6 → r ≠ 7 → r ≠ 11 → r ≠ 13 → r ≠ 14 → m' r = m r) :
    CvRegs S ℓ A n m' := by
  obtain ⟨⟨⟨h1, h3, h5⟩, h4, h8, h9, h16⟩, h10, h12, h15⟩ := h
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    rw [hf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)] <;>
    assumption

/-- The state inside the loop over the neighbours of `u`, after `k` of them. -/
def InnerInv (S ℓ A n u p Q : ℕ) (b W : List ℕ) (m₀ m : Mem) (k : ℕ) : Prop :=
  CvRegs S ℓ A n m ∧ m 14 = u ∧ m 18 = b.length ∧ m 19 = k ∧
    m 20 = (if k < b.length then 1 else 0) ∧ m 13 = p + 1 + k ∧
    m 11 = Q + (W ++ pairsAbove u (b.take k)).length ∧ MemAt m Q (W ++ pairsAbove u (b.take k)) ∧
    ∀ a, 32 ≤ a → (a < Q ∨ Q + (W ++ pairsAbove u (b.take k)).length ≤ a) → m a = m₀ a

theorem length_pairsAbove_le (u : ℕ) (b : List ℕ) : (pairsAbove u b).length ≤ 2 * b.length := by
  induction b with
  | nil => simp [pairsAbove]
  | cons v b ih =>
    unfold pairsAbove at ih ⊢
    by_cases h : u < v <;> simp [h] at ih ⊢ <;> omega

theorem pairsAbove_append (u : ℕ) (b c : List ℕ) :
    pairsAbove u (b ++ c) = pairsAbove u b ++ pairsAbove u c := by
  simp [pairsAbove, List.filter_append, List.flatMap_append]

theorem length_pairsAbove_take (u : ℕ) (b : List ℕ) (j : ℕ) :
    (pairsAbove u (b.take j)).length ≤ (pairsAbove u b).length := by
  conv_rhs => rw [← List.take_append_drop j b, pairsAbove_append]
  simp

/-- One neighbour. -/
theorem inner_step {B S ℓ A n u p Q k : ℕ} {b W : List ℕ} {m₀ m : Mem}
    (hI : InnerInv S ℓ A n u p Q b W m₀ m k) (hk : k < b.length) (hKS : nK ≤ S)
    (hb : m₀ (p + 1 + k) = b[k]) (hp32 : 32 ≤ p) (hpQ : p + 1 + b.length ≤ Q)
    (hB : Q + (W ++ pairsAbove u b).length + 2 < B) :
    Runs B innerBody m fun m' s => InnerInv S ℓ A n u p Q b W m₀ m' (k + 1) ∧ s ≤ 14 := by
  obtain ⟨hR, h14, h18, h19, h20, h13, h11, hW, hfr⟩ := hI
  obtain ⟨⟨⟨r1, r3, r5⟩, r4, r8, r9, r16⟩, r10, r12, r15⟩ := id hR
  have hstep : W ++ pairsAbove u (b.take (k + 1)) =
      (W ++ pairsAbove u (b.take k)) ++ (if u < b[k] then [u, b[k]] else []) := by
    rw [pairsAbove_take_succ hk, List.append_assoc]
  have hle := length_pairsAbove_take u b (k + 1)
  generalize hV : W ++ pairsAbove u (b.take k) = V at h11 hW hfr hstep
  generalize hV' : V ++ (if u < b[k] then [u, b[k]] else []) = V' at hstep
  have hVl : V'.length ≤ (W ++ pairsAbove u b).length := by
    have := congrArg List.length hstep; simp only [List.length_append] at this ⊢; omega
  have hVV : V.length + (if u < b[k] then 2 else 0) = V'.length := by
    rw [← hV']; split_ifs <;> simp
  have hv : m (p + 1 + k) = b[k] := by rw [hfr _ (by omega) (.inl (by omega)), hb]
  rstep; rstep
  rename_i m₁ g₁ f₁ v₁
  rstep; rstep
  rename_i m₂ g₂ f₂ v₂
  have e21 : m₂ 21 = b[k] := by rw [f₂ 21 (by decide), g₁, h13, hv]
  have e22 : m₂ 22 = if u < b[k] then 1 else 0 := by
    rw [g₂, f₁ 14 (by decide), h14, g₁, h13, hv]
  have e11 : m₂ 11 = Q + V.length := by rw [f₂ 11 (by decide), f₁ 11 (by decide), h11]
  have e14 : m₂ 14 = u := by rw [f₂ 14 (by decide), f₁ 14 (by decide), h14]
  have e3 : m₂ 3 = 1 := by rw [f₂ 3 (by decide), f₁ 3 (by decide), r3]
  have hW₂ : MemAt m₂ Q V := hW.frame fun j hj => by rw [f₂ _ (by omega), f₁ _ (by omega)]
  have hfr₂ : ∀ a, 32 ≤ a → (a < Q ∨ Q + V.length ≤ a) → m₂ a = m₀ a := fun a ha hc => by
    rw [f₂ _ (by omega), f₁ _ (by omega), hfr a ha hc]
  clear hW hfr g₁ g₂ h11 h14
  rstep
  refine Runs.mono (Q := fun m₃ k₃ => (∀ r, r < 32 → r ≠ 2 → r ≠ 11 → m₃ r = m₂ r) ∧
      m₃ 11 = Q + V'.length ∧ MemAt m₃ Q V' ∧
      (∀ a, 32 ≤ a → (a < Q ∨ Q + V'.length ≤ a) → m₃ a = m₀ a) ∧ k₃ ≤ 7)
    (Runs.ite (by omega) (by omega) ?_ ?_) ?_
  · intro heq
    have hlt : u < b[k] := by
      by_contra h; rw [e22, if_neg h, e3] at heq; exact absurd heq (by decide)
    rw [if_pos hlt] at hV' hVV
    subst hV'
    rstep
    refine Runs.storeR (p := 11) (s := 14) (by omega) (by omega) ?_
    intro m₄ s₄ fr₄
    rw [e11, e14] at s₄
    rw [e11] at fr₄
    rstep
    refine Runs.addV hKS (by decide) (by omega) (by omega) (by omega)
      (by rw [fr₄ 11 (by omega), fr₄ 3 (by omega), e11, e3]; omega) ?_
    intro m₅ g₅ f₅ v₅
    have e5 : m₅ 11 = Q + V.length + 1 := by rw [g₅, fr₄ 11 (by omega), e11, fr₄ 3 (by omega), e3]
    rstep
    refine Runs.storeR (p := 11) (s := 21) (by omega) (by omega) ?_
    intro m₆ s₆ fr₆
    rw [e5, f₅ 21 (by decide), fr₄ 21 (by omega), e21] at s₆
    rw [e5] at fr₆
    rstep
    refine Runs.addV hKS (by decide) (by omega) (by omega) (by omega)
      (by
        rw [fr₆ 11 (by omega), fr₆ 3 (by omega), e5, f₅ 3 (by decide), fr₄ 3 (by omega), e3]
        omega) ?_
    intro m₇ g₇ f₇ v₇
    have e7 : m₇ 11 = Q + V.length + 2 := by
      rw [g₇, fr₆ 11 (by omega), e5, fr₆ 3 (by omega), f₅ 3 (by decide), fr₄ 3 (by omega), e3]
    rstep
    rename_i m₈ g₈ f₈ v₈
    refine ⟨fun r hr h2 h11 => ?_, ?_, ?_, fun a ha hc => ?_, by omega⟩
    · rw [f₈ r h2, f₇ r h11, fr₆ r (by omega), f₅ r h11, fr₄ r (by omega)]
    · rw [f₈ 11 (by decide), e7]
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · have h4 : MemAt m₄ Q (V ++ [u]) := hW₂.snoc s₄ fr₄
      have h5 : MemAt m₅ Q (V ++ [u]) := h4.frame fun j hj => f₅ _ (by simp at hj; omega)
      have h6 : MemAt m₆ Q (V ++ [u] ++ [b[k]]) := h5.snoc
        (by rw [List.length_append, List.length_singleton, ← Nat.add_assoc]; exact s₆)
        (fun a ha => fr₆ a (by simp at ha; omega))
      have h8 : MemAt m₈ Q (V ++ [u] ++ [b[k]]) := h6.frame fun j hj => by
        simp at hj
        rw [f₈ _ (by omega), f₇ _ (by omega)]
      simpa using h8
    · simp at hc
      rw [f₈ a (by omega), f₇ a (by omega), fr₆ a (by omega), f₅ a (by omega), fr₄ a (by omega),
        hfr₂ a ha (by omega)]
  · intro hne
    have hlt : ¬ u < b[k] := by
      intro h; rw [e22, if_pos h, e3] at hne; exact hne rfl
    rw [if_neg hlt] at hV' hVV
    simp only [List.append_nil] at hV'
    subst hV'
    rstep
    rename_i m₈ g₈ f₈ v₈
    refine ⟨fun r hr h2 h11 => f₈ r h2, by rw [f₈ 11 (by decide), e11], hW₂.frame fun j hj =>
      f₈ _ (by omega), fun a ha hc => by rw [f₈ a (by omega), hfr₂ a ha hc], by omega⟩
  · rintro m₃ k₃ ⟨r₃, e11₃, hW₃, hfr₃, hk₃⟩
    have e13 : m₃ 13 = p + 1 + k := by rw [r₃ 13 (by omega) (by omega) (by omega), f₂ 13
        (by decide),
      f₁ 13 (by decide), h13]
    have e19 : m₃ 19 = k := by rw [r₃ 19 (by omega) (by omega) (by omega), f₂ 19 (by decide),
      f₁ 19 (by decide), h19]
    have e18 : m₃ 18 = b.length := by rw [r₃ 18 (by omega) (by omega) (by omega),
      f₂ 18 (by decide), f₁ 18 (by decide), h18]
    have e3' : m₃ 3 = 1 := by rw [r₃ 3 (by omega) (by omega) (by omega), e3]
    rstep; rstep
    rename_i m₉ g₉ f₉ v₉
    rstep; rstep
    rename_i m₁₀ g₁₀ f₁₀ v₁₀
    rstep; rstep
    rename_i m₁₁ g₁₁ f₁₁ v₁₁
    rstep
    rename_i m₁₂ g₁₂ f₁₂ v₁₂
    have e19' : m₁₁ 19 = k + 1 := by
      rw [f₁₁ 19 (by decide), g₁₀, f₉ 19 (by decide), f₉ 3 (by decide), e19, e3']
    refine ⟨⟨CvRegs.of hR fun r a b c d e f g => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha hc => ?_⟩,
      by omega⟩
    · rw [f₁₂ r b, f₁₁ r (by omega), f₁₀ r (by omega), f₉ r (by omega), r₃ r (by omega) b e,
        f₂ r (by omega), f₁ r (by omega)]
    · rw [f₁₂ 14 (by decide), f₁₁ 14 (by decide), f₁₀ 14 (by decide), f₉ 14 (by decide),
        r₃ 14 (by omega) (by omega) (by omega), e14]
    · rw [f₁₂ 18 (by decide), f₁₁ 18 (by decide), f₁₀ 18 (by decide), f₉ 18 (by decide), e18]
    · rw [f₁₂ 19 (by decide), e19']
    · rw [f₁₂ 20 (by decide), g₁₁, f₁₀ 18 (by decide), f₉ 18 (by decide), e18, ← e19',
        f₁₁ 19 (by decide)]
    · rw [f₁₂ 13 (by decide), f₁₁ 13 (by decide), f₁₀ 13 (by decide), g₉, e13, e3']; omega
    · rw [hstep, f₁₂ 11 (by decide), f₁₁ 11 (by decide), f₁₀ 11 (by decide), f₉ 11 (by decide),
        e11₃]
    · rw [hstep]
      exact hW₃.frame fun j hj => by
        rw [f₁₂ _ (by omega), f₁₁ _ (by omega), f₁₀ _ (by omega), f₉ _ (by omega)]
    · rw [hstep] at hc
      rw [f₁₂ a (by omega), f₁₁ a (by omega), f₁₀ a (by omega), f₉ a (by omega), hfr₃ a ha hc]

/-- One vertex: its degree and its neighbours. -/
theorem block_run {B S ℓ A n u p Q : ℕ} {b W : List ℕ} {m₀ m : Mem} (hR : CvRegs S ℓ A n m)
    (h14 : m 14 = u) (h13 : m 13 = p) (h11 : m 11 = Q + W.length) (hW : MemAt m Q W)
    (hfr : ∀ a, 32 ≤ a → (a < Q ∨ Q + W.length ≤ a) → m a = m₀ a) (hKS : nK ≤ S)
    (hb : MemAt m₀ p (b.length :: b)) (hp32 : 32 ≤ p) (hpQ : p + 1 + b.length ≤ Q)
    (hB : Q + (W ++ pairsAbove u b).length + 2 < B) (hun : u < n) (hnB : n < B) :
    Runs B outerBody m fun m' s => CvRegs S ℓ A n m' ∧ m' 14 = u + 1 ∧
      m' 17 = (if u + 1 < n then 1 else 0) ∧ m' 13 = p + 1 + b.length ∧
      m' 11 = Q + (W ++ pairsAbove u b).length ∧ MemAt m' Q (W ++ pairsAbove u b) ∧
      (∀ a, 32 ≤ a → (a < Q ∨ Q + (W ++ pairsAbove u b).length ≤ a) → m' a = m₀ a) ∧
      s ≤ 16 * b.length + 14 := by
  obtain ⟨⟨⟨r1, r3, r5⟩, r4, r8, r9, r16⟩, r10, r12, r15⟩ := id hR
  have hd : m p = b.length := by rw [hfr _ hp32 (.inl (by omega)), hb.head]
  have hlen : (W ++ pairsAbove u b).length ≥ W.length := by simp
  rstep; rstep
  rename_i m₁ g₁ f₁ v₁
  rstep
  refine Runs.addV hKS (by decide) (by omega) (by omega) (by omega)
    (by rw [f₁ 13 (by decide), f₁ 3 (by decide), h13, r3]; omega) ?_
  intro m₂ g₂ f₂ v₂
  rstep; rstep
  rename_i m₃ g₃ f₃ v₃
  rstep; rstep
  rename_i m₄ g₄ f₄ v₄
  have hI0 : InnerInv S ℓ A n u p Q b W m₀ m₄ 0 := by
    refine ⟨CvRegs.of hR fun r a b c d e f g => by rw [f₄ r (by omega), f₃ r (by omega),
      f₂ r (by omega), f₁ r (by omega)], ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha hc => ?_⟩
    · rw [f₄ 14 (by decide), f₃ 14 (by decide), f₂ 14 (by decide), f₁ 14 (by decide), h14]
    · rw [f₄ 18 (by decide), f₃ 18 (by decide), f₂ 18 (by decide), g₁, h13, hd]
    · rw [f₄ 19 (by decide), g₃]
    · rw [g₄, f₃ 18 (by decide), f₂ 18 (by decide), g₁, h13, hd, g₃]
    · rw [f₄ 13 (by decide), f₃ 13 (by decide), g₂, f₁ 13 (by decide), f₁ 3 (by decide), h13, r3]
    · simp only [List.take_zero, pairsAbove, List.filter_nil, List.flatMap_nil, List.append_nil]
      rw [f₄ 11 (by decide), f₃ 11 (by decide), f₂ 11 (by decide), f₁ 11 (by decide), h11]
    · simp only [List.take_zero, pairsAbove, List.filter_nil, List.flatMap_nil, List.append_nil]
      exact hW.frame fun j hj => by
        rw [f₄ _ (by omega), f₃ _ (by omega), f₂ _ (by omega), f₁ _ (by omega)]
    · simp only [List.take_zero, pairsAbove, List.filter_nil, List.flatMap_nil, List.append_nil]
        at hc
      rw [f₄ a (by omega), f₃ a (by omega), f₂ a (by omega), f₁ a (by omega), hfr a ha hc]
  clear g₁ g₂ g₃ g₄ f₁ f₂ f₃ f₄ v₁ v₂ v₃ v₄ hW hfr h11 h13 h14
  rstep
  refine Runs.mono (Q := fun m' s => InnerInv S ℓ A n u p Q b W m₀ m' b.length ∧
      s ≤ 16 * b.length + 1)
    (Runs.loop (fun m' s => ∃ k ≤ b.length, InnerInv S ℓ A n u p Q b W m₀ m' k ∧ s ≤ 16 * k)
      (fun m' => b.length - m' 19) (by omega) (by omega) ?_ ?_ ⟨0, by omega, hI0, by omega⟩) ?_
  · rintro m' s ⟨k, hk, hI, hs⟩ heq
    have hkl : k < b.length := by
      by_contra h
      rw [hI.2.2.2.2.1, if_neg h, hI.1.1.1.2.1] at heq
      exact absurd heq (by decide)
    refine Runs.mono (inner_step hI hkl hKS (hb.tail k hkl) hp32 hpQ hB) fun m'' s' ⟨hI', hs'⟩ =>
      ⟨⟨k + 1, hkl, hI', by omega⟩, ?_⟩
    rw [hI'.2.2.2.1, hI.2.2.2.1]; omega
  · rintro m' s ⟨k, hk, hI, hs⟩ hne
    have hkl : k = b.length := by
      by_contra h
      exact hne (by rw [hI.2.2.2.2.1, if_pos (by omega), hI.1.1.1.2.1])
    subst hkl
    exact ⟨hI, by omega⟩
  · rintro m' k ⟨⟨hR', e14, e18, e19, e20, e13, e11, hW', hfr'⟩, hk⟩
    rw [List.take_length] at e11 hW' hfr'
    obtain ⟨⟨⟨q1, q3, q5⟩, q4, q8, q9, q16⟩, q10, q12, q15⟩ := id hR'
    rstep
    refine Runs.addV hKS (by decide) (by omega) (by omega) (by omega)
      (by rw [e14, q3]; omega) ?_
    intro m₅ g₅ f₅ v₅
    rstep; rstep
    rename_i m₆ g₆ f₆ v₆
    rstep
    rename_i m₇ g₇ f₇ v₇
    refine ⟨CvRegs.of hR' fun r a b c d e f g => by rw [f₇ r b, f₆ r (by omega), f₅ r g], ?_, ?_,
      ?_, ?_, hW'.frame fun j hj => by rw [f₇ _ (by omega), f₆ _ (by omega), f₅ _ (by omega)],
      fun a ha hc => by rw [f₇ a (by omega), f₆ a (by omega), f₅ a (by omega), hfr' a ha hc],
      by omega⟩
    · rw [f₇ 14 (by decide), f₆ 14 (by decide), g₅, e14, q3]
    · rw [f₇ 17 (by decide), g₆, f₅ 15 (by decide), g₅, e14, q3, q15]
    · rw [f₇ 13 (by decide), f₆ 13 (by decide), f₅ 13 (by decide), e13]
    · rw [f₇ 11 (by decide), f₆ 11 (by decide), f₅ 11 (by decide), e11]

/-! ### All vertices -/

theorem blk_mem {m : Mem} {A n : ℕ} {bs : List (List ℕ)} {t : List ℕ}
    (hM : MemAt m A (n :: n :: (bs.flatMap blk ++ t))) {i : ℕ} (hi : i < bs.length) :
    MemAt m (A + 2 + ((bs.take i).flatMap blk).length) (bs[i].length :: bs[i]) := by
  have h := hM.tail.tail.left
  rw [flatMap_split bs hi] at h
  have h' := h.right.left
  rwa [show A + 1 + 1 + ((bs.take i).flatMap blk).length =
    A + 2 + ((bs.take i).flatMap blk).length by omega] at h'

theorem tail_mem {m : Mem} {A n : ℕ} {bs : List (List ℕ)} {t : List ℕ}
    (hM : MemAt m A (n :: n :: (bs.flatMap blk ++ t))) :
    MemAt m (A + 2 + (bs.flatMap blk).length) t := by
  have h := hM.tail.tail.right
  rwa [show A + 1 + 1 + (bs.flatMap blk).length = A + 2 + (bs.flatMap blk).length by omega] at h

theorem length_flatMap_take_le (bs : List (List ℕ)) (i : ℕ) :
    ((bs.take i).flatMap blk).length ≤ (bs.flatMap blk).length := by
  conv_rhs => rw [← List.take_append_drop i bs, List.flatMap_append]
  rw [List.length_append]
  exact Nat.le_add_right _ _

theorem length_emitAll_take_le (bs : List (List ℕ)) (i : ℕ) :
    (emitAll (bs.take i) 0).length ≤ (emitAll bs 0).length := by
  conv_rhs => rw [← List.take_append_drop i bs, emitAll_append]
  simp

/-- The state of the loop over the vertices, after `i` of them. -/
def OuterInv (S ℓ A n : ℕ) (bs : List (List ℕ)) (m₀ m : Mem) (i : ℕ) : Prop :=
  i ≤ n ∧ CvRegs S ℓ A n m ∧ m 14 = i ∧ m 17 = (if i < n then 1 else 0) ∧
    m 13 = A + 2 + ((bs.take i).flatMap blk).length ∧
    m 11 = A + ℓ + 2 + (emitAll (bs.take i) 0).length ∧
    MemAt m (A + ℓ + 2) (emitAll (bs.take i) 0) ∧
    ∀ a, 32 ≤ a → (a < A + ℓ + 2 ∨ A + ℓ + 2 + (emitAll (bs.take i) 0).length ≤ a) → m a = m₀ a

theorem outer_run {B S ℓ A n : ℕ} {bs : List (List ℕ)} {t : List ℕ} {m₀ m : Mem}
    (hI : OuterInv S ℓ A n bs m₀ m 0) (hn : bs.length = n) (hKS : nK ≤ S) (hA : 32 ≤ A)
    (hM : MemAt m₀ A (n :: n :: (bs.flatMap blk ++ t)))
    (hℓ : 2 + (bs.flatMap blk).length + t.length ≤ ℓ)
    (hB : A + ℓ + 2 + (emitAll bs 0).length + 2 < B) (hnB : n < B) :
    Runs B (loop 17 3 outerBody) m fun m' s => OuterInv S ℓ A n bs m₀ m' n ∧
      s ≤ 20 * (bs.flatMap blk).length + 1 := by
  refine Runs.loop (fun m' s => ∃ i, OuterInv S ℓ A n bs m₀ m' i ∧
      s ≤ 20 * ((bs.take i).flatMap blk).length)
    (fun m' => n - m' 14) (by omega) (by omega) ?_ ?_ ⟨0, hI, by omega⟩
  · rintro m' s ⟨i, ⟨hi, hR, h14, h17, h13, h11, hW, hfr⟩, hs⟩ heq
    have hin : i < n := by
      by_contra h
      rw [h17, if_neg h, hR.1.1.2.1] at heq
      exact absurd heq (by decide)
    have hib : i < bs.length := by omega
    have hsucc := flatMap_take_succ hib
    have hpre := length_flatMap_take_le bs (i + 1)
    have hem := length_emitAll_take_le bs (i + 1)
    rw [emitAll_take_succ hib] at hem
    rw [hsucc] at hpre
    simp only [List.length_append, blk, List.length_cons] at hpre
    refine Runs.mono (block_run (B := B) (u := i) (Q := A + ℓ + 2)
        (b := bs[i]) hR h14 h13 h11 hW hfr
      hKS (blk_mem hM hib) (by omega) (by omega) (by simp only [List.length_append] at hem ⊢; omega)
      hin hnB) ?_
    rintro m'' s' ⟨hR', e14, e17, e13, e11, hW', hfr', hs'⟩
    rw [← emitAll_take_succ hib] at e11 hW' hfr'
    refine ⟨⟨i + 1, ⟨by omega, hR', e14, e17, ?_, e11, hW', hfr'⟩, ?_⟩, by rw [e14, h14]; omega⟩
    · rw [e13, hsucc]; simp [blk]; omega
    · rw [hsucc]; simp only [List.length_append, blk, List.length_cons]; omega
  · rintro m' s ⟨i, ⟨hi, hR, h14, h17, h13, h11, hW, hfr⟩, hs⟩ hne
    have hin : i = n := by
      by_contra h
      exact hne (by rw [h17, if_pos (by omega), hR.1.1.2.1])
    subst hin
    refine ⟨⟨hi, hR, h14, h17, h13, h11, hW, hfr⟩, ?_⟩
    rw [← hn, List.take_length] at hs; omega

/-! ### Copying the rest -/

/-- The state of the copy loop, after `k` cells. -/
def CopyInv (S ℓ A n P Q : ℕ) (t : List ℕ) (m₀ m : Mem) (k : ℕ) : Prop :=
  k ≤ t.length ∧ CvRegs S ℓ A n m ∧ m 25 = t.length ∧ m 19 = k ∧
    m 20 = (if k < t.length then 1 else 0) ∧ m 13 = P + k ∧ m 11 = Q + k ∧
    MemAt m Q (t.take k) ∧ ∀ a, 32 ≤ a → (a < Q ∨ Q + k ≤ a) → m a = m₀ a

/-- One cell. -/
theorem copy_step {B S ℓ A n P Q k : ℕ} {t : List ℕ} {m₀ m : Mem}
    (hI : CopyInv S ℓ A n P Q t m₀ m k) (hk : k < t.length) (hKS : nK ≤ S)
    (ht : m₀ (P + k) = t[k]) (hP : 32 ≤ P) (hPQ : P + t.length ≤ Q)
    (hB : Q + t.length + 2 < B) :
    Runs B copyBody m fun m' s => CopyInv S ℓ A n P Q t m₀ m' (k + 1) ∧ s ≤ 7 := by
  obtain ⟨-, hR, h25, h19, h20, h13, h11, hW, hfr⟩ := hI
  obtain ⟨⟨⟨r1, r3, r5⟩, r4, r8, r9, r16⟩, r10, r12, r15⟩ := id hR
  have hv : m (P + k) = t[k] := by rw [hfr _ (by omega) (.inl (by omega)), ht]
  rstep; rstep
  rename_i m₁ g₁ f₁ v₁
  rstep
  refine Runs.storeR (p := 11) (s := 21) (by omega) (by omega) ?_
  intro m₂ s₂ fr₂
  rw [f₁ 11 (by decide), h11, g₁, h13, hv] at s₂
  rw [f₁ 11 (by decide), h11] at fr₂
  have e3 : m₂ 3 = 1 := by rw [fr₂ 3 (by omega), f₁ 3 (by decide), r3]
  have e13 : m₂ 13 = P + k := by rw [fr₂ 13 (by omega), f₁ 13 (by decide), h13]
  have e11 : m₂ 11 = Q + k := by rw [fr₂ 11 (by omega), f₁ 11 (by decide), h11]
  have e19 : m₂ 19 = k := by rw [fr₂ 19 (by omega), f₁ 19 (by decide), h19]
  have e25 : m₂ 25 = t.length := by rw [fr₂ 25 (by omega), f₁ 25 (by decide), h25]
  rstep
  refine Runs.addV hKS (by decide) (by omega) (by omega) (by omega) (by rw [e13, e3]; omega) ?_
  intro m₃ g₃ f₃ v₃
  rstep
  refine Runs.addV hKS (by decide) (by omega) (by omega) (by omega)
    (by rw [f₃ 11 (by decide), f₃ 3 (by decide), e11, e3]; omega) ?_
  intro m₄ g₄ f₄ v₄
  rstep
  refine Runs.addV hKS (by decide) (by omega) (by omega) (by omega)
    (by rw [f₄ 19 (by decide), f₄ 3 (by decide), f₃ 19 (by decide), f₃ 3 (by decide), e19, e3]
        omega) ?_
  intro m₅ g₅ f₅ v₅
  rstep
  refine Runs.lessV hKS (by decide) (by omega) (by omega) (by omega) ?_
  intro m₆ g₆ f₆ v₆
  refine Runs.seqs_nilV hKS (by omega) ?_
  intro m₇ g₇ f₇ v₇
  have F : ∀ a, a ≠ 2 → a ≠ 20 → a ≠ 19 → a ≠ 11 → a ≠ 13 → m₇ a = m₂ a := fun a b c d e f => by
    rw [f₇ a b, f₆ a c, f₅ a d, f₄ a e, f₃ a f]
  have e19' : m₅ 19 = k + 1 := by
    rw [g₅, f₄ 19 (by decide), f₄ 3 (by decide), f₃ 19 (by decide), f₃ 3 (by decide), e19, e3]
  have htk : t.take (k + 1) = t.take k ++ [t[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
  have hlk : (t.take k).length = k := by simp; omega
  refine ⟨⟨by omega, CvRegs.of hR fun r a b c d e f g => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun a ha hc => ?_⟩, by omega⟩
  · rw [F r b (by omega) (by omega) e f, fr₂ r (by omega), f₁ r (by omega)]
  · rw [F 25 (by decide) (by decide) (by decide) (by decide) (by decide), e25]
  · rw [f₇ 19 (by decide), f₆ 19 (by decide), e19']
  · rw [f₇ 20 (by decide), g₆, e19', f₅ 25 (by decide), f₄ 25 (by decide), f₃ 25 (by decide), e25]
  · rw [f₇ 13 (by decide), f₆ 13 (by decide), f₅ 13 (by decide), f₄ 13 (by decide), g₃, e13, e3]
    omega
  · rw [f₇ 11 (by decide), f₆ 11 (by decide), f₅ 11 (by decide), g₄, f₃ 11 (by decide),
      f₃ 3 (by decide), e11, e3]
    omega
  · rw [htk]
    have h2 : MemAt m₂ Q (t.take k ++ [t[k]]) :=
      (hW.frame fun j hj => f₁ _ (by omega)).snoc (by rw [hlk]; exact s₂)
      (fun a ha => fr₂ a (by rw [hlk] at ha; exact ha))
    exact h2.frame fun j hj => by
      simp at hj
      exact F _ (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [F a (by omega) (by omega) (by omega) (by omega) (by omega), fr₂ a (by omega),
      f₁ a (by omega), hfr a ha (by omega)]

theorem copy_run {B S ℓ A n P Q : ℕ} {t : List ℕ} {m₀ m : Mem}
    (hI : CopyInv S ℓ A n P Q t m₀ m 0) (hKS : nK ≤ S) (ht : MemAt m₀ P t) (hP : 32 ≤ P)
    (hPQ : P + t.length ≤ Q) (hB : Q + t.length + 2 < B) :
    Runs B (loop 20 3 copyBody) m fun m' s => CopyInv S ℓ A n P Q t m₀ m' t.length ∧
      s ≤ 9 * t.length + 1 := by
  refine Runs.loop (fun m' s => ∃ k, CopyInv S ℓ A n P Q t m₀ m' k ∧ s ≤ 9 * k)
    (fun m' => t.length - m' 19) (by omega) (by omega) ?_ ?_ ⟨0, hI, by omega⟩
  · rintro m' s ⟨k, hI, hs⟩ heq
    have hk : k < t.length := by
      by_contra h
      rw [hI.2.2.2.2.1, if_neg h, hI.2.1.1.1.2.1] at heq
      exact absurd heq (by decide)
    refine Runs.mono (copy_step hI hk hKS (ht k hk) hP hPQ hB) fun m'' s' ⟨hI', hs'⟩ =>
      ⟨⟨k + 1, hI', by omega⟩, ?_⟩
    rw [hI'.2.2.2.1, hI.2.2.2.1]; omega
  · rintro m' s ⟨k, hI, hs⟩ hne
    have hk : k = t.length := by
      by_contra h
      exact hne (by rw [hI.2.2.2.2.1, if_pos (by have := hI.1; omega), hI.2.1.1.1.2.1])
    subst hk
    exact ⟨hI, by omega⟩

/-! ### The conversion -/

set_option maxHeartbeats 4000000 in
-- The proof steps through many memory updates at once.
/-- `conv` writes the edge-list code `n, E, pairs, t` at `A + ℓ` and points registers `9` and `4`
at it. -/
theorem conv_run {B S ℓ A n E : ℕ} {bs : List (List ℕ)} {t' : List ℕ} {m : Mem}
    (hR : CodeRegs S ℓ A m) (hKS : nK ≤ S) (hA : 32 ≤ A) (hn : bs.length = n)
    (hM : MemAt m A (n :: n :: (bs.flatMap blk ++ E :: t')))
    (hℓ : ℓ = 2 + (bs.flatMap blk).length + (t'.length + 1)) (ht' : t'.length = E + 1)
    (hE : (emitAll bs 0).length = 2 * E) (hB : A + ℓ + 3 * E + 8 < B) (hnB : n < B) :
    Runs B conv m fun m' k => CodeRegs S (3 * E + 4) (A + ℓ) m' ∧
      MemAt m' (A + ℓ) (n :: E :: (emitAll bs 0 ++ E :: t')) ∧
      (∀ a, 32 ≤ a → (a < A + ℓ ∨ A + ℓ + (3 * E + 4) ≤ a) → m' a = m a) ∧
      k ≤ 20 * ℓ + 40 := by
  obtain ⟨⟨r1, r3, r5⟩, r4, r8, r9, r16⟩ := id hR
  have hn0 : m A = n := hM.head
  have hP := tail_mem hM
  have bR : ∀ r, r < 33 → r < B := fun r hr => by omega
  have bA1 : A + ℓ + 1 < B := by omega
  have bE2 : E + 2 < B := by omega
  have bE4 : E + 1 + 1 + (E + 1 + 1) < B := by omega
  have bE6 : 3 * E + 6 < B := by omega
  have hQ : A + ℓ + 2 + (emitAll bs 0).length + (E + 1 + 1) = A + ℓ + (3 * E + 4) := by omega
  rstep; rstep
  rename_i m₁ g₁ f₁ v₁
  rstep; rstep
  rename_i m₂ g₂ f₂ v₂
  rstep; rstep
  rename_i m₃ g₃ f₃ v₃
  rstep; rstep
  rename_i m₄ g₄ f₄ v₄
  rstep; rstep
  rename_i m₅ g₅ f₅ v₅
  rstep; rstep
  rename_i m₆ g₆ f₆ v₆
  rstep; rstep
  rename_i m₇ g₇ f₇ v₇
  have F5 : ∀ a, a ≠ 10 → a ≠ 12 → a ≠ 11 → a ≠ 13 → a ≠ 14 → m₅ a = m a :=
    fun a h10 h12 h11 h13 h14 => by rw [f₅ a h14, f₄ a h13, f₃ a h11, f₂ a h12, f₁ a h10]
  have F7 : ∀ a, a ≠ 10 → a ≠ 12 → a ≠ 11 → a ≠ 13 → a ≠ 14 → a ≠ 15 → a ≠ 17 → m₇ a = m a :=
    fun a h10 h12 h11 h13 h14 h15 h17 => by rw [f₇ a h17, f₆ a h15, F5 a h10 h12 h11 h13 h14]
  have e15 : m₆ 15 = n := by
    rw [g₆, F5 9 (by decide) (by decide) (by decide) (by decide) (by decide), r9,
      F5 A (by omega) (by omega) (by omega) (by omega) (by omega), hn0]
  have e14 : m₆ 14 = 0 := by rw [f₆ 14 (by decide), g₅]
  have R7 : CodeRegs S ℓ A m₇ := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
      rw [F7 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)] <;>
      assumption
  have hI0 : OuterInv S ℓ A n bs m m₇ 0 := by
    refine ⟨by omega, ⟨R7, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun j hj => ?_, fun a ha _ => ?_⟩
    · rw [f₇ 10 (by decide), f₆ 10 (by decide), f₅ 10 (by decide), f₄ 10 (by decide),
        f₃ 10 (by decide), f₂ 10 (by decide), g₁, r9, r4]
    · rw [f₇ 12 (by decide), f₆ 12 (by decide), f₅ 12 (by decide), f₄ 12 (by decide),
        f₃ 12 (by decide), g₂]
    · rw [f₇ 15 (by decide), e15]
    · rw [f₇ 14 (by decide), e14]
    · rw [g₇, e14, e15]
    · simp only [List.take_zero, List.flatMap_nil, List.length_nil, Nat.add_zero]
      rw [f₇ 13 (by decide), f₆ 13 (by decide), f₅ 13 (by decide), g₄, f₃ 9 (by decide),
        f₃ 12 (by decide), f₂ 9 (by decide), g₂, f₁ 9 (by decide), r9]
    · simp only [List.take_zero, emitAll, List.length_nil, Nat.add_zero]
      rw [f₇ 11 (by decide), f₆ 11 (by decide), f₅ 11 (by decide), f₄ 11 (by decide), g₃,
        f₂ 10 (by decide), g₂, g₁, r9, r4]
    · simp [emitAll] at hj
    · exact F7 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  clear g₁ g₂ g₃ g₄ g₅ g₆ g₇ f₁ f₂ f₃ f₄ f₅ f₆ f₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇ F5 e14 e15 R7
  rstep
  refine Runs.mono (outer_run (t := E :: t') hI0 hn hKS hA hM
    (by simp only [List.length_cons]; omega) (by omega) hnB) ?_
  rintro m₈ s₈ ⟨⟨-, hR8, -, -, h13, h11, hW8, hfr8⟩, hs8⟩
  rw [List.take_of_length_le (by omega)] at h13 h11 hW8 hfr8
  obtain ⟨⟨⟨q1, q3, q5⟩, q4, q8, q9, q16⟩, q10, q12, q15⟩ := id hR8
  have hs8' : s₈ ≤ 20 * (bs.flatMap blk).length + 1 := hs8
  clear hR hI0 r1 r3 r5 r4 r8 r9 r16 hn0 hM hs8
  rstep
  refine Runs.storeR (p := 10) (s := 15) (bR _ (by decide)) (bR _ (by decide)) ?_
  intro m₉ s₉ fr₉
  rw [q10, q15] at s₉
  rw [q10] at fr₉
  rstep
  refine Runs.loadV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) ?_
  intro m₁₀ g₁₀ f₁₀ v₁₀
  have e23 : m₁₀ 23 = E := by
    rw [g₁₀, fr₉ 13 (by omega), h13, fr₉ _ (by omega), hfr8 _ (by omega) (.inl (by omega)),
      hP.head]
  clear g₁₀ v₁₀
  rstep
  refine Runs.addV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) (bR _ (by decide))
    (by rw [f₁₀ 10 (by decide), f₁₀ 3 (by decide), fr₉ 10 (by omega), fr₉ 3 (by omega), q10, q3]
        exact bA1) ?_
  intro m₁₁ g₁₁ f₁₁ v₁₁
  have e24 : m₁₁ 24 = A + ℓ + 1 := by
    rw [g₁₁, f₁₀ 10 (by decide), f₁₀ 3 (by decide), fr₉ 10 (by omega), fr₉ 3 (by omega), q10, q3]
  clear g₁₁ v₁₁
  rstep
  refine Runs.storeR (p := 24) (s := 23) (bR _ (by decide)) (bR _ (by decide)) ?_
  intro m₁₂ s₁₂ fr₁₂
  rw [e24, f₁₁ 23 (by decide), e23] at s₁₂
  rw [e24] at fr₁₂
  have e12 : m₁₂ 12 = 2 := by
    rw [fr₁₂ 12 (by omega), f₁₁ 12 (by decide), f₁₀ 12 (by decide), fr₉ 12 (by omega), q12]
  have e23' : m₁₂ 23 = E := by rw [fr₁₂ 23 (by omega), f₁₁ 23 (by decide), e23]
  rstep
  refine Runs.addV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) (bR _ (by decide))
    (by rw [e23', e12]; exact bE2) ?_
  intro m₁₃ g₁₃ f₁₃ v₁₃
  have e25' : m₁₃ 25 = E + 2 := by rw [g₁₃, e23', e12]
  clear g₁₃ v₁₃ e23 e24 e23'
  rstep
  refine Runs.constV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) ?_
  intro m₁₄ g₁₄ f₁₄ v₁₄
  rstep
  refine Runs.lessV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) (bR _ (by decide)) ?_
  intro m₁₅ g₁₅ f₁₅ v₁₅
  have G' : ∀ a, a ≠ 20 → a ≠ 19 → a ≠ 25 → a ≠ A + ℓ + 1 → a ≠ 24 → a ≠ 23 → m₁₅ a = m₉ a :=
    fun a h20 h19 h25 hl1 h24 h23 => by
      rw [f₁₅ a h20, f₁₄ a h19, f₁₃ a h25, fr₁₂ a hl1, f₁₁ a h24, f₁₀ a h23]
  have G : ∀ a, a ≠ 20 → a ≠ 19 → a ≠ 25 → a ≠ A + ℓ + 1 → a ≠ 24 → a ≠ 23 → a ≠ A + ℓ →
      m₁₅ a = m₈ a := fun a h20 h19 h25 hl1 h24 h23 hl => by
    rw [G' a h20 h19 h25 hl1 h24 h23, fr₉ a hl]
  have e25 : m₁₄ 25 = E + 2 := by rw [f₁₄ 25 (by decide), e25']
  have hC0 : CopyInv S ℓ A n (A + 2 + (bs.flatMap blk).length)
      (A + ℓ + 2 + (emitAll bs 0).length) (E :: t') m₁₅ m₁₅ 0 := by
    refine ⟨by omega, CvRegs.of hR8 fun r a b c d e f g => G r (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), ?_, ?_, ?_, ?_, ?_, fun j hj => ?_,
      fun a _ _ => rfl⟩
    · rw [f₁₅ 25 (by decide), e25]; simp [ht']
    · rw [f₁₅ 19 (by decide), g₁₄]
    · rw [g₁₅, g₁₄, e25]; simp
    · rw [G 13 (by decide) (by decide) (by decide) (by omega) (by decide) (by decide) (by omega),
        h13]; rfl
    · rw [G 11 (by decide) (by decide) (by decide) (by omega) (by decide) (by decide) (by omega),
        h11]; rfl
    · simp at hj
  have hPt : MemAt m₁₅ (A + 2 + (bs.flatMap blk).length) (E :: t') := hP.frame fun j hj => by
    simp only [List.length_cons] at hj
    rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      hfr8 _ (by omega) (.inl (by omega))]
  clear f₁₀ f₁₁ v₁₄ v₁₅ g₁₄ g₁₅ e25 e25' hP hR8 q1 q3 q5 q4 q8 q9 q16 q10 q12 q15 h13 h11
  rstep
  refine Runs.mono (copy_run hC0 hKS hPt (by omega) (by simp only [List.length_cons]; omega)
    (by simp only [List.length_cons]; omega)) ?_
  rintro m₁₆ s₁₆ ⟨⟨-, hR16, c25, -, -, -, -, hW16, hfr16⟩, hs16⟩
  rw [List.take_length] at hW16
  simp only [List.length_cons, ht'] at c25 hfr16 hs16
  obtain ⟨⟨⟨p1, p3, p5⟩, p4, p8, p9, p16⟩, p10, p12, p15⟩ := id hR16
  rstep
  refine Runs.copyV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) ?_
  intro m₁₇ g₁₇ f₁₇ v₁₇
  rstep
  refine Runs.addV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) (bR _ (by decide))
    (by rw [f₁₇ 25 (by decide), c25]; exact bE4) ?_
  intro m₁₈ g₁₈ f₁₈ v₁₈
  rstep
  refine Runs.addV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) (bR _ (by decide))
    (by rw [g₁₈, f₁₈ 25 (by decide), f₁₇ 25 (by decide), c25]; omega) ?_
  intro m₁₉ g₁₉ f₁₉ v₁₉
  have e4 : m₁₉ 4 = 3 * E + 6 := by
    rw [g₁₉, g₁₈, f₁₈ 25 (by decide), f₁₇ 25 (by decide), c25]; omega
  have e12' : m₁₉ 12 = 2 := by rw [f₁₉ 12 (by decide), f₁₈ 12 (by decide), f₁₇ 12 (by decide), p12]
  rstep
  refine Runs.subV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) (bR _ (by decide))
    (by rw [e4, e12']; omega) ?_
  intro m₂₀ g₂₀ f₂₀ v₂₀
  refine Runs.seqs_nilV hKS (bR _ (by decide)) ?_
  intro m₂₁ g₂₁ f₂₁ v₂₁
  have H : ∀ a, a ≠ 2 → a ≠ 4 → a ≠ 9 → m₂₁ a = m₁₆ a := fun a h2 h4 h9 => by
    rw [f₂₁ a h2, f₂₀ a h4, f₁₉ a h4, f₁₈ a h4, f₁₇ a h9]
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, fun a ha hc => ?_, ?_⟩
  · rw [H _ (by omega) (by omega) (by omega)]; exact p1
  · rw [H _ (by omega) (by omega) (by omega)]; exact p3
  · rw [H _ (by omega) (by omega) (by omega)]; exact p5
  · rw [f₂₁ 4 (by decide), g₂₀, e4, e12']; omega
  · rw [H _ (by omega) (by omega) (by omega)]; exact p8
  · rw [f₂₁ 9 (by decide), f₂₀ 9 (by decide), f₁₉ 9 (by decide), f₁₈ 9 (by decide), g₁₇, p10]
  · rw [H _ (by omega) (by omega) (by omega)]; exact p16
  · have h0 : m₁₆ (A + ℓ) = n := by
      rw [hfr16 _ (by omega) (.inl (by omega)), G' _ (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), s₉]
    have h1 : m₁₆ (A + ℓ + 1) = E := by
      rw [hfr16 _ (by omega) (.inl (by omega)), f₁₅ _ (by omega), f₁₄ _ (by omega),
        f₁₃ _ (by omega), s₁₂]
    have hEm : MemAt m₁₆ (A + ℓ + 1 + 1) (emitAll bs 0) := fun j hj => by
      rw [show A + ℓ + 1 + 1 + j = A + ℓ + 2 + j by omega, hfr16 _ (by omega) (.inl (by omega)),
        G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hW8 j hj
    have hT : MemAt m₁₆ (A + ℓ + 1 + 1 + (emitAll bs 0).length) (E :: t') := by
      rw [show A + ℓ + 1 + 1 + (emitAll bs 0).length = A + ℓ + 2 + (emitAll bs 0).length by omega]
      exact hW16
    have hall : MemAt m₁₆ (A + ℓ) (n :: E :: (emitAll bs 0 ++ E :: t')) :=
      MemAt.cons h0 (MemAt.cons h1 (MemAt.append hEm hT))
    exact hall.frame fun j hj => H _ (by omega) (by omega) (by omega)
  · rw [H a (by omega) (by omega) (by omega), hfr16 a ha (by omega),
      G a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      hfr8 a ha (by omega)]
  · omega

end Formalgo.Algorithms.ShortestPaths
