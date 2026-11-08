import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunInit
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunConv

/-!
# The pieces of the core

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {m : Mem} {B : ℕ} {x : EInput}

theorem edgesAt_of {α : Type*} (f g h : α → ℕ) : ∀ (l : List α) (p q : ℕ),
    MemAt m p (l.flatMap fun e => [f e, g e]) → MemAt m q (l.map h) →
    EdgesAt m p q (l.map fun e => (f e, g e, h e))
  | [], _, _, _, _ => trivial
  | e :: l, p, q, h1, h2 => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append] at h1
    simp only [List.map_cons] at h2 ⊢
    exact ⟨h1.head, h1.tail.head, h2.head, edgesAt_of f g h l _ _ h1.tail.tail h2.tail⟩

/-- The edges of the input, with their weights. -/
noncomputable def triX (x : EInput) : List (ℕ × ℕ × ℕ) :=
  (lexEdges x.wg.graph).map fun e => ((e.1 : ℕ), (e.2 : ℕ), x.wg.weight s(e.1, e.2))

theorem flatMap_triX (x : EInput) : (triX x).flatMap hfN = halves x := by
  simp only [triX, halves, List.flatMap_map, hfN]

theorem adjL_halves (x : EInput) (v : ℕ) : adjL ((triX x).flatMap hfN) v = adjX x v := by
  rw [flatMap_triX]; rfl

theorem length_triX (x : EInput) : (triX x).length = numEdges x := by simp [triX, numEdges]

theorem triX_bound (x : EInput) : ∀ t ∈ triX x, t.1 + 1 ≤ x.wg.n ∧ t.2.1 + 1 ≤ x.wg.n := by
  intro t ht
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 ht
  exact ⟨e.1.2, e.2.2⟩

/-- The input code, in parts. -/
theorem memAt_input {A : ℕ} (h : MemAt m A (ncode x)) :
    m A = x.wg.n ∧ m (A + 1) = numEdges x ∧
      EdgesAt m (A + 2) (A + 2 * numEdges x + 3) (triX x) ∧
      m (A + 3 * numEdges x + 3) = x.source := by
  rw [ncode_input_eq] at h
  have hp : ∀ l : List (ℕ × ℕ), (l.flatMap fun p => [p.1, p.2]).length = 2 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons p l ih => simp [List.flatMap_cons, ih]; omega
  have hE : (edgesNat x.wg.graph).length = numEdges x := by simp [edgesNat, numEdges]
  have hl1 : ([x.wg.n, numEdges x] ++
      (edgesNat x.wg.graph).flatMap fun p => [p.1, p.2]).length = 2 + 2 * numEdges x := by
    rw [List.length_append, hp, hE]; rfl
  have hw : ((lexEdges x.wg.graph).map fun e => x.wg.weight s(e.1, e.2)).length =
      numEdges x := by simp [numEdges]
  have a2 := h.left.left.left.left
  have a3 := h.left.left.left.right
  have a4 := h.left.right
  have a5 := h.right
  simp only [List.length_append, List.length_cons, List.length_nil, hp, hE, hw] at a3 a4 a5
  have e4 : A + (0 + 1 + 1 + 2 * numEdges x + (0 + 1)) = A + 2 * numEdges x + 3 := by omega
  have e5 : A + (0 + 1 + 1 + 2 * numEdges x + (0 + 1) + numEdges x) =
      A + 3 * numEdges x + 3 := by omega
  rw [e4] at a4
  rw [e5] at a5
  have a3' : MemAt m (A + 2) ((lexEdges x.wg.graph).flatMap
      fun e => [(e.1 : ℕ), (e.2 : ℕ)]) := by
    have e : ((edgesNat x.wg.graph).flatMap fun p => [p.1, p.2]) =
        (lexEdges x.wg.graph).flatMap fun e => [(e.1 : ℕ), (e.2 : ℕ)] := by
      simp only [edgesNat, List.flatMap_map]
    rw [← e]; exact a3
  exact ⟨a2.head, a2.tail.head, edgesAt_of _ _ _ _ _ _ a3' a4, a5.head⟩

theorem EdgesAt.frame {m' : Mem} (hm : ∀ a, 32 ≤ a → m' a = m a) :
    ∀ (l : List (ℕ × ℕ × ℕ)) (p q : ℕ), 32 ≤ p → 32 ≤ q → EdgesAt m p q l → EdgesAt m' p q l
  | [], _, _, _, _, _ => trivial
  | (u, v, w) :: l, p, q, hp, hq, ⟨h1, h2, h3, h4⟩ => by
    refine ⟨by rw [hm p hp]; exact h1, by rw [hm _ (by omega)]; exact h2,
      by rw [hm q hq]; exact h3, EdgesAt.frame hm l _ _ (by omega) (by omega) h4⟩

/-- The main loop, whether or not the source is a vertex. -/
theorem finish_run {src : ℕ} (hLn : L.n = x.wg.n) (hLD : L.D = Dn x.wg.n)
    (hKB : (x.wg.n + 1) * codeMax (ncode x) < B) (hB : L.top < B)
    (hR : Rep L (start (ctxX x) src) m) (hF : Fixed L x m)
    (h12 : m 12 = if 0 < (start (ctxX x) src).deg 0 then 1 else 0) :
    Runs B (loop 12 3 mainBody) m fun m' k => Rep L (finish (ctxX x) src) m' ∧ Fixed L x m' ∧
      Frm L TW m m' ∧ k ≤ (finish (ctxX x) src).time + 1 := by
  have ht := top_ge (L := L)
  have hH := hR.H32
  by_cases hs : src < x.wg.n
  · refine Runs.mono (main_run (ctxOK x) (adjOK x) hLn hLD rfl (DInv.start (adjOK x) hs) hKB hB hR
      hF h12) fun m' k ⟨R', X', F', hk⟩ => ⟨R', X', F', ?_⟩
    have : (whileF rootsCond (mainStep (ctxX x)) (ctxX x).F (start (ctxX x) src)).time =
      (finish (ctxX x) src).time := rfl
    omega
  · have hn : (ctxX x).n ≤ src := by change x.wg.n ≤ src; omega
    have hb : finish (ctxX x) src = blank := finish_invalid hn
    have hst : start (ctxX x) src = blank := by simp only [start, if_neg (by omega : ¬src < (ctxX x).n)]
    rw [hb]
    rw [hst] at hR h12
    have hne : m 12 ≠ m 3 := by
      rw [h12, hR.one]; simp [blank]
    exact ⟨m, 1, .loopFalse (by omega) (by omega) hne, hR, hF, Frm.refl, by simp [blank]⟩

/-- The time of the model. -/
theorem finish_time (x : EInput) (src : ℕ) :
    (finish (ctxX x) src).time ≤ 65 + x.wg.n * perVertex (ctxX x) + 650 * numEdges x := by
  by_cases hs : src < x.wg.n
  · have h := (finish_spec (ctxOK x) (adjOK x) hs).2.2.2
    have h2 := sum_adjX x
    have : ∑ v ∈ Finset.range (x.wg.n + 1), ((ctxX x).adj v).length = 2 * numEdges x := h2
    rw [this] at h
    omega
  · rw [finish_invalid (show (ctxX x).n ≤ src by change x.wg.n ≤ src; omega)]
    simp [blank]

/-- The layout for an input at `A`. -/
noncomputable def layOf (x : EInput) (A : ℕ) : Lay :=
  ⟨x.wg.n, Dn x.wg.n, numEdges x, A + (ncode x).length⟩

/-- The registers fixed throughout a code program. -/
def Fx (r : ℕ) : Prop := r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 8 ∨ r = 9 ∨ r = 16

theorem Fx.keep {r : ℕ} (h : Fx r) : r < 32 ∧ r ≠ 2 ∧ r ≠ 11 ∧ r ≠ 12 ∧ ¬TS r ∧ ¬BT r ∧ ¬TB r ∧
    ¬TI r ∧ ¬TW r ∧ ¬TO r := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [TS, BT, TB, TI, TW, TO, TE, TT, TP, TM, TL, TR, TD, TC, TU, T29, T267]

theorem not_dyn {a : ℕ} (h : a < L.H) : ¬L.Dyn a := fun hd => by
  have hCH := CH_ge (L := L)
  unfold Lay.Dyn at hd
  omega

theorem core_run {S A : ℕ} (hR : CodeRegs S (ncode x).length A m) (hA : 32 ≤ A)
    (hTop : (layOf x A).top < B) (hKB : (x.wg.n + 1) * codeMax (ncode x) < B)
    (hk : ∀ v, 1 ≤ v → v ≤ x.wg.n → (finish (ctxX x) x.source).stat v = 2 →
      (finish (ctxX x) x.source).key v + 1 < B)
    (hM : MemAt m A (ncode x)) (hz : ∀ a, A + (ncode x).length ≤ a → m a = 0) :
    Runs B Prog.core m fun m' k => CodeRegs S (ncode x).length A m' ∧
      m' 10 = (layOf x A).H + 9 * (layOf x A).R ∧ m' 17 = x.wg.n + 1 ∧
      m' ((layOf x A).H + 9 * (layOf x A).R) = x.wg.n ∧
      (∀ v, 1 ≤ v → v ≤ x.wg.n → m' ((layOf x A).H + 9 * (layOf x A).R + v) =
        outVal (finish (ctxX x) x.source) v) ∧
      (∀ a, 32 ≤ a → a < (layOf x A).H → m' a = m a) ∧
      k ≤ 6 * Nat.size x.wg.n + 33 * numEdges x + 25 * x.wg.n +
        (finish (ctxX x) x.source).time + 120 := by
  obtain ⟨⟨r1, r3, r5⟩, r4, r8, r9, r16⟩ := id hR
  obtain ⟨c0, c1, cE, cs⟩ := memAt_input hM
  have hlen := length_ncode_input x
  have hLH : (layOf x A).H = A + (ncode x).length := rfl
  have hHZ : A + 3 * numEdges x + 3 < (layOf x A).H := by omega
  generalize hL : layOf x A = L at *
  have hLn : L.n = x.wg.n := by rw [← hL]; rfl
  have hLD : L.D = Dn x.wg.n := by rw [← hL]; rfl
  have hLE : L.E = numEdges x := by rw [← hL]; rfl
  have hLD' : L.D = 2 * Nat.size x.wg.n := hLD
  have H32 : 32 ≤ L.H := by omega
  have hRn : L.n + L.D + 3 = L.R := rfl
  have ht := top_ge (L := L)
  have rB : ∀ {r}, r < 32 → r < B := fun h => by omega
  have H7ge : ∀ v, L.H ≤ H7 L + v := fun v => by unfold H7; omega
  have hH8 : ∀ {a}, a < L.H → a < H8 L := fun h => by unfold H8; omega
  have hRpos : 0 < L.R := by omega
  clear ht hRn
  unfold Prog.core
  refine Runs.seqs_cons (Runs.mono (setup_run (n := x.wg.n) (E := numEdges x) hLn hLD' hLH hA r4
    r8 r9 r16 r3 c0 c1 hz hTop) fun m₁ c₁ ⟨P₁, e11, e13, hi₁, lo₁, hc₁⟩ => ?_)
  have h9₁ : m₁ 9 = A := by
    rw [lo₁ 9 (by decide) (Fx.keep (r := 9) (by simp [Fx])).2.2.2.2.1, r9]
  refine Runs.seqs_cons (Runs.mono (build_run (tri := triX x) (length_triX x) hLE hA (by omega)
    (fun t ht => by rw [hLn]; exact triX_bound x t ht) P₁ h9₁ e11 e13
    (EdgesAt.frame hi₁ _ _ _ (by omega) (by omega) cE)
    (fun v _ => by
      have h1 := H7ge v
      rw [hi₁ _ (by omega), hz _ (by omega)]) hTop)
    fun m₂ c₂ ⟨P₂, f13, f17, hL₂, lo₂, hi₂, hc₂⟩ => ?_)
  refine Runs.seqs_cons (Runs.mono (cbInit_run P₂ f13 hL₂ hTop)
    fun m₃ c₃ ⟨P₃, cb₃, hL₃, lo₃, hi₃, hc₃⟩ => ?_)
  have X₃ : Fixed L x m₃ := ⟨fun v hv => by
    have := hL₃ v hv; rw [adjL_halves] at this; exact this, cb₃⟩
  have e17 : m₃ 17 = A + 3 * numEdges x + 3 := by
    rw [lo₃ 17 (by decide) (by simp [TB]), f17]
  have eZ : m₃ (A + 3 * numEdges x + 3) = x.source := by
    rw [hi₃ _ (by omega) (.inl (hH8 hHZ)), hi₂ _ (by omega) hHZ, hi₁ _ (by omega), cs]
  refine Runs.seqs_cons (Runs.mono (source_run (C := ctxX x) P₃ X₃ e17 eZ hLn hTop)
    fun m₄ c₄ ⟨R₄, X₄, F₄, hc₄⟩ => ?_)
  -- The test of the main loop.
  refine Runs.seqs_cons (Runs.loadR (rB (by decide)) (rB (by decide)) fun m₅ g₅ f₅ => ?_)
  have a21 : m₄ 21 = L.H + 3 * L.R := R₄.base 3 (by decide)
  have d₅ : m₅ 11 = (start (ctxX x) x.source).deg 0 := by
    rw [g₅, a21]; exact R₄.arr 3 (by decide) 0 (Nat.zero_le _)
  have R₅ := R₄.regs1 (r := 11) (by simp [Tmp]) (by decide) f₅
  refine Runs.seqs_cons (Runs.lessR (rB (by decide)) (rB (by decide)) (rB (by decide))
    fun m₆ g₆ f₆ => ?_)
  have R₆ := R₅.regs1 (r := 12) (by simp [Tmp]) (by decide) f₆
  have h12 : m₆ 12 = if 0 < (start (ctxX x) x.source).deg 0 then 1 else 0 := by
    rw [g₆, R₅.zero, d₅]
  have X₆ : Fixed L x m₆ := X₄.frame H32 fun a ha _ => by
    rw [f₆ a (by omega), f₅ a (by omega)]
  -- The main loop and the output.
  refine Runs.seqs_cons (Runs.mono (finish_run hLn hLD hKB hTop R₆ X₆ h12)
    fun m₇ c₇ ⟨R₇, X₇, F₇, hc₇⟩ => ?_)
  refine Runs.seqs_cons (Runs.mono (output_run R₇ (fun v h1 h2 hs => hk v h1 (by omega) hs) hTop)
    fun m₈ c₈ ⟨R₈, a17, a0, aO, alo, ahi, hc₈⟩ => ?_)
  refine Runs.seqs_nilR (rB (by decide)) fun m₉ g₉ f₉ => ?_
  have keep : ∀ {r}, Fx r → m₉ r = m r := fun {r} h => by
    obtain ⟨l32, a2, a11, a12, b1, b2, b3, b4, b5, b6⟩ := Fx.keep h
    rw [f₉ r a2, alo r l32 b6, F₇.1 r l32 b5, f₆ r a12, f₅ r a11, F₄.1 r l32 b4, lo₃ r l32 b3,
      lo₂ r (by omega) b2, lo₁ r l32 b1]
  have b10 : m₈ 10 = L.H + 9 * L.R := R₈.base 9 (by decide)
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, fun v h1 h2 => ?_, fun a h1 h2 => ?_, ?_⟩
  · rw [keep (by simp [Fx])]; exact r1
  · rw [keep (by simp [Fx])]; exact r3
  · rw [keep (by simp [Fx])]; exact r5
  · rw [keep (by simp [Fx])]; exact r4
  · rw [keep (by simp [Fx])]; exact r8
  · rw [keep (by simp [Fx])]; exact r9
  · rw [keep (by simp [Fx])]; exact r16
  · rw [f₉ 10 (by decide), b10]
  · rw [f₉ 17 (by decide), a17, hLn]
  · rw [f₉ _ (by omega), a0, hLn]
  · rw [f₉ _ (by omega), aO v h1 (by omega)]
  · have ne : ¬L.Dyn a := not_dyn h2
    rw [f₉ a (by omega), ahi a h1 (.inl (by omega)), F₇.2 a h1 ne, f₆ a (by omega),
      f₅ a (by omega), F₄.2 a h1 ne, hi₃ a h1 (.inl (hH8 h2)), hi₂ a h1 h2, hi₁ a h1]
  · rw [hLn] at hc₃ hc₈
    omega

end Formalgo.Algorithms.ShortestPaths
