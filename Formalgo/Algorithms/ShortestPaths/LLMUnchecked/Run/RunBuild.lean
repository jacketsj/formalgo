import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunSetup

/-!
# Running the construction of the adjacency lists

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {m m' : Mem} {B : ℕ}

/-- `Lst`, with all the half-edges below `P`. -/
def LstB (L : Lay) (m : Mem) (P : ℕ) : ℕ → List (ℕ × ℕ) → Prop
  | h, [] => h = 0
  | h, (v, w) :: l => L.HE ≤ h ∧ h + 3 ≤ P ∧ m (h + 1) = v ∧ m (h + 2) = w ∧ LstB L m P (m h) l

theorem LstB.frame {P P' : ℕ} (hP : P ≤ P') (hm : ∀ a, L.HE ≤ a → a < P → m' a = m a) :
    ∀ (l : List (ℕ × ℕ)) (h : ℕ), LstB L m P h l → LstB L m' P' h l
  | [], h, hl => hl
  | (v, w) :: l, h, ⟨h1, h2, h3, h4, h5⟩ => by
    refine ⟨h1, by omega, by rw [hm _ (by omega) (by omega)]; exact h3,
      by rw [hm _ (by omega) (by omega)]; exact h4, ?_⟩
    rw [hm h h1 (by omega)]
    exact LstB.frame hP hm l _ h5

theorem LstB.toLst {P : ℕ} (hP : P ≤ L.CH) :
    ∀ (l : List (ℕ × ℕ)) (h : ℕ), LstB L m P h l → Lst L m h l
  | [], h, hl => hl
  | (v, w) :: l, h, ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, by omega, h3, h4, LstB.toLst hP l _ h5⟩

/-- The heads of the adjacency lists. -/
def H7 (L : Lay) : ℕ := L.H + 7 * L.R

/-- Add a half-edge from `M[ra]` to `M[rb]` of weight `M[14]` at `M[13]`, at the front of its
list. -/
theorem half_spec (tail : List Cmd) {ra rb p a : ℕ} (hP : Pre L m) (h13 : m 13 = p)
    (hra : m ra = a) (ha : a ≤ L.n) (hra32 : ra < 32) (hrb32 : rb < 32) (ra2 : ra ≠ 2)
    (ra15 : ra ≠ 15) (rb2 : rb ≠ 2) (rb15 : rb ≠ 15) (hp : L.HE ≤ p)
    (hp3 : p + 3 ≤ L.CH) (hB : L.top < B) {Q : Mem → ℕ → Prop}
    (hQ : ∀ m', m' 13 = p + 3 → m' p = m (H7 L + a) → m' (p + 1) = m rb → m' (p + 2) = m 14 →
      m' (H7 L + a) = p →
      (∀ x, x ≠ 2 → x ≠ 13 → x ≠ 15 → x ≠ p → x ≠ p + 1 → x ≠ p + 2 → x ≠ H7 L + a → m' x = m x) →
      Runs B (seqs tail) m' fun m'' k => Q m'' (k + 10)) :
    Runs B (seqs
        (rd 15 7 ra :: store 13 15 :: add 2 13 3 :: store 2 rb :: add 2 2 3 :: store 2 14 ::
      wr 7 ra 13 :: add 13 13 16 :: tail)) m Q := by
  have h25 : m 25 = H7 L := hP.base 7 (by omega)
  have o3 : m 3 = 1 := hP.one
  have o16 : m 16 = 3 := hP.three
  have br : breg 7 = 25 := rfl
  -- All the arithmetic, in a small context.
  obtain ⟨rB, A3, AB, pB, n0, n1, n2, nA, l0, l1, l2, lA, pA, p1A, p2A⟩ :
      (∀ {r}, r < 32 → r < B) ∧ H7 L + a + 3 ≤ p ∧ H7 L + a < B ∧ p + 3 < B ∧ p ≠ 2 ∧ p + 1 ≠ 2 ∧
        p + 2 ≠ 2 ∧ H7 L + a ≠ 2 ∧ (∀ {x}, x < 32 → x ≠ p) ∧ (∀ {x}, x < 32 → x ≠ p + 1) ∧
        (∀ {x}, x < 32 → x ≠ p + 2) ∧ (∀ {x}, x < 32 → x ≠ H7 L + a) ∧ p ≠ H7 L + a ∧
        p + 1 ≠ H7 L + a ∧ p + 2 ≠ H7 L + a := by
    have hH := hP.H32
    have ht := top_ge (L := L)
    have hCH := CH_ge (L := L)
    have hCT : L.CH ≤ L.top := by unfold Lay.top; omega
    have hRn : L.n + L.D + 3 = L.R := rfl
    have hHE : L.HE = L.H + 10 * L.R := rfl
    unfold H7
    refine ⟨fun h => by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => by omega, fun h => by omega,
      fun h => by omega, fun h => by omega, ?_, ?_, ?_⟩ <;> omega
  clear hp hp3 hP ha
  have y1 : p + 1 ≠ p := by omega
  have y2 : p + 2 ≠ p := by omega
  have y3 : p + 2 ≠ p + 1 := by omega
  refine Runs.seqs_cons (Runs.seq (Runs.addR (rB (by decide)) (by rw [br]; exact rB (by decide))
    (rB hra32) (by rw [br, h25, hra]; exact AB) fun m₁ g₁ f₁ => Runs.loadR (rB (by decide))
    (rB (by decide)) fun m₂ g₂ f₂ => ?_))
  rw [br, h25, hra] at g₁
  rw [g₁, f₁ _ nA] at g₂
  have e₂ : ∀ x, x ≠ 2 → x ≠ 15 → m₂ x = m x := fun x a b => by rw [f₂ x b, f₁ x a]
  have p13 : m₂ 13 = p := by rw [e₂ 13 (by decide) (by decide), h13]
  -- The next pointer.
  refine Runs.seqs_cons (Runs.storeR (rB (by decide)) (rB (by decide)) fun m₃ g₃ f₃ => ?_)
  rw [p13] at g₃ f₃
  rw [g₂] at g₃
  have e₃ : ∀ x, x ≠ 2 → x ≠ 15 → x ≠ p → m₃ x = m x := fun x a b c => by
    rw [f₃ x c, e₂ x a b]
  have v13 : m₃ 13 = p := by rw [e₃ 13 (by decide) (by decide) (l0 (by decide)), h13]
  have v3 : m₃ 3 = 1 := by rw [e₃ 3 (by decide) (by decide) (l0 (by decide)), o3]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [v13, v3]; exact lt_of_le_of_lt (by omega) pB) fun m₄ g₄ f₄ => ?_)
  rw [v13, v3] at g₄
  -- The target.
  refine Runs.seqs_cons (Runs.storeR (rB (by decide)) (rB hrb32) fun m₅ g₅ f₅ => ?_)
  rw [g₄] at g₅ f₅
  have e₅ : ∀ x, x ≠ 2 → x ≠ 15 → x ≠ p → x ≠ p + 1 → m₅ x = m x := fun x a b c d => by
    rw [f₅ x d, f₄ x a, e₃ x a b c]
  have w2 : m₅ 2 = p + 1 := by rw [f₅ 2 (l1 (by decide)), g₄]
  have w3 : m₅ 3 = 1 := by
    rw [e₅ 3 (by decide) (by decide) (l0 (by decide)) (l1 (by decide)), o3]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [w2, w3]; exact lt_of_le_of_lt (by omega) pB) fun m₆ g₆ f₆ => ?_)
  replace g₆ : m₆ 2 = p + 2 := by rw [g₆, w2, w3]
  -- The weight.
  refine Runs.seqs_cons (Runs.storeR (rB (by decide)) (rB (by decide)) fun m₇ g₇ f₇ => ?_)
  rw [g₆] at g₇ f₇
  have e₇ : ∀ x, x ≠ 2 → x ≠ 15 → x ≠ p → x ≠ p + 1 → x ≠ p + 2 → m₇ x = m x :=
    fun x a b c d e => by rw [f₇ x e, f₆ x a, e₅ x a b c d]
  -- The new head.
  have y25 : m₇ 25 = H7 L := by
    rw [e₇ 25 (by decide) (by decide) (l0 (by decide)) (l1 (by decide)) (l2 (by decide)), h25]
  have yra : m₇ ra = a := by
    rw [e₇ ra ra2 ra15 (l0 hra32) (l1 hra32) (l2 hra32), hra]
  refine Runs.seqs_cons (Runs.seq (Runs.addR (rB (by decide)) (by rw [br]; exact rB (by decide))
    (rB hra32) (by rw [br, y25, yra]; exact AB) fun m₈ g₈ f₈ =>
      Runs.store (rB (by decide)) (rB (by decide)) ?_))
  rw [br, y25, yra] at g₈
  have v13' : m₈ 13 = p := by
    rw [f₈ 13 (by decide), e₇ 13 (by decide) (by decide) (l0 (by decide)) (l1 (by decide))
      (l2 (by decide)), h13]
  rw [g₈, v13']
  set m₉ := update m₈ (H7 L + a) p with hm₉
  have f₉ : ∀ x, x ≠ H7 L + a → m₉ x = m₈ x := fun x h => update_of_ne h _ _
  have s₉ : m₉ (H7 L + a) = p := update_self _ _ _
  have e₉ : ∀ x, x ≠ 2 → x ≠ 15 → x ≠ p → x ≠ p + 1 → x ≠ p + 2 → x ≠ H7 L + a → m₉ x = m x :=
    fun x a' b c d e h => by rw [f₉ x h, f₈ x a', e₇ x a' b c d e]
  have y13 : m₉ 13 = p := by rw [f₉ 13 (lA (by decide)), v13']
  have y16 : m₉ 16 = 3 := by
    rw [e₉ 16 (by decide) (by decide) (l0 (by decide)) (l1 (by decide)) (l2 (by decide))
      (lA (by decide)), o16]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [y13, y16]; exact pB) fun m₁₀ g₁₀ f₁₀ => ?_)
  rw [y13, y16] at g₁₀
  have q₉ : ∀ x, x ≠ 13 → m₁₀ x = m₉ x := f₁₀
  have n13 : ∀ {x}, 32 ≤ x → x ≠ 13 := fun h e => by subst e; exact absurd h (by decide)
  have g32 : 32 ≤ p := by
    by_contra hc; exact l0 (show p < 32 by exact Nat.lt_of_not_le hc) rfl
  have g32a : 32 ≤ H7 L + a := by
    by_contra hc; exact lA (show H7 L + a < 32 by exact Nat.lt_of_not_le hc) rfl
  refine Runs.mono (hQ m₁₀ g₁₀ ?_ ?_ ?_ ?_ fun x a2 a13 a15 ap ap1 ap2 aA => ?_)
    fun m'' k h => ?_
  · rw [q₉ _ (n13 g32), f₉ _ pA, f₈ _ n0, f₇ _ (Ne.symm (by omega)), f₆ _ n0,
      f₅ _ (Ne.symm y1), f₄ _ n0, g₃]
  · rw [q₉ _ (n13 (by omega)), f₉ _ p1A, f₈ _ n1, f₇ _ (Ne.symm y3), f₆ _ n1, g₅,
      f₄ rb rb2, e₃ rb rb2 rb15 (l0 hrb32)]
  · rw [q₉ _ (n13 (by omega)), f₉ _ p2A, f₈ _ n2, g₇, f₆ 14 (by decide),
      e₅ 14 (by decide) (by decide) (l0 (by decide)) (l1 (by decide))]
  · rw [q₉ _ (n13 g32a), s₉]
  · rw [q₉ x a13, e₉ x a2 a15 ap ap1 ap2 aA]
  · convert h using 1
    ring

/-- The adjacency list of `a` once the half-edges `H` are added. -/
def adjL (H : List (ℕ × ℕ × ℕ)) (a : ℕ) : List (ℕ × ℕ) :=
  (H.reverse.filter fun h => h.1 = a).map fun h => (h.2.1, h.2.2)

theorem adjL_snoc (H : List (ℕ × ℕ × ℕ)) (h : ℕ × ℕ × ℕ) (a : ℕ) :
    adjL (H ++ [h]) a = if h.1 = a then (h.2.1, h.2.2) :: adjL H a else adjL H a := by
  by_cases e : h.1 = a <;> simp [adjL, List.reverse_append, e]

/-- The heads hold the lists of `H`, below `P`. -/
def HI (L : Lay) (m : Mem) (P : ℕ) (H : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ v ≤ L.n, LstB L m P (m (H7 L + v)) (adjL H v)

theorem HI.push {P p a b w : ℕ} {H : List (ℕ × ℕ × ℕ)} (hI : HI L m P H) (hPp : P ≤ p)
    (hHE : L.HE ≤ p) (ha : a ≤ L.n) (e0 : m' p = m (H7 L + a)) (e1 : m' (p + 1) = b)
    (e2 : m' (p + 2) = w) (e3 : m' (H7 L + a) = p)
    (hf : ∀ x, L.HE ≤ x → x < P → m' x = m x)
    (hh : ∀ v ≤ L.n, v ≠ a → m' (H7 L + v) = m (H7 L + v)) :
    HI L m' (p + 3) (H ++ [(a, b, w)]) := fun v hv => by
  rw [adjL_snoc]
  by_cases e : a = v
  · subst e
    rw [if_pos rfl, e3]
    refine ⟨hHE, le_refl _, e1, e2, ?_⟩
    rw [e0]
    exact LstB.frame (by omega) hf _ _ (hI a ha)
  · rw [if_neg e, hh v hv (Ne.symm e)]
    exact LstB.frame (by omega) hf _ _ (hI v hv)

/-- The registers the construction uses. -/
def BT (a : ℕ) : Prop :=
  a = 2 ∨ a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 17 ∨ a = 29 ∨ a = 30 ∨ a = 31

theorem breg_not_BT {k : ℕ} (hk : k < 10) : ¬BT (breg k) := by
  unfold breg BT; split_ifs <;> omega

theorem Pre.keep (h : Pre L m) (hm : ∀ a, a < 32 → ¬BT a → m' a = m a)
    (hd : ∀ a, L.Dyn a → m' a = m a) : Pre L m' := by
  refine ⟨h.H32, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · rw [hm _ (breg_lt k hk) (breg_not_BT hk)]; exact h.base k hk
  · rw [hm 27 (by decide) (by simp [BT])]; exact h.n
  · rw [hm 28 (by decide) (by simp [BT])]; exact h.D
  · rw [hm 3 (by decide) (by simp [BT])]; exact h.one
  · rw [hm 8 (by decide) (by simp [BT])]; exact h.zero
  · rw [hm 16 (by decide) (by simp [BT])]; exact h.three
  · rw [hd a ha]; exact h.dyn a ha

/-- Heap cells and low cells are not the ones a half-edge writes. -/
theorem off_cells {p a x : ℕ} (hp : L.HE ≤ p) (hp3 : p + 3 ≤ L.CH) (ha : a ≤ L.n)
    (hx : L.Dyn x ∨ x < L.H) : x ≠ p ∧ x ≠ p + 1 ∧ x ≠ p + 2 ∧ x ≠ H7 L + a := by
  have hRn : L.n + L.D + 3 = L.R := rfl
  have hHE : L.HE = L.H + 10 * L.R := rfl
  unfold H7
  rcases hx with hd | hl
  · unfold Lay.Dyn at hd; omega
  · omega

/-- Below `p`, a half-edge changes only head `a`. -/
theorem heads_keep {P p a : ℕ} (hf : ∀ x, x ≠ 2 → x ≠ 13 → x ≠ 15 → x ≠ p → x ≠ p + 1 →
      x ≠ p + 2 → x ≠ H7 L + a → m' x = m x) (H32 : 32 ≤ L.H) (hPp : P ≤ p) (hHE : L.HE ≤ p)
    (ha : a ≤ L.n) :
    (∀ x, L.HE ≤ x → x < P → m' x = m x) ∧
      ∀ v ≤ L.n, v ≠ a → m' (H7 L + v) = m (H7 L + v) := by
  have hRn : L.n + L.D + 3 = L.R := rfl
  have hHE' : L.HE = L.H + 10 * L.R := rfl
  refine ⟨fun x h1 h2 => hf x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by unfold H7; omega), fun v hv hva => hf _ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;> unfold H7 <;> omega

theorem buildBody_spec {u v w P p q Z : ℕ} {H : List (ℕ × ℕ × ℕ)} (hP : Pre L m) (h13 : m 13 = P)
    (h30 : m 30 = p) (h31 : m 31 = q) (h17 : m 17 = Z) (c0 : m p = u) (c1 : m (p + 1) = v)
    (c2 : m q = w) (hu : u + 1 ≤ L.n) (hv : v + 1 ≤ L.n) (hHE : L.HE ≤ P) (hP6 : P + 6 ≤ L.CH)
    (hp32 : 32 ≤ p) (hq32 : 32 ≤ q) (hpH : p + 2 < L.H) (hqH : q + 1 < L.H) (hI : HI L m P H)
    (hB : L.top < B) :
    Runs B buildBody m fun m' k => Pre L m' ∧ m' 13 = P + 6 ∧ m' 30 = p + 2 ∧ m' 31 = q + 1 ∧
      m' 17 = Z ∧ m' 15 = (if q + 1 < Z then 1 else 0) ∧
      HI L m' (P + 6) (H ++ [(u + 1, v + 1, w)] ++ [(v + 1, u + 1, w)]) ∧
      (∀ a, a < L.H → ¬BT a → m' a = m a) ∧ (∀ a, 32 ≤ a → a < L.H → m' a = m a) ∧ k ≤ 31 := by
  have H32 := hP.H32
  have o3 : m 3 = 1 := hP.one
  have hu' : u + 1 < B ∧ v + 1 < B ∧ p + 2 < B ∧ q + 1 < B ∧ (∀ {r}, r < 32 → r < B) := by
    have ht := top_ge (L := L)
    have hRn : L.n + L.D + 3 = L.R := rfl
    refine ⟨?_, ?_, ?_, ?_, fun h => ?_⟩ <;> omega
  obtain ⟨uB, vB, pB, qB, rB⟩ := hu'
  have hne : ∀ {x}, 32 ≤ x → x ≠ 2 ∧ x ≠ 11 ∧ x ≠ 12 ∧ x ≠ 14 := fun h => by omega
  unfold buildBody
  -- Read the edge.
  refine Runs.seqs_cons (Runs.loadR (rB (by decide)) (rB (by decide)) fun m₁ g₁ f₁ => ?_)
  rw [h30, c0] at g₁
  have y3 : m₁ 3 = 1 := by rw [f₁ 3 (by decide), o3]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [g₁, y3]; exact uB) fun m₂ g₂ f₂ => ?_)
  rw [g₁, y3] at g₂
  have z30 : m₂ 30 = p := by rw [f₂ 30 (by decide), f₁ 30 (by decide), h30]
  have z3 : m₂ 3 = 1 := by rw [f₂ 3 (by decide), y3]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [z30, z3]; exact lt_of_le_of_lt (by omega) pB) fun m₃ g₃ f₃ => ?_)
  rw [z30, z3] at g₃
  refine Runs.seqs_cons (Runs.loadR (rB (by decide)) (rB (by decide)) fun m₄ g₄ f₄ => ?_)
  rw [g₃, f₃ _ (hne (by omega)).1, f₂ _ (hne (by omega)).2.1, f₁ _ (hne (by omega)).2.1, c1] at g₄
  have y3' : m₄ 3 = 1 := by rw [f₄ 3 (by decide), f₃ 3 (by decide), z3]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [g₄, y3']; exact vB) fun m₅ g₅ f₅ => ?_)
  rw [g₄, y3'] at g₅
  refine Runs.seqs_cons (Runs.loadR (rB (by decide)) (rB (by decide)) fun m₆ g₆ f₆ => ?_)
  have e₆ : ∀ x, x ≠ 2 → x ≠ 11 → x ≠ 12 → x ≠ 14 → m₆ x = m x := fun x a b c d => by
    rw [f₆ x d, f₅ x c, f₄ x c, f₃ x a, f₂ x b, f₁ x b]
  rw [f₅ 31 (by decide), f₄ 31 (by decide), f₃ 31 (by decide), f₂ 31 (by decide),
    f₁ 31 (by decide), h31, f₅ q (hne hq32).2.2.1, f₄ q (hne hq32).2.2.1, f₃ q (hne hq32).1,
    f₂ q (hne hq32).2.1, f₁ q (hne hq32).2.1, c2] at g₆
  have ee : ∀ {x}, 32 ≤ x → m₆ x = m x := fun h => by
    obtain ⟨a, b, c, d⟩ := hne h; exact e₆ _ a b c d
  have P₆ : Pre L m₆ := hP.keep (fun a _ hT => e₆ a (fun e => hT (by simp [BT, e]))
    (fun e => hT (by simp [BT, e])) (fun e => hT (by simp [BT, e]))
    (fun e => hT (by simp [BT, e])))
    (fun a hd => ee (by
      have hCH := CH_ge (L := L)
      unfold Lay.Dyn at hd
      have : L.CH ≤ a ∨ L.H ≤ a := by omega
      omega))
  have I₆ : HI L m₆ P H := fun x hx => by
    have hge : 32 ≤ H7 L + x := by unfold H7; omega
    rw [ee hge]
    exact LstB.frame (le_refl _) (fun a h1 _ => ee (by
      have : L.HE = L.H + 10 * L.R := rfl
      omega)) _ _ (hI x hx)
  have v11 : m₆ 11 = u + 1 := by
    rw [f₆ 11 (by decide), f₅ 11 (by decide), f₄ 11 (by decide), f₃ 11 (by decide), g₂]
  have v12 : m₆ 12 = v + 1 := by rw [f₆ 12 (by decide), g₅]
  have v13 : m₆ 13 = P := by rw [e₆ 13 (by decide) (by decide) (by decide) (by decide), h13]
  have hP3 : P + 3 ≤ L.CH := by omega
  have hP33 : P + 3 + 3 ≤ L.CH := by omega
  have hHE3 : L.HE ≤ P + 3 := by omega
  clear f₁ f₂ f₃ f₄ f₅ f₆ g₁ g₂ g₃ g₄ g₅ y3 y3' z3 z30
  -- The two half-edges.
  refine half_spec _ P₆ v13 v11 hu (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hHE hP3 hB fun m₇ a13 a0 a1 a2 a3 af => ?_
  rw [v12] at a1
  rw [g₆] at a2
  have o₇ : ∀ {x}, (L.Dyn x ∨ x < L.H) → x ≠ 2 → x ≠ 13 → x ≠ 15 → m₇ x = m₆ x :=
      fun hx h2 h13' h15 => by
    obtain ⟨c1, c2, c3, c4⟩ := off_cells hHE hP3 hu hx
    exact af _ h2 h13' h15 c1 c2 c3 c4
  have lowH : ∀ {x}, x < 32 → (L.Dyn x ∨ x < L.H) := fun h => .inr (by omega)
  have dyn2 : ∀ {x}, L.Dyn x → x ≠ 2 ∧ x ≠ 13 ∧ x ≠ 15 := fun hd => by
    have hCH := CH_ge (L := L)
    unfold Lay.Dyn at hd
    omega
  have P₇ : Pre L m₇ := P₆.keep (fun x hx hT => o₇ (lowH hx) (fun e => hT (by simp [BT, e]))
    (fun e => hT (by simp [BT, e])) (fun e => hT (by simp [BT, e])))
    (fun x hd => o₇ (.inl hd) (dyn2 hd).1 (dyn2 hd).2.1 (dyn2 hd).2.2)
  obtain ⟨k1, k2⟩ := heads_keep (P := P) af H32 (le_refl _) hHE hu
  have I₇ : HI L m₇ (P + 3) (H ++ [(u + 1, v + 1, w)]) :=
    I₆.push (le_refl _) hHE hu a0 a1 a2 a3 k1 k2
  have w12 : m₇ 12 = v + 1 := by
    rw [o₇ (lowH (by decide)) (by decide) (by decide) (by decide), v12]
  have w11 : m₇ 11 = u + 1 := by
    rw [o₇ (lowH (by decide)) (by decide) (by decide) (by decide), v11]
  have w14 : m₇ 14 = w := by
    rw [o₇ (lowH (by decide)) (by decide) (by decide) (by decide), g₆]
  refine half_spec _ P₇ a13 w12 hv (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hHE3 hP33 hB fun m₈ b13 b0 b1 b2 b3 bf => ?_
  rw [w11] at b1
  rw [w14] at b2
  have o₈ : ∀ {x}, (L.Dyn x ∨ x < L.H) → x ≠ 2 → x ≠ 13 → x ≠ 15 → m₈ x = m₇ x :=
      fun hx h2 h13' h15 => by
    obtain ⟨c1, c2, c3, c4⟩ := off_cells hHE3 hP33 hv hx
    exact bf _ h2 h13' h15 c1 c2 c3 c4
  have P₈ : Pre L m₈ := P₇.keep (fun x hx hT => o₈ (lowH hx) (fun e => hT (by simp [BT, e]))
    (fun e => hT (by simp [BT, e])) (fun e => hT (by simp [BT, e])))
    (fun x hd => o₈ (.inl hd) (dyn2 hd).1 (dyn2 hd).2.1 (dyn2 hd).2.2)
  obtain ⟨k3, k4⟩ := heads_keep (P := P + 3) bf H32 (le_refl _) hHE3 hv
  have I₈ : HI L m₈ (P + 3 + 3) (H ++ [(u + 1, v + 1, w)] ++ [(v + 1, u + 1, w)]) :=
    I₇.push (le_refl _) hHE3 hv b0 b1 b2 b3 k3 k4
  have c₈ : ∀ {x}, x < L.H → x ≠ 2 → x ≠ 13 → x ≠ 15 → m₈ x = m₆ x := fun hx h2 h13' h15 => by
    rw [o₈ (.inr hx) h2 h13' h15, o₇ (.inr hx) h2 h13' h15]
  have r30 : m₈ 30 = p := by
    rw [c₈ (by omega) (by decide) (by decide) (by decide),
      e₆ 30 (by decide) (by decide) (by decide) (by decide), h30]
  have r31 : m₈ 31 = q := by
    rw [c₈ (by omega) (by decide) (by decide) (by decide),
      e₆ 31 (by decide) (by decide) (by decide) (by decide), h31]
  have r17 : m₈ 17 = Z := by
    rw [c₈ (by omega) (by decide) (by decide) (by decide),
      e₆ 17 (by decide) (by decide) (by decide) (by decide), h17]
  have r3 : m₈ 3 = 1 := P₈.one
  -- Move on.
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [r30, r3]; exact lt_of_le_of_lt (by omega) pB) fun m₉ g₉ f₉ => ?_)
  rw [r30, r3] at g₉
  have s3 : m₉ 3 = 1 := by rw [f₉ 3 (by decide), r3]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [g₉, s3]; exact pB) fun m₁₀ g₁₀ f₁₀ => ?_)
  rw [g₉, s3] at g₁₀
  have t31 : m₁₀ 31 = q := by rw [f₁₀ 31 (by decide), f₉ 31 (by decide), r31]
  have t3 : m₁₀ 3 = 1 := by rw [f₁₀ 3 (by decide), s3]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [t31, t3]; exact qB) fun m₁₁ g₁₁ f₁₁ => ?_)
  rw [t31, t3] at g₁₁
  refine Runs.seqs_cons (Runs.lessR (rB (by decide)) (rB (by decide)) (rB (by decide))
    fun m₁₂ g₁₂ f₁₂ => ?_)
  have u17 : m₁₁ 17 = Z := by
    rw [f₁₁ 17 (by decide), f₁₀ 17 (by decide), f₉ 17 (by decide), r17]
  rw [g₁₁, u17] at g₁₂
  refine Runs.seqs_nilR (by have := rB (show 2 < 32 by decide); exact this) fun m₁₃ g₁₃ f₁₃ => ?_
  have E : ∀ x, x ≠ 2 → x ≠ 15 → x ≠ 30 → x ≠ 31 → m₁₃ x = m₈ x := fun x a b c d => by
    rw [f₁₃ x a, f₁₂ x b, f₁₁ x d, f₁₀ x c, f₉ x c]
  have E' : ∀ {x}, 32 ≤ x → m₁₃ x = m₈ x := fun h => E _ (by omega) (by omega) (by omega) (by omega)
  refine ⟨P₈.keep (fun x _ hT => E x (fun e => hT (by simp [BT, e])) (fun e => hT (by simp [BT, e]))
      (fun e => hT (by simp [BT, e])) (fun e => hT (by simp [BT, e])))
      (fun x hd => E' (by
        have hCH := CH_ge (L := L)
        unfold Lay.Dyn at hd
        omega)), ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, fun x hx hT => ?_, fun x h1 h2 => ?_, ?_⟩
  · rw [E 13 (by decide) (by decide) (by decide) (by decide), b13]
  · rw [f₁₃ 30 (by decide), f₁₂ 30 (by decide), f₁₁ 30 (by decide), g₁₀]
  · rw [f₁₃ 31 (by decide), f₁₂ 31 (by decide), g₁₁]
  · rw [E 17 (by decide) (by decide) (by decide) (by decide), r17]
  · rw [f₁₃ 15 (by decide), g₁₂]
  · have hge : 32 ≤ H7 L + x := by unfold H7; omega
    rw [E' hge]
    exact LstB.frame (le_refl _) (fun a h1 _ => E' (by
      have : L.HE = L.H + 10 * L.R := rfl
      omega)) _ _ (I₈ x hx)
  · have n2 : x ≠ 2 := fun e => hT (by simp [BT, e])
    have n13 : x ≠ 13 := fun e => hT (by simp [BT, e])
    have n15 : x ≠ 15 := fun e => hT (by simp [BT, e])
    rw [E x n2 n15 (fun e => hT (by simp [BT, e])) (fun e => hT (by simp [BT, e])),
      c₈ hx n2 n13 n15, e₆ x n2 (fun e => hT (by simp [BT, e])) (fun e => hT (by simp [BT, e]))
      (fun e => hT (by simp [BT, e]))]
  · rw [E' h1, c₈ h2 (by omega) (by omega) (by omega), ee h1]
  · norm_num

/-- The edges `(u, v, w)`, with `u, v` from `p` and `w` from `q`. -/
def EdgesAt (m : Mem) : ℕ → ℕ → List (ℕ × ℕ × ℕ) → Prop
  | _, _, [] => True
  | p, q, (u, v, w) :: l => m p = u ∧ m (p + 1) = v ∧ m q = w ∧ EdgesAt m (p + 2) (q + 1) l

/-- The two half-edges of an edge. -/
def hfN (t : ℕ × ℕ × ℕ) : List (ℕ × ℕ × ℕ) :=
  [(t.1 + 1, t.2.1 + 1, t.2.2), (t.2.1 + 1, t.1 + 1, t.2.2)]

/-- The construction's state in memory. -/
structure BuildR (L : Lay) (m₀ : Mem) (A E : ℕ) (pre rest : List (ℕ × ℕ × ℕ)) (m : Mem) : Prop where
  ok : Pre L m
  r13 : m 13 = L.HE + 6 * pre.length
  r30 : m 30 = A + 2 + 2 * pre.length
  r31 : m 31 = A + 2 * E + 3 + pre.length
  r17 : m 17 = A + 3 * E + 3
  r15 : m 15 = if A + 2 * E + 3 + pre.length < A + 3 * E + 3 then 1 else 0
  hi : HI L m (L.HE + 6 * pre.length) (pre.flatMap hfN)
  lo : ∀ a, a < L.H → ¬BT a → m a = m₀ a
  hi' : ∀ a, 32 ≤ a → a < L.H → m a = m₀ a
  at' : EdgesAt m₀ (A + 2 + 2 * pre.length) (A + 2 * E + 3 + pre.length) rest

theorem BuildR.step {m₀ : Mem} {A E : ℕ} {pre rest : List (ℕ × ℕ × ℕ)} {t : ℕ × ℕ × ℕ}
    (h : BuildR L m₀ A E pre (t :: rest) m) (hE : L.E = E) (hlen : pre.length < E)
    (hA : 32 ≤ A) (hH : A + 3 * E + 4 ≤ L.H) (htn : t.1 + 1 ≤ L.n ∧ t.2.1 + 1 ≤ L.n)
    (hB : L.top < B) :
    Runs B buildBody m fun m' k => BuildR L m₀ A E (pre ++ [t]) rest m' ∧ k ≤ 31 := by
  obtain ⟨u, v, w⟩ := t
  obtain ⟨hP, r13, r30, r31, r17, r15, hI, lo, hi', c0, c1, c2, c3⟩ := h
  have hHE : L.HE ≤ L.HE + 6 * pre.length := by omega
  have hP6 : L.HE + 6 * pre.length + 6 ≤ L.CH := by
    have : L.CH = L.HE + 6 * L.E := rfl
    omega
  have hc0 : m (A + 2 + 2 * pre.length) = u := by rw [hi' _ (by omega) (by omega)]; exact c0
  have hc1 : m (A + 2 + 2 * pre.length + 1) = v := by rw [hi' _ (by omega) (by omega)]; exact c1
  have hc2 : m (A + 2 * E + 3 + pre.length) = w := by rw [hi' _ (by omega) (by omega)]; exact c2
  refine Runs.mono (buildBody_spec hP r13 r30 r31 r17 hc0 hc1 hc2 htn.1 htn.2 hHE hP6 (by omega)
    (by omega) (by omega) (by omega) hI hB)
    fun m' k ⟨P', a13, a30, a31, a17, a15, I', alo, ahi, hk⟩ => ⟨?_, hk⟩
  have hl : (pre ++ [(u, v, w)]).length = pre.length + 1 := by simp
  refine ⟨P', ?_, ?_, ?_, a17, ?_, ?_, fun a ha hT => ?_, fun a h1 h2 => ?_, ?_⟩
  · rw [a13, hl]; omega
  · rw [a30, hl]; omega
  · rw [a31, hl]; omega
  · rw [a15, hl]; rfl
  · rw [hl, show L.HE + 6 * (pre.length + 1) = L.HE + 6 * pre.length + 6 by omega,
      List.flatMap_append]
    simpa [hfN, List.append_assoc] using I'
  · rw [alo a ha hT, lo a ha hT]
  · rw [ahi a h1 h2, hi' a h1 h2]
  · rw [hl]
    have e1 : A + 2 + 2 * (pre.length + 1) = A + 2 + 2 * pre.length + 2 := by omega
    have e2 : A + 2 * E + 3 + (pre.length + 1) = A + 2 * E + 3 + pre.length + 1 := by omega
    rw [e1, e2]; exact c3

theorem build_run {tri : List (ℕ × ℕ × ℕ)} {A E : ℕ} (hlen : tri.length = E) (hE : L.E = E)
    (hA : 32 ≤ A) (hH : A + 3 * E + 4 ≤ L.H) (htn : ∀ t ∈ tri, t.1 + 1 ≤ L.n ∧ t.2.1 + 1 ≤ L.n)
    (hP : Pre L m) (h9 : m 9 = A) (h11 : m 11 = E) (h13 : m 13 = L.HE)
    (hEd : EdgesAt m (A + 2) (A + 2 * E + 3) tri) (hz : ∀ v ≤ L.n, m (H7 L + v) = 0)
    (hB : L.top < B) :
    Runs B build m fun m' k => Pre L m' ∧ m' 13 = L.CH ∧ m' 17 = A + 3 * E + 3 ∧
      (∀ v ≤ L.n, Lst L m' (m' (H7 L + v)) (adjL (tri.flatMap hfN) v)) ∧
      (∀ a, a < L.H → ¬BT a → m' a = m a) ∧ (∀ a, 32 ≤ a → a < L.H → m' a = m a) ∧
      k ≤ 33 * E + 12 := by
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have hCHE : L.CH = L.HE + 6 * L.E := rfl
  have hCT : L.CH ≤ L.top := by unfold Lay.top; omega
  have hCH := CH_ge (L := L)
  have hHE' : L.HE = L.H + 10 * L.R := rfl
  have H32 := hP.H32
  have o3 : m 3 = 1 := hP.one
  have rB : ∀ {r}, r < 32 → r < B := fun h => by omega
  have bA : A + 3 * E + 4 < B := by omega
  clear ht hRn hCT hCH hHE'
  unfold build
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [h9, o3]; omega) fun m₁ g₁ f₁ => ?_)
  rw [h9, o3] at g₁
  have y3 : m₁ 3 = 1 := by rw [f₁ 3 (by decide), o3]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [g₁, y3]; omega) fun m₂ g₂ f₂ => ?_)
  rw [g₁, y3] at g₂
  have e11 : m₂ 11 = E := by rw [f₂ 11 (by decide), f₁ 11 (by decide), h11]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [g₂, e11]; omega) fun m₃ g₃ f₃ => ?_)
  rw [g₂, e11] at g₃
  have e11' : m₃ 11 = E := by rw [f₃ 11 (by decide), e11]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [g₃, e11']; omega) fun m₄ g₄ f₄ => ?_)
  rw [g₃, e11'] at g₄
  have y3' : m₄ 3 = 1 := by rw [f₄ 3 (by decide), f₃ 3 (by decide), f₂ 3 (by decide), y3]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [g₄, y3']; omega) fun m₅ g₅ f₅ => ?_)
  rw [g₄, y3'] at g₅
  have e11'' : m₅ 11 = E := by rw [f₅ 11 (by decide), f₄ 11 (by decide), e11']
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [g₅, e11'']; omega) fun m₆ g₆ f₆ => ?_)
  rw [g₅, e11''] at g₆
  refine Runs.seqs_cons (Runs.lessR (rB (by decide)) (rB (by decide)) (rB (by decide))
    fun m₇ g₇ f₇ => ?_)
  rw [f₆ 31 (by decide), g₅, g₆] at g₇
  have F₇ : ∀ a, a ≠ 15 → a ≠ 17 → a ≠ 30 → a ≠ 31 → m₇ a = m a := fun a a15 a17 a30 a31 => by
    rw [f₇ a a15, f₆ a a17, f₅ a a31, f₄ a a31, f₃ a a31, f₂ a a30, f₁ a a30]
  have E₇ : ∀ a, ¬BT a → m₇ a = m a := fun a hT =>
    F₇ a (fun e => hT (by simp [BT, e])) (fun e => hT (by simp [BT, e]))
      (fun e => hT (by simp [BT, e])) (fun e => hT (by simp [BT, e]))
  have hi₇ : ∀ {a}, 32 ≤ a → m₇ a = m a := fun h => E₇ _ (by simp only [BT]; omega)
  have B₀ : BuildR L m A E [] tri m₇ := by
    refine ⟨hP.keep (fun a _ hT => E₇ a hT) (fun a hd => hi₇ (by
        have hCH := CH_ge (L := L)
        unfold Lay.Dyn at hd
        omega)), ?_, ?_, ?_, ?_, ?_, fun v hv => ?_, fun a _ hT => E₇ a hT,
      fun a h1 _ => hi₇ h1, ?_⟩
    · rw [F₇ 13 (by decide) (by decide) (by decide) (by decide), h13]
      rfl
    · rw [f₇ 30 (by decide), f₆ 30 (by decide), f₅ 30 (by decide), f₄ 30 (by decide),
        f₃ 30 (by decide), g₂]
      simp only [List.length_nil]
    · rw [f₇ 31 (by decide), f₆ 31 (by decide), g₅]
      simp only [List.length_nil]; omega
    · rw [f₇ 17 (by decide), g₆]; omega
    · rw [g₇]
      simp only [List.length_nil, Nat.add_zero]
      have e1 : A + 1 + 1 + E + E + 1 = A + 2 * E + 3 := by omega
      have e2 : A + 1 + 1 + E + E + 1 + E = A + 3 * E + 3 := by omega
      rw [e2, e1]
    · have hge : 32 ≤ H7 L + v := by unfold H7; omega
      rw [hi₇ hge, hz v hv]
      simp [adjL, LstB]
    · simpa using hEd
  clear g₁ g₂ g₃ g₄ g₅ g₆ g₇ f₁ f₂ f₃ f₄ f₅ f₆ f₇ F₇ y3 y3' e11 e11' e11''
  let P : Mem → ℕ → Prop := fun m' c => ∃ pre rest, tri = pre ++ rest ∧
    BuildR L m A E pre rest m' ∧ c ≤ 33 * pre.length
  refine Runs.seqs_cons (Runs.loop P (fun m' => A + 3 * E + 3 - m' 31) (rB (by decide))
    (rB (by decide)) ?_ ?_ ⟨[], tri, rfl, B₀, by simp⟩)
  · rintro m' c ⟨pre, rest, hts, hR, hc⟩ heq
    have o' : m' 3 = 1 := hR.ok.one
    have hlt : pre.length < E := by
      rw [hR.r15, o'] at heq
      by_contra hn
      rw [if_neg (by omega)] at heq
      omega
    rcases rest with _ | ⟨t, r⟩
    · rw [List.append_nil] at hts; rw [← hts] at hlt; omega
    · have htm : t ∈ tri := by rw [hts]; simp
      refine Runs.mono (hR.step hE hlt hA hH (htn t htm) hB) fun m₁ k ⟨R₁, hk⟩ =>
        ⟨⟨pre ++ [t], r, by simp [hts], R₁, ?_⟩, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · rw [R₁.r31, hR.r31]
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · rintro m' c ⟨pre, rest, hts, hR, hc⟩ heq
    have o' : m' 3 = 1 := hR.ok.one
    have hge : E ≤ pre.length := by
      rw [hR.r15, o'] at heq
      by_contra hn
      exact heq (by rw [if_pos (by omega)])
    have hl : pre.length + rest.length = E := by
      rw [← hlen, hts, List.length_append]
    have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    rw [List.append_nil] at hts
    subst hts
    refine Runs.seqs_nilR (rB (by decide)) fun m₁ g₁ f₁ => ?_
    have hH2 : ∀ {a}, 32 ≤ a → m₁ a = m' a := fun h => f₁ _ (by omega)
    have hlen' : L.HE + 6 * tri.length = L.CH := by rw [hCHE, hE, hlen]
    refine ⟨hR.ok.keep (fun a _ hT => f₁ a fun e => hT (by simp [BT, e]))
        (fun a hd => f₁ a (by
          have hCH := CH_ge (L := L)
          unfold Lay.Dyn at hd
          omega)), ?_, by rw [f₁ 17 (by decide), hR.r17], fun v hv => ?_,
      fun a ha hT => ?_, fun a h1 h2 => ?_, ?_⟩
    · rw [f₁ 13 (by decide), hR.r13, hlen']
    · have hge' : 32 ≤ H7 L + v := by unfold H7; omega
      rw [hH2 hge']
      have := hR.hi v hv
      rw [hlen'] at this
      refine LstB.toLst (P := L.CH) (le_refl _) _ _ ?_
      exact LstB.frame (le_refl _) (fun a h1 _ => hH2 (by
        have : L.HE = L.H + 10 * L.R := rfl
        omega)) _ _ this
    · rw [f₁ a fun e => hT (by simp [BT, e]), hR.lo a ha hT]
    · rw [hH2 h1, hR.hi' a h1 h2]
    · rw [hlen] at hc; omega

end Formalgo.Algorithms.ShortestPaths
