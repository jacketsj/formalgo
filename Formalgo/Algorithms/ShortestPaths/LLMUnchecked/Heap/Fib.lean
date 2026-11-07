import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.Heap
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# The degree bound

LLM-generated; not checked by a human.

A node of degree `d` has at least `fib (d + 2)` descendants, so degrees stay below `2 · size n`.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St Finset

variable {s : St} {M : Finset ℕ}

/-- `v` lies in the tree below `x`. -/
inductive Desc (s : St) (M : Finset ℕ) (x : ℕ) : ℕ → Prop
  | self : Desc s M x x
  | step {v : ℕ} : v ∈ M → s.par v ≠ 0 → Desc s M x (s.par v) → Desc s M x v

theorem Desc.trans {a b v : ℕ} (h₁ : Desc s M a b) (h₂ : Desc s M b v) : Desc s M a v := by
  induction h₂ with
  | self => exact h₁
  | step hv hp _ ih => exact .step hv hp ih

theorem Desc.ht_le (h : Forest s M 0) {a v : ℕ} (hd : Desc s M a v) (hv : v ∈ M) :
    s.ht v ≤ s.ht a := by
  induction hd with
  | self => exact le_refl _
  | step hv' hp hd' ih =>
    have := h.height _ hv' hp
    have := ih (h.up _ hv' hp).1
    omega

theorem Desc.mem (h : Forest s M 0) {a v : ℕ} (hd : Desc s M a v) (ha : a ∈ M) : v ∈ M := by
  cases hd with
  | self => exact ha
  | step hv _ _ => exact hv

/-- The ancestors of a node form a chain. -/
theorem Desc.chain {a b v : ℕ} (ha : Desc s M a v) (hb : Desc s M b v) :
    Desc s M a b ∨ Desc s M b a := by
  induction ha with
  | self => exact .inr hb
  | @step w hw hp hd ih =>
    cases hb with
    | self => exact .inl (.step hw hp hd)
    | step _ _ hb' => exact ih hb'

/-- The nodes below `x`. -/
noncomputable def sub (s : St) (M : Finset ℕ) (x : ℕ) : Finset ℕ :=
  open Classical in M.filter (Desc s M x)

theorem mem_sub {x v : ℕ} : v ∈ sub s M x ↔ v ∈ M ∧ Desc s M x v := by
  classical
  simp [sub]

theorem sub_subset {x : ℕ} : sub s M x ⊆ M := fun _ hv => (mem_sub.1 hv).1

/-- The children of `x`. -/
def kids (s : St) (M : Finset ℕ) (x : ℕ) : Finset ℕ := M.filter fun c => s.par c = x

/-- Ranks under an injective key run through `0, …, |T| - 1`. -/
theorem sum_rank (f g : ℕ → ℕ) : ∀ T : Finset ℕ, Set.InjOn f T →
    ∑ c ∈ T, g (T.filter fun c' => f c' < f c).card = ∑ i ∈ range T.card, g i := by
  intro T
  induction T using Finset.induction_on_max_value f with
  | empty => intro; simp
  | insert a T haT hmax ih =>
    intro hinj
    have hinjT : Set.InjOn f T := hinj.mono (fun x hx => by simp [hx])
    have hlt : ∀ x ∈ T, f x < f a := fun x hx => lt_of_le_of_ne (hmax x hx) fun he =>
      haT (by rw [← hinj (by simp [hx]) (by simp) he]; exact hx)
    rw [sum_insert haT, card_insert_of_notMem haT, sum_range_succ]
    have h1 : (insert a T).filter (fun c' => f c' < f a) = T := by
      ext c; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hc, hlt'⟩
        · omega
        · exact hc
      · intro hc; exact ⟨.inr hc, hlt c hc⟩
    have h2 : ∀ c ∈ T, (insert a T).filter (fun c' => f c' < f c) =
        T.filter (fun c' => f c' < f c) := by
      intro c hc; rw [filter_insert, if_neg (by have := hlt c hc; omega)]
    rw [h1, sum_congr rfl fun c hc => by rw [h2 c hc], ih hinjT, add_comm]

theorem sum_fib (d : ℕ) : ∑ i ∈ range d, Nat.fib (i + 1) + 1 = Nat.fib (d + 2) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, show d + 1 + 2 = d + 3 by omega, Nat.fib_add_two (n := d + 1)]
    rw [show d + 1 + 1 = d + 2 by omega]; omega

/-- A node of degree `d` has at least `fib (d + 2)` nodes below it. -/
theorem Forest.fib_le (h : Forest s M 0) :
    ∀ k, ∀ x ∈ M, s.ht x = k → Nat.fib (s.deg x + 2) ≤ (sub s M x).card := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro x hx hk
  have hx0 : x ≠ 0 := fun h0 => h.zero (h0 ▸ hx)
  -- The children's trees are disjoint, and below `x` but without `x`.
  have hkid : ∀ c ∈ kids s M x, c ∈ M ∧ s.par c = x ∧ s.ht c < s.ht x := by
    intro c hc
    simp only [kids, mem_filter] at hc
    refine ⟨hc.1, hc.2, ?_⟩
    have := h.height c hc.1 (by rw [hc.2]; exact hx0); rw [hc.2] at this; exact this
  have hdisj : (kids s M x : Set ℕ).PairwiseDisjoint (sub s M) := by
    intro c hc c' hc' hne
    simp only [Function.onFun, disjoint_left, mem_sub]
    rintro v ⟨_, hcv⟩ ⟨_, hc'v⟩
    obtain ⟨cM, cp, cht⟩ := hkid c hc
    obtain ⟨c'M, c'p, c'ht⟩ := hkid c' hc'
    -- Two children of `x` on one chain are equal.
    have key : ∀ a b, a ∈ kids s M x → b ∈ kids s M x → Desc s M a b → a = b := by
      intro a b ha hb hab
      cases hab with
      | self => rfl
      | step _ hp hd =>
        rw [(hkid b hb).2.1] at hd
        have := hd.ht_le h hx
        have := (hkid a ha).2.2
        omega
    rcases hcv.chain hc'v with hd | hd
    · exact hne (key c c' hc hc' hd)
    · exact hne (key c' c hc' hc hd).symm
  have hsub : insert x ((kids s M x).biUnion (sub s M)) ⊆ sub s M x := by
    intro v hv
    rcases mem_insert.1 hv with rfl | hv
    · exact mem_sub.2 ⟨hx, .self⟩
    · obtain ⟨c, hc, hvc⟩ := mem_biUnion.1 hv
      obtain ⟨cM, cp, _⟩ := hkid c hc
      obtain ⟨vM, hd⟩ := mem_sub.1 hvc
      exact mem_sub.2 ⟨vM, (Desc.step cM (by rw [cp]; exact hx0) (by rw [cp]; exact .self)).trans hd⟩
  have hxn : x ∉ (kids s M x).biUnion (sub s M) := by
    intro hv
    obtain ⟨c, hc, hvc⟩ := mem_biUnion.1 hv
    have := (mem_sub.1 hvc).2.ht_le h hx
    have := (hkid c hc).2.2
    omega
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem hxn, card_biUnion hdisj] at hcard
  -- Each child's tree is large.
  have hchild : ∀ c ∈ kids s M x, Nat.fib (older s M c + 1) ≤ (sub s M c).card := by
    intro c hc
    obtain ⟨cM, cp, cht⟩ := hkid c hc
    have h1 := ih (s.ht c) (by omega) c cM rfl
    have h2 := h.fib c cM (by rw [cp]; exact hx0) (fun h0 => h.zero (h0 ▸ cM))
    have h3 := h.mark c cM
    exact (Nat.fib_mono (by omega)).trans h1
  -- The ranks of the children.
  have hrank : ∑ c ∈ kids s M x, Nat.fib (older s M c + 1) =
      ∑ i ∈ range (s.deg x), Nat.fib (i + 1) := by
    have hk : (kids s M x).card = s.deg x := h.card_children hx
    rw [← hk]
    have := sum_rank s.lt (fun i => Nat.fib (i + 1)) (kids s M x) (by
      intro c hc c' hc' he
      obtain ⟨cM, cp, _⟩ := hkid c hc
      obtain ⟨c'M, c'p, _⟩ := hkid c' hc'
      exact (h.ltinj c cM c' c'M (by rw [cp]; exact hx0) (by rw [cp, c'p]) he.symm).symm)
    rw [← this]
    refine sum_congr rfl fun c hc => ?_
    congr 2
    simp only [older, kids, filter_filter, (hkid c hc).2.1]
  have := sum_le_sum hchild
  have := sum_fib (s.deg x)
  omega

theorem fib_ge_pow (k : ℕ) : 2 ^ (k / 2) ≤ Nat.fib (k + 2) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | _ | k
  · simp
  · simp [Nat.fib_add_two]
  · have := ih k (by omega)
    rw [show k + 2 + 2 = k + 4 by omega, Nat.fib_add_two (n := k + 2)]
    have hm := Nat.fib_mono (show k + 2 ≤ k + 3 by omega)
    rw [show (k + 2) / 2 = k / 2 + 1 by omega, pow_succ, show k + 2 + 1 = k + 3 by omega]
    omega

/-- Degrees stay below `2 · size n`. -/
theorem Forest.deg_lt (h : Forest s M 0) {n : ℕ} (hM : ∀ v ∈ M, 1 ≤ v ∧ v ≤ n) {x : ℕ}
    (hx : x ∈ M) : s.deg x < 2 * Nat.size n := by
  have h1 := h.fib_le _ x hx rfl
  have h2 : (sub s M x).card ≤ n := by
    refine (card_le_card sub_subset).trans ?_
    calc M.card ≤ ((range (n + 1)).erase 0).card := card_le_card fun v hv => by
          have := hM v hv; simp only [mem_erase, mem_range]; omega
      _ = n := by rw [card_erase_of_mem (by simp), card_range]; rfl
  have h3 := fib_ge_pow (s.deg x)
  have h4 : n < 2 ^ Nat.size n := Nat.lt_size_self n
  have h5 : 2 ^ (s.deg x / 2) < 2 ^ Nat.size n := by omega
  have h6 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 h5
  omega

end Formalgo.Algorithms.ShortestPaths
