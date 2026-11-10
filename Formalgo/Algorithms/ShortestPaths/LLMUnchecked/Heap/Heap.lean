import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Model
import Mathlib.Data.Finset.Card

/-!
# Invariants of the Fibonacci heap

LLM-generated; not checked by a human.

`M` is the set of nodes in the heap. `Forest` describes the trees below the roots; the degree
condition may fail at one node `e` (in a cascade of cuts). `RootList` says the root array lists
the roots, except the loose roots `L` (taken out during consolidation).
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St

variable {R : Type*} [LinearOrder R]

/-- The siblings of `v` linked before it. -/
def older (s : StW R) (M : Finset ℕ) (v : ℕ) : ℕ :=
  (M.filter fun c => s.par c = s.par v ∧ s.lt c < s.lt v).card

/-- The trees of the heap. -/
structure Forest (s : StW R) (M : Finset ℕ) (e : ℕ) : Prop where
  zero : 0 ∉ M
  up : ∀ v ∈ M, s.par v ≠ 0 →
    s.par v ∈ M ∧ s.pos v < s.deg (s.par v) ∧ s.ch (s.par v) (s.pos v) = v
  down : ∀ x ∈ M, ∀ j < s.deg x, s.ch x j ∈ M ∧ s.par (s.ch x j) = x ∧ s.pos (s.ch x j) = j
  order : ∀ v ∈ M, s.par v ≠ 0 → s.key (s.par v) ≤ s.key v
  height : ∀ v ∈ M, s.par v ≠ 0 → s.ht v < s.ht (s.par v)
  fib : ∀ v ∈ M, s.par v ≠ 0 → v ≠ e → older s M v ≤ s.deg v + s.mark v
  ltinj : ∀ v ∈ M, ∀ w ∈ M, s.par v ≠ 0 → s.par w = s.par v → s.lt w = s.lt v → w = v
  ltclock : ∀ v ∈ M, s.par v ≠ 0 → s.lt v < s.clock
  mark : ∀ v ∈ M, s.mark v ≤ 1

/-- The root array lists the roots not in `L`. -/
structure RootList (s : StW R) (M L : Finset ℕ) : Prop where
  loose : ∀ v ∈ L, v ∈ M ∧ s.par v = 0
  list : ∀ j < s.deg 0, s.ch 0 j ∈ M ∧ s.ch 0 j ∉ L ∧ s.par (s.ch 0 j) = 0 ∧ s.pos (s.ch 0 j) = j
  root : ∀ v ∈ M, s.par v = 0 → v ∉ L → s.pos v < s.deg 0 ∧ s.ch 0 (s.pos v) = v

variable {s s' : StW R} {M L : Finset ℕ} {e : ℕ}

/-! ### Changing fields the invariants do not see -/

theorem Forest.congr (h : Forest s M e) (hpar : s'.par = s.par) (hlt : s'.lt = s.lt)
    (hclock : s'.clock = s.clock) (hht : s'.ht = s.ht)
    (hdeg : ∀ x ∈ M, s'.deg x = s.deg x) (hch : ∀ x ∈ M, s'.ch x = s.ch x)
    (hkey : ∀ x ∈ M, s'.key x = s.key x) (hmark : ∀ x ∈ M, s'.mark x = s.mark x)
    (hpos : ∀ v ∈ M, s.par v ≠ 0 → s'.pos v = s.pos v) : Forest s' M e := by
  have hold : ∀ v, older s' M v = older s M v := by intro v; simp [older, hpar, hlt]
  refine ⟨h.zero, fun v hv hp => ?_, fun x hx j hj => ?_, fun v hv hp => ?_, fun v hv hp => ?_,
    fun v hv hp he => ?_, fun v hv w hw hp => ?_, fun v hv hp => ?_, fun v hv => ?_⟩
  · rw [hpar] at hp ⊢
    obtain ⟨h1, h2, h3⟩ := h.up v hv hp
    rw [hpos v hv hp, hdeg _ h1, hch _ h1]; exact ⟨h1, h2, h3⟩
  · rw [hdeg x hx] at hj
    obtain ⟨h1, h2, h3⟩ := h.down x hx j hj
    rw [hch x hx, hpar, hpos _ h1 (by rw [h2]; exact fun h0 => h.zero (h0 ▸ hx))]
    exact ⟨h1, h2, h3⟩
  · rw [hpar] at hp ⊢; rw [hkey _ (h.up v hv hp).1, hkey v hv]; exact h.order v hv hp
  · rw [hpar] at hp ⊢; rw [hht]; exact h.height v hv hp
  · rw [hpar] at hp; rw [hold, hdeg v hv, hmark v hv]; exact h.fib v hv hp he
  · rw [hpar] at hp ⊢; rw [hlt]; exact h.ltinj v hv w hw hp
  · rw [hpar] at hp; rw [hlt, hclock]; exact h.ltclock v hv hp
  · rw [hmark v hv]; exact h.mark v hv

omit [LinearOrder R] in
theorem RootList.congr (h : RootList s M L) (hpar : ∀ v ∈ M, s'.par v = s.par v)
    (hdeg : s'.deg 0 = s.deg 0) (hch : s'.ch 0 = s.ch 0)
    (hpos : ∀ v ∈ M, s.par v = 0 → s'.pos v = s.pos v) : RootList s' M L := by
  refine ⟨fun v hv => ?_, fun j hj => ?_, fun v hv hp hL => ?_⟩
  · obtain ⟨h1, h2⟩ := h.loose v hv; exact ⟨h1, by rw [hpar v h1, h2]⟩
  · rw [hdeg] at hj; rw [hch]
    obtain ⟨h1, h2, h3, h4⟩ := h.list j hj
    exact ⟨h1, h2, by rw [hpar _ h1, h3], by rw [hpos _ h1 h3, h4]⟩
  · rw [hpar v hv] at hp
    rw [hpos v hv hp, hdeg, hch]; exact h.root v hv hp hL

/-- The exception does not matter at a root. -/
theorem Forest.of_root (h : Forest s M e) (he : s.par e = 0) : Forest s M 0 :=
  { h with fib := fun v hv hp _ => h.fib v hv hp (by rintro rfl; exact hp he) }

theorem Forest.any (h : Forest s M 0) (e : ℕ) : Forest s M e :=
  { h with fib := fun v hv hp _ => h.fib v hv hp (by rintro rfl; exact h.zero hv) }

/-! ### Children -/

/-- A node has as many children as its degree. -/
theorem Forest.card_children (h : Forest s M e) {x : ℕ} (hx : x ∈ M) :
    (M.filter fun c => s.par c = x).card = s.deg x := by
  have : (M.filter fun c => s.par c = x) = (Finset.range (s.deg x)).image (s.ch x) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hc, rfl⟩
      have hp : s.par c ≠ 0 := fun h0 => h.zero (h0 ▸ hx)
      exact ⟨s.pos c, (h.up c hc hp).2.1, (h.up c hc hp).2.2⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(h.down x hx j hj).1, (h.down x hx j hj).2.1⟩
  rw [this, Finset.card_image_of_injOn]
  · simp
  · intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rw [← (h.down x hx i hi).2.2, ← (h.down x hx j hj).2.2, hij]

end Formalgo.Algorithms.ShortestPaths
