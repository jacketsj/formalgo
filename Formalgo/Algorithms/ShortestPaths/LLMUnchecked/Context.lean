import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Dijkstra.DijkstraFinish
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.IO

/-!
# The model's data for an input

LLM-generated; not checked by a human.

Edge `i` of the code gives the half-edges `u → v` and `v → u`, each put at the front of its
vertex's list, so a list holds its half-edges latest first.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

/-- The capacity of a child array: twice the bit length of `n`. -/
def Dn (n : ℕ) : ℕ := 2 * Nat.size n

/-- The half-edges `(source id, target id, weight)`, in the order they are added. -/
noncomputable def halves (x : EInput) : List (ℕ × ℕ × ℕ) :=
  (lexEdges x.wg.graph).flatMap fun e =>
    [((e.1 : ℕ) + 1, (e.2 : ℕ) + 1, x.wg.weight s(e.1, e.2)),
      ((e.2 : ℕ) + 1, (e.1 : ℕ) + 1, x.wg.weight s(e.1, e.2))]

/-- The adjacency list of vertex id `a`. -/
noncomputable def adjX (x : EInput) (a : ℕ) : List (ℕ × ℕ) :=
  ((halves x).reverse.filter fun h => h.1 = a).map fun h => (h.2.1, h.2.2)

/-- The model's data for an input. -/
noncomputable def ctxX (x : EInput) : Ctx :=
  ⟨x.wg.n, Dn x.wg.n, x.wg.n + Dn x.wg.n + 2 * numEdges x + 2, adjX x⟩

theorem ctxOK (x : EInput) : CtxOK (ctxX x) := ⟨rfl, by simp [ctxX]; omega⟩

theorem length_halves (x : EInput) : (halves x).length = 2 * numEdges x := by
  simp only [halves, numEdges, List.length_flatMap, List.length_cons, List.length_nil]
  induction (lexEdges x.wg.graph) <;> simp_all; omega

theorem mem_halves {x : EInput} {h : ℕ × ℕ × ℕ} : h ∈ halves x ↔ ∃ a b : Fin x.wg.n,
    (a, b) ∈ lexEdges x.wg.graph ∧ (h = ((a : ℕ) + 1, (b : ℕ) + 1, x.wg.weight s(a, b)) ∨
      h = ((b : ℕ) + 1, (a : ℕ) + 1, x.wg.weight s(a, b))) := by
  simp only [halves, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false, Prod.exists]

theorem mem_adjX {x : EInput} {a : ℕ} {p : ℕ × ℕ} :
    p ∈ adjX x a ↔ ∃ h ∈ halves x, h.1 = a ∧ p = (h.2.1, h.2.2) := by
  simp only [adjX, List.mem_map, List.mem_filter, List.mem_reverse, decide_eq_true_eq]
  constructor
  · rintro ⟨h, ⟨hm, ha⟩, rfl⟩; exact ⟨h, hm, ha, rfl⟩
  · rintro ⟨h, hm, ha, rfl⟩; exact ⟨h, ⟨hm, ha⟩, rfl⟩

theorem weight_le_codeMax (x : EInput) {a b : Fin x.wg.n} (h : (a, b) ∈ lexEdges x.wg.graph) :
    x.wg.weight s(a, b) ≤ codeMax (ncode x) :=
  le_codeMax (by
    rw [ncode_input_eq]
    simp only [List.mem_append, List.mem_cons, List.mem_map]
    exact .inl (.inr ⟨(a, b), h, rfl⟩))

theorem adjOK (x : EInput) : AdjOK (ctxX x) x.wg (codeMax (ncode x)) := by
  refine ⟨rfl, fun u p hp => ?_, fun u v huv => ?_, fun a p hp => ?_, fun a => ?_⟩
  · obtain ⟨h, hm, ha, rfl⟩ := mem_adjX.1 hp
    obtain ⟨a, b, hab, rfl | rfl⟩ := mem_halves.1 hm
    · have : a = u := Fin.ext (by simp at ha; omega)
      subst this
      exact ⟨b, (mem_edges.1 hab).2, rfl⟩
    · have : b = u := Fin.ext (by simp at ha; omega)
      subst this
      exact ⟨a, (mem_edges.1 hab).2.symm, by simp [Sym2.eq_swap]⟩
  · refine mem_adjX.2 ?_
    rcases lt_or_gt_of_ne (fun h : u = v => huv.ne h) with hlt | hlt
    · exact ⟨_, mem_halves.2 ⟨u, v, mem_edges.2 ⟨hlt, huv⟩, .inl rfl⟩, rfl, rfl⟩
    · exact ⟨_, mem_halves.2 ⟨v, u, mem_edges.2 ⟨hlt, huv.symm⟩, .inr rfl⟩, rfl,
        by simp [Sym2.eq_swap]⟩
  · obtain ⟨h, hm, _, rfl⟩ := mem_adjX.1 hp
    obtain ⟨a, b, hab, rfl | rfl⟩ := mem_halves.1 hm <;> exact weight_le_codeMax x hab
  · change (adjX x a).length ≤ x.wg.n + Dn x.wg.n + 2 * numEdges x + 2
    have : (adjX x a).length ≤ (halves x).length := by
      simp only [adjX, List.length_map]
      exact (List.length_filter_le _ _).trans (by simp)
    rw [length_halves] at this; omega

/-- Splitting a list by its first components. -/
theorem sum_filter_length {β : Type*} (S : Finset ℕ) :
    ∀ L : List (ℕ × β), (∀ h ∈ L, h.1 ∈ S) →
      ∑ a ∈ S, (L.filter fun h => h.1 = a).length = L.length
  | [], _ => by simp
  | h :: L, hL => by
    have ih := sum_filter_length S L fun h' hh' => hL h' (List.mem_cons_of_mem _ hh')
    simp only [List.filter_cons, List.length_cons]
    rw [← ih]
    have : ∀ a, (if decide (h.1 = a) = true then (h :: L.filter fun h => h.1 = a)
        else L.filter fun h => h.1 = a).length =
        (if h.1 = a then 1 else 0) + (L.filter fun h => h.1 = a).length := by
      intro a; by_cases ha : h.1 = a <;> simp [ha]; omega
    rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_add_distrib,
      Finset.sum_ite_eq S h.1 (fun _ => 1), if_pos (hL h (List.mem_cons_self))]
    omega

theorem sum_adjX (x : EInput) :
    ∑ a ∈ Finset.range (x.wg.n + 1), (adjX x a).length = 2 * numEdges x := by
  rw [← length_halves, ← List.length_reverse]
  have := sum_filter_length (Finset.range (x.wg.n + 1)) (halves x).reverse (fun h hh => by
    rw [List.mem_reverse] at hh
    obtain ⟨a, b, _, rfl | rfl⟩ := mem_halves.1 hh <;> simp)
  rw [← this]
  simp only [adjX, List.length_map]

end Formalgo.Algorithms.ShortestPaths
