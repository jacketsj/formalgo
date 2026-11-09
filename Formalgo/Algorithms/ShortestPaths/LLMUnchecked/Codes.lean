import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Dijkstra.Dist
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Machine.CodeAlgorithm

/-!
# Codes of graphs and distances

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked

/-- The number written for a distance: the distance, or `0` for `⊤`. -/
def encDist (d : ℕ∞) : ℕ := d.toNat

theorem ncode_output (y : List ℕ∞) : ncode (y.map encDist) = y.length :: y.map encDist := by
  rw [ncode_list, List.length_map]; congr 1
  induction y with
  | nil => rfl
  | cons d y ih => rw [List.map_cons, List.flatMap_cons, ih]; rfl

/-! ### The edge list -/

section Edges

variable {n : ℕ} {G : SimpleGraph (Fin n)}

theorem nodup_edges : (lexEdges G).Nodup := by
  classical
  unfold lexEdges
  refine List.nodup_flatMap.2 ⟨fun u _ => ?_, ?_⟩
  · exact ((List.nodup_finRange n).filter _).map fun a b h => by simpa using h
  · refine (List.nodup_finRange n).pairwise_of_forall_ne fun a _ b _ hab => ?_
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro p ⟨v, _, rfl⟩ ⟨v', _, h⟩
    exact hab (congrArg Prod.fst h).symm

theorem length_edges : (lexEdges G).length = G.edgeSet.ncard := by
  classical
  have hinj : Set.InjOn (fun e : Fin n × Fin n => s(e.1, e.2)) {e | e ∈ lexEdges G} := by
    rintro ⟨a, b⟩ ha ⟨c, d⟩ hc h
    simp only [Set.mem_setOf_eq, mem_edges] at ha hc
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd (ha.1.trans hc.1) (lt_irrefl _)
  have himg : G.edgeSet = (fun e : Fin n × Fin n => s(e.1, e.2)) '' {e | e ∈ lexEdges G} := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [SimpleGraph.mem_edgeSet, Set.mem_image, Set.mem_setOf_eq, Prod.exists, mem_edges]
      constructor
      · intro hab
        rcases lt_trichotomy a b with h | h | h
        · exact ⟨a, b, ⟨h, hab⟩, rfl⟩
        · subst h; exact absurd hab (G.irrefl)
        · exact ⟨b, a, ⟨h, hab.symm⟩, Sym2.eq_swap⟩
      · rintro ⟨c, d, ⟨_, hcd⟩, h⟩
        rw [Sym2.eq_iff] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hcd
        · exact hcd.symm
  rw [himg, Set.ncard_image_of_injOn hinj,
    show {e | e ∈ lexEdges G} = ((lexEdges G).toFinset : Set (Fin n × Fin n)) by ext; simp,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup nodup_edges]

end Edges

/-- The weights in the code are those of the edges, in order. -/
theorem values_eq (x : EInput) : (edgeList x.graph).map x.weight =
    (lexEdges x.wg.graph).map fun e => x.wg.weight s(e.1, e.2) := by
  classical
  have key : ∀ l : List (Fin x.n × Fin x.n), (∀ e ∈ l, s(e.1, e.2) ∈ x.graph.edgeSet) →
      (l.filterMap fun e => if h : s(e.1, e.2) ∈ x.graph.edgeSet then
        some (⟨_, h⟩ : x.graph.edgeSet) else none).map x.weight =
      l.map fun e => x.wg.weight s(e.1, e.2) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons e l ih =>
      intro h
      have he := h e List.mem_cons_self
      rw [List.filterMap_cons, dif_pos he, List.map_cons, List.map_cons,
        ih fun a ha => h a (List.mem_cons_of_mem _ ha)]
      exact congrArg (· :: _) (wg_weight x he).symm
  refine key _ fun e he => ?_
  obtain ⟨u, v⟩ := e
  exact (SimpleGraph.mem_edgeSet _).2 (mem_edges.1 he).2

end Formalgo.Algorithms.ShortestPaths
