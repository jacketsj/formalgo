import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Dijkstra.Dist
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Machine.CodeAlgorithm

/-!
# Codes of graphs and distances

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked

/-- The edges of a graph as pairs of numbers. -/
noncomputable def edgesNat {n : ℕ} (G : SimpleGraph (Fin n)) : List (ℕ × ℕ) :=
  (Code.edges G).map fun e => ((e.1 : ℕ), (e.2 : ℕ))

theorem layout_graph (G : Σ n, SimpleGraph (Fin n)) : Layout G :=
  (layout_nat G.1).prod (layout_list fun p _ => (layout_nat p.1).prod (layout_nat p.2))

theorem readsBack_graphCode (G : Σ n, SimpleGraph (Fin n)) : ReadsBack (G.1, edgesNat G.2) :=
  (readsBack_nat G.1).prod (readsBack_list fun p _ => (readsBack_nat p.1).prod (readsBack_nat p.2))

theorem skips_graph (G : Σ n, SimpleGraph (Fin n)) : Skips G :=
  fun w hw hf s hs => (readsBack_graphCode G).skips w hw hf s hs

/-- The parts of the code of an input. -/
noncomputable def inTuple (x : Input) : ((Σ n, SimpleGraph (Fin n)) × List ℕ) × ℕ :=
  ((⟨x.n, x.graph⟩, (edgeList x.graph).map x.weight), x.source)

theorem encode_input {Value : Type*} [Code ℕ Value] (x : Input) :
    (Code.encode x : List Value) = Code.encode (inTuple x) := rfl

theorem decode_input {Value : Type*} [Code ℕ Value] (s : ℕ → Value) :
    (Code.decode s : Input × _).2 =
      (Code.decode s : (((Σ n, SimpleGraph (Fin n)) × List ℕ) × ℕ) × _).2 := rfl

theorem layout_input (x : Input) : Layout x := fun w hw hf => by
  have hp : Layout (inTuple x) := ((layout_graph ⟨x.n, x.graph⟩).prod
    (layout_list fun v _ => layout_nat v)).prod (layout_nat x.source)
  have e : ncode x = ncode (inTuple x) := encode_input x
  have e' : wcode w x = wcode w (inTuple x) := encode_input x
  rw [e', e]
  exact hp w hw fun v hv => hf v (by rw [e]; exact hv)

theorem skips_input (x : Input) : Skips x := fun w hw hf s hs => by
  have hp : Skips (inTuple x) := ((skips_graph ⟨x.n, x.graph⟩).prod
    (readsBack_list (α := ℕ) fun v _ => readsBack_nat v).skips).prod
    (readsBack_nat x.source).skips
  have e : ncode x = ncode (inTuple x) := encode_input x
  have e' : wcode w x = wcode w (inTuple x) := encode_input x
  rw [decode_input, e']
  exact hp w hw (fun v hv => hf v (by rw [e]; exact hv)) s (by rw [← e']; exact hs)

/-- The number writing a distance. -/
def encDist (d : ℕ∞) : ℕ := if d = ⊤ then 0 else d.toNat + 1

theorem ncode_enat (d : ℕ∞) : ncode d = [encDist d] := rfl

theorem layout_enat (d : ℕ∞) : Layout d := layout_nat (encDist d)

theorem readsBack_enat (d : ℕ∞) : ReadsBack d := fun w hw hf s hs => by
  have h := readsBack_nat (encDist d) w hw hf s hs
  show (let (k, stream) : ℕ × _ := Code.decode s
    (if k = 0 then ⊤ else ((k - 1 : ℕ) : ℕ∞), stream)) = _
  rw [h]
  refine Prod.ext ?_ rfl
  induction d using ENat.recTopCoe with
  | top => simp [encDist]
  | coe d => simp [encDist]

theorem layout_output (y : List ℕ∞) : Layout y := layout_list fun d _ => layout_enat d

theorem readsBack_output (y : List ℕ∞) : ReadsBack y := readsBack_list fun d _ => readsBack_enat d

theorem ncode_output (y : List ℕ∞) : ncode y = y.length :: y.map encDist := by
  rw [ncode_list]; congr 1
  induction y with
  | nil => rfl
  | cons d y ih => rw [List.flatMap_cons, ih, ncode_enat]; rfl

/-! ### The edge list -/

section Edges

variable {n : ℕ} {G : SimpleGraph (Fin n)}

theorem mem_edges {u v : Fin n} : (u, v) ∈ Code.edges G ↔ u < v ∧ G.Adj u v := by
  classical
  unfold Code.edges
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨u', v', ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨u, v, ⟨h1, h2⟩, rfl, rfl⟩

theorem nodup_edges : (Code.edges G).Nodup := by
  classical
  unfold Code.edges
  refine List.nodup_flatMap.2 ⟨fun u _ => ?_, ?_⟩
  · exact ((List.nodup_finRange n).filter _).map fun a b h => by simpa using h
  · refine (List.nodup_finRange n).pairwise_of_forall_ne fun a _ b _ hab => ?_
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro p ⟨v, _, rfl⟩ ⟨v', _, h⟩
    exact hab (congrArg Prod.fst h).symm

theorem length_edges : (Code.edges G).length = G.edgeSet.ncard := by
  classical
  have hinj : Set.InjOn (fun e : Fin n × Fin n => s(e.1, e.2)) {e | e ∈ Code.edges G} := by
    rintro ⟨a, b⟩ ha ⟨c, d⟩ hc h
    simp only [Set.mem_setOf_eq, mem_edges] at ha hc
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd (ha.1.trans hc.1) (lt_irrefl _)
  have himg : G.edgeSet = (fun e : Fin n × Fin n => s(e.1, e.2)) '' {e | e ∈ Code.edges G} := by
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
    show {e | e ∈ Code.edges G} = ((Code.edges G).toFinset : Set (Fin n × Fin n)) by ext; simp,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup nodup_edges]

end Edges

/-- The weights in the code are those of the edges, in order. -/
theorem values_eq (x : Input) : (edgeList x.graph).map x.weight =
    (Code.edges x.wg.graph).map fun e => x.wg.weight s(e.1, e.2) := by
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
