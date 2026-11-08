import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.IO
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunConv

/-!
# The statement's codes on the tape

LLM-generated; not checked by a human.

The input `⟨n, G, weight, source⟩` is written as `n`, then `n` and, for each vertex, its degree and
its neighbours in increasing order, then the number of edges and the weights in lexicographic order
of the edges, then the source. The output `⟨n, d⟩` is written as `n, n, d 0, …, d (n - 1)`.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked

/-! ### Sorting `Fin n` -/

theorem sort_univ_fin (n : ℕ) :
    (Set.finite_univ.toFinset : Finset (Fin n)).sort = List.finRange n := by
  rw [Set.Finite.toFinset_univ]; exact Fin.sort_univ n

theorem position_fin {n : ℕ} (a : Fin n) : Code.position a = a.val := by
  unfold Code.position
  rw [sort_univ_fin]; exact List.idxOf_finRange a

open Classical in
theorem sort_set_fin {n : ℕ} (s : Set (Fin n)) :
    s.toFinite.toFinset.sort = (List.finRange n).filter (· ∈ s) := by
  refine List.SortedLT.eq_of_mem_iff (Finset.sortedLT_sort _)
    (List.sortedLT_iff_pairwise.2 ((List.sortedLT_iff_pairwise.1 (List.sortedLT_finRange n)).filter
      _)) fun a => ?_
  simp

/-! ### Codes as tuples -/

/-- The neighbours of `u`, in increasing order. -/
noncomputable def nbrs {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) : List ℕ :=
  ((List.finRange n).filter fun v =>
    @decide (v ∈ G.neighborSet u) (Classical.propDecidable _)).map Fin.val

/-- The neighbours of each vertex. -/
noncomputable def nbrLists {n : ℕ} (G : SimpleGraph (Fin n)) : List (List ℕ) :=
  (List.finRange n).map (nbrs G)

/-- The weights, in increasing order of the edges. -/
noncomputable def wts (x : Input) : List ℕ :=
  ((Set.finite_univ.toFinset : Finset (Edges x.2.1)).sort).map x.2.2.1

/-- The parts of the code of an input. -/
noncomputable def inT (x : Input) : ℕ × List (List ℕ) × List ℕ × ℕ :=
  (x.1, nbrLists x.2.1, wts x, x.2.2.2)

section Encode

variable {V : Type*} [Code ℕ V]

theorem encode_set_fin {n : ℕ} (s : Set (Fin n)) :
    (Code.encode s : List V) = Code.encode
      (((List.finRange n).filter (fun v => @decide (v ∈ s) (Classical.propDecidable _))).map
        Fin.val) := by
  change (Code.encode (s.toFinite.toFinset.sort.map Code.position) : List V) = _
  rw [sort_set_fin]
  congr 1
  exact List.map_congr_left fun a _ => position_fin a

theorem encode_graph_fin {n : ℕ} (G : SimpleGraph (Fin n)) :
    (Code.encode G : List V) = Code.encode (nbrLists G) := by
  change (Code.encode (((Set.finite_univ.toFinset : Finset (Fin n)).sort).map
    G.neighborSet) : List V) = _
  rw [sort_univ_fin]
  change (Code.encode ((List.finRange n).map G.neighborSet).length : List V) ++
      ((List.finRange n).map G.neighborSet).flatMap (Code.encode (Value := V)) =
    (Code.encode (nbrLists G).length : List V) ++ (nbrLists G).flatMap (Code.encode (Value := V))
  simp only [nbrLists, List.length_map, List.flatMap_map]
  congr 1
  exact List.flatMap_congr fun u _ => encode_set_fin (G.neighborSet u)

theorem encode_input (x : Input) : (Code.encode x : List V) = Code.encode (inT x) := by
  obtain ⟨n, G, w, s⟩ := x
  change (Code.encode n : List V) ++ ((Code.encode G : List V) ++
      ((Code.encode (wts ⟨n, G, w, s⟩) : List V) ++ (Code.encode s : List V))) =
    (Code.encode n : List V) ++ ((Code.encode (nbrLists G) : List V) ++
      ((Code.encode (wts ⟨n, G, w, s⟩) : List V) ++ (Code.encode s : List V)))
  rw [encode_graph_fin]

theorem encode_output (y : Σ n, Fin n → ℕ∞) :
    (Code.encode y : List V) = Code.encode (y.1, (List.finRange y.1).map y.2) := by
  obtain ⟨n, d⟩ := y
  change (Code.encode n : List V) ++
    (Code.encode (((Set.finite_univ.toFinset : Finset (Fin n)).sort).map d) : List V) = _
  rw [sort_univ_fin]; rfl

end Encode

theorem ncode_input (x : Input) : ncode x = ncode (inT x) := encode_input x

theorem wcode_input (w : ℕ) (x : Input) : wcode w x = wcode w (inT x) := encode_input x

theorem ncode_out (y : Σ n, Fin n → ℕ∞) : ncode y = ncode (y.1, (List.finRange y.1).map y.2) :=
  encode_output y

theorem wcode_out (w : ℕ) (y : Σ n, Fin n → ℕ∞) :
    wcode w y = wcode w (y.1, (List.finRange y.1).map y.2) := encode_output y

/-! ### Decoding -/

section Decode

variable {V : Type*}

theorem decode_sigma {α : Type*} {β : α → Type*} [Code α V] [∀ a, Code (β a) V] (s : ℕ → V) :
    (Code.decode s : (Σ a, β a) × _) =
      (⟨(Code.decode s : α × _).1, (Code.decode (Code.decode s : α × _).2 : β _ × _).1⟩,
        (Code.decode (Code.decode s : α × _).2 : β (Code.decode s : α × _).1 × _).2) := rfl

theorem decodeMany_snd {α β : Type*} [Code α V] [Code β V]
    (h : ∀ s : ℕ → V, (Code.decode s : α × _).2 = (Code.decode s : β × _).2) :
    ∀ (k : ℕ) (s : ℕ → V),
      (Code.decodeMany k s : List α × _).2 = (Code.decodeMany k s : List β × _).2
  | 0, _ => rfl
  | k + 1, s => by
    change (Code.decodeMany k (Code.decode s : α × _).2 : List α × _).2 =
      (Code.decodeMany k (Code.decode s : β × _).2 : List β × _).2
    rw [h]; exact decodeMany_snd h k _

variable [Code ℕ V]

theorem decode_graph_snd {n : ℕ} (s : ℕ → V) :
    (Code.decode s : SimpleGraph (Fin n) × _).2 = (Code.decode s : List (List ℕ) × _).2 := by
  change (Code.decodeMany (Code.decode s : ℕ × _).1 (Code.decode s : ℕ × _).2 :
      List (Set (Fin n)) × _).2 = (Code.decodeMany (Code.decode s : ℕ × _).1
      (Code.decode s : ℕ × _).2 : List (List ℕ) × _).2
  exact decodeMany_snd (α := Set (Fin n)) (β := List ℕ) (fun _ => rfl) _ _

theorem decode_rest_snd {n : ℕ} (s : ℕ → V) :
    (Code.decode s : (Σ G : SimpleGraph (Fin n), (Edges G → ℕ) × ℕ) × _).2 =
      (Code.decode s : (List (List ℕ) × List ℕ × ℕ) × _).2 := by
  rw [decode_sigma (V := V) (α := SimpleGraph (Fin n)) (β := fun G => (Edges G → ℕ) × ℕ) s,
    decode_prod (α := List (List ℕ)) (β := List ℕ × ℕ) s,
    decode_prod (α := List ℕ) (β := ℕ) (V := V)]
  change (Code.decode (Code.decode (Code.decode s : SimpleGraph (Fin n) × (ℕ → V)).2 :
      List ℕ × (ℕ → V)).2 : ℕ × (ℕ → V)).2 = _
  rw [decode_graph_snd]

end Decode

theorem fits_input {w : ℕ} {x : Input} : Fits w x ↔ Fits w (inT x) := by
  unfold Fits; rw [ncode_input]

theorem layout_inT (x : Input) : Layout (inT x) :=
  (layout_nat _).prod ((layout_list fun _ _ => layout_list fun _ _ => layout_nat _).prod
    ((layout_list fun _ _ => layout_nat _).prod (layout_nat _)))

theorem layout_input (x : Input) : Layout x := fun w hw hf => by
  rw [wcode_input, ncode_input]; exact layout_inT x w hw (fits_input.1 hf)

theorem readsBack_inT (x : Input) : ReadsBack (inT x) :=
  (readsBack_nat _).prod ((readsBack_list fun _ _ => readsBack_list fun _ _ => readsBack_nat _).prod
    ((readsBack_list fun _ _ => readsBack_nat _).prod (readsBack_nat _)))

theorem skips_input (x : Input) : Skips x := fun w hw hf s hs => by
  rw [fits_input] at hf
  rw [wcode_input] at hs ⊢
  have h := (readsBack_inT x).skips w hw hf s hs
  rw [decode_prod] at h
  rw [decode_sigma (V := BitVec w) (α := ℕ)
    (β := fun n => Σ G : SimpleGraph (Fin n), (Edges G → ℕ) × ℕ) s]
  change (Code.decode (Code.decode s : ℕ × _).2 :
    (Σ G : SimpleGraph (Fin (Code.decode s : ℕ × _).1), (Edges G → ℕ) × ℕ) × _).2 = _
  rw [decode_rest_snd]
  exact h

theorem fits_out {w : ℕ} {y : Σ n, Fin n → ℕ∞} :
    Fits w y ↔ Fits w (y.1, (List.finRange y.1).map y.2) := by
  unfold Fits; rw [ncode_out]

theorem layout_out (y : Σ n, Fin n → ℕ∞) : Layout y := fun w hw hf => by
  rw [wcode_out, ncode_out]
  exact ((layout_nat _).prod (layout_output _)) w hw (fits_out.1 hf)

theorem readsBack_out (y : Σ n, Fin n → ℕ∞) : ReadsBack y := fun w hw hf s hs => by
  obtain ⟨n, d⟩ := y
  rw [fits_out, fits_prod] at hf
  rw [wcode_out, wcode_prod] at hs ⊢
  have h₁ := readsBack_nat n w hw hf.1 s hs.append_left
  have h₂ := readsBack_output ((List.finRange n).map d) w hw hf.2 _ hs.append_right
  rw [decode_sigma (V := BitVec w) (α := ℕ) (β := fun n => Fin n → ℕ∞) s, h₁]
  change ((⟨n, fun a => ((Code.decode (fun i => s (i + (wcode w n).length)) :
      List ℕ∞ × (ℕ → BitVec w)).1).getD (Code.position a) default⟩ : Σ n, Fin n → ℕ∞),
    (Code.decode (fun i => s (i + (wcode w n).length)) : List ℕ∞ × (ℕ → BitVec w)).2) = _
  rw [h₂]
  refine Prod.ext ?_ ?_
  · simp only
    congr 1
    funext a
    rw [position_fin]
    simp
  · funext i
    simp only [List.length_append]
    congr 1
    omega

/-! ### The tape -/

theorem flatMap_ncode_blk (bs : List (List ℕ)) : bs.flatMap ncode = bs.flatMap blk :=
  List.flatMap_congr fun b _ => by rw [ncode_list, flatMap_ncode_nats]; rfl

theorem ncode_input_tape (x : Input) : ncode x = x.1 :: x.1 ::
    ((nbrLists x.2.1).flatMap blk ++ (wts x).length :: (wts x ++ [x.2.2.2])) := by
  rw [ncode_input]
  simp only [inT, ncode_prod, ncode_nat, ncode_list, flatMap_ncode_nats, flatMap_ncode_blk]
  simp [nbrLists]

theorem emitAll_eq (bs : List (List ℕ)) (u : ℕ) :
    emitAll bs u = (List.range bs.length).flatMap fun i => pairsAbove (u + i) (bs.getD i []) := by
  induction bs generalizing u with
  | nil => rfl
  | cons b bs ih =>
    rw [emitAll, ih, List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    exact List.flatMap_congr fun i _ => by rw [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 i]

theorem nbrLists_getD {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    (nbrLists G).getD u.val [] = nbrs G u := by
  simp [nbrLists, List.getD_eq_getElem?_getD]

theorem pairsAbove_nbrs {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    pairsAbove u.val (nbrs G u) = (((List.finRange n).filter fun v =>
      @decide (u < v ∧ G.Adj u v) (Classical.propDecidable _)).map (u, ·)).flatMap
        fun e => [(e.1 : ℕ), (e.2 : ℕ)] := by
  unfold pairsAbove nbrs
  rw [List.filter_map, List.flatMap_map, List.filter_filter, List.flatMap_map]
  congr 1
  refine List.filter_congr fun v _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Function.comp_apply,
    SimpleGraph.mem_neighborSet, Fin.lt_def]

theorem emitAll_nbr {n : ℕ} (G : SimpleGraph (Fin n)) :
    emitAll (nbrLists G) 0 = (edgesNat G).flatMap fun p => [p.1, p.2] := by
  rw [emitAll_eq, show (nbrLists G).length = n by simp [nbrLists],
    ← List.map_coe_finRange_eq_range, List.flatMap_map, edgesNat, List.flatMap_map, lexEdges,
    List.flatMap_assoc]
  refine List.flatMap_congr fun u _ => ?_
  rw [Nat.zero_add, nbrLists_getD, pairsAbove_nbrs]
  congr 1
  congr 1
  exact List.filter_congr fun w _ => by simp

theorem length_pairs (l : List (ℕ × ℕ)) : (l.flatMap fun p => [p.1, p.2]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [List.flatMap_cons, ih]; ring

/-! ### The weights in lexicographic order -/

theorem mem_lexEdges_map {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n ×ₗ Fin n) :
    p ∈ (lexEdges G).map toLex ↔ p ∈ Edges G := by
  constructor
  · rintro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact mem_edges.1 he
  · intro h
    exact List.mem_map.2 ⟨ofLex p, mem_edges.2 h, rfl⟩

theorem pairwise_lexEdges {n : ℕ} (G : SimpleGraph (Fin n)) :
    ((lexEdges G).map toLex).Pairwise (· < ·) := by
  have hfr := List.sortedLT_iff_pairwise.1 (List.sortedLT_finRange n)
  unfold lexEdges
  rw [List.map_flatMap, List.pairwise_flatMap]
  refine ⟨fun u _ => ?_, hfr.imp fun {u u'} huu' => ?_⟩
  · rw [List.map_map, List.pairwise_map]
    refine (hfr.filter _).imp ?_
    intro v v' h
    exact Prod.Lex.toLex_lt_toLex.2 (.inr ⟨rfl, h⟩)
  · intro a ha b hb
    simp only [List.map_map, List.mem_map, Function.comp_apply] at ha hb
    obtain ⟨v, -, rfl⟩ := ha
    obtain ⟨v', -, rfl⟩ := hb
    exact Prod.Lex.toLex_lt_toLex.2 (.inl huu')

theorem sort_edges_val {n : ℕ} (G : SimpleGraph (Fin n)) :
    ((Set.finite_univ.toFinset : Finset (Edges G)).sort).map Subtype.val =
      (lexEdges G).map toLex := by
  refine List.SortedLT.eq_of_mem_iff ?_ (List.sortedLT_iff_pairwise.2 (pairwise_lexEdges G))
    fun p => ?_
  · refine List.sortedLT_iff_pairwise.2 ?_
    rw [List.pairwise_map]
    exact (List.sortedLT_iff_pairwise.1 (Finset.sortedLT_sort _)).imp fun h => h
  · rw [mem_lexEdges_map]
    simp only [List.mem_map, Finset.mem_sort, Set.Finite.mem_toFinset, Set.mem_univ, true_and]
    exact ⟨fun ⟨q, hq⟩ => hq ▸ q.2, fun h => ⟨⟨p, h⟩, rfl⟩⟩

theorem toE_weight (x : Input) {e : Fin x.1 × Fin x.1} (he : e ∈ lexEdges x.2.1) :
    (toE x).wg.weight s(e.1, e.2) = x.2.2.1 ⟨toLex e, mem_edges.1 he⟩ := by
  have he' := mem_edges.1 he
  refine (wg_weight (toE x) (e := s(e.1, e.2)) he'.2).trans ?_
  change lexW x.2.2.1 s(e.1, e.2) = _
  exact (lexW_eq x.2.2.1 he'.2).trans (dif_pos he'.1)

theorem wts_eq (x : Input) :
    (lexEdges (toE x).wg.graph).map (fun e => (toE x).wg.weight s(e.1, e.2)) = wts x := by
  classical
  obtain ⟨n, G, w, src⟩ := x
  let wf : Fin n ×ₗ Fin n → ℕ := fun p => if h : p ∈ Edges G then w ⟨p, h⟩ else 0
  have h1 : wts ⟨n, G, w, src⟩ = (lexEdges G).map (wf ∘ toLex) := by
    have : wts ⟨n, G, w, src⟩ = (((Set.finite_univ.toFinset : Finset (Edges G)).sort).map
        Subtype.val).map wf := by
      rw [List.map_map]
      exact List.map_congr_left fun e _ => by
        simp only [Function.comp_apply, wf, dif_pos e.2, Subtype.coe_eta]
    rw [this, sort_edges_val, List.map_map]
  rw [h1]
  refine List.map_congr_left fun (e : Fin n × Fin n) he => ?_
  have h2 : toLex e ∈ Edges G := mem_edges.1 he
  refine (toE_weight ⟨n, G, w, src⟩ he).trans ?_
  simp only [Function.comp_apply, wf]
  rw [dif_pos h2]

theorem length_wts (x : Input) : (wts x).length = (lexEdges (toE x).wg.graph).length := by
  rw [← wts_eq, List.length_map]

theorem ncode_toE (x : Input) : ncode (toE x) = x.1 :: (wts x).length ::
    (emitAll (nbrLists x.2.1) 0 ++ (wts x).length :: (wts x ++ [x.2.2.2])) := by
  rw [ncode_input_eq, ← wts_eq, emitAll_nbr]
  simp only [List.length_map, numEdges, List.cons_append, List.append_assoc, List.nil_append]
  rfl

theorem length_emitAll (x : Input) :
    (emitAll (nbrLists x.2.1) 0).length = 2 * (wts x).length := by
  rw [emitAll_nbr, length_pairs, length_wts, edgesNat, List.length_map]
  rfl

/-! ### The degree sum -/

theorem length_nbrs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    (nbrs G u).length = G.degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter, nbrs,
    List.length_map, ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext v
  simp

theorem length_blocks {n : ℕ} (G : SimpleGraph (Fin n)) :
    ((nbrLists G).flatMap blk).length = n + 2 * (lexEdges G).length := by
  classical
  have h : ((nbrLists G).flatMap blk).length = ∑ u, (G.degree u + 1) := by
    rw [Fin.sum_univ_def, List.length_flatMap, nbrLists, List.map_map]
    congr 1
    exact List.map_congr_left fun u _ => by simp [blk, length_nbrs]
  rw [h, Finset.sum_add_distrib, SimpleGraph.sum_degrees_eq_twice_card_edges, length_edges,
    ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  simp; ring

end Formalgo.Algorithms.ShortestPaths
