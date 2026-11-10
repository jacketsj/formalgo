import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunCore
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.InputCode
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Size

/-!
# Proof that a TD word RAM finds shortest paths in `O(E + V log V)` steps

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Function

/-- The distances from the source, or `⊤` everywhere if it is not a vertex. -/
noncomputable def spf (x : EInput) : List ℕ∞ :=
  if h : x.source < x.wg.n then List.ofFn (x.wg.dist ⟨x.source, h⟩)
  else List.replicate x.wg.n ⊤

theorem length_spf (x : EInput) : (spf x).length = x.wg.n := by
  unfold spf; split <;> simp

/-- The numbers the core writes for the distances. -/
noncomputable def spo (x : EInput) : List ℕ := (spf x).map encDist

/-- The memory the core uses from `A`. -/
noncomputable def needF (x : EInput) : ℕ :=
  let n := x.wg.n; let E := numEdges x
  (3 * E + 4) + 10 * (n + Dn n + 3) + 6 * E + (n + 1) + n * (Dn n + 1) + 1 +
    (codeMax (ncode x) + 1) * (codeMax (ncode x) + 1)

/-- The steps of the core, up to the constant. -/
noncomputable def coreTime (x : EInput) : ℕ :=
  2000 * (numEdges x + x.wg.n * (Dn x.wg.n + 1) + 1)

theorem n_le_codeMax' (x : EInput) : x.wg.n ≤ codeMax (ncode x) :=
  le_codeMax (by rw [ncode_input_eq]; simp)

theorem encDist_le (x : EInput) : ∀ d ∈ spf x,
    encDist d ≤ codeMax (ncode x) * codeMax (ncode x) + 1 := by
  intro d hd
  unfold spf at hd
  split_ifs at hd with hs
  · obtain ⟨v, rfl⟩ := List.mem_ofFn.1 hd
    obtain ⟨hI, _, hout, _⟩ := finish_spec (ctxOK x) (adjOK x) hs
    rw [← hout v]
    unfold outVal
    split_ifs with hst
    · have h1 := hI.kb ((v : ℕ) + 1) (by rw [hst]; omega)
      have h2 := card_done_le x.wg.n (finish (ctxX x) x.source)
      have h3 := Nat.mul_le_mul_right (codeMax (ncode x)) (h2.trans (n_le_codeMax' x))
      omega
    · omega
  · rw [List.eq_of_mem_replicate hd]; simp [encDist]

/-! ### Bounds -/

theorem ncode_spf (x : EInput) : ncode (spo x) = x.wg.n :: (spf x).map encDist := by
  rw [spo, ncode_output, length_spf]

theorem n_le_codeMax (x : EInput) : x.wg.n ≤ codeMax (ncode x) :=
  le_codeMax (by rw [ncode_input_eq]; simp)

theorem E_le_codeMax (x : EInput) : numEdges x ≤ codeMax (ncode x) :=
  le_codeMax (by rw [ncode_input_eq]; simp)

theorem size_le_log (n : ℕ) : Nat.size n ≤ Nat.log 2 n + 1 :=
  Nat.size_le.2 (Nat.lt_pow_succ_log_self (by decide) n)

theorem poly_lt {M w : ℕ} (hw : 16 ≤ w) (hM : (M + 1) ^ 4 ≤ 2 ^ w) :
    3 * (M * M) + 75 * M + 133 < 2 ^ w := by
  have h16 : 2 ^ 16 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  by_cases hs : M ≤ 9
  · have : M * M ≤ 81 := Nat.mul_le_mul hs hs
    omega
  · have h1 : (M + 1) ^ 4 = (M + 1) ^ 2 * (M + 1) ^ 2 := by ring
    have h2 : 121 * (M + 1) ^ 2 ≤ (M + 1) ^ 2 * (M + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (by nlinarith)
    have h3 : (M + 1) ^ 2 = M * M + 2 * M + 1 := by ring
    omega

/-! ### The core -/

theorem out_eq (x : EInput) {j : ℕ} (hj : j < x.wg.n) :
    outVal (finish (ctxX x) x.source) (j + 1) = (ncode (spo x))[j + 1]! := by
  have hl : j + 1 < (ncode (spo x)).length := by rw [ncode_spf]; simp [length_spf, hj]
  rw [getElem!_pos (ncode (spo x)) (j + 1) hl]
  simp only [ncode_spf, List.getElem_cons_succ, List.getElem_map]
  by_cases hs : x.source < x.wg.n
  · obtain ⟨-, -, hout, -⟩ := finish_spec (ctxOK x) (adjOK x) hs
    have := hout ⟨j, hj⟩
    simp only [spf, dif_pos hs, List.getElem_ofFn]
    exact this
  · rw [finish_invalid (show (ctxX x).n ≤ x.source by change x.wg.n ≤ _; omega)]
    simp [spf, dif_neg hs, outVal, blank, encDist]

theorem core_time (x : EInput) {k : ℕ}
    (hk : k ≤ 6 * Nat.size x.wg.n + 33 * numEdges x + 25 * x.wg.n +
      (finish (ctxX x) x.source).time + 120) : k ≤ coreTime x := by
  have h1 := finish_time x x.source
  have h2 : Nat.size x.wg.n ≤ x.wg.n := Nat.size_le.2 Nat.lt_two_pow_self
  have h3 : x.wg.n * perVertex (ctxX x) =
      200 * (x.wg.n * (Dn x.wg.n + 1)) + 20 * x.wg.n := by
    change x.wg.n * (200 * (Dn x.wg.n + 1) + 20) = _
    ring
  have h4 : x.wg.n ≤ x.wg.n * (Dn x.wg.n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold coreTime
  omega

/-! ### The statement's input and output -/

theorem foldr_max_le {l : List ℕ} {a M : ℕ} (ha : a ≤ M) (h : ∀ v ∈ l, v ≤ M) :
    l.foldr max a ≤ M := by
  induction l with
  | nil => exact ha
  | cons v l ih =>
    exact max_le (h v (List.mem_cons_self ..)) (ih fun u hu => h u (List.mem_cons_of_mem _ hu))

theorem len_input (x : Input) : (ncode x).length = x.1 + 3 * (wts x).length + 4 := by
  have h2 : (lexEdges x.2.1).length = (wts x).length := (length_wts x).symm
  rw [ncode_input_tape]
  simp only [List.length_cons, List.length_append, List.length_nil, length_blocks]
  omega

theorem len_toE (x : Input) : (ncode (toE x)).length = 3 * (wts x).length + 4 := by
  rw [ncode_toE]
  simp only [List.length_cons, List.length_append, List.length_nil, length_emitAll]
  omega

theorem codeMax_toE (x : Input) : codeMax (ncode (toE x)) ≤ codeMax (ncode x) := by
  have hx : ∀ u ∈ x.1 :: x.1 :: ((nbrLists x.2.1).flatMap blk ++ (wts x).length ::
      (wts x ++ [x.2.2.2])), u ≤ codeMax (ncode x) := fun u hu =>
    le_codeMax (by rw [ncode_input_tape]; exact hu)
  have hl := length_le_codeMax (ncode x)
  rw [len_input] at hl
  have hn := hx _ (List.mem_cons_self ..)
  refine foldr_max_le (by rw [len_toE]; omega) fun v hv => ?_
  rw [ncode_toE] at hv
  rcases List.mem_cons.1 hv with rfl | hv
  · exact hn
  rcases List.mem_cons.1 hv with rfl | hv
  · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_cons_self ..))))
  rcases List.mem_append.1 hv with hv | hv
  · rw [emitAll_nbr] at hv
    obtain ⟨p, hp, hv⟩ := List.mem_flatMap.1 hv
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact le_trans e.1.isLt.le hn
    · exact le_trans e.2.isLt.le hn
  · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hv)))

/-- The distances, as the statement's output. -/
noncomputable def spfN (x : Input) : Σ n, Fin n → ℕ := ⟨x.1, fun v => (spo (toE x)).getD v 0⟩

theorem map_spfN (x : Input) : (List.finRange x.1).map (spfN x).2 = spo (toE x) := by
  have hl : (spo (toE x)).length = x.1 := by rw [spo, List.length_map]; exact length_spf (toE x)
  refine List.ext_getElem (by simp only [List.length_map]; exact List.length_finRange.trans hl.symm)
    fun i h1 h2 => ?_
  simp [spfN, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem ncode_spfN (x : Input) : ncode (spfN x) = x.1 :: ncode (spo (toE x)) := by
  rw [ncode_out, ncode_prod, ncode_nat]
  change [x.1] ++ ncode ((List.finRange x.1).map (spfN x).2) = _
  rw [map_spfN]; rfl

theorem len_spfN (x : Input) : (ncode (spfN x)).length = x.1 + 2 := by
  rw [ncode_spfN, ncode_spf]
  simp only [List.length_cons, List.length_map, length_spf]
  rfl

/-- `spec` accepts, for a connected graph and a source vertex, the weight of a lightest walk from
the source to each vertex. -/
def AcceptsDist (spec : IOSpec Input (Σ n, Fin n → ℕ)) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)) (w : G.edgeSet → ℕ) (s : ℕ) (out : Σ n, Fin n → ℕ),
    (G.Connected → ∀ h : s < n, ∃ f : Fin n → ℕ, out = ⟨n, f⟩ ∧ ∀ v,
      IsLeast {(p.darts.map fun d => w ⟨d.edge, d.edge_mem⟩).sum | p : G.Walk ⟨s, h⟩ v} (f v)) →
    spec.valid ⟨n, G, w, s⟩ out

/-- Over a nonempty index, the infimum of natural numbers is their least value. -/
theorem isLeast_iInf {ι : Sort*} [Nonempty ι] (f : ι → ℕ) : IsLeast (Set.range f) (⨅ i, f i) :=
  ⟨csInf_mem (Set.range_nonempty f), fun _ ⟨i, hi⟩ => hi ▸ ciInf_le (OrderBot.bddBelow _) i⟩

theorem spfN_valid {spec : IOSpec Input (Σ n, Fin n → ℕ)} (hspec : AcceptsDist spec) (x : Input) :
    spec.valid x (spfN x) := by
  obtain ⟨n, G, w, s⟩ := x
  refine hspec n G w s _ fun hG h => ⟨(spfN ⟨n, G, w, s⟩).2, rfl, fun v => ?_⟩
  haveI : Nonempty (G.Walk ⟨s, h⟩ v) := hG.preconnected _ _
  have hv : (spfN ⟨n, G, w, s⟩).2 v =
      ⨅ p : G.Walk ⟨s, h⟩ v, (p.darts.map fun d => w ⟨d.edge, d.edge_mem⟩).sum := by
    have hs : (toE ⟨n, G, w, s⟩).source < (toE ⟨n, G, w, s⟩).wg.n := h
    change (spo (toE ⟨n, G, w, s⟩)).getD v 0 = _
    simp only [spo, spf, dif_pos hs]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_ofFn]
    rw [dif_pos (show (v : ℕ) < (toE ⟨n, G, w, s⟩).wg.n from v.isLt), Option.map_some,
      Option.getD_some]
    exact dist_toE ⟨n, G, w, s⟩ _ _
  rw [hv]
  exact isLeast_iInf _

/-! ### The program -/

/-- Put `n` before the core's output, and point registers `4` and `9` back at the input. -/
def post : Cmd := seqs [.load 29 9, .add 4 4 29, .sub 9 9 4, .sub 10 10 3, .store 10 29,
  .add 17 17 3]

/-- Convert the input, run the core, and put `n` before its output. -/
def coreN : Cmd := seqs [conv, Prog.core, post]

set_option maxHeartbeats 1000000 in
theorem post_run {B S ℓ' A' n O : ℕ} {m : Mem} (hR : CodeRegs S ℓ' A' m) (hKS : nK ≤ S)
    (h10 : m 10 = O) (h17 : m 17 = n + 1) (hn : m A' = n) (hA' : 32 ≤ A') (hℓ : ℓ' + n ≤ A')
    (hO : A' < O) (hB : O + n + 2 < B) :
    Runs B post m fun m' k => CodeRegs S (ℓ' + n) (A' - (ℓ' + n)) m' ∧ m' 10 = O - 1 ∧
      m' 17 = n + 2 ∧ m' (O - 1) = n ∧ (∀ a, 32 ≤ a → a ≠ O - 1 → m' a = m a) ∧ k ≤ 7 := by
  obtain ⟨⟨r1, r3, r5⟩, r4, r8, r9, r16⟩ := id hR
  have bR : ∀ r, r < 33 → r < B := fun r hr => by omega
  rstep
  refine Runs.loadV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) ?_
  intro m₁ g₁ f₁ v₁
  have e29 : m₁ 29 = n := by rw [g₁, r9, hn]
  rstep
  refine Runs.addV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) (bR _ (by decide))
    (by rw [f₁ 4 (by decide), e29, r4]; omega) ?_
  intro m₂ g₂ f₂ v₂
  have e4 : m₂ 4 = ℓ' + n := by rw [g₂, f₁ 4 (by decide), e29, r4]
  rstep
  refine Runs.subV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) (bR _ (by decide))
    (by rw [e4, f₂ 9 (by decide), f₁ 9 (by decide), r9]; exact hℓ) ?_
  intro m₃ g₃ f₃ v₃
  have e3 : m₃ 3 = 1 := by rw [f₃ 3 (by decide), f₂ 3 (by decide), f₁ 3 (by decide), r3]
  have e10' : m₃ 10 = O := by rw [f₃ 10 (by decide), f₂ 10 (by decide), f₁ 10 (by decide), h10]
  rstep
  refine Runs.subV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) (bR _ (by decide))
    (by rw [e10', e3]; omega) ?_
  intro m₄ g₄ f₄ v₄
  have e10 : m₄ 10 = O - 1 := by rw [g₄, e10', e3]
  rstep
  refine Runs.storeR (p := 10) (s := 29) (bR _ (by decide)) (bR _ (by decide)) ?_
  intro m₅ s₅ fr₅
  rw [e10, f₄ 29 (by decide), f₃ 29 (by decide), f₂ 29 (by decide), e29] at s₅
  rw [e10] at fr₅
  have e17 : m₅ 17 = n + 1 := by
    rw [fr₅ 17 (by omega), f₄ 17 (by decide), f₃ 17 (by decide), f₂ 17 (by decide),
      f₁ 17 (by decide), h17]
  have e3' : m₅ 3 = 1 := by rw [fr₅ 3 (by omega), f₄ 3 (by decide), e3]
  rstep
  refine Runs.addV hKS (by decide) (bR _ (by decide)) (bR _ (by decide)) (bR _ (by decide))
    (by rw [e17, e3']; omega) ?_
  intro m₆ g₆ f₆ v₆
  refine Runs.seqs_nilV hKS (bR _ (by decide)) ?_
  intro m₇ g₇ f₇ v₇
  have F : ∀ a, a ≠ 2 → a ≠ 17 → a ≠ O - 1 → a ≠ 10 → a ≠ 9 → a ≠ 4 → a ≠ 29 → m₇ a = m a :=
    fun a h2 h17 hO1 h10 h9 h4 h29 => by
      rw [f₇ a h2, f₆ a h17, fr₅ a hO1, f₄ a h10, f₃ a h9, f₂ a h4, f₁ a h29]
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, fun a ha hne => F a (by omega) (by omega)
    hne (by omega) (by omega) (by omega) (by omega), by omega⟩
  · rw [F _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r1
  · rw [F _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r3
  · rw [F _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r5
  · rw [f₇ 4 (by decide), f₆ 4 (by decide), fr₅ 4 (by omega), f₄ 4 (by decide), f₃ 4 (by decide),
      e4]
  · rw [F _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r8
  · rw [f₇ 9 (by decide), f₆ 9 (by decide), fr₅ 9 (by omega), f₄ 9 (by decide), g₃, e4,
      f₂ 9 (by decide), f₁ 9 (by decide), r9]
  · rw [F _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r16
  · rw [f₇ 10 (by decide), f₆ 10 (by decide), fr₅ 10 (by omega), e10]
  · rw [f₇ 17 (by decide), g₆, e17, e3']
  · rw [f₇ _ (by omega), f₆ _ (by omega), s₅]

/-- The memory used from `A`. -/
noncomputable def needN (x : Input) : ℕ := (ncode x).length + needF (toE x)

/-- The steps of `coreN`, up to the constant. -/
noncomputable def timeN (x : Input) : ℕ := 20 * (ncode x).length + 60 + coreTime (toE x)

set_option maxHeartbeats 4000000 in
theorem coreN_spec : CodeSpec coreN spfN timeN needN := by
  intro B S A m x hR hKS hAS hneed hcB hcode hzero
  have hA : 32 ≤ A := by omega
  have hM : MemAt m A (ncode x) := fun j hj => by
    have h := hcode j hj
    rw [vm_high hKS (by omega), getElem!_pos (ncode x) j hj] at h
    exact h
  have hz : ∀ a, A + (ncode x).length ≤ a → m a = 0 := fun a ha => by
    have h := hzero a ha
    rwa [vm_high hKS (by omega)] at h
  have hT := ncode_input_tape x
  have hnB : x.1 < B := hcB _ (by rw [hT]; exact List.mem_cons_self ..)
  have hMB : codeMax (ncode (toE x)) * codeMax (ncode (toE x)) + 1 < B := by
    have := codeMax_toE x
    have hN : needF (toE x) = (3 * numEdges (toE x) + 4) + 10 * (x.1 + Dn x.1 + 3) +
        6 * numEdges (toE x) + (x.1 + 1) + x.1 * (Dn x.1 + 1) + 1 +
        (codeMax (ncode (toE x)) + 1) * (codeMax (ncode (toE x)) + 1) := rfl
    have hsq : (codeMax (ncode (toE x)) + 1) * (codeMax (ncode (toE x)) + 1) =
        codeMax (ncode (toE x)) * codeMax (ncode (toE x)) + 2 * codeMax (ncode (toE x)) + 1 := by
      ring
    unfold needN at hneed
    omega
  have hKB : (x.1 + 1) * codeMax (ncode (toE x)) < B := by
    have hn := n_le_codeMax (toE x)
    have := Nat.mul_le_mul_right (codeMax (ncode (toE x)))
      (show x.1 + 1 ≤ codeMax (ncode (toE x)) + 1 by change (toE x).wg.n + 1 ≤ _; omega)
    have e : (codeMax (ncode (toE x)) + 1) * codeMax (ncode (toE x)) =
        codeMax (ncode (toE x)) * codeMax (ncode (toE x)) + codeMax (ncode (toE x)) := by ring
    have hN : needF (toE x) = (3 * numEdges (toE x) + 4) + 10 * (x.1 + Dn x.1 + 3) +
        6 * numEdges (toE x) + (x.1 + 1) + x.1 * (Dn x.1 + 1) + 1 +
        (codeMax (ncode (toE x)) + 1) * (codeMax (ncode (toE x)) + 1) := rfl
    have hsq : (codeMax (ncode (toE x)) + 1) * (codeMax (ncode (toE x)) + 1) =
        codeMax (ncode (toE x)) * codeMax (ncode (toE x)) + 2 * codeMax (ncode (toE x)) + 1 := by
      ring
    unfold needN at hneed
    omega
  have hnum : numEdges (toE x) = (wts x).length := (length_wts x).symm
  have hfb : ((nbrLists x.2.1).flatMap blk).length = x.1 + 2 * (wts x).length := by
    rw [length_blocks, ← hnum]; rfl
  have hEm := length_emitAll x
  have hlx := len_input x
  have hle := len_toE x
  have hNF : needF (toE x) = (3 * (wts x).length + 4) + 10 * (x.1 + Dn x.1 + 3) +
      6 * (wts x).length + (x.1 + 1) + x.1 * (Dn x.1 + 1) + 1 +
      (codeMax (ncode (toE x)) + 1) * (codeMax (ncode (toE x)) + 1) := by
    rw [← hnum]; rfl
  have hTop : (layOf (toE x) (A + (ncode x).length)).top < B := by
    have : (layOf (toE x) (A + (ncode x).length)).top = A + (ncode x).length +
        (ncode (toE x)).length + 10 * (x.1 + Dn x.1 + 3) + 6 * numEdges (toE x) + (x.1 + 1) +
        x.1 * (Dn x.1 + 1) := rfl
    unfold needN at hneed
    omega
  have hH : (layOf (toE x) (A + (ncode x).length)).H =
      A + (ncode x).length + (ncode (toE x)).length := rfl
  have hR9 : (layOf (toE x) (A + (ncode x).length)).H +
      9 * (layOf (toE x) (A + (ncode x).length)).R =
      A + (ncode x).length + (ncode (toE x)).length + 9 * (x.1 + Dn x.1 + 3) := rfl
  have hBO : A + (ncode x).length + (ncode (toE x)).length + 9 * (x.1 + Dn x.1 + 3) + x.1 + 2 <
      B := by
    unfold needN at hneed
    omega
  have hlo : (ncode (spfN x)).length = x.1 + 2 := len_spfN x
  have hneedO : A + (ncode x).length + (ncode (toE x)).length + 9 * (x.1 + Dn x.1 + 3) - 1 +
      (x.1 + 2) ≤ A + needN x := by
    unfold needN
    omega
  generalize hO : (layOf (toE x) (A + (ncode x).length)).H +
    9 * (layOf (toE x) (A + (ncode x).length)).R = O at hR9
  generalize hE : (wts x).length = E at hT hfb hEm hlx hle hNF hnum
  generalize hℓ : (ncode x).length = ℓ at hR hM hz hlx hTop hH hR9 hBO hneedO hO
  rw [hT] at hM
  have ht' : (wts x ++ [x.2.2.2]).length = E + 1 := by
    rw [List.length_append, List.length_singleton, hE]
  have hℓc : ℓ = 2 + ((nbrLists x.2.1).flatMap blk).length + ((wts x ++ [x.2.2.2]).length + 1) := by
    rw [ht', hfb]; omega
  have hBc : A + ℓ + 3 * E + 8 < B := by unfold needN at hneed; omega
  refine Runs.seqs_cons (Runs.mono (conv_run (bs := nbrLists x.2.1) (t' := wts x ++ [x.2.2.2])
    hR hKS hA (by simp [nbrLists]) hM hℓc ht' hEm hBc hnB) ?_)
  rintro m₁ k₁ ⟨hR₁, hM₁, hfr₁, hk₁⟩
  have hM₁' : MemAt m₁ (A + ℓ) (ncode (toE x)) := by rw [ncode_toE, hE]; exact hM₁
  have hR₁' : CodeRegs S (ncode (toE x)).length (A + ℓ) m₁ := by rw [hle]; exact hR₁
  have hz₁ : ∀ a, A + ℓ + (ncode (toE x)).length ≤ a → m₁ a = 0 := fun a ha => by
    rw [hfr₁ a (by omega) (.inr (by omega)), hz a (by omega)]
  refine Runs.seqs_cons (Runs.mono (core_run hR₁' (by omega) hTop hKB hM₁' hz₁) ?_)
  rintro m₂ k₂ ⟨R₂, z10, z17, z0, zO, zhi, hk₂⟩
  rw [hO] at z10 z0 zO
  have hAO : A + ℓ + 1 ≤ O := by rw [hR9]; omega
  have hneedO' : O - 1 + (x.1 + 2) ≤ A + needN x := by rw [hR9]; exact hneedO
  have hAn : m₂ (A + ℓ) = x.1 := by
    rw [zhi _ (by omega) (by rw [hH]; omega)]; exact hM₁.head
  refine Runs.seqs_cons (Runs.mono (post_run (n := x.1) R₂ hKS z10 z17 hAn (by omega) (by omega)
    (by omega) (by omega)) ?_)
  rintro m₃ k₃ ⟨R₃, e10, e17, eO, hfr₃, hk₃⟩
  rw [show (ncode (toE x)).length + x.1 = ℓ by omega, show A + ℓ - ℓ = A by omega] at R₃
  refine Runs.seqs_nilR (by omega) fun m₄ g₄ f₄ => ?_
  obtain ⟨⟨q1, q3, q5⟩, q4, q8, q9, q16⟩ := R₃
  have hxn : (toE x).wg.n = x.1 := rfl
  clear * - hKS hA hAS hnB hMB hlo hAO hneedO' hH z0 zO zhi hfr₁ hfr₃ e10 e17 eO q1 q3 q5 q4 q8
    q9 q16 g₄ f₄ hk₁ hk₂ hk₃ hxn hℓ
  have hfr : ∀ b, 32 ≤ b → b < A → m₄ b = m b := fun b h1 h2 => by
    rw [f₄ b (by omega), hfr₃ b h1 (by omega), zhi b h1 (by rw [hH]; omega),
      hfr₁ b h1 (.inl (by omega))]
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, fun j hj => ?_, fun v hv => ?_,
    fun a ha => ?_, ?_⟩
  · rw [f₄ _ (by decide)]; exact q1
  · rw [f₄ _ (by decide)]; exact q3
  · rw [f₄ _ (by decide)]; exact q5
  · rw [f₄ _ (by decide)]; exact q4
  · rw [f₄ _ (by decide)]; exact q8
  · rw [f₄ _ (by decide)]; exact q9
  · rw [f₄ _ (by decide)]; exact q16
  · rw [f₄ 10 (by decide), e10]; omega
  · rw [f₄ 10 (by decide), e10, hlo]; omega
  · rw [f₄ 17 (by decide), e17, hlo]
  · rw [hlo] at hj
    rw [f₄ 10 (by decide), e10, vm_high hKS (by omega), f₄ _ (by omega)]
    rcases j with _ | j
    · rw [Nat.add_zero, eO, ncode_spfN]; rfl
    · rw [show O - 1 + (j + 1) = O + j by omega, hfr₃ _ (by omega) (by omega), ncode_spfN,
        List.getElem!_cons_succ]
      rcases j with _ | j
      · rw [Nat.add_zero, z0, ncode_spf]; rfl
      · rw [zO _ (by omega) (by omega), out_eq (toE x) (by omega)]
  · rw [ncode_spfN] at hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hnB
    · rw [ncode_spf] at hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hnB
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hv
        have := encDist_le (toE x) d hd
        omega
  · unfold vm
    split_ifs with h1 h2
    · exact hfr _ (by omega) (by omega)
    · rfl
    · exact hfr _ (by omega) (by omega)
  · have := core_time (toE x) hk₂
    unfold timeN
    omega

/-! ### Bounds -/

theorem hS_N (x : Input) :
    3 * ((ncode x).length + 1) + 3 * (ncode (spfN x)).length + nK ≤ 6 * (ncode x).length + 70 := by
  rw [len_spfN, len_input]; omega

theorem hneed_N (x : Input) : (ncode x).length + nK ≤ needN x := by
  unfold needN; simp only [needF]; omega

theorem E_le_codeMaxN (x : Input) : (wts x).length ≤ codeMax (ncode x) :=
  le_codeMax (by rw [ncode_input_tape]; simp)

theorem n_le_codeMaxN (x : Input) : x.1 ≤ codeMax (ncode x) :=
  le_codeMax (by rw [ncode_input_tape]; simp)

theorem hbig_N (x : Input) (w : ℕ) (hw : 16 ≤ w) (hM : (codeMax (ncode x) + 1) ^ 4 ≤ 2 ^ w) :
    6 * (ncode x).length + 70 + nK + needN x < 2 ^ w := by
  have hn := n_le_codeMaxN x
  have hE := E_le_codeMaxN x
  have hl := length_le_codeMax (ncode x)
  have hc := codeMax_toE x
  have hnum : numEdges (toE x) = (wts x).length := (length_wts x).symm
  have hs : Nat.size x.1 ≤ x.1 := Nat.size_le.2 Nat.lt_two_pow_self
  have hns : x.1 * Nat.size x.1 ≤ codeMax (ncode x) * codeMax (ncode x) :=
    Nat.mul_le_mul hn (hs.trans hn)
  have hcc : (codeMax (ncode (toE x)) + 1) * (codeMax (ncode (toE x)) + 1) ≤
      (codeMax (ncode x) + 1) * (codeMax (ncode x) + 1) := Nat.mul_le_mul (by omega) (by omega)
  have e2 : (codeMax (ncode x) + 1) * (codeMax (ncode x) + 1) =
      codeMax (ncode x) * codeMax (ncode x) + 2 * codeMax (ncode x) + 1 := by ring
  have e : x.1 * (2 * Nat.size x.1 + 1) = 2 * (x.1 * Nat.size x.1) + x.1 := by ring
  have := poly_lt hw hM
  have hlx := len_input x
  have hNF : needF (toE x) = (3 * numEdges (toE x) + 4) + 10 * (x.1 + Dn x.1 + 3) +
      6 * numEdges (toE x) + (x.1 + 1) + x.1 * (Dn x.1 + 1) + 1 +
      (codeMax (ncode (toE x)) + 1) * (codeMax (ncode (toE x)) + 1) := rfl
  simp only [needN, hNF, Dn, hnum] at *
  omega

theorem hfy_N (x : Input) : ∀ v ∈ ncode (spfN x), v < (codeMax (ncode x) + 1) ^ 4 := by
  intro v hv
  have hc := codeMax_toE x
  have hn := n_le_codeMaxN x
  have h1 : (codeMax (ncode x) + 1) ^ 4 = (codeMax (ncode x) + 1) * (codeMax (ncode x) + 1) *
    ((codeMax (ncode x) + 1) * (codeMax (ncode x) + 1)) := by ring
  have hM1 : 1 ≤ codeMax (ncode x) := by
    have := length_le_codeMax (ncode x); rw [len_input] at this; omega
  have h2 : codeMax (ncode x) * codeMax (ncode x) + 1 < (codeMax (ncode x) + 1) *
      (codeMax (ncode x) + 1) := by nlinarith
  have h3 : (codeMax (ncode x) + 1) * (codeMax (ncode x) + 1) ≤ (codeMax (ncode x) + 1) *
      (codeMax (ncode x) + 1) * ((codeMax (ncode x) + 1) * (codeMax (ncode x) + 1)) :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have hcc : codeMax (ncode (toE x)) * codeMax (ncode (toE x)) ≤
      codeMax (ncode x) * codeMax (ncode x) := Nat.mul_le_mul hc hc
  rw [ncode_spfN] at hv
  rcases List.mem_cons.1 hv with rfl | hv
  · nlinarith
  rw [ncode_spf] at hv
  rcases List.mem_cons.1 hv with rfl | hv
  · change x.1 < _; nlinarith
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hv
    have := encDist_le (toE x) d hd
    omega

theorem time_boundN (n E : ℕ) :
    20 * (n + 3 * E + 4) + 60 + 2000 * (E + n * (2 * Nat.size n + 1) + 1) +
      33 * (n + 3 * E + 4) + 25 * (n + 2) + 340 ≤ 10432 * (E + n * Nat.log 2 n) + 10432 := by
  have hs := size_le_log n
  have h1 : n * (2 * Nat.size n + 1) ≤ n * (2 * Nat.log 2 n + 3) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : n * (2 * Nat.log 2 n + 3) = 2 * (n * Nat.log 2 n) + 3 * n := by ring
  have h3 : n ≤ n * Nat.log 2 n + 1 := by
    by_cases hn : n ≤ 1
    · omega
    · have : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) (by simpa using (by omega : 2 ≤ n))
      nlinarith
  omega

theorem time_N (x : Input) :
    timeN x + 33 * (ncode x).length + 25 * (ncode (spfN x)).length + 340 ≤
      (fun x : Input => 10432 * (x.2.1.edgeSet.ncard + x.1 * Nat.log 2 x.1) + 10432) x := by
  have hnum : numEdges (toE x) = (wts x).length := (length_wts x).symm
  have hE : x.2.1.edgeSet.ncard = (wts x).length := by
    rw [← length_edges, ← hnum]; rfl
  rw [len_spfN, len_input]
  simp only [timeN, coreTime, Dn, hnum, len_input, hE]
  exact time_boundN x.1 (wts x).length

theorem small_coreN : Small 16 (codeProgram setScan lenScan coreN).lines := by decide +kernel

/-- A TD word RAM with `<`, `+` and `−` solves, in `O(E + V log V)` steps, any spec that accepts
the shortest-path distances. -/
theorem shortestPaths_wordRAM (spec : IOSpec Input (Σ n, Fin n → ℕ)) (hspec : AcceptsDist spec) :
    ∃ c, (tdWordRAM [.less, .add, .sub]).SolvableWithin spec fun ⟨V, G, _⟩ =>
      c * (G.edgeSet.ncard + V * Nat.log 2 V) + c :=
  ⟨10432, solvableWithin_code (W := 16) (scale := 4) coreN_spec (lenScan_spec spfN) setScan_spec
    layout_input skips_input layout_out readsBack_out
    (fun x h => by have := len_input x; rw [h] at this; simp at this)
    (by omega) (by omega) small_coreN hS_N hneed_N
    (fun x w hw hM => hbig_N x w hw hM) hfy_N spec (spfN_valid hspec) _ time_N⟩

end Formalgo.Algorithms.ShortestPaths
