import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunCore
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Size

/-!
# Proof that a TD word RAM finds shortest paths in `O(E + V log V)` steps

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Function

/-- The distances from the source, or `⊤` everywhere if it is not a vertex. -/
noncomputable def spf (x : Input) : List ℕ∞ :=
  if h : x.source < x.wg.n then List.ofFn (x.wg.dist ⟨x.source, h⟩)
  else List.replicate x.wg.n ⊤

theorem length_spf (x : Input) : (spf x).length = x.wg.n := by
  unfold spf; split <;> simp

/-- The memory the core uses from `A`. -/
noncomputable def needF (x : Input) : ℕ :=
  let n := x.wg.n; let E := numEdges x
  (3 * E + 4) + 10 * (n + Dn n + 3) + 6 * E + (n + 1) + n * (Dn n + 1) + 1 +
    (codeMax (ncode x) + 1) * (codeMax (ncode x) + 1)

/-- Where the registers are saved. -/
noncomputable def SfF (x : Input) : ℕ := 16 * (numEdges x + x.wg.n) + 64

/-- The steps of the core, up to the constant. -/
noncomputable def coreTime (x : Input) : ℕ :=
  2000 * (numEdges x + x.wg.n * (Dn x.wg.n + 1) + 1)

/-- `M[0] := 16 (E + n) + 64`, from `E` in cell `7` and `n` in cell `4`. -/
def setS : Cmd := seq (const 2 7) (seq (load 0 2) (seq (const 2 4) (seq (load 2 2)
  (seq (add 0 0 2) (seq (add 0 0 0) (seq (add 0 0 0) (seq (add 0 0 0) (seq (add 0 0 0)
  (seq (const 2 64) (add 0 0 2))))))))))

/-- `M[4] := 3 E + 4`, from `E` in register `7`. -/
def lenC : Cmd := seq (add 4 7 7) (seq (add 4 4 7) (seq (const 2 4) (add 4 4 2)))

theorem initMem_n (w : ℕ) (x : Input) : initMem w x 4 = x.wg.n := by
  have h := initMem_code_elem (w := w) (x := x) (j := 0) (by rw [length_ncode_input]; omega)
  rw [h, ncode_input_eq]; rfl

theorem initMem_E (w : ℕ) (x : Input) : initMem w x 7 = numEdges x := by
  have h := initMem_code_elem (w := w) (x := x) (j := 1) (by rw [length_ncode_input]; omega)
  rw [h, ncode_input_eq]; rfl

theorem setS_spec : SetSSpec setS SfF := by
  intro B w x hB
  have h4 := initMem_n w x
  have h7 := initMem_E w x
  unfold SfF at hB ⊢
  generalize initMem w x = m at h4 h7 ⊢
  refine ⟨_, _, .seq (.const (by omega) (by omega)) (.seq (.load (by omega) (by omega))
    (.seq (.const (by omega) (by omega)) (.seq (.load (by omega) (by omega))
    (.seq (.add (by omega) (by omega) (by omega) ?_) (.seq (.add (by omega) (by omega) (by omega) ?_)
    (.seq (.add (by omega) (by omega) (by omega) ?_) (.seq (.add (by omega) (by omega) (by omega) ?_)
    (.seq (.add (by omega) (by omega) (by omega) ?_) (.seq (.const (by omega) (by omega))
    (.add (by omega) (by omega) (by omega) ?_)))))))))), ?_, ?_, by omega⟩ <;>
    first
    | (intro a ha hb; simp [update_apply, ha, hb])
    | (simp [update_apply, h4, h7]; omega)

theorem lenC_spec : LenSpec lenC spf := by
  intro B S w m x hKS hB hS hR hreg
  have h7 : m 7 = numEdges x := by rw [hreg 7 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega), initMem_E]
  rw [length_ncode_input] at hS
  refine ⟨_, _, .seq (.add (by omega) (by omega) (by omega) (by rw [h7]; omega))
    (.seq (.add (by omega) (by omega) (by omega) (by simp [h7]; omega))
    (.seq (.const (by omega) (by omega)) (.add (by omega) (by omega) (by omega)
      (by simp [h7]; omega)))), ?_, ?_, ?_, by omega⟩
  · simp [h7, length_ncode_input]; omega
  · intro r h2 h4; simp [update_apply, h2, h4]
  · funext a; unfold vm
    split_ifs
    · rw [update_of_ne (by omega), update_of_ne (by omega), update_of_ne (by omega),
        update_of_ne (by omega)]
    · rfl
    · rw [update_of_ne (by omega), update_of_ne (by omega), update_of_ne (by omega),
        update_of_ne (by omega)]

theorem n_le_codeMax' (x : Input) : x.wg.n ≤ codeMax (ncode x) :=
  le_codeMax (by rw [ncode_input_eq]; simp)

theorem encDist_le (x : Input) : ∀ d ∈ spf x,
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

theorem ncode_spf (x : Input) : ncode (spf x) = x.wg.n :: (spf x).map encDist := by
  rw [ncode_output, length_spf]

theorem n_le_codeMax (x : Input) : x.wg.n ≤ codeMax (ncode x) :=
  le_codeMax (by rw [ncode_input_eq]; simp)

theorem E_le_codeMax (x : Input) : numEdges x ≤ codeMax (ncode x) :=
  le_codeMax (by rw [ncode_input_eq]; simp)

theorem size_le_log (n : ℕ) : Nat.size n ≤ Nat.log 2 n + 1 :=
  Nat.size_le.2 (Nat.lt_pow_succ_log_self (by decide) n)

theorem hS_spf (x : Input) :
    3 * ((ncode x).length + 1) + 3 * (ncode (spf x)).length + nK ≤ SfF x := by
  rw [length_ncode_input, ncode_spf]; simp [length_spf, SfF]; omega

theorem hneed_spf (x : Input) : (ncode x).length + nK ≤ needF x := by
  rw [length_ncode_input]; simp only [needF]; omega

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

theorem hbig_spf (x : Input) (w : ℕ) (hw : 16 ≤ w)
    (hM : (codeMax (ncode x) + 1) ^ 4 ≤ 2 ^ w) : SfF x + nK + needF x < 2 ^ w := by
  have hn := n_le_codeMax x
  have hE := E_le_codeMax x
  have hs : Nat.size x.wg.n ≤ x.wg.n := Nat.size_le.2 (Nat.lt_two_pow_self)
  have hns : x.wg.n * Nat.size x.wg.n ≤ codeMax (ncode x) * codeMax (ncode x) :=
    Nat.mul_le_mul hn (hs.trans hn)
  have := poly_lt hw hM
  simp only [SfF, needF, Dn]
  have e : x.wg.n * (2 * Nat.size x.wg.n + 1) =
    2 * (x.wg.n * Nat.size x.wg.n) + x.wg.n := by ring
  have e2 : (codeMax (ncode x) + 1) * (codeMax (ncode x) + 1) =
    codeMax (ncode x) * codeMax (ncode x) + 2 * codeMax (ncode x) + 1 := by ring
  omega

theorem hfy_spf (x : Input) : ∀ v ∈ ncode (spf x), v < (codeMax (ncode x) + 1) ^ 4 := by
  intro v hv
  have h1 : (codeMax (ncode x) + 1) ^ 4 = (codeMax (ncode x) + 1) * (codeMax (ncode x) + 1) *
    ((codeMax (ncode x) + 1) * (codeMax (ncode x) + 1)) := by ring
  have hM1 : 1 ≤ codeMax (ncode x) := by
    have := length_le_codeMax (ncode x); rw [length_ncode_input] at this; omega
  have h2 : codeMax (ncode x) * codeMax (ncode x) + 1 < (codeMax (ncode x) + 1) *
      (codeMax (ncode x) + 1) := by nlinarith
  have h3 : (codeMax (ncode x) + 1) * (codeMax (ncode x) + 1) ≤ (codeMax (ncode x) + 1) *
      (codeMax (ncode x) + 1) * ((codeMax (ncode x) + 1) * (codeMax (ncode x) + 1)) :=
    Nat.le_mul_of_pos_right _ (by positivity)
  rw [ncode_spf] at hv
  rcases List.mem_cons.1 hv with rfl | hv
  · have := n_le_codeMax x; nlinarith
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hv
    have := encDist_le x d hd
    omega

theorem spf_valid (x : Input) : shortestPaths.valid x (spf x) := by
  intro h
  have h' : x.source < x.wg.n := h
  simp only [spf, dif_pos h']
  congr 1
  funext v
  exact dist_wg x _ _

theorem time_bound (n E : ℕ) :
    2000 * (E + n * (2 * Nat.size n + 1) + 1) + 13 * (3 * E + 4) + 25 * (n + 1) + 330 ≤
      10432 * (E + n * Nat.log 2 n) + 10432 := by
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

theorem time_spf (x : Input) :
    coreTime x + 13 * (ncode x).length + 25 * (ncode (spf x)).length + 330 ≤
      10432 * (x.wg.graph.edgeSet.ncard + x.wg.n * Nat.log 2 x.wg.n) + 10432 := by
  rw [length_ncode_input, ncode_spf, ← length_edges]
  simpa only [List.length_cons, List.length_map, length_spf, coreTime, Dn, numEdges] using
    time_bound x.wg.n (numEdges x)

theorem small_core : Small 16 (codeProgram setS lenC Prog.core).lines := by decide +kernel

/-! ### The core -/

theorem out_eq (x : Input) {j : ℕ} (hj : j < x.wg.n) :
    outVal (finish (ctxX x) x.source) (j + 1) = (ncode (spf x))[j + 1]! := by
  have hl : j + 1 < (ncode (spf x)).length := by rw [ncode_spf]; simp [length_spf, hj]
  rw [getElem!_pos (ncode (spf x)) (j + 1) hl]
  simp only [ncode_spf, List.getElem_cons_succ, List.getElem_map]
  by_cases hs : x.source < x.wg.n
  · obtain ⟨-, -, hout, -⟩ := finish_spec (ctxOK x) (adjOK x) hs
    have := hout ⟨j, hj⟩
    simp only [spf, dif_pos hs, List.getElem_ofFn]
    exact this
  · rw [finish_invalid (show (ctxX x).n ≤ x.source by change x.wg.n ≤ _; omega)]
    simp [spf, dif_neg hs, outVal, blank, encDist]

theorem key_lt (x : Input) {B : ℕ} (hB : codeMax (ncode x) * codeMax (ncode x) + 1 < B) (v : ℕ)
    (hv : (finish (ctxX x) x.source).stat v = 2) : (finish (ctxX x) x.source).key v + 1 < B := by
  by_cases hs : x.source < x.wg.n
  · obtain ⟨hI, -, -, -⟩ := finish_spec (ctxOK x) (adjOK x) hs
    have h1 := hI.kb v (by rw [hv]; omega)
    have h2 := card_done_le x.wg.n (finish (ctxX x) x.source)
    have h3 := Nat.mul_le_mul_right (codeMax (ncode x)) (h2.trans (n_le_codeMax x))
    omega
  · rw [finish_invalid (show (ctxX x).n ≤ x.source by change x.wg.n ≤ _; omega)] at hv
    simp [blank] at hv

theorem core_time (x : Input) {k : ℕ}
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

theorem core_spec : CodeSpec Prog.core spf coreTime needF := by
  intro B S A m x hR hKS hAS hneed hcB hcode hzero
  have hA : 32 ≤ A := by omega
  have hlen := length_ncode_input x
  have hnM := n_le_codeMax x
  have hsq : (codeMax (ncode x) + 1) * (codeMax (ncode x) + 1) =
      codeMax (ncode x) * codeMax (ncode x) + 2 * codeMax (ncode x) + 1 := by ring
  have hN : needF x = (3 * numEdges x + 4) + 10 * (x.wg.n + Dn x.wg.n + 3) + 6 * numEdges x +
      (x.wg.n + 1) + x.wg.n * (Dn x.wg.n + 1) + 1 +
      (codeMax (ncode x) + 1) * (codeMax (ncode x) + 1) := rfl
  have hTop : (layOf x A).top < B := by
    have : (layOf x A).top = A + (ncode x).length + 10 * (x.wg.n + Dn x.wg.n + 3) +
        6 * numEdges x + (x.wg.n + 1) + x.wg.n * (Dn x.wg.n + 1) := rfl
    omega
  have hKB : (x.wg.n + 1) * codeMax (ncode x) < B := by
    have := Nat.mul_le_mul_right (codeMax (ncode x)) (show x.wg.n + 1 ≤ codeMax (ncode x) + 1 by
      omega)
    have e : (codeMax (ncode x) + 1) * codeMax (ncode x) =
        codeMax (ncode x) * codeMax (ncode x) + codeMax (ncode x) := by ring
    omega
  have hMB : codeMax (ncode x) * codeMax (ncode x) + 1 < B := by omega
  have hM : MemAt m A (ncode x) := fun j hj => by
    have h := hcode j hj
    rw [vm_high hKS (by omega), getElem!_pos (ncode x) j hj] at h
    exact h
  have hz : ∀ a, A + (ncode x).length ≤ a → m a = 0 := fun a ha => by
    have h := hzero a ha
    rwa [vm_high hKS (by omega)] at h
  refine Runs.mono (core_run hR hA hTop hKB (fun v _ _ hs => key_lt x hMB v hs) hM hz)
    fun m' k ⟨R', z10, z17, z0, zO, zhi, hk'⟩ => ?_
  have hlo : (ncode (spf x)).length = x.wg.n + 1 := by rw [ncode_spf]; simp [length_spf]
  have hH : (layOf x A).H = A + (ncode x).length := rfl
  have hR9 : (layOf x A).H + 9 * (layOf x A).R =
      A + (ncode x).length + 9 * (x.wg.n + Dn x.wg.n + 3) := rfl
  refine ⟨R', ?_, ?_, ?_, fun j hj => ?_, fun v hv => ?_, fun a ha => ?_, core_time x hk'⟩
  · rw [z10, hR9]; omega
  · rw [z10, hR9, hlo]; omega
  · rw [z17, hlo]
  · rw [hlo] at hj
    rw [z10, vm_high hKS (by rw [hR9]; omega)]
    rcases j with _ | j
    · rw [Nat.add_zero, z0, ncode_spf]; rfl
    · rw [zO _ (by omega) (by omega), out_eq x (by omega)]
  · rw [ncode_spf] at hv
    rcases List.mem_cons.1 hv with rfl | hv
    · omega
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hv
      have := encDist_le x d hd
      omega
  · unfold vm
    split_ifs with h1 h2
    · exact zhi _ (by omega) (by omega)
    · rfl
    · exact zhi _ (by omega) (by omega)

/-- A TD word RAM with `<`, `+` and `−` finds shortest paths in `O(E + V log V)` steps. -/
theorem shortestPathsInEPlusVLogV : ShortestPathsInEPlusVLogV :=
  ⟨10432, solvableWithin_code (W := 16) (scale := 4) core_spec lenC_spec setS_spec layout_input
    skips_input layout_output readsBack_output
    (fun x h => by have := length_ncode_input x; rw [h] at this; simp at this)
    (by omega) (by omega) small_core hS_spf hneed_spf
    (fun x w hw hM => hbig_spf x w hw hM) hfy_spf shortestPaths spf_valid _ time_spf⟩

end Formalgo.Algorithms.ShortestPaths
