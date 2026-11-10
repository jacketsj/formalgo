import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Algorithm
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Context

/-!
# Memory and the model

LLM-generated; not checked by a human.

`Rep L σ m` says the memory `m` holds the model state `σ` in the layout `L`; `Fixed` covers the
data that does not change once built: the adjacency lists and the child-array addresses.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

/-- Where the arrays are. -/
structure Lay where
  n : ℕ
  D : ℕ
  E : ℕ
  H : ℕ

namespace Lay

variable (L : Lay)

/-- The stride of the arrays. -/
def R : ℕ := L.n + L.D + 3
/-- The start of the half-edges. -/
def HE : ℕ := L.H + 10 * L.R
/-- The start of the child arrays. -/
def CH : ℕ := L.HE + 6 * L.E
/-- The child array of `v`. -/
def cb (v : ℕ) : ℕ := if v = 0 then L.CH else L.CH + (L.n + 1) + (v - 1) * (L.D + 1)
/-- Its capacity. -/
def cap (v : ℕ) : ℕ := if v = 0 then L.n + 1 else L.D + 1
/-- The end of the child arrays. -/
def top : ℕ := L.CH + (L.n + 1) + L.n * (L.D + 1)
/-- The largest index of array `k`. -/
def bnd (k : ℕ) : ℕ := if k = 6 then L.D else L.n

/-- The addresses the heap writes. -/
def Dyn (a : ℕ) : Prop := (L.H ≤ a ∧ a < L.H + 7 * L.R) ∨ (L.CH ≤ a ∧ a < L.top)

end Lay

/-- Array `k` of the model. -/
def fld (σ : St) : ℕ → ℕ → ℕ
  | 0 => σ.key
  | 1 => σ.stat
  | 2 => σ.par
  | 3 => σ.deg
  | 4 => σ.mark
  | 5 => σ.pos
  | 6 => σ.tbl
  | _ => fun _ => 0

/-- Set entry `i` of array `k`. -/
def setFld (k i v : ℕ) (σ : St) : St :=
  match k with
  | 0 => { σ with key := update σ.key i v }
  | 1 => { σ with stat := update σ.stat i v }
  | 2 => { σ with par := update σ.par i v }
  | 3 => { σ with deg := update σ.deg i v }
  | 4 => { σ with mark := update σ.mark i v }
  | 5 => { σ with pos := update σ.pos i v }
  | 6 => { σ with tbl := update σ.tbl i v }
  | _ => σ

/-- Set child `j` of `p`. -/
def setCh (p j v : ℕ) (σ : St) : St := { σ with ch := update σ.ch p (update (σ.ch p) j v) }

/-- The scratch registers. -/
def Tmp (r : ℕ) : Prop :=
  r = 2 ∨ r = 6 ∨ r = 7 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 17 ∨ r = 30 ∨ r = 31

/-- The memory holds the model state. -/
structure Rep (L : Lay) (σ : St) (m : Mem) : Prop where
  H32 : 32 ≤ L.H
  base : ∀ k < 10, m (breg k) = L.H + k * L.R
  n : m 27 = L.n
  D : m 28 = L.D
  hmin : m 29 = σ.hmin
  one : m 3 = 1
  zero : m 8 = 0
  three : m 16 = 3
  arr : ∀ k < 7, ∀ i ≤ L.bnd k, m (L.H + k * L.R + i) = fld σ k i
  ch : ∀ v ≤ L.n, ∀ j < L.cap v, m (L.cb v + j) = σ.ch v j

variable {L : Lay} {σ : St} {m m' : Mem}

theorem breg_lt (k : ℕ) (hk : k < 10) : breg k < 32 := by unfold breg; split_ifs <;> omega

theorem breg_not_tmp {k : ℕ} (hk : k < 10) : ¬Tmp (breg k) := by
  unfold breg Tmp; split_ifs <;> omega

theorem bnd_lt_R (k : ℕ) : L.bnd k < L.R := by unfold Lay.bnd Lay.R; split_ifs <;> omega

theorem cb_slot {v j : ℕ} (hv : v ≤ L.n) (hj : j < L.cap v) :
    L.CH ≤ L.cb v + j ∧ L.cb v + j < L.top := by
  unfold Lay.cb Lay.cap Lay.top at *
  split_ifs at * with h
  · omega
  · have : (v - 1) * (L.D + 1) + (L.D + 1) ≤ L.n * (L.D + 1) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega

theorem cb_inj {v j v' j' : ℕ} (hj : j < L.cap v) (hj' : j' < L.cap v')
    (h : L.cb v + j = L.cb v' + j') : v = v' ∧ j = j' := by
  unfold Lay.cb Lay.cap at *
  split_ifs at * with h1 h2 h2
  · omega
  · have : 0 ≤ (v' - 1) * (L.D + 1) := Nat.zero_le _; omega
  · have : 0 ≤ (v - 1) * (L.D + 1) := Nat.zero_le _; omega
  · have e : (v - 1) * (L.D + 1) + j = (v' - 1) * (L.D + 1) + j' := by omega
    have h3 := congrArg (· / (L.D + 1)) e
    have h4 := congrArg (· % (L.D + 1)) e
    simp only [Nat.mul_comm (v - 1), Nat.mul_comm (v' - 1), Nat.mul_add_div (by omega : 0 < L.D + 1),
      Nat.mul_add_mod, Nat.div_eq_of_lt hj, Nat.div_eq_of_lt hj', Nat.mod_eq_of_lt hj,
      Nat.mod_eq_of_lt hj'] at h3 h4
    omega

theorem CH_ge : L.H + 10 * L.R ≤ L.CH := by unfold Lay.CH Lay.HE; omega

/-- Changes outside `Rep`'s cells keep it. -/
theorem Rep.congr (h : Rep L σ m) (hm : ∀ a, ¬Tmp a → a < 32 → m' a = m a)
    (hhi : ∀ a, 32 ≤ a → m' a = m a) : Rep L σ m' := by
  have hr : ∀ a, ¬Tmp a → m' a = m a := fun a ha => by
    by_cases h32 : a < 32
    · exact hm a ha h32
    · exact hhi a (by omega)
  refine ⟨h.H32, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk i hi => ?_, fun v hv j hj => ?_⟩
  · rw [hr _ (breg_not_tmp hk)]; exact h.base k hk
  · rw [hr 27 (by simp [Tmp])]; exact h.n
  · rw [hr 28 (by simp [Tmp])]; exact h.D
  · rw [hr 29 (by simp [Tmp])]; exact h.hmin
  · rw [hr 3 (by simp [Tmp])]; exact h.one
  · rw [hr 8 (by simp [Tmp])]; exact h.zero
  · rw [hr 16 (by simp [Tmp])]; exact h.three
  · rw [hhi _ (by have := h.H32; omega)]; exact h.arr k hk i hi
  · rw [hhi _ (by have := cb_slot hv hj; have := h.H32; have := CH_ge (L := L); omega)]
    exact h.ch v hv j hj

theorem fld_setFld_self {k i v : ℕ} (hk : k < 7) : fld (setFld k i v σ) k = update (fld σ k) i v := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> first | rfl | omega

theorem fld_setFld_ne {k k' i v : ℕ} (hk : k < 7) (hne : k' ≠ k) :
    fld (setFld k i v σ) k' = fld σ k' := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    (rcases k' with _ | _ | _ | _ | _ | _ | _ | k') <;> first | rfl | omega

theorem ch_setFld {k i v : ℕ} : (setFld k i v σ).ch = σ.ch := by
  unfold setFld; split <;> rfl

theorem hmin_setFld {k i v : ℕ} : (setFld k i v σ).hmin = σ.hmin := by
  unfold setFld; split <;> rfl

/-- Storing into array `k`. -/
theorem Rep.store (h : Rep L σ m) {k i v : ℕ} (hk : k < 7) (hi : i ≤ L.bnd k) :
    Rep L (setFld k i v σ) (update m (L.H + k * L.R + i) v) := by
  have hR := bnd_lt_R (L := L) k
  have hH := h.H32
  have hCH := CH_ge (L := L)
  have hne : ∀ a, a < 32 → a ≠ L.H + k * L.R + i := fun a ha => by omega
  refine ⟨hH, fun k' hk' => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k' hk' i' hi' => ?_,
    fun v' hv' j hj => ?_⟩
  · rw [update_of_ne (hne _ (breg_lt k' hk'))]; exact h.base k' hk'
  · rw [update_of_ne (hne 27 (by omega))]; exact h.n
  · rw [update_of_ne (hne 28 (by omega))]; exact h.D
  · rw [update_of_ne (hne 29 (by omega)), hmin_setFld]; exact h.hmin
  · rw [update_of_ne (hne 3 (by omega))]; exact h.one
  · rw [update_of_ne (hne 8 (by omega))]; exact h.zero
  · rw [update_of_ne (hne 16 (by omega))]; exact h.three
  · have hR' := bnd_lt_R (L := L) k'
    rcases eq_or_ne k' k with rfl | hkk
    · rw [fld_setFld_self hk, update_apply, update_apply]
      by_cases hii : i' = i
      · subst hii; simp
      · rw [if_neg (by omega), if_neg hii]; exact h.arr k' hk' i' hi'
    · rw [fld_setFld_ne hk hkk, update_of_ne]
      · exact h.arr k' hk' i' hi'
      · intro he
        have : k' * L.R + i' = k * L.R + i := by omega
        rcases lt_or_gt_of_ne hkk with hlt | hlt
        · have := Nat.mul_le_mul_right L.R (show k' + 1 ≤ k by omega)
          rw [Nat.succ_mul] at this; omega
        · have := Nat.mul_le_mul_right L.R (show k + 1 ≤ k' by omega)
          rw [Nat.succ_mul] at this; omega
  · have := cb_slot hv' hj
    have hk7 : k * L.R + i < 7 * L.R := by
      have := Nat.mul_le_mul_right L.R (show k + 1 ≤ 7 by omega); rw [Nat.succ_mul] at this; omega
    rw [update_of_ne (by omega), ch_setFld]; exact h.ch v' hv' j hj

/-- Storing into a child array. -/
theorem Rep.chstore (h : Rep L σ m) {p j v : ℕ} (hp : p ≤ L.n) (hj : j < L.cap p) :
    Rep L (setCh p j v σ) (update m (L.cb p + j) v) := by
  have hH := h.H32
  have hCH := CH_ge (L := L)
  have hs := cb_slot hp hj
  have hne : ∀ a, a < 32 → a ≠ L.cb p + j := fun a ha => by omega
  refine ⟨hH, fun k' hk' => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k' hk' i' hi' => ?_,
    fun v' hv' j' hj' => ?_⟩
  · rw [update_of_ne (hne _ (breg_lt k' hk'))]; exact h.base k' hk'
  · rw [update_of_ne (hne 27 (by omega))]; exact h.n
  · rw [update_of_ne (hne 28 (by omega))]; exact h.D
  · rw [update_of_ne (hne 29 (by omega))]; exact h.hmin
  · rw [update_of_ne (hne 3 (by omega))]; exact h.one
  · rw [update_of_ne (hne 8 (by omega))]; exact h.zero
  · rw [update_of_ne (hne 16 (by omega))]; exact h.three
  · have hR' := bnd_lt_R (L := L) k'
    have hk7 : k' * L.R + i' < 7 * L.R := by
      have := Nat.mul_le_mul_right L.R (show k' + 1 ≤ 7 by omega); rw [Nat.succ_mul] at this; omega
    rw [update_of_ne (by omega)]; exact h.arr k' hk' i' hi'
  · change update m (L.cb p + j) v (L.cb v' + j') = update σ.ch p (update (σ.ch p) j v) v' j'
    by_cases he : L.cb v' + j' = L.cb p + j
    · obtain ⟨rfl, rfl⟩ := cb_inj hj' hj he
      simp
    · rw [update_of_ne he]
      rw [h.ch v' hv' j' hj']
      by_cases hvp : v' = p
      · subst hvp; rw [update_self, update_of_ne (fun hc => he (by rw [hc]))]
      · rw [update_of_ne hvp]

/-! ### The data that does not change -/

/-- The half-edges from `h` list `l`. -/
def Lst (L : Lay) (m : Mem) : ℕ → List (ℕ × ℕ) → Prop
  | h, [] => h = 0
  | h, (v, w) :: l => L.HE ≤ h ∧ h + 3 ≤ L.CH ∧ m (h + 1) = v ∧ m (h + 2) = w ∧ Lst L m (m h) l

/-- The adjacency lists and the child-array addresses. -/
structure Fixed (L : Lay) (x : EInput) (m : Mem) : Prop where
  head : ∀ v ≤ L.n, Lst L m (m (L.H + 7 * L.R + v)) (adjX x v)
  cbv : ∀ v ≤ L.n, m (L.H + 8 * L.R + v) = L.cb v

theorem Lst.frame (H32 : 32 ≤ L.H) (hm : ∀ a, 32 ≤ a → ¬L.Dyn a → m' a = m a) :
    ∀ (l : List (ℕ × ℕ)) (h : ℕ), Lst L m h l → Lst L m' h l
  | [], h, hl => hl
  | (v, w) :: l, h, ⟨h1, h2, h3, h4, h5⟩ => by
    have hHE : L.H + 7 * L.R ≤ L.HE := by unfold Lay.HE; omega
    have nd : ∀ a, L.HE ≤ a → a < L.CH → ¬L.Dyn a := fun a ha ha' hd => by
      unfold Lay.Dyn Lay.top at hd; omega
    have e : ∀ a, L.HE ≤ a → a < L.CH → m' a = m a := fun a ha ha' => hm a (by omega) (nd a ha ha')
    refine ⟨h1, h2, by rw [e _ (by omega) (by omega)]; exact h3,
      by rw [e _ (by omega) (by omega)]; exact h4, ?_⟩
    rw [e h h1 (by omega)]
    exact Lst.frame H32 hm l _ h5

theorem Fixed.frame {x : EInput} (hF : Fixed L x m) (H32 : 32 ≤ L.H)
    (hm : ∀ a, 32 ≤ a → ¬L.Dyn a → m' a = m a) : Fixed L x m' := by
  have hR : L.H + 9 * L.R ≤ L.HE := by unfold Lay.HE; omega
  have hCH := CH_ge (L := L)
  have nd : ∀ a, L.H + 7 * L.R ≤ a → a < L.H + 9 * L.R → ¬L.Dyn a := fun a ha ha' hd => by
    unfold Lay.Dyn Lay.top at hd; omega
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · have hR' : v < L.R := by unfold Lay.R; omega
    rw [hm _ (by omega) (nd _ (by omega) (by omega))]
    exact Lst.frame H32 hm _ _ (hF.head v hv)
  · have hR' : v < L.R := by unfold Lay.R; omega
    rw [hm _ (by omega) (nd _ (by omega) (by omega))]; exact hF.cbv v hv

end Formalgo.Algorithms.ShortestPaths
