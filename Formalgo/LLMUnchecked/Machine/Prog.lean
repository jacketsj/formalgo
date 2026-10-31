import Formalgo.LLMUnchecked.Machine.Harness

/-!
# Registers and virtual memory

LLM-generated; not checked by a human.

Fixed registers, and the memory a body sees: cells below `nK` come from the buffer at `S`, so
that registers are separate from it.
-/

namespace Formalgo.LLMUnchecked

open Function Cmd

/-- The number of registers. -/
scoped notation "nK" => (32 : ℕ)
/-- Register holding `S`. -/
scoped notation "rS" => (1 : ℕ)
/-- Register holding `1`. -/
scoped notation "rOne" => (3 : ℕ)
/-- Register holding `nK`. -/
scoped notation "rK" => (5 : ℕ)
/-- Register for comparisons in `vaddr`. -/
scoped notation "rT" => (6 : ℕ)
/-- Register for physical addresses in `vaddr`. -/
scoped notation "rP" => (7 : ℕ)

/-- Close a goal about reads of updated memories by cases. -/
macro "memo" : tactic => `(tactic| first
  | omega
  | ((try simp (disch := omega) only [Function.update_self, Function.update_of_ne])
     first
       | omega
       | (split_ifs <;> omega)
       | (simp only [Function.update_apply]; split_ifs <;> omega)))

/-- `memo`, also rewriting with the given conditional equations. -/
macro "memo" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| first
  | omega
  | ((try simp (disch := omega) only [Function.update_self, Function.update_of_ne, $ts,*])
     first
       | omega
       | (split_ifs <;> omega)
       | (simp only [Function.update_apply]; split_ifs <;> omega)))

/-- The memory a body sees: the buffer in place of the registers, and `0` where it is. -/
def vm (S : ℕ) (m : Mem) (a : ℕ) : ℕ :=
  if a < nK then m (S + a) else if S ≤ a ∧ a < S + nK then 0 else m a

/-- The fixed registers hold their values. -/
def Regs (S : ℕ) (m : Mem) : Prop := m rS = S ∧ m rOne = 1 ∧ m rK = nK

theorem vm_high {S a : ℕ} {m : Mem} (hKS : nK ≤ S) (ha : S + nK ≤ a) : vm S m a = m a := by
  simp only [vm]; split_ifs <;> omega

theorem vm_update_reg {S r v : ℕ} {m : Mem} (hr : r < nK) (hS : nK ≤ S) :
    vm S (update m r v) = vm S m := by
  funext a; simp only [vm, update_apply]; split_ifs <;> first | rfl | omega

theorem vm_update_high {S p v : ℕ} {m : Mem} (hp : nK ≤ p) (hpS : p < S ∨ S + nK ≤ p) :
    vm S (update m p v) = update (vm S m) p v := by
  funext a
  by_cases ha : a = p
  · subst ha; simp only [vm, update_apply, if_pos rfl]; split_ifs <;> first | rfl | omega
  · simp only [vm, update_apply, ha, if_false]
    split_ifs <;> first | rfl | omega

theorem vm_update_buf {S j v : ℕ} {m : Mem} (hj : j < nK) :
    vm S (update m (S + j) v) = update (vm S m) j v := by
  funext a
  by_cases ha : a = j
  · subst ha; simp [vm, hj]
  · simp only [vm, update_apply, ha, if_false]
    split_ifs <;> first | rfl | omega

theorem Regs.update {S r v : ℕ} {m : Mem} (h : Regs S m) (hr : r ≠ rS ∧ r ≠ rOne ∧ r ≠ rK) :
    Regs S (Function.update m r v) := by
  obtain ⟨h1, h3, h5⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp [update_apply, *] <;> omega

/-- The physical address of virtual address `M[va]`, into `rP`. -/
def vaddr (va : ℕ) : Cmd := seq (less rT va rK) (ite rT rOne (add rP va rS) (copy rP va))

/-- `M[d] := vm[M[va]]`. -/
def vread (d va : ℕ) : Cmd := seq (vaddr va) (load d rP)

/-- `vm[M[va]] := M[src]`. -/
def vwrite (va src : ℕ) : Cmd := seq (vaddr va) (store rP src)

/-- The physical address of a virtual address. -/
def paddr (S a : ℕ) : ℕ := if a < nK then S + a else a

theorem exec_vaddr {B S va : ℕ} {m : Mem} (hR : Regs S m) (hva : va < nK) (hvaT : va ≠ rT)
    (hB : S + nK < B) :
    ∃ m' k, Exec B (vaddr va) m k m' ∧ k ≤ 4 ∧ m' rP = paddr S (m va) ∧
      ∀ a, a ≠ rT → a ≠ rP → m' a = m a := by
  obtain ⟨h1, h3, h5⟩ := hR
  have hl := Exec.less (B := B) (m := m) (d := rT) (l := va) (r := rK) (by omega) (by omega)
    (by omega)
  set m₁ := update m rT (if m va < m rK then 1 else 0)
  have h₁va : m₁ va = m va := by simp [m₁, update_apply, hvaT]
  have h₁1 : m₁ rS = S := by simp [m₁, update_apply, h1]
  have h₁3 : m₁ rOne = 1 := by simp [m₁, update_apply, h3]
  by_cases hlt : m va < nK
  · have e := Exec.iteTrue (B := B) (m := m₁) (l := rT) (r := rOne) (e := copy rP va)
      (by omega) (by omega) (by simp [m₁, update_apply, h3, h5, hlt])
      (.add (m := m₁) (d := rP) (l := va) (r := rS) (by omega) (by omega) (by omega)
        (by rw [h₁va, h₁1]; omega))
    refine ⟨_, _, .seq hl e, by omega, ?_, ?_⟩
    · simp [paddr, hlt, h₁va, h₁1, Nat.add_comm]
    · intro a ha hb; simp [m₁, update_apply, ha, hb]
  · have e := Exec.iteFalse (B := B) (m := m₁) (l := rT) (r := rOne) (t := add rP va rS)
      (by omega) (by omega) (by simp [m₁, update_apply, h3, h5, hlt])
      (.copy (m := m₁) (d := rP) (s := va) (by omega) (by omega))
    refine ⟨_, _, .seq hl e, by omega, ?_, ?_⟩
    · simp [paddr, hlt, h₁va]
    · intro a ha hb; simp [m₁, update_apply, ha, hb]

theorem vm_of_frame {S : ℕ} {m m' : Mem} (hKS : nK ≤ S)
    (h : ∀ a, a ≠ rT → a ≠ rP → m' a = m a) : vm S m' = vm S m := by
  funext a; simp only [vm]; split_ifs <;> first | rfl | exact h _ (by omega) (by omega)

theorem Regs.of_frame {S : ℕ} {m m' : Mem} (hR : Regs S m)
    (h : ∀ a, a ≠ rT → a ≠ rP → m' a = m a) : Regs S m' := by
  obtain ⟨a, b, c⟩ := hR
  exact ⟨by rw [h _ (by omega) (by omega), a], by rw [h _ (by omega) (by omega), b],
    by rw [h _ (by omega) (by omega), c]⟩

theorem paddr_read {S a : ℕ} {m m' : Mem} (hKS : nK ≤ S) (ha : a < S ∨ S + nK ≤ a)
    (h : ∀ a, a ≠ rT → a ≠ rP → m' a = m a) : m' (paddr S a) = vm S m a := by
  unfold paddr vm; split_ifs <;> first | omega | exact h _ (by omega) (by omega)

theorem exec_vread {B S d va : ℕ} {m : Mem} (hR : Regs S m) (hva : va < nK) (hvaT : va ≠ rT)
    (hd : d < nK) (hdR : d ≠ rS ∧ d ≠ rOne ∧ d ≠ rK) (hKS : nK ≤ S) (hB : S + nK < B)
    (hsrc : m va < S ∨ S + nK ≤ m va) :
    ∃ m' k, Exec B (vread d va) m k m' ∧ k ≤ 5 ∧ Regs S m' ∧ m' d = vm S m (m va) ∧
      vm S m' = vm S m ∧ ∀ a, a ≠ rT → a ≠ rP → a ≠ d → m' a = m a := by
  obtain ⟨m₁, k₁, e₁, hk₁, h₁P, h₁⟩ := exec_vaddr (B := B) hR hva hvaT hB
  have e₂ := Exec.load (B := B) (m := m₁) (d := d) (p := rP) (by omega) (by omega)
  refine ⟨_, _, .seq e₁ e₂, by omega, (hR.of_frame h₁).update hdR, ?_, ?_, ?_⟩
  · simp [h₁P, paddr_read hKS hsrc h₁]
  · rw [vm_update_reg hd hKS, vm_of_frame hKS h₁]
  · intro a ha hb hc; simp [update_apply, hc, h₁ a ha hb]

theorem exec_vwrite {B S va src : ℕ} {m : Mem} (hR : Regs S m) (hva : va < nK) (hvaT : va ≠ rT)
    (hsrcK : src < nK) (hsrc : src ≠ rT ∧ src ≠ rP) (hKS : nK ≤ S) (hB : S + nK < B)
    (hdst : m va < S ∨ S + nK ≤ m va) :
    ∃ m' k, Exec B (vwrite va src) m k m' ∧ k ≤ 5 ∧ Regs S m' ∧
      vm S m' = update (vm S m) (m va) (m src) ∧ ∀ a < nK, a ≠ rT → a ≠ rP → m' a = m a := by
  obtain ⟨m₁, k₁, e₁, hk₁, h₁P, h₁⟩ := exec_vaddr (B := B) hR hva hvaT hB
  have e₂ := Exec.store (B := B) (m := m₁) (p := rP) (s := src) (by omega) (by omega)
  have hsrc₁ : m₁ src = m src := h₁ _ hsrc.1 hsrc.2
  have hR₁ := hR.of_frame h₁
  refine ⟨_, _, .seq e₁ e₂, by omega, ?_, ?_, ?_⟩
  · obtain ⟨a, b, c⟩ := hR₁
    rw [h₁P]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [update_apply, paddr] <;> split_ifs <;> first
      | assumption | omega
  · rw [h₁P, hsrc₁]
    unfold paddr
    split_ifs with hlt
    · rw [vm_update_buf hlt, vm_of_frame hKS h₁]
    · rw [vm_update_high (by omega) hdst, vm_of_frame hKS h₁]
  · intro a ha hb hc
    rw [h₁P]; simp only [update_apply, paddr]
    split_ifs <;> first | omega | exact h₁ a hb hc

/-! ### Running commands, by continuations -/

/-- `c` runs from `m` to a memory and cost satisfying `Q`. -/
def Runs (B : ℕ) (c : Cmd) (m : Mem) (Q : Mem → ℕ → Prop) : Prop :=
  ∃ m' k, Exec B c m k m' ∧ Q m' k

namespace Runs

variable {B : ℕ} {m : Mem} {Q : Mem → ℕ → Prop}

theorem seq {a b : Cmd} (h : Runs B a m fun m₁ k₁ => Runs B b m₁ fun m₂ k₂ => Q m₂ (k₁ + k₂)) :
    Runs B (.seq a b) m Q := by
  obtain ⟨m₁, k₁, e₁, m₂, k₂, e₂, hQ⟩ := h
  exact ⟨m₂, k₁ + k₂, .seq e₁ e₂, hQ⟩

theorem seqs_cons {c : Cmd} {cs : List Cmd}
    (h : Runs B c m fun m₁ k₁ => Runs B (seqs cs) m₁ fun m₂ k₂ => Q m₂ (k₁ + k₂)) :
    Runs B (seqs (c :: cs)) m Q := seq h

theorem seqs_nil (hB : 2 < B) (h : Q (update m 2 0) 1) : Runs B (seqs []) m Q :=
  ⟨_, _, .const hB (by omega), h⟩

theorem const {d v : ℕ} (hd : d < B) (hv : v < B) (h : Q (update m d v) 1) :
    Runs B (.const d v) m Q := ⟨_, _, .const hd hv, h⟩

theorem copy {d s : ℕ} (hd : d < B) (hs : s < B) (h : Q (update m d (m s)) 1) :
    Runs B (.copy d s) m Q := ⟨_, _, .copy hd hs, h⟩

theorem load {d p : ℕ} (hd : d < B) (hp : p < B) (h : Q (update m d (m (m p))) 1) :
    Runs B (.load d p) m Q := ⟨_, _, .load hd hp, h⟩

theorem store {p s : ℕ} (hp : p < B) (hs : s < B) (h : Q (update m (m p) (m s)) 1) :
    Runs B (.store p s) m Q := ⟨_, _, .store hp hs, h⟩

theorem add {d l r : ℕ} (hd : d < B) (hl : l < B) (hr : r < B) (hlr : m l + m r < B)
    (h : Q (update m d (m l + m r)) 1) : Runs B (.add d l r) m Q :=
  ⟨_, _, .add hd hl hr hlr, h⟩

theorem sub {d l r : ℕ} (hd : d < B) (hl : l < B) (hr : r < B) (hlr : m r ≤ m l)
    (h : Q (update m d (m l - m r)) 1) : Runs B (.sub d l r) m Q :=
  ⟨_, _, .sub hd hl hr hlr, h⟩

theorem less {d l r : ℕ} (hd : d < B) (hl : l < B) (hr : r < B)
    (h : Q (update m d (if m l < m r then 1 else 0)) 1) : Runs B (.less d l r) m Q :=
  ⟨_, _, .less hd hl hr, h⟩

theorem ite {l r : ℕ} {t e : Cmd} (hl : l < B) (hr : r < B)
    (ht : m l = m r → Runs B t m fun m' k => Q m' (k + 2))
    (he : m l ≠ m r → Runs B e m fun m' k => Q m' (k + 1)) : Runs B (.ite l r t e) m Q := by
  by_cases h : m l = m r
  · obtain ⟨m', k, e', hQ⟩ := ht h; exact ⟨m', k + 2, .iteTrue hl hr h e', hQ⟩
  · obtain ⟨m', k, e', hQ⟩ := he h; exact ⟨m', k + 1, .iteFalse hl hr h e', hQ⟩

theorem loop {l r : ℕ} {body : Cmd} (P : Mem → ℕ → Prop) (μ : Mem → ℕ) (hl : l < B) (hr : r < B)
    (hstep : ∀ m s, P m s → m l = m r →
      Runs B body m fun m' k => P m' (s + k + 2) ∧ μ m' < μ m)
    (hexit : ∀ m s, P m s → m l ≠ m r → Q m (s + 1)) (h0 : P m 0) :
    Runs B (.loop l r body) m Q := by
  obtain ⟨m', k, e, hQ⟩ := Exec.loop_of P μ Q hl hr
    (fun m s hP heq => by
      obtain ⟨m', k, e, hP', hμ⟩ := hstep m s hP heq
      exact ⟨m', k, e, hP', hμ⟩) hexit m 0 h0
  exact ⟨m', k, e, by simpa using hQ⟩

theorem mono {c : Cmd} {Q' : Mem → ℕ → Prop} (h : Runs B c m Q) (hQ : ∀ m k, Q m k → Q' m k) :
    Runs B c m Q' := by
  obtain ⟨m', k, e, hq⟩ := h; exact ⟨m', k, e, hQ _ _ hq⟩

theorem vread {S d va : ℕ} (hR : Regs S m) (hva : va < nK) (hvaT : va ≠ rT) (hd : d < nK)
    (hdR : d ≠ rS ∧ d ≠ rOne ∧ d ≠ rK) (hKS : nK ≤ S) (hB : S + nK < B)
    (hsrc : m va < S ∨ S + nK ≤ m va)
    (h : ∀ m' k, k ≤ 5 → Regs S m' → m' d = vm S m (m va) → vm S m' = vm S m →
      (∀ a, a ≠ rT → a ≠ rP → a ≠ d → m' a = m a) → Q m' k) :
    Runs B (vread d va) m Q := by
  obtain ⟨m', k, e, hk, hR', hd', hvm, hfr⟩ := exec_vread hR hva hvaT hd hdR hKS hB hsrc
  exact ⟨m', k, e, h m' k hk hR' hd' hvm hfr⟩

theorem vwrite {S va src : ℕ} (hR : Regs S m) (hva : va < nK) (hvaT : va ≠ rT)
    (hsrcK : src < nK) (hsrc : src ≠ rT ∧ src ≠ rP) (hKS : nK ≤ S) (hB : S + nK < B)
    (hdst : m va < S ∨ S + nK ≤ m va)
    (h : ∀ m' k, k ≤ 5 → Regs S m' → vm S m' = update (vm S m) (m va) (m src) →
      (∀ a < nK, a ≠ rT → a ≠ rP → m' a = m a) → Q m' k) :
    Runs B (vwrite va src) m Q := by
  obtain ⟨m', k, e, hk, hR', hvm, hfr⟩ := exec_vwrite hR hva hvaT hsrcK hsrc hKS hB hdst
  exact ⟨m', k, e, h m' k hk hR' hvm hfr⟩

/-! Register commands, with the new memory kept abstract. -/

theorem constR {d v : ℕ} (hd : d < B) (hv : v < B)
    (h : ∀ m', m' d = v → (∀ a, a ≠ d → m' a = m a) → Q m' 1) : Runs B (.const d v) m Q :=
  const hd hv (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem copyR {d s : ℕ} (hd : d < B) (hs : s < B)
    (h : ∀ m', m' d = m s → (∀ a, a ≠ d → m' a = m a) → Q m' 1) : Runs B (.copy d s) m Q :=
  copy hd hs (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem loadR {d p : ℕ} (hd : d < B) (hp : p < B)
    (h : ∀ m', m' d = m (m p) → (∀ a, a ≠ d → m' a = m a) → Q m' 1) : Runs B (.load d p) m Q :=
  load hd hp (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem storeR {p s : ℕ} (hp : p < B) (hs : s < B)
    (h : ∀ m', m' (m p) = m s → (∀ a, a ≠ m p → m' a = m a) → Q m' 1) :
    Runs B (.store p s) m Q :=
  store hp hs (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem addR {d l r : ℕ} (hd : d < B) (hl : l < B) (hr : r < B) (hlr : m l + m r < B)
    (h : ∀ m', m' d = m l + m r → (∀ a, a ≠ d → m' a = m a) → Q m' 1) :
    Runs B (.add d l r) m Q :=
  add hd hl hr hlr (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem subR {d l r : ℕ} (hd : d < B) (hl : l < B) (hr : r < B) (hlr : m r ≤ m l)
    (h : ∀ m', m' d = m l - m r → (∀ a, a ≠ d → m' a = m a) → Q m' 1) :
    Runs B (.sub d l r) m Q :=
  sub hd hl hr hlr (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem lessR {d l r : ℕ} (hd : d < B) (hl : l < B) (hr : r < B)
    (h : ∀ m', m' d = (if m l < m r then 1 else 0) → (∀ a, a ≠ d → m' a = m a) → Q m' 1) :
    Runs B (.less d l r) m Q :=
  less hd hl hr (h _ (by simp) fun a ha => by simp [update_apply, ha])

theorem seqs_nilR (hB : 2 < B) (h : ∀ m', m' 2 = 0 → (∀ a, a ≠ 2 → m' a = m a) → Q m' 1) :
    Runs B (seqs []) m Q :=
  seqs_nil hB (h _ (by simp) fun a ha => by simp [update_apply, ha])

end Runs

theorem vm_of_reg {S d : ℕ} {m m' : Mem} (hd : d < nK) (hKS : nK ≤ S)
    (h : ∀ a, a ≠ d → m' a = m a) : vm S m' = vm S m := by
  funext a; simp only [vm]; split_ifs <;> first | rfl | exact h _ (by omega)

theorem Regs.of_reg {S d : ℕ} {m m' : Mem} (hR : Regs S m) (hd : d ≠ rS ∧ d ≠ rOne ∧ d ≠ rK)
    (h : ∀ a, a ≠ d → m' a = m a) : Regs S m' := by
  obtain ⟨a, b, c⟩ := hR
  exact ⟨by rw [h _ (by omega), a], by rw [h _ (by omega), b], by rw [h _ (by omega), c]⟩

theorem vm_of_store {S p v : ℕ} {m m' : Mem} (hp : nK ≤ p) (hpS : p < S ∨ S + nK ≤ p)
    (hv : m' p = v) (h : ∀ a, a ≠ p → m' a = m a) : vm S m' = update (vm S m) p v := by
  have : m' = update m p v := by
    funext a; by_cases ha : a = p
    · subst ha; simp [hv]
    · simp [update_apply, ha, h a ha]
  rw [this, vm_update_high hp hpS]

namespace Runs

variable {B : ℕ} {m : Mem} {Q : Mem → ℕ → Prop}

/-! Register commands, also keeping `vm`. -/

theorem constV {S d v : ℕ} (hKS : nK ≤ S) (hdK : d < nK) (hd : d < B) (hv : v < B)
    (h : ∀ m', m' d = v → (∀ a, a ≠ d → m' a = m a) → vm S m' = vm S m → Q m' 1) :
    Runs B (.const d v) m Q :=
  constR hd hv fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg hdK hKS h₂)

theorem copyV {S d s : ℕ} (hKS : nK ≤ S) (hdK : d < nK) (hd : d < B) (hs : s < B)
    (h : ∀ m', m' d = m s → (∀ a, a ≠ d → m' a = m a) → vm S m' = vm S m → Q m' 1) :
    Runs B (.copy d s) m Q :=
  copyR hd hs fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg hdK hKS h₂)

theorem loadV {S d p : ℕ} (hKS : nK ≤ S) (hdK : d < nK) (hd : d < B) (hp : p < B)
    (h : ∀ m', m' d = m (m p) → (∀ a, a ≠ d → m' a = m a) → vm S m' = vm S m → Q m' 1) :
    Runs B (.load d p) m Q :=
  loadR hd hp fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg hdK hKS h₂)

theorem addV {S d l r : ℕ} (hKS : nK ≤ S) (hdK : d < nK) (hd : d < B) (hl : l < B) (hr : r < B)
    (hlr : m l + m r < B)
    (h : ∀ m', m' d = m l + m r → (∀ a, a ≠ d → m' a = m a) → vm S m' = vm S m → Q m' 1) :
    Runs B (.add d l r) m Q :=
  addR hd hl hr hlr fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg hdK hKS h₂)

theorem subV {S d l r : ℕ} (hKS : nK ≤ S) (hdK : d < nK) (hd : d < B) (hl : l < B) (hr : r < B)
    (hlr : m r ≤ m l)
    (h : ∀ m', m' d = m l - m r → (∀ a, a ≠ d → m' a = m a) → vm S m' = vm S m → Q m' 1) :
    Runs B (.sub d l r) m Q :=
  subR hd hl hr hlr fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg hdK hKS h₂)

theorem lessV {S d l r : ℕ} (hKS : nK ≤ S) (hdK : d < nK) (hd : d < B) (hl : l < B)
    (hr : r < B)
    (h : ∀ m', m' d = (if m l < m r then 1 else 0) → (∀ a, a ≠ d → m' a = m a) →
      vm S m' = vm S m → Q m' 1) :
    Runs B (.less d l r) m Q :=
  lessR hd hl hr fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg hdK hKS h₂)

theorem seqs_nilV {S : ℕ} (hKS : nK ≤ S) (hB : 2 < B)
    (h : ∀ m', m' 2 = 0 → (∀ a, a ≠ 2 → m' a = m a) → vm S m' = vm S m → Q m' 1) :
    Runs B (seqs []) m Q :=
  seqs_nilR hB fun m' h₁ h₂ => h m' h₁ h₂ (vm_of_reg (by omega) hKS h₂)

end Runs

/-- Solve a goal about register values, from the facts in context. -/
macro "rs" : tactic => `(tactic| first
  | omega
  | ((simp (disch := omega) only [*, Function.update_self, Function.update_of_ne]) <;> first
      | omega
      | (split_ifs <;> omega)))

/-- Run the next register command. -/
macro "rstep" : tactic => `(tactic| first
  | refine Runs.seqs_cons ?_
  | refine Runs.seq ?_
  | (refine Runs.seqs_nilV (by assumption) (by omega) ?_; intro _ _ _ _)
  | (refine Runs.constV (by assumption) (by omega) (by omega) (by omega) ?_; intro _ _ _ _)
  | (refine Runs.copyV (by assumption) (by omega) (by omega) (by omega) ?_; intro _ _ _ _)
  | (refine Runs.loadV (by assumption) (by omega) (by omega) (by omega) ?_; intro _ _ _ _)
  | (refine Runs.addV (by assumption) (by omega) (by omega) (by omega) (by omega) (by rs) ?_;
      intro _ _ _ _)
  | (refine Runs.subV (by assumption) (by omega) (by omega) (by omega) (by omega) (by rs) ?_;
      intro _ _ _ _)
  | (refine Runs.lessV (by assumption) (by omega) (by omega) (by omega) (by omega) ?_;
      intro _ _ _ _))

/-- The harness, with the body described through `vm`. -/
theorem exec_harness_vm {B S N : ℕ} {setS body : Cmd} {m₀ m₁ : Mem} {k₀ : ℕ} (final : Mem)
    (T : ℕ) (hKS : nK ≤ S) (hNS : N ≤ S) (hB : S + nK < B)
    (hset : Exec B setS m₀ k₀ m₁) (hm₁0 : m₁ 0 = S) (hm₁ : ∀ a, a ≠ 0 → a ≠ 2 → m₁ a = m₀ a)
    (h00 : m₀ 0 = 1) (h02 : m₀ 2 = 0) (h03 : m₀ 3 = 1) (hblank : ∀ a, S ≤ a → m₀ a = 0)
    (hf0 : final 0 = 1) (hf2 : final 2 = 0)
    (hbody : ∀ m, m rS = S → (∀ a, vm S m a = m₀ a) → (∀ r, 3 ≤ r → r < nK → m r = m₀ r) →
      ∃ m' k, Exec B body m k m' ∧ k ≤ T ∧ m' rS = S ∧
        ∀ a < S, a ≠ 0 → a ≠ 2 → vm S m' a = final a) :
    ∃ m' k, Exec B (harness nK setS body) m₀ k m' ∧ k ≤ k₀ + T + 8 * nK ∧
      ∀ i < N, m' i = final i := by
  refine exec_harness final T (by omega) hKS hNS hB hset hm₁0 hm₁ h00 h02 h03 hblank hf0 hf2 ?_
  intro m hm1 hbuf hrest
  have hvm : ∀ a, vm S m a = m₀ a := by
    intro a; simp only [vm]
    split_ifs with h1 h2
    · exact hbuf a h1
    · exact (hblank a h2.1).symm
    · exact hrest a (by omega) (by omega)
  obtain ⟨m', k, e, hk, h1, hfin⟩ := hbody m hm1 hvm (fun r hr hr' => hrest r hr (by omega))
  refine ⟨m', k, e, hk, h1, ?_, ?_⟩
  · intro j hj hj0 hj2
    have := hfin j (by omega) hj0 hj2
    simpa [vm, hj] using this
  · intro a ha haN
    have := hfin a (by omega) (by omega) (by omega)
    simpa [vm, show ¬ a < 32 by omega, show ¬ (S ≤ a ∧ a < S + 32) by omega] using this

end Formalgo.LLMUnchecked
