import Formalgo.Algorithms.Sorting.Proof

/-!
# Sorting
-/

namespace Formalgo.Algorithms.Sorting

/-- Sorting: the output is the input in nondecreasing order. -/
def sorting : IOSpec (List ℕ) (List ℕ) where
  valid input output := output.Perm input ∧ output.Pairwise (· ≤ ·)

/-- Some program solves `spec` within `time input` steps on each input, with the standard tape
coding. -/
def SolvableWithin {Instruction Address Value Input Output : Type*} [NatCast Address]
    [DecidableEq Address] [Inhabited Value] [Code Input Value] [Code Output Value]
    (semantics : Semantics Instruction Bool Address Value) (spec : IOSpec Input Output)
    (time : Input → ℕ) : Prop :=
  ∃ (PC : Type) (_ : Fintype PC) (program : Program PC Instruction Bool),
    let algorithm : Algorithm PC Instruction Bool Address Value Input Output :=
      ⟨program, .standard⟩
    Solves algorithm semantics spec ∧
      ∀ input, HaltsWithin algorithm semantics input (time input)

/-- A TD word RAM with `<`, `+` and `−` sorts in `O(n log n)` steps. -/
theorem sortsInNLogN :
    ∃ c, (tdWordRAM [.less, .add, .sub]).SolvableWithin sorting
      fun list => c * list.length * Nat.log 2 list.length + c :=
  MergeSort.wordRAM sorting fun _ _ => And.intro

/-- An integer RAM with `<`, `+` and `−` sorts in `O(n log n)` steps. -/
theorem sortsInNLogN_integerRAM :
    ∃ c, SolvableWithin IntegerRAM.withAddSub.semantics sorting
      fun list => c * list.length * Nat.log 2 list.length + c :=
  MergeSort.integerRAM sorting fun _ _ => And.intro

end Formalgo.Algorithms.Sorting
