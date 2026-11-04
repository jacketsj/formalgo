import Formalgo.Algorithms.Sorting.Proof

/-!
# Sorting
-/

namespace Formalgo.Algorithms.Sorting

/-- Sorting: the output is the input in nondecreasing order. -/
def sorting : IOSpec (List ℕ) (List ℕ) where
  valid input output := output.Perm input ∧ output.Pairwise (· ≤ ·)

/-- A TD word RAM with `<`, `+` and `−` sorts in `O(n log n)` steps. -/
theorem sortsInNLogN :
    ∃ c, (tdWordRAM [.less, .add, .sub]).SolvableWithin sorting
      fun list => c * list.length * Nat.log 2 list.length + c :=
  MergeSort.wordRAM sorting fun _ _ => And.intro

/-- An integer RAM with `<`, `+` and `−` sorts in `O(n log n)` steps. -/
theorem sortsInNLogN_integerRAM :
    ∃ c, IntegerRAM.withAddSub.semantics.SolvableWithin sorting
      fun list => c * list.length * Nat.log 2 list.length + c :=
  MergeSort.integerRAM sorting fun _ _ => And.intro

end Formalgo.Algorithms.Sorting
