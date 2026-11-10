import Formalgo.Algorithms.Sorting.Proof

/-!
# Sorting
-/

namespace Formalgo.Algorithms.Sorting

/-- Sorting a list of elements of `α`: the output is the input in nondecreasing order. -/
def sorting (α : Type*) [LinearOrder α] : IOSpec (List α) (List α) where
  valid input output := output.Perm input ∧ output.Pairwise (· ≤ ·)

/-- A TD word RAM with `<`, `+` and `−` sorts in `O(n log n)` steps. -/
theorem sortsInNLogN :
    ∃ c, (tdWordRAM [.less, .add, .sub]).SolvableWithin (sorting ℕ)
      fun list => c * list.length * Nat.log 2 list.length + c :=
  MergeSort.wordRAM _ fun _ _ => And.intro

/-- An integer RAM with `<`, `+` and `−` sorts in `O(n log n)` steps. -/
theorem sortsInNLogN_integerRAM :
    ∃ c, IntegerRAM.withAddSub.semantics.SolvableWithin (sorting ℕ)
      fun list => c * list.length * Nat.log 2 list.length + c :=
  MergeSort.integerRAM _ fun _ _ => And.intro

/-- A real RAM with `<`, `+` and `−` sorts in `O(n log n)` steps. -/
theorem sortsInNLogN_realRAM :
    ∃ c, RealRAM.withAddSub.semantics.SolvableWithin (sorting ℕ)
      fun list => c * list.length * Nat.log 2 list.length + c :=
  MergeSort.realRAM _ fun _ _ => And.intro

end Formalgo.Algorithms.Sorting
