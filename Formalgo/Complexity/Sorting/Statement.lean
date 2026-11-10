import Formalgo.Algorithms.Sorting.Statement
import Formalgo.Complexity.Sorting.LLMUnchecked.Proof

/-!
# Sorting lower bound
Sorting `n` reals on a real RAM takes `Ω(n log n)` steps, whatever its operations among `+`, `−`,
`*`, `/` and `<` (Paul and Simon 1980, "Decision trees and random access machines").
-/

namespace Formalgo.Complexity.Sorting

open Algorithms.Sorting

/-- Every real RAM program that sorts lists of reals takes `Ω(n log n)` steps on some input of
each length `n`. -/
theorem sortingLowerBound (operations : List RealRAM.Operation) : ∃ c, ∀ (PC : Type) [Fintype PC]
    (program : (realRAM operations).Program PC),
    let algorithm : Algorithm PC _ Bool ℕ ℝ (List ℝ) (List ℝ) := ⟨program, .standard⟩
    Solves algorithm (realRAM operations).semantics (sorting ℝ) →
    ∀ n, ∃ x : List ℝ, x.length = n ∧
      ∀ t, HaltsWithin algorithm (realRAM operations).semantics x t → n * Nat.log 2 n ≤ c * t + c :=
  ⟨2048, fun _ _ program => lowerBound _ (fun _ _ => id) program⟩

end Formalgo.Complexity.Sorting
