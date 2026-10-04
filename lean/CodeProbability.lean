import CodeResult

noncomputable section
open scoped BigOperators
open Finset
namespace DNA
variable {K α : Type*} [Field K] [Fintype α] [DecidableEq α] [Nonempty α]

/-- Ordered read words that still leave two possible codeword values at i. -/
def badReadWords (C : Submodule K (α → K)) (i : α) (t : ℕ) : Finset (Fin t → α) := by
  classical
  exact univ.filter (fun w => ¬ CodeRecovers C (univ.image w) i)

omit [Nonempty α] in
theorem code_word_failure_probability (C : Submodule K (α → K)) (i : α) (t : ℕ) :
    wordAvg t (codeFailure C i) ∅ =
      ((badReadWords C i t).card : ℝ) / (Fintype.card α : ℝ) ^ t := by
  classical
  simp [wordAvg, codeFailure, badReadWords, size, Finset.sum_ite]

omit [Nonempty α] in
/-- The expectation is the sum of exact finite failure counts divided by
the number of equiprobable read words. -/
theorem codeExpectedReads_eq_count_series (C : Submodule K (α → K)) (i : α) :
    codeExpectedReads C i = ∑' t,
      ((badReadWords C i t).card : ℝ) / (Fintype.card α : ℝ) ^ t := by
  unfold codeExpectedReads
  congr 1
  funext t
  exact code_word_failure_probability C i t

end DNA
