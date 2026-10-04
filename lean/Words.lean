import Sampling
import Mathlib.Data.Fin.Tuple.Basic

set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators
open Finset
namespace DNA
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Average over all words of length t, each with its exact iid uniform weight.
The union remembers which indices occurred; multiplicities remain in the
number of words, so this is sampling WITH replacement. -/
def wordAvg (t : ℕ) (f : Finset α → ℝ) (S : Finset α) : ℝ :=
  (∑ w : Fin t → α, f (S ∪ univ.image w)) / size (α := α) ^ t

lemma image_cons (t : ℕ) (x : α) (w : Fin t → α) :
    univ.image (Fin.cons x w) = insert x (univ.image w) := by
  apply Finset.coe_injective
  simp [Fin.range_cons]

lemma word_sum_succ (t : ℕ) (f : Finset α → ℝ) (S : Finset α) :
    (∑ w : Fin (t + 1) → α, f (S ∪ univ.image w)) =
      ∑ x : α, ∑ w : Fin t → α, f (insert x S ∪ univ.image w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (t + 1) => α)).sum_comp
    (fun w => f (S ∪ univ.image w))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro w _
  simp [Fin.consEquiv, image_cons, union_insert, insert_union]

theorem avg_eq_uniform_words (t : ℕ) (f : Finset α → ℝ) (S : Finset α) :
    avg t f S = wordAvg t f S := by
  induction t generalizing S with
  | zero => simp [wordAvg]
  | succ t ih =>
    simp only [avg_succ, step, ih, wordAvg]
    rw [word_sum_succ, pow_succ, ← Finset.sum_div]
    simp only [div_div]

/-- The normalization is exactly the number of iid words, not the number
of subsets or permutations. -/
theorem word_count (t : ℕ) :
    (Fintype.card (Fin t → α) : ℝ) = size (α := α) ^ t := by
  simp [size]

end DNA
