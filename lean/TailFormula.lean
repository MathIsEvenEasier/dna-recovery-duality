import Occupancy
import Mathlib.Data.Fintype.Powerset

set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators
open Finset
namespace DNA
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

lemma avg_mul (t : ℕ) (c : ℝ) (f : Finset α → ℝ) (S : Finset α) :
    avg t (fun S => c * f S) S = c * avg t f S := by
  induction t generalizing S with
  | zero => rfl
  | succ t ih => simp only [avg_succ, step, ih, ← Finset.mul_sum, mul_div_assoc]

lemma avg_sum {β : Type*} (B : Finset β) (f : β → Finset α → ℝ)
    (t : ℕ) (S : Finset α) :
    avg t (fun S => ∑ b ∈ B, f b S) S = ∑ b ∈ B, avg t (f b) S := by
  induction t generalizing S with
  | zero => rfl
  | succ t ih =>
    simp only [avg_succ, step, ih]
    rw [Finset.sum_comm, Finset.sum_div]

def avoiding (i : α) : Finset (Finset α) := univ.filter (fun S => i ∉ S)

lemma spike_expansion (f : Finset α → ℝ) (i : α)
    (hf : ∀ S, i ∈ S → f S = 0) :
    (fun S => ∑ A ∈ avoiding i, f A * spike A S) = f := by
  funext S
  by_cases h : i ∈ S
  · simp [avoiding, spike, mul_ite, h, hf S h]
  · simp [avoiding, spike, mul_ite, h]

/-- The full sampling-to-subsets bridge. Its left-hand side is the
infinite tail sum of exact uniform iid word probabilities. -/
theorem hasSum_subset_formula (f : Finset α → ℝ) (i : α)
    (hf : ∀ S, i ∈ S → f S = 0) :
    HasSum (fun t => wordAvg t f ∅)
      (∑ A ∈ avoiding i, f A / ((Fintype.card α - 1).choose A.card : ℝ)) := by
  have hA (A : Finset α) (hA : A ∈ avoiding i) :
      HasSum (fun t => f A * avg t (spike A) ∅)
        (f A / ((Fintype.card α - 1).choose A.card : ℝ)) := by
    have hh := (hasSum_exact_state A i (by simpa [avoiding] using hA)).mul_left (f A)
    simpa only [mul_one_div] using hh
  have hsum := hasSum_sum hA
  have heq (t : ℕ) :
      (∑ A ∈ avoiding i, f A * avg t (spike A) ∅) = wordAvg t f ∅ := by
    simp_rw [← avg_mul]
    rw [← avg_sum, spike_expansion f i hf, avg_eq_uniform_words]
  simpa only [heq] using hsum

theorem tsum_subset_formula (f : Finset α → ℝ) (i : α)
    (hf : ∀ S, i ∈ S → f S = 0) :
    (∑' t, wordAvg t f ∅) =
      ∑ A ∈ avoiding i, f A / ((Fintype.card α - 1).choose A.card : ℝ) :=
  (hasSum_subset_formula f i hf).tsum_eq

end DNA
