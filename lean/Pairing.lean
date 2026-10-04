import Sampling
import Mathlib.Data.Fintype.Powerset

set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators
open Finset
namespace DNA
variable {β : Type*} [Fintype β] [DecidableEq β]

def subsetWeight (S : Finset β) : ℝ :=
  1 / ((Fintype.card β).choose S.card : ℝ)

lemma subsetWeight_compl (S : Finset β) : subsetWeight Sᶜ = subsetWeight S := by
  simp only [subsetWeight, Finset.card_compl]
  rw [Nat.choose_symm (Finset.card_le_univ S)]

lemma subsetWeight_total :
    (∑ S : Finset β, subsetWeight S) = (Fintype.card β : ℝ) + 1 := by
  unfold subsetWeight
  rw [← Finset.powerset_univ, Finset.sum_powerset]
  simp only [Finset.card_univ]
  have he (j : ℕ) (hj : j ∈ range (Fintype.card β + 1)) :
      (∑ S ∈ powersetCard j (univ : Finset β),
        1 / ((Fintype.card β).choose S.card : ℝ)) = 1 := by
    rw [Finset.sum_powersetCard j (univ : Finset β) (fun s => (1 : ℝ) / ((Fintype.card β).choose s : ℝ))]
    have hpos : 0 < (Fintype.card β).choose j := Nat.choose_pos (by simpa using hj)
    simp [nsmul_eq_mul, Nat.ne_of_gt hpos]
  rw [Finset.sum_congr rfl he]
  simp

/-- Complementation pairs the two rank-increment profiles. This theorem
is the finite algebraic part, and deliberately does not redefine an
expectation to be this sum. -/
theorem complementary_weighted_sums (f g : Finset β → ℝ)
    (h : ∀ S, f S + g Sᶜ = 1) :
    (∑ S : Finset β, subsetWeight S * f S) +
      (∑ S : Finset β, subsetWeight S * g S) = (Fintype.card β : ℝ) + 1 := by
  let e : Finset β ≃ Finset β :=
    { toFun := fun S => Sᶜ
      invFun := fun S => Sᶜ
      left_inv := fun S => compl_compl S
      right_inv := fun S => compl_compl S }
  have hg : (∑ S : Finset β, subsetWeight S * g S) =
      ∑ S : Finset β, subsetWeight S * g Sᶜ := by
    rw [← e.sum_comp (fun S => subsetWeight S * g S)]
    apply Finset.sum_congr rfl
    intro S _
    change subsetWeight Sᶜ * g Sᶜ = subsetWeight S * g Sᶜ
    rw [subsetWeight_compl]
  rw [hg, ← Finset.sum_add_distrib]
  simp_rw [← mul_add, h, mul_one]
  exact subsetWeight_total

variable {α : Type*} [DecidableEq α]

lemma groundWeight_total (s : Finset α) :
    (∑ A ∈ s.powerset, 1 / (s.card.choose A.card : ℝ)) = s.card + 1 := by
  rw [Finset.sum_powerset]
  have he (j) (hj : j ∈ range (s.card + 1)) :
      (∑ A ∈ powersetCard j s, 1 / (s.card.choose A.card : ℝ)) = 1 := by
    rw [Finset.sum_powersetCard j s (fun k => (1 : ℝ) / (s.card.choose k : ℝ))]
    have hp := Nat.choose_pos (by simpa using hj : j ≤ s.card)
    simp [nsmul_eq_mul, Nat.ne_of_gt hp]
  rw [Finset.sum_congr rfl he]
  simp

theorem pairing_on (s : Finset α) (f g : Finset α → ℝ)
    (h : ∀ A ⊆ s, f A + g (s \ A) = 1) :
    (∑ A ∈ s.powerset, f A / (s.card.choose A.card : ℝ)) +
      (∑ A ∈ s.powerset, g A / (s.card.choose A.card : ℝ)) = s.card + 1 := by
  have hinv (A : Finset α) (hA : A ⊆ s) : s \ (s \ A) = A := by
    ext x
    simp only [mem_sdiff]
    constructor
    · tauto
    · intro hx; exact ⟨hA hx, by tauto⟩
  have hg : (∑ A ∈ s.powerset, g A / (s.card.choose A.card : ℝ)) =
      ∑ A ∈ s.powerset, g (s \ A) / (s.card.choose A.card : ℝ) := by
    apply Finset.sum_bij (fun A _ => s \ A)
    · intro A _; exact mem_powerset.mpr sdiff_subset
    · intro A hA B hB heq
      have hh := congrArg (fun X => s \ X) heq
      simpa only [hinv A (mem_powerset.mp hA), hinv B (mem_powerset.mp hB)] using hh
    · intro B hB
      exact ⟨s \ B, mem_powerset.mpr sdiff_subset, hinv B (mem_powerset.mp hB)⟩
    · intro A hA
      have hAs := mem_powerset.mp hA
      rw [hinv A hAs, card_sdiff_of_subset hAs, Nat.choose_symm (card_le_card hAs)]
  rw [hg, ← Finset.sum_add_distrib]
  calc
    (∑ A ∈ s.powerset, (f A / (s.card.choose A.card : ℝ) +
      g (s \ A) / (s.card.choose A.card : ℝ))) =
        ∑ A ∈ s.powerset, 1 / (s.card.choose A.card : ℝ) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [← add_div, h A (mem_powerset.mp hA)]
    _ = s.card + 1 := groundWeight_total s

end DNA
