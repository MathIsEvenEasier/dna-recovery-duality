import CodeGenerator
import Result

noncomputable section
open scoped BigOperators
open Finset
namespace DNA
variable {K α : Type*} [Field K] [Fintype α] [DecidableEq α] [Nonempty α]

def codeFailure (C : Submodule K (α → K)) (i : α) (S : Finset α) : ℝ := by
  classical
  exact if CodeRecovers C S i then 0 else 1

omit [Nonempty α] [Fintype α] [DecidableEq α] in
theorem codeFailure_absorbed (C : Submodule K (α → K)) (i : α)
    (S : Finset α) (hi : i ∈ S) : codeFailure C i S = 0 := by
  classical
  simp [codeFailure, codeRecovers_of_mem C S i hi]

omit [Nonempty α] in
theorem complementary_codeFailure (C : Submodule K (α → K)) (i : α)
    (S : Finset α) (hi : i ∉ S) :
    codeFailure C i S + codeFailure (codeDual C) i ((univ.erase i) \ S) = 1 := by
  classical
  simp only [codeFailure, code_complementary_recovery C S i hi]
  by_cases h : CodeRecovers C S i <;> simp [h]

/-- Expected reads in the exact uniform iid word model, expressed as a
tail sum; zero coordinates are known before any read. -/
def codeExpectedReads (C : Submodule K (α → K)) (i : α) : ℝ :=
  ∑' t, wordAvg t (codeFailure C i) ∅

theorem codeExpectedReads_hasSum (C : Submodule K (α → K)) (i : α) :
    HasSum (fun t => wordAvg t (codeFailure C i) ∅)
      (∑ A ∈ (univ.erase i).powerset,
        codeFailure C i A / ((Fintype.card α - 1).choose A.card : ℝ)) := by
  simpa only [avoiding_eq_powerset] using
    hasSum_subset_formula (codeFailure C i) i (codeFailure_absorbed C i)

theorem codeExpectedReads_formula (C : Submodule K (α → K)) (i : α) :
    codeExpectedReads C i = ∑ A ∈ (univ.erase i).powerset,
      codeFailure C i A / ((Fintype.card α - 1).choose A.card : ℝ) :=
  (codeExpectedReads_hasSum C i).tsum_eq

/-- Coordinatewise duality for every linear code over every field. -/
theorem codeExpectedReads_dual (C : Submodule K (α → K)) (i : α) :
    codeExpectedReads C i + codeExpectedReads (codeDual C) i = Fintype.card α := by
  rw [codeExpectedReads_formula, codeExpectedReads_formula]
  have hh := pairing_on ((univ : Finset α).erase i) (codeFailure C i)
    (codeFailure (codeDual C) i) (fun A hA => complementary_codeFailure C i A
      (fun hi => (Finset.mem_erase.mp (hA hi)).1 rfl))
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos
  simpa [Finset.card_erase_of_mem, Nat.cast_sub hn] using hh

def CodeRecoveryBalanced (C : Submodule K (α → K)) : Prop :=
  ∀ i j, codeExpectedReads C i = codeExpectedReads C j

/-- The recovery-balance conjecture, with the explicit time-zero convention
and tail-sum definition of expectation. -/
theorem codeRecoveryBalanced_dual_iff (C : Submodule K (α → K)) :
    CodeRecoveryBalanced (codeDual C) ↔ CodeRecoveryBalanced C := by
  constructor
  · intro h i j
    have hi := codeExpectedReads_dual C i
    have hj := codeExpectedReads_dual C j
    have he := h i j
    linarith
  · intro h i j
    have hi := codeExpectedReads_dual C i
    have hj := codeExpectedReads_dual C j
    have he := h i j
    linarith

theorem self_dual_codeExpectedReads (C : Submodule K (α → K))
    (hD : codeDual C = C) (i : α) :
    codeExpectedReads C i = (Fintype.card α : ℝ) / 2 := by
  have h := codeExpectedReads_dual C i
  rw [hD] at h
  linarith

end DNA
