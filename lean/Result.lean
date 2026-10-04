import TailFormula
import MatroidDual

noncomputable section
open scoped BigOperators
open Finset
namespace DNA
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Expected reads, defined by the tail sum of exact uniform iid word
probabilities. A loop is recovered already at time zero. -/
def expectedReads (M : Matroid α) (i : α) : ℝ :=
  ∑' t, wordAvg t (failure M i) ∅

omit [Nonempty α] in
lemma avoiding_eq_powerset (i : α) :
    avoiding i = ((univ : Finset α).erase i).powerset := by
  ext A
  simp [avoiding, Finset.subset_erase]

theorem expectedReads_formula (M : Matroid α) (hE : M.E = Set.univ) (i : α) :
    expectedReads M i = ∑ A ∈ ((univ : Finset α).erase i).powerset,
      failure M i A / ((Fintype.card α - 1).choose A.card : ℝ) := by
  unfold expectedReads
  rw [tsum_subset_formula (failure M i) i (failure_absorbed M i hE), avoiding_eq_powerset]

theorem expectedReads_dual (M : Matroid α) (hE : M.E = Set.univ) (i : α) :
    expectedReads M i + expectedReads M✶ i = Fintype.card α := by
  have hdE : M✶.E = Set.univ := by simpa using hE
  rw [expectedReads_formula M hE, expectedReads_formula M✶ hdE]
  have hh := pairing_on ((univ : Finset α).erase i) (failure M i) (failure M✶ i)
    (fun A hA => complementary_failure M hE i A
      (fun hi => (Finset.mem_erase.mp (hA hi)).1 rfl))
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos
  simpa [Finset.card_erase_of_mem, Nat.cast_sub hn] using hh

def RecoveryBalanced (M : Matroid α) : Prop :=
  ∀ i j, expectedReads M i = expectedReads M j

theorem recoveryBalanced_dual_iff (M : Matroid α) (hE : M.E = Set.univ) :
    RecoveryBalanced M✶ ↔ RecoveryBalanced M := by
  constructor
  · intro h i j
    have hi := expectedReads_dual M hE i
    have hj := expectedReads_dual M hE j
    have he := h i j
    linarith
  · intro h i j
    have hi := expectedReads_dual M hE i
    have hj := expectedReads_dual M hE j
    have he := h i j
    linarith

theorem self_dual_expectedReads (M : Matroid α) (hE : M.E = Set.univ)
    (hD : M✶ = M) (i : α) : expectedReads M i = (Fintype.card α : ℝ) / 2 := by
  have h := expectedReads_dual M hE i
  rw [hD] at h
  linarith

end DNA
