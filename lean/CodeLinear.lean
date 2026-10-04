import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Finset
namespace DNA
variable {K α : Type*} [Field K] [Fintype α] [DecidableEq α]

/-- Orthogonal code under the ordinary, non-Hermitian dot product. -/
def codeDual (C : Submodule K (α → K)) : Submodule K (α → K) :=
  C.dualAnnihilator.comap (dotProductEquiv K α).toLinearMap

@[simp] theorem mem_codeDual (C : Submodule K (α → K)) (y : α → K) :
    y ∈ codeDual C ↔ ∀ x ∈ C, dotProduct x y = 0 := by
  simp [codeDual, Submodule.mem_dualAnnihilator, dotProduct_comm]

/-- Reading S determines coordinate i for code C. The zero-word formulation
is proved equivalent below to agreement of arbitrary codewords. -/
def CodeRecovers (C : Submodule K (α → K)) (S : Finset α) (i : α) : Prop :=
  ∀ x ∈ C, (∀ j ∈ S, x j = 0) → x i = 0

omit [Fintype α] [DecidableEq α] in
theorem codeRecovers_iff_agreement (C : Submodule K (α → K)) (S : Finset α) (i : α) :
    CodeRecovers C S i ↔
      ∀ x ∈ C, ∀ y ∈ C, (∀ j ∈ S, x j = y j) → x i = y i := by
  constructor
  · intro h x hx y hy he
    have hh := h (x - y) (C.sub_mem hx hy) (fun j hj => sub_eq_zero.mpr (he j hj))
    exact sub_eq_zero.mp hh
  · intro h x hx hz
    simpa using h x hx 0 C.zero_mem hz

def coordinateForm (C : Submodule K (α → K)) (i : α) : C →ₗ[K] K :=
  (LinearMap.proj i).comp C.subtype

omit [DecidableEq α] in
/-- Recovery is equivalent to a linear decoder from the observed symbols. -/
theorem codeRecovers_iff_decoder (C : Submodule K (α → K)) (S : Finset α) (i : α) :
    CodeRecovers C S i ↔
      ∃ c : S → K, ∀ x ∈ C, x i = ∑ j : S, c j * x j := by
  classical
  constructor
  · intro h
    have hs : coordinateForm C i ∈ Submodule.span K
        (Set.range (fun j : S => coordinateForm C j)) := by
      apply mem_span_of_iInf_ker_le_ker
      intro x hx
      apply h x x.property
      intro j hj
      have hh := ((Submodule.mem_iInf _).mp hx) (⟨j, hj⟩ : S)
      exact hh
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hs
    refine ⟨c, fun x hx => ?_⟩
    have hh := LinearMap.congr_fun hc (⟨x, hx⟩ : C)
    simpa [coordinateForm, LinearMap.sum_apply] using hh.symm
  · rintro ⟨c, hc⟩ x hx hz
    rw [hc x hx]
    apply Finset.sum_eq_zero
    intro j _
    simp [hz j j.property]

omit [Fintype α] [DecidableEq α] in
theorem codeRecovers_of_mem (C : Submodule K (α → K)) (S : Finset α) (i : α)
    (hi : i ∈ S) : CodeRecovers C S i := fun _ _ h => h i hi

/-- A linear decoder yields a dual codeword with target value one and
support inside S union {i}. -/
theorem dual_witness_of_recovers (C : Submodule K (α → K)) (S : Finset α) (i : α)
    (hi : i ∉ S) (h : CodeRecovers C S i) :
    ∃ y ∈ codeDual C, y i = 1 ∧ ∀ j ∈ (univ.erase i) \ S, y j = 0 := by
  classical
  obtain ⟨c, hc⟩ := (codeRecovers_iff_decoder C S i).mp h
  let y : α → K := Pi.single i 1 - ∑ j : S, c j • Pi.single (j : α) 1
  have hji (j : S) : (j : α) ≠ i := by
    intro he; exact hi (he ▸ j.property)
  refine ⟨y, ?_, ?_, ?_⟩
  · apply (mem_codeDual C y).mpr
    intro x hx
    simp only [y, dotProduct_sub, dotProduct_sum, dotProduct_smul,
      dotProduct_single_one, smul_eq_mul]
    exact sub_eq_zero.mpr (hc x hx)
  · simp [y, hji]
  · intro j hj
    have hji' : j ≠ i := (mem_erase.mp (mem_sdiff.mp hj).1).1
    have hjS : j ∉ S := (mem_sdiff.mp hj).2
    have hkj (k : S) : (k : α) ≠ j := by
      intro he; exact hjS (he ▸ k.property)
    simp [y, hji', hkj]

/-- If primal observations leave an ambiguity, the complementary dual
observations determine the target. Orthogonality leaves only one product. -/
theorem dual_recovers_of_not_recovers (C : Submodule K (α → K)) (S : Finset α) (i : α)
    (h : ¬ CodeRecovers C S i) : CodeRecovers (codeDual C) ((univ.erase i) \ S) i := by
  classical
  unfold CodeRecovers at h
  push Not at h
  obtain ⟨x, hx, hxS, hxi⟩ := h
  intro y hy hyT
  have hd : dotProduct x y = x i * y i := by
    unfold dotProduct
    apply Finset.sum_eq_single i
    · intro j _ hji
      by_cases hjS : j ∈ S
      · simp [hxS j hjS]
      · have hjT : j ∈ (univ.erase i) \ S := by simp [hji, hjS]
        simp [hyT j hjT]
    · simp
  have hz := (mem_codeDual C y).mp hy x hx
  rw [hd] at hz
  exact (mul_eq_zero.mp hz).resolve_left hxi

/-- Complementary observations in orthogonal dual codes have opposite
recoverability. No matroid representation is assumed in this theorem. -/
theorem code_complementary_recovery (C : Submodule K (α → K)) (S : Finset α) (i : α)
    (hi : i ∉ S) :
    CodeRecovers (codeDual C) ((univ.erase i) \ S) i ↔ ¬ CodeRecovers C S i := by
  constructor
  · intro hd h
    obtain ⟨y, hy, hyi, hyT⟩ := dual_witness_of_recovers C S i hi h
    have hz := hd y hy hyT
    rw [hyi] at hz
    exact one_ne_zero hz
  · exact dual_recovers_of_not_recovers C S i

end DNA
