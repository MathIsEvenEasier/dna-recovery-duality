import CodeLinear
import Mathlib.LinearAlgebra.Matrix.DotProduct

noncomputable section
open scoped BigOperators
open Finset
namespace DNA
variable {K α β : Type*} [Field K] [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- A generator specified by its columns g j. Message u produces the
coordinate dotProduct (g j) u, i.e. the ordinary generator-matrix code. -/
def encoder (g : α → β → K) : (β → K) →ₗ[K] (α → K) :=
  LinearMap.pi (fun j => (dotProductEquiv K β) (g j))

def generatedCode (g : α → β → K) : Submodule K (α → K) :=
  LinearMap.range (encoder g)

omit [DecidableEq α] in
/-- The operational recovery definition agrees with the generator-column
span criterion used in the DNA random-access model. -/
theorem generatedCode_recovers_iff_span (g : α → β → K) (S : Finset α) (i : α) :
    CodeRecovers (generatedCode g) S i ↔
      g i ∈ Submodule.span K (Set.range (fun j : S => g j)) := by
  classical
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (codeRecovers_iff_decoder (generatedCode g) S i).mp h
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨c, ?_⟩
    apply dotProduct_eq
    intro u
    have hh := hc (encoder g u) ⟨u, rfl⟩
    change dotProduct (g i) u = ∑ j : S, c j * dotProduct (g j) u at hh
    simpa only [sum_dotProduct, smul_dotProduct, smul_eq_mul] using hh.symm
  · intro h
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp h
    apply (codeRecovers_iff_decoder (generatedCode g) S i).mpr
    refine ⟨c, ?_⟩
    rintro x ⟨u, rfl⟩
    change dotProduct (g i) u = ∑ j : S, c j * dotProduct (g j) u
    rw [← hc]
    simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul]

end DNA
