import Pairing
import Mathlib.Combinatorics.Matroid.Rank.ENat

set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators
open Finset
namespace DNA
variable {α : Type*} [Fintype α] [DecidableEq α]

def rankReal (M : Matroid α) (S : Finset α) : ℝ := (M.eRk (S : Set α)).toNat

def failure (M : Matroid α) (i : α) (S : Finset α) : ℝ := by
  classical
  exact if i ∈ M.closure (S : Set α) then 0 else 1

lemma rank_ne_top (M : Matroid α) (S : Set α) : M.eRk S ≠ ⊤ :=
  Matroid.eRk_ne_top_iff.mpr (Matroid.RankFinite.isRkFinite S)

lemma rank_insert (M : Matroid α) (i : α) (hi : i ∈ M.E) (S : Finset α) :
    rankReal M (insert i S) = rankReal M S + failure M i S := by
  classical
  by_cases h : i ∈ M.closure (S : Set α)
  · have he : M.eRk (insert i (S : Set α)) = M.eRk (S : Set α) := by
      rw [← M.eRk_closure_eq, Matroid.closure_insert_eq_of_mem_closure h, M.eRk_closure_eq]
    simp only [rankReal, Finset.coe_insert, he, failure, ite_eq_left h, add_zero]
  · have he := Matroid.eRk_insert_eq_add_one (M := M) (X := (S : Set α)) ⟨hi, h⟩
    simp only [rankReal, Finset.coe_insert, he, failure, ite_eq_right h]
    rw [ENat.toNat_add (rank_ne_top M _) (by simp)]
    simp

lemma rank_dual (M : Matroid α) (hE : M.E = Set.univ) (S : Finset α) :
    rankReal M✶ S + rankReal M univ = rankReal M Sᶜ + S.card := by
  have he := M.eRk_dual_add_eRank (S : Set α) (by simp [hE])
  have ht : M.eRank ≠ ⊤ := (M.eRank_ne_top_iff).mpr inferInstance
  have hc : (S : Set α).encard ≠ ⊤ := S.finite_toSet.encard_lt_top.ne
  have hnat := congrArg ENat.toNat he
  rw [ENat.toNat_add (rank_ne_top _ _) ht,
    ENat.toNat_add (rank_ne_top _ _) hc] at hnat
  rw [Matroid.eRank_def, hE] at hnat
  have hcomp : Set.univ \ (S : Set α) = (Sᶜ : Finset α) := by ext x; simp
  rw [hcomp, Set.encard_coe_eq_coe_finsetCard, ENat.toNat_natCast] at hnat
  unfold rankReal
  simp only [Finset.coe_univ]
  exact_mod_cast hnat

lemma failure_absorbed (M : Matroid α) (i : α) (hE : M.E = Set.univ)
    (S : Finset α) (hi : i ∈ S) : failure M i S = 0 := by
  classical
  have h : i ∈ M.closure (S : Set α) :=
    M.mem_closure_of_mem hi (by simp [hE])
  simp [failure, h]

lemma complementary_failure (M : Matroid α) (hE : M.E = Set.univ)
    (i : α) (S : Finset α) (hiS : i ∉ S) :
    failure M i S + failure M✶ i ((univ.erase i) \ S) = 1 := by
  let T : Finset α := (univ.erase i) \ S
  have hiT : i ∉ T := by simp [T]
  have hTc : Tᶜ = insert i S := by
    ext x
    by_cases hxi : x = i <;> simp [T, hxi, hiS]
  have hTi : (insert i T)ᶜ = S := by
    ext x
    by_cases hxi : x = i <;> simp [T, hxi, hiS]
  have h1 := rank_dual M hE T
  have h2 := rank_dual M hE (insert i T)
  rw [hTc] at h1
  rw [hTi, card_insert_of_notMem hiT, Nat.cast_add, Nat.cast_one] at h2
  have h3 := rank_insert M i (by simp [hE]) S
  have h4 := rank_insert M✶ i (by simp [hE]) T
  change failure M i S + failure M✶ i T = 1
  linarith

end DNA
