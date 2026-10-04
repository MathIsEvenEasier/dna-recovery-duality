import Words

set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators
open Finset
namespace DNA

def coefficient (n a s : ℕ) : ℝ :=
  (n : ℝ) / ((n - a : ℕ) * ((n - s).choose (a - s) : ℝ))

lemma coefficient_nonneg (n a s : ℕ) : 0 ≤ coefficient n a s := by
  unfold coefficient
  positivity

lemma coefficient_le (n a s : ℕ) (ha : a < n) (hs : s ≤ a) :
    coefficient n a s ≤ n := by
  have hc : 0 < (n - s).choose (a - s) := Nat.choose_pos (by omega)
  have hd : (1 : ℝ) ≤ (n - a : ℕ) * ((n - s).choose (a - s) : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos (by omega : 0 < n - a) hc))
  exact div_le_self (by positivity) hd

lemma coefficient_diag (n a : ℕ) :
    coefficient n a a = (n : ℝ) / (n - a : ℕ) := by
  simp [coefficient]

lemma coefficient_recurrence (n a s : ℕ) (ha : a < n) (hs : s < a) :
    (n - s : ℕ) * coefficient n a s =
      (a - s : ℕ) * coefficient n a (s + 1) := by
  have h1 : n - (s + 1) + 1 = n - s := by omega
  have h2 : a - (s + 1) + 1 = a - s := by omega
  have hid := Nat.add_one_mul_choose_eq (n - (s + 1)) (a - (s + 1))
  rw [h1, h2] at hid
  have hidR : (n - s : ℕ) * ((n - (s + 1)).choose (a - (s + 1)) : ℝ) =
      ((n - s).choose (a - s) : ℝ) * (a - s : ℕ) := by
    exact_mod_cast hid
  have hc : (n - s).choose (a - s) ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hc' : (n - (s + 1)).choose (a - (s + 1)) ≠ 0 :=
    Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hna : n - a ≠ 0 := by omega
  unfold coefficient
  field_simp
  nlinarith

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

def occupation (A S : Finset α) : ℝ :=
  if S ⊆ A then coefficient (Fintype.card α) A.card S.card else 0

def spike (A S : Finset α) : ℝ := if S = A then 1 else 0

lemma occupation_nonneg (A S : Finset α) : 0 ≤ occupation A S := by
  unfold occupation
  split_ifs
  · exact coefficient_nonneg _ _ _
  · rfl

lemma occupation_bound (A S : Finset α) (ha : A.card < Fintype.card α) :
    occupation A S ≤ size (α := α) := by
  unfold occupation size
  split_ifs with h
  · exact coefficient_le _ _ _ ha (card_le_card h)
  · positivity

lemma occupation_absorbed (A : Finset α) (i : α) (hi : i ∉ A)
    (S : Finset α) (hS : i ∈ S) : occupation A S = 0 := by
  exact ite_eq_right (fun h => hi (h hS))

lemma occupation_step (A S : Finset α) (ha : A.card < Fintype.card α) :
    occupation A S = spike A S + step (occupation A) S := by
  by_cases hS : S ⊆ A
  · by_cases heq : S = A
    · subst S
      have hx (x : α) : occupation A (insert x A) =
          if x ∈ A then occupation A A else 0 := by
        by_cases hx : x ∈ A
        · simp [hx, insert_eq_of_mem hx]
        · simp [occupation, hx, insert_subset_iff]
      simp only [step, hx]
      simp only [spike, ite_true]
      simp only [occupation, ite_eq_left (Subset.refl A), coefficient_diag]
      have hn : (size (α := α)) ≠ 0 := ne_of_gt size_pos
      have hna : (Fintype.card α - A.card : ℕ) ≠ 0 := by omega
      simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      simp only [size]
      rw [Nat.cast_sub (by omega : A.card ≤ Fintype.card α)]
      have hnr : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
      have har : (Fintype.card α : ℝ) - A.card ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt ha))
      field_simp
      ring
    · have hlt : S.card < A.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hS, heq⟩)
      let b := coefficient (Fintype.card α) A.card (S.card + 1)
      have hx (x : α) : occupation A (insert x S) =
          (if x ∈ S then occupation A S else 0) +
          (if x ∈ A \ S then b else 0) := by
        by_cases hxS : x ∈ S
        · simp [hxS, insert_eq_of_mem hxS]
        · by_cases hxA : x ∈ A
          · simp [occupation, insert_subset_iff, hS, hxS, hxA, b, card_insert_of_notMem]
          · simp [occupation, insert_subset_iff, hS, hxS, hxA]
      have hstep : step (occupation A) S =
          ((S.card : ℝ) * occupation A S + (A.card - S.card : ℕ) * b) /
            size (α := α) := by
        simp only [step, hx, Finset.sum_add_distrib]
        simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff_of_subset hS]
      rw [hstep]
      simp only [spike, ite_eq_right heq, zero_add, occupation, ite_eq_left hS]
      have hc := coefficient_recurrence (Fintype.card α) A.card S.card ha hlt
      change (Fintype.card α - S.card : ℕ) * coefficient (Fintype.card α) A.card S.card =
        (A.card - S.card : ℕ) * b at hc
      rw [Nat.cast_sub (by omega : S.card ≤ Fintype.card α)] at hc
      apply (eq_div_iff (ne_of_gt size_pos)).2
      unfold size
      nlinarith
  · have heq : S ≠ A := fun h => hS (h ▸ Subset.refl A)
    have hx (x : α) : occupation A (insert x S) = 0 := by
      apply ite_eq_right
      intro hh
      exact hS (fun _ hmem => hh (mem_insert_of_mem hmem))
    rw [show occupation A S = 0 from ite_eq_right hS]
    simp only [spike, ite_eq_right heq, step, hx, Finset.sum_const_zero, zero_div, add_zero]

lemma card_lt_of_missing (A : Finset α) (i : α) (hi : i ∉ A) :
    A.card < Fintype.card α := by
  have hne : A ≠ univ := by intro h; exact hi (h ▸ mem_univ i)
  simpa using card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ A, hne⟩)

theorem hasSum_occupation (A : Finset α) (i : α) (hi : i ∉ A) (S : Finset α) :
    HasSum (fun t => avg t (spike A) S) (occupation A S) := by
  have ha := card_lt_of_missing A i hi
  apply hasSum_of_potential (spike A) (occupation A) i (size (α := α))
  · intro U; unfold spike; split_ifs <;> norm_num
  · exact fun U => occupation_step A U ha
  · exact occupation_absorbed A i hi
  · exact occupation_nonneg A
  · exact fun U => occupation_bound A U ha

lemma coefficient_start (n a : ℕ) (ha : a < n) :
    coefficient n a 0 = 1 / ((n - 1).choose a : ℝ) := by
  have hn : n - 1 + 1 = n := by omega
  have hid := Nat.choose_mul_succ_eq (n - 1) a
  rw [hn] at hid
  have hidR : ((n - 1).choose a : ℝ) * n = (n.choose a : ℝ) * (n - a : ℕ) := by
    exact_mod_cast hid
  have hc : n.choose a ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hc' : (n - 1).choose a ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hna : n - a ≠ 0 := by omega
  simp only [coefficient, Nat.sub_zero]
  field_simp
  nlinarith

theorem hasSum_exact_state (A : Finset α) (i : α) (hi : i ∉ A) :
    HasSum (fun t => avg t (spike A) ∅)
      (1 / ((Fintype.card α - 1).choose A.card : ℝ)) := by
  have h := hasSum_occupation A i hi ∅
  simpa [occupation, coefficient_start _ _ (card_lt_of_missing A i hi)] using h

end DNA
