import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
Uniform iid reads on a finite coordinate set, represented by their exact
first-step averaging operator. The potential theorem proves an infinite
tail-sum identity; no convergence assumption is supplied by the caller.
-/

set_option linter.unusedSectionVars false

noncomputable section
open scoped BigOperators
open Finset Filter

namespace DNA

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

def size : ℝ := Fintype.card α

lemma size_pos : 0 < size (α := α) := by
  change (0 : ℝ) < (Fintype.card α : ℝ)
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)

lemma one_le_size : 1 ≤ size (α := α) := by
  change (1 : ℝ) ≤ (Fintype.card α : ℝ)
  exact_mod_cast (Fintype.card_pos : 1 ≤ Fintype.card α)

def step (f : Finset α → ℝ) (S : Finset α) : ℝ :=
  (∑ x : α, f (insert x S)) / size (α := α)

def avg : ℕ → (Finset α → ℝ) → Finset α → ℝ
  | 0, f => f
  | t + 1, f => step (avg t f)

@[simp] lemma avg_zero (f : Finset α → ℝ) (S) : avg 0 f S = f S := rfl
@[simp] lemma avg_succ (t) (f : Finset α → ℝ) (S) :
    avg (t + 1) f S = step (avg t f) S := rfl

lemma step_sub (f g : Finset α → ℝ) : step (f - g) = step f - step g := by
  funext S
  simp [step, Finset.sum_sub_distrib, sub_div]

lemma avg_sub (t) (f g : Finset α → ℝ) : avg t (f - g) = avg t f - avg t g := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step (avg t (f - g)) = step (avg t f) - step (avg t g)
    rw [ih, step_sub]

lemma avg_step (t) (f : Finset α → ℝ) : avg t (step f) = avg (t + 1) f := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step (avg t (step f)) = step (avg (t + 1) f)
    rw [ih]

lemma avg_nonneg (f : Finset α → ℝ) (hf : ∀ S, 0 ≤ f S) :
    ∀ t S, 0 ≤ avg t f S := by
  intro t
  induction t with
  | zero => exact hf
  | succ t ih =>
    intro S
    exact div_nonneg (Finset.sum_nonneg fun x _ => ih (insert x S)) size_pos.le

lemma avg_absorbed (f : Finset α → ℝ) (i : α)
    (hf : ∀ S, i ∈ S → f S = 0) : ∀ t S, i ∈ S → avg t f S = 0 := by
  intro t
  induction t with
  | zero => exact hf
  | succ t ih =>
    intro S hi
    simp only [avg_succ, step]
    have : (∑ x : α, avg t f (insert x S)) = 0 :=
      Finset.sum_eq_zero fun x _ => ih _ (mem_insert_of_mem hi)
    rw [this, zero_div]

def missRate : ℝ := (size (α := α) - 1) / size (α := α)

lemma missRate_nonneg : 0 ≤ missRate (α := α) :=
  div_nonneg (sub_nonneg.mpr one_le_size) size_pos.le

lemma missRate_lt_one : missRate (α := α) < 1 := by
  rw [missRate, div_lt_one size_pos]
  linarith

lemma avg_geometric_bound (f : Finset α → ℝ) (i : α) (B : ℝ)
    (hf : ∀ S, i ∈ S → f S = 0) (hB : ∀ S, f S ≤ B) :
    ∀ t S, avg t f S ≤ missRate (α := α) ^ t * B := by
  intro t
  induction t with
  | zero => simpa using hB
  | succ t ih =>
    intro S
    have hz := avg_absorbed f i hf t (insert i S) (mem_insert_self i S)
    have he := Finset.sum_erase_add (s := (univ : Finset α))
      (f := fun x => avg t f (insert x S)) (mem_univ i)
    have hsum : (∑ x : α, avg t f (insert x S)) ≤
        (size (α := α) - 1) * (missRate (α := α) ^ t * B) := by
      rw [← he, hz, add_zero]
      calc
        (∑ x ∈ (univ : Finset α).erase i, avg t f (insert x S))
            ≤ ∑ x ∈ (univ : Finset α).erase i, missRate (α := α) ^ t * B :=
              Finset.sum_le_sum fun x _ => ih (insert x S)
        _ = (size (α := α) - 1) * (missRate (α := α) ^ t * B) := by
          simp [size, Finset.card_erase_of_mem, Nat.cast_sub Fintype.card_pos]
    calc
      avg (t + 1) f S ≤ ((size (α := α) - 1) *
          (missRate (α := α) ^ t * B)) / size (α := α) :=
        div_le_div_of_nonneg_right hsum size_pos.le
      _ = missRate (α := α) ^ (t + 1) * B := by
        rw [pow_succ, missRate]
        ring

lemma avg_tendsto_zero (f : Finset α → ℝ) (i : α) (B : ℝ)
    (hf : ∀ S, i ∈ S → f S = 0) (h0 : ∀ S, 0 ≤ f S)
    (hB : ∀ S, f S ≤ B) (S : Finset α) :
    Tendsto (fun t => avg t f S) atTop (nhds 0) := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (missRate_nonneg (α := α)) (missRate_lt_one (α := α))).mul_const B
  simp only [zero_mul] at hp
  exact squeeze_zero (fun t => avg_nonneg f h0 t S)
    (fun t => avg_geometric_bound f i B hf hB t S) hp

lemma partial_sum_potential (d g : Finset α → ℝ)
    (hg : ∀ S, g S = d S + step g S) :
    ∀ h S, (∑ t ∈ range h, avg t d S) = g S - avg h g S := by
  have hd : d = g - step g := by
    funext S
    have h := hg S
    simp only [Pi.sub_apply]
    linarith
  have hdif (t) (S) : avg t d S = avg t g S - avg (t + 1) g S := by
    rw [hd, avg_sub, avg_step]
    rfl
  intro h
  induction h with
  | zero => simp
  | succ h ih =>
    intro S
    rw [sum_range_succ, ih S, hdif]
    ring

/-- A verified bridge from the exact iid tail recurrence to its infinite sum.
The designated coordinate makes convergence geometric, even if other
coordinates recover the target earlier. -/
theorem hasSum_of_potential (d g : Finset α → ℝ) (i : α) (B : ℝ)
    (hd : ∀ S, 0 ≤ d S)
    (hg : ∀ S, g S = d S + step g S)
    (habs : ∀ S, i ∈ S → g S = 0)
    (h0 : ∀ S, 0 ≤ g S) (hB : ∀ S, g S ≤ B) (S : Finset α) :
    HasSum (fun t => avg t d S) (g S) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun t => avg_nonneg d hd t S) (g S)).2
  simp_rw [partial_sum_potential d g hg]
  simpa using tendsto_const_nhds.sub (avg_tendsto_zero g i B habs h0 hB S)

theorem tsum_of_potential (d g : Finset α → ℝ) (i : α) (B : ℝ)
    (hd : ∀ S, 0 ≤ d S)
    (hg : ∀ S, g S = d S + step g S)
    (habs : ∀ S, i ∈ S → g S = 0)
    (h0 : ∀ S, 0 ≤ g S) (hB : ∀ S, g S ≤ B) (S : Finset α) :
    (∑' t, avg t d S) = g S :=
  (hasSum_of_potential d g i B hd hg habs h0 hB S).tsum_eq

end DNA
