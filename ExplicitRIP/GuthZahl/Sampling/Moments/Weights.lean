/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Sampling.Defs

/-!
# Finite Bernoulli weights

The powerset weights have mass one. Splitting subsets according to whether
they contain a new element gives a two-term recursion for weighted sums.
-/

public section

namespace ExplicitRIP.GuthZahl
namespace Sampling

open Classical in
/-- Bernoulli weights sum to one over the subsets of a finite set. -/
theorem _root_.ExplicitRIP.GuthZahl.bernoulliWeight_sum {α : Type*} (q : ℝ) (S : Finset α) :
    (∑ T ∈ S.powerset, bernoulliWeight q S T) = 1 := by
  simp only [bernoulliWeight, Finset.sum_pow_mul_eq_add_pow,
    show q + (1 - q) = 1 by ring, one_pow]

open Classical in
theorem bernoulliWeight_insert_notMem {α : Type*} (q : ℝ)
    (S T : Finset α) (a : α) (ha : a ∉ S) (hT : T ⊆ S) :
    bernoulliWeight q (insert a S) T = (1 - q) * bernoulliWeight q S T := by
  have hcard : S.card + 1 - T.card = S.card - T.card + 1 := by
    have := Finset.card_le_card hT
    omega
  rw [bernoulliWeight, bernoulliWeight, Finset.card_insert_of_notMem ha,
    hcard, pow_succ]
  ring

open Classical in
theorem bernoulliWeight_insert_mem {α : Type*} (q : ℝ)
    (S T : Finset α) (a : α) (ha : a ∉ S) (hT : T ⊆ S) :
    bernoulliWeight q (insert a S) (insert a T) = q * bernoulliWeight q S T := by
  have haT : a ∉ T := fun h => ha (hT h)
  rw [bernoulliWeight, bernoulliWeight, Finset.card_insert_of_notMem ha,
    Finset.card_insert_of_notMem haT, Nat.add_sub_add_right, pow_succ]
  ring

open Classical in
theorem sum_bernoulliWeight_insert {α : Type*} (q : ℝ)
    (S : Finset α) (a : α) (ha : a ∉ S) (f : Finset α → ℝ) :
    (∑ T ∈ (insert a S).powerset, bernoulliWeight q (insert a S) T * f T) =
      (1 - q) * (∑ T ∈ S.powerset, bernoulliWeight q S T * f T) +
        q * (∑ T ∈ S.powerset, bernoulliWeight q S T * f (insert a T)) := by
  rw [Finset.sum_powerset_insert ha, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro T hT
    rw [bernoulliWeight_insert_notMem q S T a ha (Finset.mem_powerset.mp hT),
      mul_assoc]
  · apply Finset.sum_congr rfl
    intro T hT
    rw [bernoulliWeight_insert_mem q S T a ha (Finset.mem_powerset.mp hT),
      mul_assoc]

open Classical in
theorem sum_bernoulliWeight_mul_add {α : Type*} (q : ℝ)
    (S : Finset α) (f : Finset α → ℝ) (b : ℝ) :
    (∑ T ∈ S.powerset, bernoulliWeight q S T * (f T + b)) =
      (∑ T ∈ S.powerset, bernoulliWeight q S T * f T) + b := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, bernoulliWeight_sum, one_mul]

open Classical in
theorem sum_bernoulliWeight_mul_sq_add {α : Type*} (q : ℝ)
    (S : Finset α) (f : Finset α → ℝ) (b : ℝ) :
    (∑ T ∈ S.powerset, bernoulliWeight q S T * (f T + b) ^ 2) =
      (∑ T ∈ S.powerset, bernoulliWeight q S T * f T ^ 2) +
        2 * b * (∑ T ∈ S.powerset, bernoulliWeight q S T * f T) + b ^ 2 := by
  calc
    _ = ∑ T ∈ S.powerset,
        (bernoulliWeight q S T * f T ^ 2 +
          2 * b * (bernoulliWeight q S T * f T) + b ^ 2 * bernoulliWeight q S T) := by
      apply Finset.sum_congr rfl
      intro T _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, bernoulliWeight_sum, mul_one]

end Sampling
end ExplicitRIP.GuthZahl

end
