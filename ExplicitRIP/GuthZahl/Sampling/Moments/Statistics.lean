/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Sampling.Moments.Weights

/-!
# Moments of the number of sampled witnesses

Adding one element to the ground set adds either zero or one to the witness
count. Powerset recursion proves its first and raw second moments, and
expansion of a square gives the centered second moment.
-/

public section

namespace ExplicitRIP.GuthZahl
namespace Sampling

open Classical in
theorem sum_bernoulliWeight_inter_insert {α : Type*} (q : ℝ)
    (S W : Finset α) (a : α) (ha : a ∉ S) (f : ℝ → ℝ) :
    (∑ T ∈ (insert a S).powerset,
      bernoulliWeight q (insert a S) T * f ((T ∩ W).card : ℝ)) =
      (1 - q) * (∑ T ∈ S.powerset,
        bernoulliWeight q S T * f ((T ∩ W.erase a).card : ℝ)) +
      q * (∑ T ∈ S.powerset,
        bernoulliWeight q S T *
          f (((T ∩ W.erase a).card : ℝ) + if a ∈ W then 1 else 0)) := by
  have haT : ∀ T ∈ S.powerset, a ∉ T :=
    fun T hT h => ha (Finset.mem_powerset.mp hT h)
  have hinter : ∀ T ∈ S.powerset, T ∩ W = T ∩ W.erase a := by
    intro T hT
    rw [Finset.inter_erase, Finset.erase_eq_of_notMem]
    exact fun h => haT T hT (Finset.mem_inter.mp h).1
  rw [sum_bernoulliWeight_insert q S a ha]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro T hT
    rw [hinter T hT]
  · congr 1
    apply Finset.sum_congr rfl
    intro T hT
    by_cases haW : a ∈ W
    · rw [Finset.insert_inter_of_mem haW,
        Finset.card_insert_of_notMem
          (fun h => haT T hT (Finset.mem_inter.mp h).1),
        Nat.cast_add, Nat.cast_one, hinter T hT, ite_eq_left haW]
    · rw [Finset.insert_inter_of_notMem haW, hinter T hT, ite_eq_right haW, add_zero]

open Classical in
theorem card_eq_card_erase_add_indicator {α : Type*} (W : Finset α) (a : α) :
    (W.card : ℝ) = ((W.erase a).card : ℝ) + if a ∈ W then 1 else 0 := by
  by_cases haW : a ∈ W
  · rw [ite_eq_left haW]
    exact_mod_cast (Finset.card_erase_add_one haW).symm
  · rw [ite_eq_right haW, Finset.erase_eq_of_notMem haW, add_zero]

open Classical in
/-- The weighted size of the intersection with a fixed subset has mean `q * card W`. -/
theorem _root_.ExplicitRIP.GuthZahl.bernoulli_first_moment {α : Type*} (q : ℝ)
    (S W : Finset α) (hW : W ⊆ S) :
    (∑ T ∈ S.powerset, bernoulliWeight q S T * ((T ∩ W).card : ℝ)) =
      q * W.card := by
  induction S using Finset.induction_on generalizing W with
  | empty =>
    have hWempty : W = ∅ := Finset.subset_empty.mp hW
    subst W
    simp only [Finset.inter_empty, Finset.card_empty, Nat.cast_zero, mul_zero,
      Finset.sum_const_zero]
  | @insert a S ha ih =>
    have hWe : W.erase a ⊆ S := Finset.subset_insert_iff.mp hW
    rw [sum_bernoulliWeight_inter_insert q S W a ha (fun x => x),
      sum_bernoulliWeight_mul_add]
    simp only [ih _ hWe]
    rw [card_eq_card_erase_add_indicator W a]
    ring

open Classical in
theorem sum_bernoulliWeight_mul_inter_card_sq {α : Type*} (q : ℝ)
    (S W : Finset α) (hW : W ⊆ S) :
    (∑ T ∈ S.powerset, bernoulliWeight q S T * ((T ∩ W).card : ℝ) ^ 2) =
      (q * W.card) ^ 2 + q * (1 - q) * W.card := by
  induction S using Finset.induction_on generalizing W with
  | empty =>
    have hWempty : W = ∅ := Finset.subset_empty.mp hW
    subst W
    simp only [Finset.inter_empty, Finset.card_empty, Nat.cast_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, add_zero]
  | @insert a S ha ih =>
    have hWe : W.erase a ⊆ S := Finset.subset_insert_iff.mp hW
    rw [sum_bernoulliWeight_inter_insert q S W a ha (fun x => x ^ 2),
      sum_bernoulliWeight_mul_sq_add]
    simp only [ih _ hWe, bernoulli_first_moment q S (W.erase a) hWe]
    rw [card_eq_card_erase_add_indicator W a]
    by_cases haW : a ∈ W
    · simp only [ite_eq_left haW]
      ring
    · simp only [ite_eq_right haW]
      ring

open Classical in
/-- The weighted size of the intersection with a fixed subset has second centered moment `q * (1
- q) * card W`. -/
theorem _root_.ExplicitRIP.GuthZahl.bernoulli_second_moment {α : Type*} (q : ℝ)
    (S W : Finset α) (hW : W ⊆ S) :
    (∑ T ∈ S.powerset, bernoulliWeight q S T *
      (((T ∩ W).card : ℝ) - q * W.card) ^ 2) = q * (1 - q) * W.card := by
  simp only [sub_eq_add_neg]
  rw [sum_bernoulliWeight_mul_sq_add,
    sum_bernoulliWeight_mul_inter_card_sq q S W hW,
    bernoulli_first_moment q S W hW]
  ring

end Sampling
end ExplicitRIP.GuthZahl

end
