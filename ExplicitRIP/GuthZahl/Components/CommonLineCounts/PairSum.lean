/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring

/-!
# Degree bounds summed over pairs of factors

Counting each pair once absorbs the factor two in the common-surface line bound.
-/

public section

namespace ExplicitRIP.GuthZahl.Components.CommonLineCounts

/-- Twice the sum of products over distinct unordered pairs is at most the squared sum. -/
theorem sum_pair_bounds_le_sq_sum {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (d : ι → ℕ) :
    (∑ i ∈ s, ∑ j ∈ s with i < j, 2 * d i * d j) ≤ (∑ i ∈ s, d i) ^ 2 := by
  classical
  induction s using Finset.induction_on_min with
  | empty => simp only [Finset.sum_empty, zero_pow (by decide : 2 ≠ 0), le_refl]
  | insert a s ha ih =>
    have has : a ∉ s := fun h => (lt_irrefl a) (ha a h)
    have hpairs :
        (∑ i ∈ insert a s, ∑ j ∈ insert a s with i < j, 2 * d i * d j) =
          2 * d a * (∑ i ∈ s, d i) +
            (∑ i ∈ s, ∑ j ∈ s with i < j, 2 * d i * d j) := by
      rw [Finset.sum_insert has, Finset.filter_insert, ite_eq_right (lt_irrefl a),
        Finset.filter_true_of_mem ha, ← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.filter_insert, ite_eq_right (not_lt_of_ge (ha i hi).le)]
    rw [hpairs, Finset.sum_insert has]
    calc
      _ ≤ 2 * d a * (∑ i ∈ s, d i) + (∑ i ∈ s, d i) ^ 2 :=
        Nat.add_le_add_left ih _
      _ ≤ d a ^ 2 + (2 * d a * (∑ i ∈ s, d i) + (∑ i ∈ s, d i) ^ 2) :=
        Nat.le_add_left _ _
      _ = (d a + ∑ i ∈ s, d i) ^ 2 := by ring

end ExplicitRIP.GuthZahl.Components.CommonLineCounts

end
