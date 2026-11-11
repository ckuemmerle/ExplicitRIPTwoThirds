/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# A coefficient of a product of polynomials

If each factor `f i` has degree at most `d i`, the coefficient of the product at `∑ d i` is the
product of the coefficients at `d i`. Mathlib's `Polynomial.coeff_prod_of_natDegree_le` is the
case of a uniform bound. -/

public section

namespace ExplicitRIP

open Finset

/-- The coefficient at the sum of degree bounds in a product. -/
theorem coeff_prod_sum_of_natDegree_le {K : Type*} [Field K] {α : Type*} (S : Finset α)
    (f : α → Polynomial K) (d : α → ℕ) (hd : ∀ i ∈ S, (f i).natDegree ≤ d i) :
    (∏ i ∈ S, f i).coeff (∑ i ∈ S, d i) = ∏ i ∈ S, (f i).coeff (d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [prod_empty, sum_empty, Polynomial.coeff_one_zero]
  | @insert i S hi ih =>
    rw [prod_insert hi, sum_insert hi, prod_insert hi]
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hd i (mem_insert_self _ _))]
    · rw [ih (fun j hj => hd j (mem_insert_of_mem hj))]
    · exact (Polynomial.natDegree_prod_le _ _).trans
        (sum_le_sum fun j hj => hd j (mem_insert_of_mem hj))

end ExplicitRIP
