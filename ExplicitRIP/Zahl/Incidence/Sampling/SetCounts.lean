/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Sampling.Mean

/-! # Passing pointwise survival estimates to finite set counts -/

public section

namespace ExplicitRIP.Zahl.Sampling

open scoped BigOperators

open Classical in
lemma sum_indicator_le_ncard {α : Type*} (P : Finset α) (Q : Set α) (hQ : Q.Finite) :
    (∑ x ∈ P, if x ∈ Q then (1 : ℝ) else 0) ≤ (Q.ncard : ℝ) := by
  rw [Finset.sum_boole]
  have hsub : (↑(P.filter (· ∈ Q)) : Set α) ⊆ Q := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  exact_mod_cast (by simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hQ)

open Classical in
lemma mean_ncard_lower {α Ω : Type*} (A : Finset Ω) (P : Set α) (hP : P.Finite)
    (Q : Ω → Set α) (hQ : ∀ ω ∈ A, (Q ω).Finite) (c : ℝ)
    (hc : ∀ x ∈ P, c ≤ Finset.expect A (fun ω => if x ∈ Q ω then (1 : ℝ) else 0)) :
    c * (P.ncard : ℝ) ≤ Finset.expect A (fun ω => ((Q ω).ncard : ℝ)) := by
  calc
    _ = ∑ _x ∈ hP.toFinset, c := by
      rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card P hP, mul_comm]
    _ ≤ ∑ x ∈ hP.toFinset,
        Finset.expect A (fun ω => if x ∈ Q ω then (1 : ℝ) else 0) := by
      exact Finset.sum_le_sum fun x hx => hc x (hP.mem_toFinset.mp hx)
    _ = Finset.expect A (fun ω => ∑ x ∈ hP.toFinset, if x ∈ Q ω then (1 : ℝ) else 0) :=
      (Finset.expect_sum_comm _ _ _).symm
    _ ≤ _ := Finset.expect_le_expect fun ω hω => sum_indicator_le_ncard _ _ (hQ ω hω)

end ExplicitRIP.Zahl.Sampling
