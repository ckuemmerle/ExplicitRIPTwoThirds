/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.ACC.Dickson
public import ExplicitRIP.GuthZahl.ACC.Division

/-!
# Field-uniform quantitative ACC for polynomial ideals

Controlled Dickson bounds and degree-compatible multivariate division bound the
first redundant polynomial in a degree-controlled sequence. The bound depends only
on the number of variables and the degree-control function.
-/

public section

namespace ExplicitRIP.GuthZahl

/-- The polynomial special case of quantitative ACC, with a field-uniform bound. The formal proof
uses controlled Dickson sequences and degree-compatible division in place of the argument using
ordinary Hilbert-polynomial coefficients in [GZ, Appendix A]. -/
theorem quantitative_acc (N : ℕ) (τ : ℕ → ℕ) :
    ∃ M : ℕ, ∀ (K : Type*) [Field K] (fs : ℕ → MvPolynomial (Fin N) K),
      (∀ j, (fs j).totalDegree ≤ τ j) →
      ∃ r ≤ M, fs r ∈ Ideal.span (fs '' Set.Iio r) := by
  classical
  obtain ⟨M, hM⟩ := controlled_dickson_bound N τ
  refine ⟨M, ?_⟩
  intro K _ fs hdegree
  by_contra hnone
  let gs : Fin (M + 1) → MvPolynomial (Fin N) K := fun i => fs i.val
  have hstrict : ∀ i, gs i ∉ Ideal.span (gs '' Set.Iio i) := by
    intro i hi
    apply hnone
    refine ⟨i.val, Nat.le_of_lt_succ i.isLt, ?_⟩
    apply Ideal.span_mono (s := gs '' Set.Iio i) ?_ hi
    rintro f ⟨j, hj, rfl⟩
    exact ⟨j.val, hj, rfl⟩
  obtain ⟨a, ha, hbad⟩ := strict_polynomial_sequence_monomials N (M + 1) τ K gs
    (fun i => hdegree i.val) hstrict
  exact Nat.not_succ_le_self M (hM (M + 1) a ha hbad)

end ExplicitRIP.GuthZahl

end
