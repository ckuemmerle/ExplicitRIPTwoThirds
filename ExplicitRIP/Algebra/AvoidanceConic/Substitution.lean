/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Algebra.PolynomialCoeff

/-!
# Degree and leading coefficients under affine substitution

The highest coefficient of a homogeneous form restricted to an affine line is
its value on the direction. This supplies the nonzero cubic term of a norm graph.
-/

@[expose] public section

noncomputable section
namespace ExplicitRIP.Avconic

open MvPolynomial Finset

variable {K σ τ : Type*} [Field K]

/-- Substitution of affine linear polynomials does not increase total degree. -/
theorem totalDegree_aeval_linear_le
    (f : σ → MvPolynomial τ K) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (P : MvPolynomial σ K) : (aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [aeval_monomial, algebraMap_eq]
  apply le_trans (totalDegree_mul _ _)
  simp only [totalDegree_C, zero_add]
  apply le_trans (totalDegree_finsetProd _ _)
  apply le_trans (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans ?_)
  · simpa only [Finsupp.sum] using le_totalDegree hm
  · simpa using Nat.mul_le_mul_left (m i) (hf i)

/-- The analogous degree bound for univariate affine substitution. -/
theorem natDegree_aeval_linear_le
    (f : σ → Polynomial K) (hf : ∀ i, (f i).natDegree ≤ 1)
    (P : MvPolynomial σ K) : (aeval f P).natDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [aeval_monomial, Polynomial.algebraMap_eq]
  apply le_trans Polynomial.natDegree_mul_le
  simp only [Polynomial.natDegree_C, zero_add]
  apply le_trans (Polynomial.natDegree_prod_le _ _)
  apply le_trans (Finset.sum_le_sum fun i _ => Polynomial.natDegree_pow_le.trans ?_)
  · simpa only [Finsupp.sum] using le_totalDegree hm
  · simpa using Nat.mul_le_mul_left (m i) (hf i)

/-- Restriction of a multivariate polynomial to an affine line. -/
def affineRestriction (a v : σ → K) : MvPolynomial σ K →ₐ[K] Polynomial K :=
  aeval fun i => Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X

theorem natDegree_affineRestriction_le (a v : σ → K) (P : MvPolynomial σ K) :
    (affineRestriction a v P).natDegree ≤ P.totalDegree := by
  apply natDegree_aeval_linear_le
  intro i
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp only [Polynomial.natDegree_C, zero_le]
  · exact Polynomial.natDegree_C_mul_le _ _ |>.trans (by simp)

/-- The top coefficient of a homogeneous form on an affine line is the form's
value at the line direction, including when that value is zero. -/
theorem coeff_affineRestriction_of_isHomogeneous (a v : σ → K)
    (P : MvPolynomial σ K) (n : ℕ) (hP : P.IsHomogeneous n) :
    (affineRestriction a v P).coeff n = eval v P := by
  classical
  conv_lhs => rw [P.as_sum, map_sum, Polynomial.finsetSum_coeff]
  conv_rhs => rw [P.as_sum, map_sum]
  apply sum_congr rfl
  intro m hm
  rw [affineRestriction, aeval_monomial, Polynomial.algebraMap_eq,
    Polynomial.coeff_C_mul, eval_monomial]
  congr 1
  rw [hP.degree_eq_sum_deg_support hm]
  have hlin (i : σ) :
      (Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
      ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)))
  simp only [Finsupp.prod]
  rw [coeff_prod_sum_of_natDegree_le m.support _ (fun i => m i)
    (fun i _ => by simpa only [mul_one] using
      (Polynomial.natDegree_pow_le_of_le (m i) (hlin i)))]
  apply prod_congr rfl
  intro i _
  simpa only [mul_one, Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_one, ite_false, zero_add, mul_one,
    Nat.one_ne_zero] using Polynomial.coeff_pow_of_natDegree_le (m := m i) (hlin i)

theorem eval_affineRestriction (a v : σ → K) (P : MvPolynomial σ K) (t : K) :
    Polynomial.eval t (affineRestriction a v P) = eval (fun i => a i + v i * t) P := by
  change ((Polynomial.aeval t).comp (affineRestriction a v)) P = _
  have he : (Polynomial.aeval t).comp (affineRestriction a v) =
      aeval (fun i => a i + v i * t) := by
    ext i
    simp only [AlgHom.comp_apply, affineRestriction, aeval_X, map_add, map_mul,
      Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
  rw [he]
  rfl

end ExplicitRIP.Avconic

end
