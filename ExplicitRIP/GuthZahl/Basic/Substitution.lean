/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs

/-!
# Degree bounds for polynomial substitution

Substitution by polynomials of degree at most `d` multiplies total degree by at most `d`.
Affine univariate substitutions preserve the total-degree bound.
-/

public section

namespace ExplicitRIP.GuthZahl

theorem totalDegree_eval₂_le {σ τ R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (g : σ → MvPolynomial τ S) (p : MvPolynomial σ R)
    (d : ℕ) (hg : ∀ i, (g i).totalDegree ≤ d) :
    (MvPolynomial.eval₂Hom (MvPolynomial.C.comp φ) g p).totalDegree ≤
      p.totalDegree * d := by
  classical
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a ha
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [RingHom.comp_apply, MvPolynomial.totalDegree_C, zero_add]
  calc
    _ ≤ ∑ i ∈ a.support, (g i ^ a i).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ a.support, a i * d := by
      apply Finset.sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))
    _ = (a.sum fun _ n => n) * d := (Finset.sum_mul ..).symm
    _ ≤ p.totalDegree * d := Nat.mul_le_mul_right _ (MvPolynomial.le_totalDegree ha)

theorem natDegree_eval₂_le {K σ : Type*} [CommSemiring K]
    (p : MvPolynomial σ K) (v : σ → Polynomial K)
    (hv : ∀ i, (v i).natDegree ≤ 1) :
    (p.eval₂ Polynomial.C v).natDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  calc
    (Polynomial.C (p.coeff d) * ∏ i ∈ d.support, v i ^ d i).natDegree
        ≤ (Polynomial.C (p.coeff d)).natDegree +
          (∏ i ∈ d.support, v i ^ d i).natDegree := Polynomial.natDegree_mul_le
    _ = (∏ i ∈ d.support, v i ^ d i).natDegree := by rw [Polynomial.natDegree_C, zero_add]
    _ ≤ ∑ i ∈ d.support, (v i ^ d i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum fun i _ =>
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (d i) (hv i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

end ExplicitRIP.GuthZahl

end
