/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.Restriction
public import ExplicitRIP.Algebra.PolynomialCoeff

/-!
# Highest coefficients of affine line restrictions

At a bound for the total degree, the coefficient in a line restriction depends
only on the direction. This handles common transversals parallel to one of
three skew lines without adding a point at infinity to the affine carrier.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- An affine linear polynomial has degree at most one. -/
theorem natDegree_affine_le (a v : K) :
    (Polynomial.C a + Polynomial.C v * Polynomial.X).natDegree ≤ 1 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · rw [Polynomial.natDegree_C]
    exact Nat.zero_le 1
  · simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le v 1

/-- The coefficient at the full monomial degree depends only on direction. -/
theorem coeff_restrictLine_monomial_top (d : Fin 3 →₀ ℕ) (c : K) (a v : Point K) :
    (restrictLine (MvPolynomial.monomial d c) a v).coeff (d.sum fun _ e => e) =
      c * ∏ i ∈ d.support, (v i) ^ d i := by
  classical
  change (MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X)
    (MvPolynomial.monomial d c)).coeff _ = _
  rw [MvPolynomial.eval₂_monomial, Polynomial.coeff_C_mul]
  congr 1
  change (∏ i ∈ d.support,
    (Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) ^ d i).coeff
      (∑ i ∈ d.support, d i) = _
  rw [coeff_prod_sum_of_natDegree_le _ _ _ (fun i hi =>
    Polynomial.natDegree_pow_le.trans (by simpa only [Nat.mul_one] using
      (Nat.mul_le_mul_left (d i) (natDegree_affine_le (a i) (v i)))))]
  apply Finset.prod_congr rfl
  intro i hi
  have h := Polynomial.coeff_pow_of_natDegree_le
    (m := d i) (natDegree_affine_le (a i) (v i))
  simpa only [Nat.mul_one, Polynomial.coeff_add, Polynomial.coeff_C,
    one_ne_zero, ↓reduceIte, Polynomial.coeff_C_mul_X, zero_add] using h

/-- At a total-degree bound, changing the base point preserves the leading coefficient. -/
theorem coeff_restrictLine_eq_of_totalDegree_le {f : Poly K} {n : ℕ}
    (hf : f.totalDegree ≤ n) (a b v : Point K) :
    (restrictLine f a v).coeff n = (restrictLine f b v).coeff n := by
  classical
  have hmono (d : Fin 3 →₀ ℕ) (hd : d ∈ f.support) (c : K) :
      (restrictLine (MvPolynomial.monomial d c) a v).coeff n =
        (restrictLine (MvPolynomial.monomial d c) b v).coeff n := by
    have hdle := (MvPolynomial.le_totalDegree hd).trans hf
    by_cases heq : d.sum (fun _ e => e) = n
    · rw [← heq, coeff_restrictLine_monomial_top, coeff_restrictLine_monomial_top]
    · have hlt : d.sum (fun _ e => e) < n := lt_of_le_of_ne hdle heq
      have hdeg : (MvPolynomial.monomial d c).totalDegree < n :=
        (MvPolynomial.totalDegree_monomial_le _ _).trans_lt hlt
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        ((restrictLine_natDegree_le _ _ _).trans_lt hdeg),
        Polynomial.coeff_eq_zero_of_natDegree_lt
        ((restrictLine_natDegree_le _ _ _).trans_lt hdeg)]
  have expand (x : Point K) : (restrictLine f x v).coeff n =
      ∑ d ∈ f.support, (restrictLine (MvPolynomial.monomial d (f.coeff d)) x v).coeff n := by
    conv_lhs => rw [f.as_sum]
    rw [show restrictLine (∑ d ∈ f.support, MvPolynomial.monomial d (f.coeff d)) x v =
      ∑ d ∈ f.support, restrictLine (MvPolynomial.monomial d (f.coeff d)) x v from
        map_sum (MvPolynomial.eval₂Hom Polynomial.C
          (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X)) _ _]
    simp only [Polynomial.finsetSum_coeff]
  rw [expand a, expand b]
  exact Finset.sum_congr rfl (fun d hd => hmono d hd _)

/-- A direction shared with a contained line kills the coefficient at the total-degree bound. -/
theorem coeff_restrictLine_eq_zero_of_parallel {f : Poly K} {n : ℕ}
    (hf : f.totalDegree ≤ n) {A L : Line K} (hA : LineOn f A)
    (hdir : L.1.direction = A.1.direction) (b v : Point K) (hv : v ∈ L.1.direction) :
    (restrictLine f b v).coeff n = 0 := by
  obtain ⟨a, ha⟩ := line_nonempty A
  rw [coeff_restrictLine_eq_of_totalDegree_le hf b a v,
    hA a ha v (hdir ▸ hv), Polynomial.coeff_zero]

end ExplicitRIP.GuthZahl.RuledSurfaces
end
