/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Basic.Substitution
public import ExplicitRIP.GuthZahl.Jets.Defs

/-!
# Translation and Hasse coefficients

The symmetry of `f(x+y)` transfers its outer degree bound to each coefficient polynomial.
-/

public section

namespace ExplicitRIP.GuthZahl

namespace Hasse

theorem coeff_commAlgEquiv {R σ τ : Type*} [CommSemiring R]
    (p : MvPolynomial σ (MvPolynomial τ R)) (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    ((MvPolynomial.commAlgEquiv R σ τ p).coeff b).coeff a =
      (p.coeff a).coeff b := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial c q =>
    induction q using MvPolynomial.induction_on' with
    | monomial d k =>
      change (((AddMonoidAlgebra.commAlgEquiv R)
        (AddMonoidAlgebra.single c (AddMonoidAlgebra.single d k))).coeff b).coeff a =
          ((AddMonoidAlgebra.single c (AddMonoidAlgebra.single d k)).coeff a).coeff b
      rw [AddMonoidAlgebra.commAlgEquiv_single_single]
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs <;> simp_all
    | add q₁ q₂ h₁ h₂ =>
      simpa only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
        congrArg₂ (· + ·) h₁ h₂
  | add p₁ p₂ h₁ h₂ =>
    simpa only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
      congrArg₂ (· + ·) h₁ h₂

theorem commAlgEquiv_translatedPolynomial {K : Type*} [Field K] (f : Poly K) :
    MvPolynomial.commAlgEquiv K (Fin 3) (Fin 3) (translatedPolynomial f) =
      translatedPolynomial f := by
  let T := MvPolynomial.eval₂Hom (MvPolynomial.C.comp (MvPolynomial.C : K →+* Poly K))
    (fun i : Fin 3 => MvPolynomial.C (MvPolynomial.X i) + MvPolynomial.X i)
  have h : (MvPolynomial.commAlgEquiv K (Fin 3) (Fin 3)).toRingHom.comp T = T := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp only [RingHom.comp_apply, T, MvPolynomial.eval₂Hom_C]
      change MvPolynomial.commAlgEquiv K (Fin 3) (Fin 3)
        (MvPolynomial.C (MvPolynomial.C k)) = MvPolynomial.C (MvPolynomial.C k)
      rw [MvPolynomial.commAlgEquiv_C, MvPolynomial.map_C]
    · intro i
      simp only [RingHom.comp_apply, T, MvPolynomial.eval₂Hom_X']
      change MvPolynomial.commAlgEquiv K (Fin 3) (Fin 3)
        (MvPolynomial.C (MvPolynomial.X i) + MvPolynomial.X i) =
          MvPolynomial.C (MvPolynomial.X i) + MvPolynomial.X i
      simp only [map_add,
        MvPolynomial.commAlgEquiv_C_X, MvPolynomial.commAlgEquiv_X, add_comm]
  exact DFunLike.congr_fun h f

theorem translatedPolynomial_totalDegree_le {K : Type*} [Field K] (f : Poly K) :
    (translatedPolynomial f).totalDegree ≤ f.totalDegree := by
  simpa only [translatedPolynomial, mul_one] using
    totalDegree_eval₂_le (MvPolynomial.C : K →+* Poly K)
      (fun i : Fin 3 => MvPolynomial.C (MvPolynomial.X i) + MvPolynomial.X i)
      f 1 (fun i => by
        apply (MvPolynomial.totalDegree_add _ _).trans
        simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, max_eq_right,
          zero_le]
        exact le_rfl)

/-- Each Hasse coefficient polynomial has total degree at most that of the original polynomial. -/
theorem _root_.ExplicitRIP.GuthZahl.hasseCoefficient_totalDegree_le {K : Type*} [Field K]
    (f : Poly K) (a : Fin 3 →₀ ℕ) :
    (hasseCoefficient f a).totalDegree ≤ f.totalDegree := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro b hb
  apply (MvPolynomial.le_totalDegree (p := translatedPolynomial f) ?_).trans
    (translatedPolynomial_totalDegree_le f)
  rw [MvPolynomial.mem_support_iff]
  intro h
  have hb' := MvPolynomial.mem_support_iff.mp hb
  apply hb'
  change ((translatedPolynomial f).coeff a).coeff b = 0
  rw [← coeff_commAlgEquiv, commAlgEquiv_translatedPolynomial, h,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

end Hasse

end ExplicitRIP.GuthZahl

end
