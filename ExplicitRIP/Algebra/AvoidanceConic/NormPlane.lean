/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Algebra.AvoidanceConic.Plane
public import ExplicitRIP.Algebra.AvoidanceConic.Substitution
public import ExplicitRIP.HermitianForms.Defs.SelectedVertices
public import ExplicitRIP.Algebra.FieldNorm
public import ExplicitRIP.HermitianForms.LightCone.FrameSelection

/-!
# Cubic equations for translated norm graphs on a plane

The field norm is a homogeneous cubic with no nonzero zero. Independent plane directions ensure
that at least one projected direction is nonzero.

Source: [KM, Section 4.2 and proof of Lemma 7(b)].
-/

@[expose] public section

noncomputable section
namespace ExplicitRIP.Avconic

open MvPolynomial
open scoped Matrix

variable {K : Type*} [Field K]

abbrev FourSpace (K : Type*) := K × K × K × K

/-- Projection onto the three norm coordinates. -/
def firstThree (x : FourSpace K) : K × K × K := (x.1, x.2.1, x.2.2.1)

/-- The three coordinates as an evaluation vector. -/
def projection (x : FourSpace K) : Fin 3 → K := ![x.1, x.2.1, x.2.2.1]

/-- A scalar affine linear form in the two plane parameters. -/
def affineForm (a b c : K) : Bivariate K := C a + C b * X 0 + C c * X 1

theorem totalDegree_affineForm_le (a b c : K) : (affineForm a b c).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    exact max_le (by simp) ((totalDegree_mul _ _).trans (by simp))
  · exact (totalDegree_mul _ _).trans (by simp)

@[simp] theorem eval_affineForm (a b c : K) (q : Fin 2 → K) :
    eval q (affineForm a b c) = a + b * q 0 + c * q 1 := by
  simp only [affineForm, map_add, map_mul, eval_C, eval_X]

/-- Restriction of the translated graph equation to the affine plane. -/
def normPlanePolynomial (N : MvPolynomial (Fin 3) K) (x₀ u w : FourSpace K) (τ : K) :
    Bivariate K :=
  aeval (fun i => affineForm (projection x₀ i) (projection u i) (projection w i)) N +
    C τ - affineForm x₀.2.2.2 u.2.2.2 w.2.2.2

theorem eval_normPlanePolynomial (N : MvPolynomial (Fin 3) K)
    (x₀ u w : FourSpace K) (τ : K) (q : Fin 2 → K) :
    eval q (normPlanePolynomial N x₀ u w τ) =
      eval (projection (planeMap x₀ u w q)) N + τ - (planeMap x₀ u w q).2.2.2 := by
  change (aeval q) (normPlanePolynomial N x₀ u w τ) = _
  rw [normPlanePolynomial, map_sub, map_add, comp_aeval_apply]
  have he : (fun i => (aeval q) (affineForm (projection x₀ i) (projection u i)
      (projection w i))) = projection (planeMap x₀ u w q) := by
    funext i
    fin_cases i <;> simp [affineForm, projection, planeMap, smul_eq_mul] <;> ring
  rw [he]
  simp only [aeval_eq_eval, eval_C, eval_affineForm, planeMap, Prod.snd_add,
    Prod.smul_snd, smul_eq_mul]
  ring

theorem totalDegree_normPlanePolynomial_le (N : MvPolynomial (Fin 3) K)
    (hN : N.IsHomogeneous 3) (x₀ u w : FourSpace K) (τ : K) :
    (normPlanePolynomial N x₀ u w τ).totalDegree ≤ 3 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · exact (totalDegree_aeval_linear_le _
        (fun _ => totalDegree_affineForm_le _ _ _) N).trans hN.totalDegree_le
    · simp only [totalDegree_C, zero_le]
  · exact (totalDegree_affineForm_le _ _ _).trans (by decide)

theorem affineRestriction_normPlanePolynomial (N : MvPolynomial (Fin 3) K)
    (x₀ u w : FourSpace K) (τ : K) (v : Fin 2 → K) :
    affineRestriction 0 v (normPlanePolynomial N x₀ u w τ) =
      affineRestriction (projection x₀)
        (fun i => projection u i * v 0 + projection w i * v 1) N + Polynomial.C τ -
      (Polynomial.C x₀.2.2.2 +
        Polynomial.C (u.2.2.2 * v 0 + w.2.2.2 * v 1) * Polynomial.X) := by
  rw [normPlanePolynomial, map_sub, map_add, comp_aeval_apply]
  have he : (fun i => affineRestriction 0 v
      (affineForm (projection x₀ i) (projection u i) (projection w i))) =
      (fun i => Polynomial.C (projection x₀ i) +
        Polynomial.C (projection u i * v 0 + projection w i * v 1) * Polynomial.X) := by
    funext i
    simp only [affineForm, map_add, map_mul, affineRestriction, aeval_C, aeval_X,
      Polynomial.algebraMap_eq, Pi.zero_apply, Polynomial.C_0, zero_add]
    ring
  rw [he]
  simp only [affineForm, map_add, map_mul, affineRestriction, aeval_C, aeval_X,
    Polynomial.algebraMap_eq, Pi.zero_apply, Polynomial.C_0, zero_add]
  ring

theorem coeff_three_normPlanePolynomial (N : MvPolynomial (Fin 3) K)
    (hN : N.IsHomogeneous 3) (x₀ u w : FourSpace K) (τ : K) (v : Fin 2 → K) :
    (affineRestriction 0 v (normPlanePolynomial N x₀ u w τ)).coeff 3 =
      eval (fun i => projection u i * v 0 + projection w i * v 1) N := by
  rw [affineRestriction_normPlanePolynomial, Polynomial.coeff_sub, Polynomial.coeff_add,
    coeff_affineRestriction_of_isHomogeneous _ _ _ _ hN]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide,
    ite_false, add_zero, sub_zero]

/-- A two-dimensional plane cannot project to zero in all three norm coordinates. -/
theorem firstThree_ne_zero_or (u w : FourSpace K) (huw : LinearIndependent K ![u, w]) :
    firstThree u ≠ 0 ∨ firstThree w ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨a, b, c, d⟩ := u
  obtain ⟨e, f, g, k⟩ := w
  have ha : a = 0 := congrArg Prod.fst h.1
  have hb : b = 0 := congrArg (fun z : K × K × K => z.2.1) h.1
  have hc : c = 0 := congrArg (fun z : K × K × K => z.2.2) h.1
  have he : e = 0 := congrArg Prod.fst h.2
  have hf : f = 0 := congrArg (fun z : K × K × K => z.2.1) h.2
  have hg : g = 0 := congrArg (fun z : K × K × K => z.2.2) h.2
  subst a; subst b; subst c; subst e; subst f; subst g
  have hw : (0, 0, 0, k) ≠ (0 : FourSpace K) := by
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using huw.ne_zero 1
  have hk : k ≠ 0 := by intro h; apply hw; subst k; rfl
  have hdep := (linearIndependent_fin2.mp huw).2 (d / k)
  apply hdep
  ext <;> simp [smul_eq_mul, hk]

/-- The norm graph equation has degree exactly three on every affine plane. -/
theorem totalDegree_normPlanePolynomial (N : MvPolynomial (Fin 3) K)
    (hN : N.IsHomogeneous 3)
    (hNzero : ∀ z : K × K × K, z ≠ 0 → eval ![z.1, z.2.1, z.2.2] N ≠ 0)
    (x₀ u w : FourSpace K) (huw : LinearIndependent K ![u, w]) (τ : K) :
    (normPlanePolynomial N x₀ u w τ).totalDegree = 3 := by
  apply le_antisymm (totalDegree_normPlanePolynomial_le N hN x₀ u w τ)
  rcases firstThree_ne_zero_or u w huw with hu | hw
  · have hn : (affineRestriction 0 ![1, 0]
        (normPlanePolynomial N x₀ u w τ)).coeff 3 ≠ 0 := by
      rw [coeff_three_normPlanePolynomial N hN]
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero,
        add_zero, firstThree, projection] using hNzero (firstThree u) hu
    exact (Polynomial.le_natDegree_of_ne_zero hn).trans (natDegree_affineRestriction_le _ _ _)
  · have hn : (affineRestriction 0 ![0, 1]
        (normPlanePolynomial N x₀ u w τ)).coeff 3 ≠ 0 := by
      rw [coeff_three_normPlanePolynomial N hN]
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero,
        zero_add, firstThree, projection] using hNzero (firstThree w) hw
    exact (Polynomial.le_natDegree_of_ne_zero hn).trans (natDegree_affineRestriction_le _ _ _)

end ExplicitRIP.Avconic

end
