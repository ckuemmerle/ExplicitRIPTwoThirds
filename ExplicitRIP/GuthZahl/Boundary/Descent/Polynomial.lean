/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Boundary.Defs

/-!
# Polynomial equations of split quadrics

The determinant after an invertible homogeneous coordinate change gives a
nonzero affine polynomial of total degree at most two.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.Boundary.Descent

variable {K : Type*} [Field K]

/-- The determinant on four coordinates viewed as a two-by-two matrix. -/
def determinantFour (v : Fin 4 → K) : K := v 0 * v 3 - v 1 * v 2

theorem determinantFour_smul (t : K) (v : Fin 4 → K) :
    determinantFour (t • v) = t ^ 2 * determinantFour v := by
  simp only [determinantFour, Pi.smul_apply, smul_eq_mul]
  ring

theorem determinantFour_add_sub (v w : Fin 4 → K) :
    determinantFour (v + w) + determinantFour (v - w) =
      2 * (determinantFour v + determinantFour w) := by
  simp only [determinantFour, Pi.add_apply, Pi.sub_apply]
  ring

/-- One affine coordinate of a homogeneous linear transformation. -/
noncomputable def affineCoordinate (Q : Zahl.SplitQuadric K) (i : Fin 4) : Poly K :=
  MvPolynomial.C (Q (Pi.single 0 1) i) +
    ∑ j : Fin 3, MvPolynomial.C (Q (Pi.single j.succ 1) i) * MvPolynomial.X j

theorem eval_affineCoordinate (Q : Zahl.SplitQuadric K) (i : Fin 4) (x : Point K) :
    MvPolynomial.eval x (affineCoordinate Q i) = Q (Zahl.homogenize x) i := by
  have hx : Zahl.homogenize x =
      Pi.single 0 1 + ∑ j : Fin 3, x j • (Pi.single j.succ 1 : Fin 4 → K) := by
    ext k
    fin_cases k <;> simp [Zahl.homogenize, Fin.sum_univ_three]
  rw [hx]
  simp only [affineCoordinate, map_add, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, map_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm]

theorem totalDegree_affineCoordinate_le (Q : Zahl.SplitQuadric K) (i : Fin 4) :
    (affineCoordinate Q i).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp only [MvPolynomial.totalDegree_C, zero_le]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j _
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add, le_refl]

/-- The affine determinant equation of a split quadric. -/
noncomputable def determinantPolynomial (Q : Zahl.SplitQuadric K) : Poly K :=
  affineCoordinate Q 0 * affineCoordinate Q 3 -
    affineCoordinate Q 1 * affineCoordinate Q 2

theorem eval_determinantPolynomial (Q : Zahl.SplitQuadric K) (x : Point K) :
    MvPolynomial.eval x (determinantPolynomial Q) = Zahl.quadricValue Q x := by
  simp only [determinantPolynomial, map_sub, map_mul, eval_affineCoordinate, Zahl.quadricValue]

theorem totalDegree_determinantPolynomial_le (Q : Zahl.SplitQuadric K) :
    (determinantPolynomial Q).totalDegree ≤ 2 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (totalDegree_affineCoordinate_le Q 0)
        (totalDegree_affineCoordinate_le Q 3))
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (totalDegree_affineCoordinate_le Q 1)
        (totalDegree_affineCoordinate_le Q 2))

/-- A split quadric cannot have the whole affine chart as its zero set. -/
theorem determinantPolynomial_ne_zero (h2 : (2 : K) ≠ 0) (Q : Zahl.SplitQuadric K) :
    determinantPolynomial Q ≠ 0 := by
  intro hp
  have hchart (x : Point K) : determinantFour (Q (Zahl.homogenize x)) = 0 := by
    change Zahl.quadricValue Q x = 0
    rw [← eval_determinantPolynomial, hp, map_zero]
  have hnonzero (v : Fin 4 → K) (hv : v 0 ≠ 0) : determinantFour (Q v) = 0 := by
    let x : Point K := fun i => (v 0)⁻¹ * v i.succ
    have hx : Zahl.homogenize x = (v 0)⁻¹ • v := by
      ext i
      fin_cases i <;> simp [Zahl.homogenize, x, hv]
    have h := hchart x
    rw [hx, map_smul, determinantFour_smul] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (inv_ne_zero hv))
  have hall (v : Fin 4 → K) : determinantFour (Q v) = 0 := by
    by_cases hv : v 0 ≠ 0
    · exact hnonzero v hv
    push Not at hv
    let e : Fin 4 → K := Pi.single 0 1
    have he : determinantFour (Q e) = 0 := hnonzero e (by simp [e])
    have hplus : determinantFour (Q (v + e)) = 0 := hnonzero _ (by simp [e, hv])
    have hminus : determinantFour (Q (v - e)) = 0 := hnonzero _ (by simp [e, hv])
    have h := determinantFour_add_sub (Q v) (Q e)
    rw [← map_add, ← map_sub, hplus, hminus, he, add_zero, add_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left h2
  have h := hall (Q.symm ![1, 0, 0, 1])
  apply (one_ne_zero : (1 : K) ≠ 0)
  simpa only [Q.apply_symm_apply, determinantFour, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail,
    mul_one, zero_mul, sub_zero] using h

end ExplicitRIP.GuthZahl.Boundary.Descent

end
