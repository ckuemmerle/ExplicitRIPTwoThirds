/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# A polynomial for the norm in three coordinates

The determinant of the matrix of multiplication is a homogeneous cubic in any
three linear coordinates. This construction keeps polynomial homogeneity distinct
from homogeneity of the resulting function over a finite field.
-/

@[expose] public section

noncomputable section

namespace ExplicitRIP.NormPolynomial

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The matrix of linear forms for multiplication by a generic coordinate vector. -/
def coordinateMatrix (b : Module.Basis (Fin 3) K A) (x : Fin 3 → A) :
    Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) K) := fun i j =>
  MvPolynomial.C (Algebra.leftMulMatrix b (x 0) i j) * MvPolynomial.X 0 +
    MvPolynomial.C (Algebra.leftMulMatrix b (x 1) i j) * MvPolynomial.X 1 +
    MvPolynomial.C (Algebra.leftMulMatrix b (x 2) i j) * MvPolynomial.X 2

/-- The determinant polynomial representing the norm in the chosen coordinates. -/
def normPolynomial (b : Module.Basis (Fin 3) K A) (x : Fin 3 → A) :
    MvPolynomial (Fin 3) K :=
  (coordinateMatrix b x).det

theorem coordinateMatrix_isHomogeneous (b : Module.Basis (Fin 3) K A) (x : Fin 3 → A)
    (i j : Fin 3) : (coordinateMatrix b x i j).IsHomogeneous 1 := by
  exact ((MvPolynomial.isHomogeneous_C_mul_X _ _).add
    (MvPolynomial.isHomogeneous_C_mul_X _ _)).add
    (MvPolynomial.isHomogeneous_C_mul_X _ _)

theorem normPolynomial_isHomogeneous (b : Module.Basis (Fin 3) K A) (x : Fin 3 → A) :
    (normPolynomial b x).IsHomogeneous 3 := by
  have h (i j k l m n : Fin 3) :
      (coordinateMatrix b x i j * coordinateMatrix b x k l *
        coordinateMatrix b x m n).IsHomogeneous 3 :=
    ((coordinateMatrix_isHomogeneous b x i j).mul
      (coordinateMatrix_isHomogeneous b x k l)).mul
      (coordinateMatrix_isHomogeneous b x m n)
  rw [normPolynomial, Matrix.det_fin_three]
  exact ((((h 0 0 1 1 2 2).sub (h 0 0 1 2 2 1)).sub (h 0 1 1 0 2 2)).add
    (h 0 1 1 2 2 0) |>.add (h 0 2 1 0 2 1)).sub (h 0 2 1 1 2 0)

theorem eval_coordinateMatrix (b : Module.Basis (Fin 3) K A) (x : Fin 3 → A)
    (w : K × K × K) :
    (coordinateMatrix b x).map (MvPolynomial.eval ![w.1, w.2.1, w.2.2]) =
      Algebra.leftMulMatrix b (w.1 • x 0 + w.2.1 • x 1 + w.2.2 • x 2) := by
  ext i j
  simp only [Matrix.map_apply, coordinateMatrix, map_add, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, map_smul, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem eval_normPolynomial (b : Module.Basis (Fin 3) K A) (x : Fin 3 → A)
    (w : K × K × K) :
    MvPolynomial.eval ![w.1, w.2.1, w.2.2] (normPolynomial b x) =
      Algebra.norm K (w.1 • x 0 + w.2.1 • x 1 + w.2.2 • x 2) := by
  rw [normPolynomial, RingHom.map_det, Algebra.norm_eq_matrix_det b]
  exact congrArg Matrix.det (eval_coordinateMatrix b x w)

end ExplicitRIP.NormPolynomial

end

end
