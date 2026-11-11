/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.Defs.HermitianGraph
public import ExplicitRIP.HermitianForms.RankOne.Basic

/-!
# Coordinates for the Hermitian graph

The Hermitian-forms model of `VO₄⁻(p)` uses coordinates `(a, b₁, b₂, c)` with determinant
`ac - b₁² - b₂²`. A nonzero Hermitian matrix has rank one exactly when its determinant vanishes.
This criterion supplies the common-neighbor calculations for the parameters of [KM, Section 3].
-/

@[expose] public section

namespace ExplicitRIP.Hfsrg

open scoped Matrix

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

abbrev Vertex := ZMod p × ZMod p × ZMod p × ZMod p

abbrev Extension := QuadraticAlgebra (ZMod p) (-1) 0

/-- The determinant in base-field coordinates. -/
def quad (x : Vertex p) : ZMod p :=
  x.1 * x.2.2.2 - x.2.1 ^ 2 - x.2.2.1 ^ 2

omit [Fact (p % 4 = 3)] in
theorem norm_mk (b c : ZMod p) :
    (QuadraticAlgebra.norm (⟨b, c⟩ : Extension p)) = b ^ 2 + c ^ 2 := by
  simp [QuadraticAlgebra.norm_def, sq]

omit [Fact (p % 4 = 3)] in
@[simp] theorem quad_zero : quad p 0 = 0 := by simp [quad]

omit [Fact (p % 4 = 3)] in
@[simp] theorem quad_neg (x : Vertex p) : quad p (-x) = quad p x := by
  simp [quad]

omit [Fact (p % 4 = 3)] in
theorem quad_sub_comm (x y : Vertex p) : quad p (x - y) = quad p (y - x) := by
  rw [← quad_neg, neg_sub]

theorem hermitianMatrix_sub (x y : Vertex p) :
    hermitianMatrix p (x - y) = hermitianMatrix p x - hermitianMatrix p y := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hermitianMatrix]; ring

theorem hermitianMatrix_injective : Function.Injective (hermitianMatrix p) := by
  intro x y h
  have h00 := congrArg (fun M => (M 0 0).re) h
  have h01 := congrArg (fun M => (M 0 1).re) h
  have h01' := congrArg (fun M => (M 0 1).im) h
  have h11 := congrArg (fun M => (M 1 1).re) h
  exact Prod.ext h00 (Prod.ext h01 (Prod.ext h01' h11))

@[simp] theorem hermitianMatrix_zero : hermitianMatrix p 0 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [hermitianMatrix]

theorem det_hermitianMatrix (x : Vertex p) :
    (hermitianMatrix p x).det = (⟨quad p x, 0⟩ : Extension p) := by
  simp only [hermitianMatrix, Matrix.det_fin_two]
  ext <;> simp [quad, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring

theorem adj_iff (x y : Vertex p) :
    (hermitianGraph p).Adj x y ↔ x ≠ y ∧ quad p (x - y) = 0 := by
  have hr (u v : Vertex p) :
      (hermitianMatrix p u - hermitianMatrix p v).rank = 1 ↔
        u ≠ v ∧ quad p (u - v) = 0 := by
    rw [← hermitianMatrix_sub, Rank1.matrix_rank_eq_one_iff, det_hermitianMatrix]
    simp only [← hermitianMatrix_zero p, (hermitianMatrix_injective p).ne_iff,
      sub_ne_zero, QuadraticAlgebra.ext_iff, QuadraticAlgebra.re_zero,
      QuadraticAlgebra.im_zero, and_true]
  simp only [hermitianGraph, SimpleGraph.fromRel_adj, hr, quad_sub_comm p y x]
  tauto

end ExplicitRIP.Hfsrg
