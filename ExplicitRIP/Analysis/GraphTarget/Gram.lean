/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.UnsignedRIPConstant
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# Absolute Gram errors for a general two-distance frame

This proves the entrywise identity on supports used in [KM, proof of Theorem 1] before (16).
Only the given Gram formula and nonnegative coefficients are needed; no particular host graph
or realization is used.
-/

public section

open scoped Matrix

namespace ExplicitRIP.GraphTarget

open Classical in
/-- The absolute support Gram error is the weighted adjacency/complement sum. -/
theorem abs_gram_error_submatrix {V m : Type*} [DecidableEq V] [Fintype m]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (Γ : Finset V) (Φ : Matrix m Γ ℝ)
    (hgram : Φᵀ * Φ = (1 - a • G.adjMatrix ℝ +
      b • (Matrix.of (fun _ _ => (1 : ℝ)) - 1 - G.adjMatrix ℝ)).submatrix
        (Subtype.val : Γ → V) (Subtype.val : Γ → V))
    (S : Finset Γ) :
    (((Φᴴ * Φ - 1).map fun z => ‖z‖).submatrix
      (Subtype.val : S → Γ) (Subtype.val : S → Γ)) =
        a • (G.comap (fun i : S => i.1.1)).adjMatrix ℝ +
          b • (G.comap (fun i : S => i.1.1))ᶜ.adjMatrix ℝ := by
  classical
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hgram]
  ext x y
  have heq : x.1.1 = y.1.1 ↔ x = y := by
    constructor
    · intro h
      exact Subtype.ext (Subtype.ext h)
    · exact congrArg (fun i : S => i.1.1)
  have heq' : x.1 = y.1 ↔ x = y := Subtype.val_injective.eq_iff
  simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.one_apply, SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj,
    SimpleGraph.comap_adj, ne_eq, heq, heq']
  by_cases hxy : x = y
  · subst y
    simp only [not_true_eq_false, SimpleGraph.irrefl, ite_true, ite_false,
      mul_zero, sub_zero, sub_self, norm_zero, add_zero, false_and]
  · by_cases hadj : G.Adj x.1.1 y.1.1
    · simp only [hxy, hadj, not_false_eq_true, not_true_eq_false, ite_false, ite_true,
        mul_one, mul_zero, sub_zero, sub_self, zero_sub, add_zero, true_and]
      rw [norm_neg, Real.norm_of_nonneg ha]
    · simp only [hxy, hadj, not_false_eq_true, ite_false, ite_true, mul_one,
        mul_zero, sub_zero, sub_self, zero_add, and_self]
      exact Real.norm_of_nonneg hb

end ExplicitRIP.GraphTarget
