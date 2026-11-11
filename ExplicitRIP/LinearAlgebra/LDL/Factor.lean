/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.LinearAlgebra.LDL.Residual
public import ExplicitRIP.Frozen.Defs.LDLPivots
public import ExplicitRIP.Frozen.Defs.LDLFactor

/-!
# Pivot rows and the exact Gram identity

The rational residual decomposition yields a rational weighted factorization and the real factor
specified by the definition of the Cholesky factor.
-/

@[expose] public section

namespace ExplicitRIP.LDL

open Matrix

variable {v : ℕ} (G : Matrix (Fin v) (Fin v) ℚ)

/-- Membership in the pivot list is exactly the nonzero diagonal condition. -/
theorem mem_pivots_iff (k : Fin v) :
    k ∈ ldlPivots G ↔ ldlResidual G k k k ≠ 0 := by
  simp [ldlPivots]

/-- The retained pivots of a PSD matrix are positive. -/
theorem pivot_pos (hG : G.PosSemidef) (k : Fin v) (hk : k ∈ ldlPivots G) :
    0 < ldlResidual G k k k :=
  lt_of_le_of_ne (residual_posSemidef G hG k).diag_nonneg
    ((mem_pivots_iff G k).mp hk).symm

/-- The pivot list preserves the increasing elimination order. -/
theorem pivots_get_strictMono : StrictMono (ldlPivots G).get := by
  intro i j hij
  exact (List.Pairwise.filter _ (List.pairwise_lt_finRange v)).rel_get_of_lt hij

/-- Filtering a list does not affect a sum whose omitted terms vanish. -/
theorem sum_map_filter_of_eq_zero {ι A : Type*} [AddCommMonoid A]
    (p : ι → Prop) [DecidablePred p] (f : ι → A)
    (hf : ∀ i, ¬ p i → f i = 0) (l : List ι) :
    ((l.filter p).map f).sum = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : p i
    · simp [hi, ih]
    · simp [hi, ih, hf i hi]

/-- Sums of pivot contributions may be indexed by the retained pivot list. -/
theorem sum_pivots {A : Type*} [AddCommMonoid A] (f : Fin v → A)
    (hf : ∀ k : Fin v, ldlResidual G k k k = 0 → f k = 0) :
    (∑ r : Fin (ldlPivots G).length, f ((ldlPivots G).get r)) = ∑ k : Fin v, f k := by
  classical
  calc
    _ = ((ldlPivots G).map f).sum := by
      simpa only [List.get_eq_getElem] using Fin.sum_univ_fun_getElem (ldlPivots G) f
    _ = ((List.finRange v).map f).sum := by
      unfold ldlPivots
      exact sum_map_filter_of_eq_zero _ f (fun k hk => hf k (not_not.mp hk)) _
    _ = _ := (Fin.sum_univ_def f).symm

/-- The unscaled rational rows attached to retained pivots. -/
def rationalRows : Matrix (Fin (ldlPivots G).length) (Fin v) ℚ :=
  fun r x => ldlResidual G ((ldlPivots G).get r) ((ldlPivots G).get r) x

/-- The diagonal rational weights in the residual decomposition. -/
def pivotWeights : Matrix (Fin (ldlPivots G).length) (Fin (ldlPivots G).length) ℚ :=
  Matrix.diagonal fun r =>
    (ldlResidual G ((ldlPivots G).get r) ((ldlPivots G).get r) ((ldlPivots G).get r))⁻¹

/-- The residual decomposition is a weighted rational Gram factorization. -/
theorem rational_factorization (hG : G.PosSemidef) :
    (rationalRows G)ᵀ * pivotWeights G * rationalRows G = G := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [pivotWeights, Matrix.mul_diagonal, Matrix.transpose_apply, rationalRows]
  calc
    _ = ∑ r : Fin (ldlPivots G).length,
        (ldlResidual G ((ldlPivots G).get r) ((ldlPivots G).get r)
          ((ldlPivots G).get r))⁻¹ *
        ldlResidual G ((ldlPivots G).get r) ((ldlPivots G).get r) i *
        ldlResidual G ((ldlPivots G).get r) ((ldlPivots G).get r) j := by
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := (sum_pivots G _ (by intro k hk; simp only [hk, _root_.inv_zero, zero_mul])).trans
      (decomposition G hG i j)

/-- Positive square roots of the pivots give the real Cholesky factor. -/
theorem factor_transpose_mul_self (hG : G.PosSemidef) :
    (ldlFactor G)ᵀ * ldlFactor G = G.map (fun q : ℚ => (q : ℝ)) := by
  ext i j
  rw [Matrix.mul_apply]
  calc
    _ = ∑ r : Fin (ldlPivots G).length,
        (((ldlResidual G ((ldlPivots G).get r) ((ldlPivots G).get r)
          ((ldlPivots G).get r))⁻¹ *
        ldlResidual G ((ldlPivots G).get r) ((ldlPivots G).get r) i *
        ldlResidual G ((ldlPivots G).get r) ((ldlPivots G).get r) j : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro r _
      have hd : 0 ≤ (ldlResidual G ((ldlPivots G).get r) ((ldlPivots G).get r)
          ((ldlPivots G).get r) : ℝ) := by
        exact_mod_cast (pivot_pos G hG _ (List.get_mem _ _)).le
      simp only [Matrix.transpose_apply, ldlFactor]
      rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hd]
      simp only [Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv]
      ring
    _ = G.map (fun q : ℚ => (q : ℝ)) i j := by
      rw [← Rat.cast_sum]
      congr 1
      exact (sum_pivots G _ (by intro k hk; simp only [hk, _root_.inv_zero, zero_mul])).trans
        (decomposition G hG i j)

end ExplicitRIP.LDL
