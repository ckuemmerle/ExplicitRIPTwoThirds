/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.OpNorm
public import ExplicitRIP.Analysis.Gershgorin.HermitianBound

/-!
# Hermitian threshold decompositions

Entrywise modulus thresholds preserve Hermitian symmetry because transposed entries have equal
moduli.

Source: [KM, Section 2.2, (6)].
-/

public section

open scoped Matrix

namespace ExplicitRIP.Hybrid

/-- The Euclidean operator norm satisfies the triangle inequality. -/
theorem opNorm_add_le {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A B : Matrix m n 𝕜) :
    ExplicitRIP.opNorm (A + B) ≤ ExplicitRIP.opNorm A + ExplicitRIP.opNorm B := by
  simp only [ExplicitRIP.opNorm, map_add]
  exact norm_add_le _ _

/-- Zeroing entries above a modulus threshold preserves Hermitian symmetry. -/
theorem isHermitian_threshold {q : Type*} {M : Matrix q q ℂ}
    (hM : M.IsHermitian) (τ : ℝ) :
    (Matrix.of fun i j ↦ if τ < ‖M i j‖ then 0 else M i j).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star (if τ < ‖M j i‖ then 0 else M j i) =
    if τ < ‖M i j‖ then 0 else M i j
  rw [← ExplicitRIP.Gersh.norm_apply_eq_norm_transpose hM i j]
  by_cases h : τ < ‖M i j‖
  · simp only [ite_eq_left h, star_zero]
  · simp only [ite_eq_right h, hM.apply i j]

/-- The complementary large-entry piece is Hermitian as well. -/
theorem isHermitian_threshold_complement {q : Type*} {M : Matrix q q ℂ}
    (hM : M.IsHermitian) (τ : ℝ) :
    (M - Matrix.of fun i j ↦ if τ < ‖M i j‖ then 0 else M i j).IsHermitian :=
  hM.sub (isHermitian_threshold hM τ)

end ExplicitRIP.Hybrid
