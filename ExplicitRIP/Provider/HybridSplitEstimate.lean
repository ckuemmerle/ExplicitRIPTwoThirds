/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.HybridSplit.Basic
public import ExplicitRIP.Frozen.Defs.DRNorm
import ExplicitRIP.Analysis.LevDR.RectangleBound
import ExplicitRIP.Frozen.LevDRBound

/-!
# Proof of [KM, (6)]: the hybrid estimate

Source: [KM, Section 2.2, (6)].

The triangle inequality combines the logarithmic discrete Rayleigh estimate for large entries
with the Hermitian Gershgorin estimate for small entries. For a principal Gram submatrix
`M = X + Y`, with `X` above the threshold and `Y` at or below it, this gives
`‖M‖_{2→2} ≤ ‖X‖_{2→2} + ‖Y‖_{2→2} ≲ log(2k) ‖X‖_DR + ‖Y‖_{1→1}`.
-/

public section

open scoped Matrix

/-- The large-entry and small-entry pieces satisfy the hybrid operator norm estimate. -/
theorem ExplicitRIP.Provider.hybrid_split_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (Φ : Matrix m n ℂ)
      (τ : ℝ) (k : ℕ) (S : Finset n), S.card = k →
        let M : Matrix S S ℂ :=
          (Φᴴ * Φ - 1).submatrix (Subtype.val : S → n) (Subtype.val : S → n)
        let Y : Matrix S S ℂ := Matrix.of fun i j => if τ < ‖M i j‖ then 0 else M i j
        let X : Matrix S S ℂ := M - Y
        ExplicitRIP.opNorm M ≤ ExplicitRIP.opNorm X + ExplicitRIP.opNorm Y ∧
          ExplicitRIP.opNorm X + ExplicitRIP.opNorm Y ≤
            C * (Real.log (2 * k) * ExplicitRIP.drNorm X + ExplicitRIP.oneToOneNorm Y) := by
  obtain ⟨C₀, hC₀, hLev⟩ := ExplicitRIP.lev_dr_bound
  refine ⟨max C₀ 1, lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro m n _ _ _ Φ τ k S hS
  let M : Matrix S S ℂ :=
    (Φᴴ * Φ - 1).submatrix (Subtype.val : S → n) (Subtype.val : S → n)
  let Y : Matrix S S ℂ := Matrix.of fun i j ↦ if τ < ‖M i j‖ then 0 else M i j
  let X : Matrix S S ℂ := M - Y
  change ExplicitRIP.opNorm M ≤ ExplicitRIP.opNorm X + ExplicitRIP.opNorm Y ∧
    ExplicitRIP.opNorm X + ExplicitRIP.opNorm Y ≤
      max C₀ 1 * (Real.log (2 * k) * ExplicitRIP.drNorm X + ExplicitRIP.oneToOneNorm Y)
  have hM : M.IsHermitian :=
    ((Matrix.isHermitian_conjTranspose_mul_self Φ).sub Matrix.isHermitian_one).submatrix _
  have hY : Y.IsHermitian := ExplicitRIP.Hybrid.isHermitian_threshold hM τ
  have hcard : Fintype.card S = k := (Fintype.card_coe S).trans hS
  have hXbound := hLev S X
  rw [hcard] at hXbound
  have hYbound := ExplicitRIP.Gersh.opNorm_le_oneToOneNorm_of_isHermitian hY
  have hlog : 0 ≤ Real.log (2 * (k : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using Real.log_natCast_nonneg (2 * k)
  have hXterm : 0 ≤ Real.log (2 * (k : ℝ)) * ExplicitRIP.drNorm X :=
    mul_nonneg hlog (ExplicitRIP.Lev.dr_norm_nonneg X)
  have hYterm : 0 ≤ ExplicitRIP.oneToOneNorm Y :=
    ExplicitRIP.Gersh.oneToOneNorm_nonneg Y
  constructor
  · calc
      ExplicitRIP.opNorm M = ExplicitRIP.opNorm (X + Y) := by
        rw [show X + Y = M from sub_add_cancel M Y]
      _ ≤ ExplicitRIP.opNorm X + ExplicitRIP.opNorm Y :=
        ExplicitRIP.Hybrid.opNorm_add_le X Y
  · calc
      ExplicitRIP.opNorm X + ExplicitRIP.opNorm Y ≤
          C₀ * Real.log (2 * (k : ℝ)) * ExplicitRIP.drNorm X + ExplicitRIP.oneToOneNorm Y :=
        add_le_add hXbound hYbound
      _ = C₀ * (Real.log (2 * (k : ℝ)) * ExplicitRIP.drNorm X) +
          1 * ExplicitRIP.oneToOneNorm Y := by rw [mul_assoc, one_mul]
      _ ≤ max C₀ 1 * (Real.log (2 * (k : ℝ)) * ExplicitRIP.drNorm X) +
          max C₀ 1 * ExplicitRIP.oneToOneNorm Y :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hXterm)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hYterm)
      _ = max C₀ 1 * (Real.log (2 * (k : ℝ)) * ExplicitRIP.drNorm X +
          ExplicitRIP.oneToOneNorm Y) := (mul_add _ _ _).symm
