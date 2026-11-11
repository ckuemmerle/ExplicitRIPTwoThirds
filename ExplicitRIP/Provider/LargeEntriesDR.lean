/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.LargeEntries.Bounds

/-!
# Proof of [KM, (8)]: large Gram entries and their support

Source: [KM, Section 2.2, (8)].

Support domination and the coherence envelope bound the discrete Rayleigh norm of the
large-entry part of a threshold decomposition. For unit-norm columns, the large-entry matrix `X`
and its support indicator `A` satisfy `‖|X|‖_DR ≤ ‖X‖_max ‖A‖_DR` and `‖X‖_max ≤ μ`.
-/

public section

open scoped Matrix

/-- Large-entry support domination and its coherence envelope. -/
theorem ExplicitRIP.Provider.large_entries_dr_bound :
    ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (Φ : Matrix m n ℂ),
      (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) → ∀ (τ : ℝ) (S : Finset n),
        let M : Matrix S S ℂ := (Φᴴ * Φ - 1).submatrix (Subtype.val : S → n) (Subtype.val : S → n)
        let X : Matrix S S ℂ := Matrix.of fun i j => if τ < ‖M i j‖ then M i j else 0
        let A : Matrix S S ℝ := Matrix.of fun i j => if X i j = 0 then 0 else 1
        ExplicitRIP.drNorm (X.map fun z => ‖z‖) ≤
            (⨆ ij : S × S, ‖X ij.1 ij.2‖) * ExplicitRIP.drNorm A ∧
          (⨆ ij : S × S, ‖X ij.1 ij.2‖) ≤ ExplicitRIP.coherence Φ := by
  intro m n _ _ _ Φ hΦ τ S
  dsimp only
  exact ⟨ExplicitRIP.Large.drNorm_abs_le_max_mul_support _,
    ExplicitRIP.Large.threshold_max_le_coherence Φ hΦ τ S⟩
