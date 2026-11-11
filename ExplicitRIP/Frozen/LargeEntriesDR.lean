/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.DRNorm
public import ExplicitRIP.Frozen.Defs.Coherence
import ExplicitRIP.Provider.LargeEntriesDR

/-!
# [KM, (8)]: controlling large Gram entries by their support

Source: [KM, Section 2.2, (8)].
-/

public section

open scoped Matrix

/-- [KM, (8)]. For `Φ` with unit-norm columns, a support `S`, `M = (Φ^* Φ - I)[S]`, a threshold
`τ`, the part `X` of `M` above the threshold and its support indicator `A`,
`‖|X|‖_DR ≤ ‖X‖_max ‖A‖_DR` and `‖X‖_max ≤ μ`. -/
theorem ExplicitRIP.large_entries_dr_bound :
    ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (Φ : Matrix m n ℂ),
      (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) → ∀ (τ : ℝ) (S : Finset n),
        let M : Matrix S S ℂ := (Φᴴ * Φ - 1).submatrix (Subtype.val : S → n) (Subtype.val : S → n)
        let X : Matrix S S ℂ := Matrix.of fun i j => if τ < ‖M i j‖ then M i j else 0
        let A : Matrix S S ℝ := Matrix.of fun i j => if X i j = 0 then 0 else 1
        ExplicitRIP.drNorm (X.map fun z => ‖z‖) ≤
            (⨆ ij : S × S, ‖X ij.1 ij.2‖) * ExplicitRIP.drNorm A ∧
          (⨆ ij : S × S, ‖X ij.1 ij.2‖) ≤ ExplicitRIP.coherence Φ :=
by exact ExplicitRIP.Provider.large_entries_dr_bound
