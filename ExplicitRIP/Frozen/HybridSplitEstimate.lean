/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.OpNorm
public import ExplicitRIP.Frozen.Defs.DRNorm
public import ExplicitRIP.Frozen.Defs.OneToOneNorm
import ExplicitRIP.Provider.HybridSplitEstimate

/-!
# [KM, (6)]: splitting large and small Gram entries

Source: [KM, Section 2.2, (6)].
-/

public section

open scoped Matrix

/-- [KM, (6)]. There is an absolute constant `C` such that for every `k × k` principal submatrix
`M` of `Φ^* Φ - I` and threshold `τ`, if `Y` is obtained from `M` by zeroing the entries of
modulus above `τ` and `X = M - Y`, then
`‖M‖_{2→2} ≤ ‖X‖_{2→2} + ‖Y‖_{2→2} ≤ C (log(2k) ‖X‖_DR + ‖Y‖_{1→1})`. -/
theorem ExplicitRIP.hybrid_split_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (Φ : Matrix m n ℂ)
      (τ : ℝ) (k : ℕ) (S : Finset n), S.card = k →
        let M : Matrix S S ℂ :=
          (Φᴴ * Φ - 1).submatrix (Subtype.val : S → n) (Subtype.val : S → n)
        let Y : Matrix S S ℂ := Matrix.of fun i j => if τ < ‖M i j‖ then 0 else M i j
        let X : Matrix S S ℂ := M - Y
        ExplicitRIP.opNorm M ≤ ExplicitRIP.opNorm X + ExplicitRIP.opNorm Y ∧
          ExplicitRIP.opNorm X + ExplicitRIP.opNorm Y ≤
            C * (Real.log (2 * k) * ExplicitRIP.drNorm X + ExplicitRIP.oneToOneNorm Y) :=
by exact ExplicitRIP.Provider.hybrid_split_estimate
