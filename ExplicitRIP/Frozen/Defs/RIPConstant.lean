/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.OpNorm

/-!
# The restricted isometry constant

Source: [KM, Section 1, the definition of δ_k before (1)].
-/

@[expose] public section

open scoped Matrix

/-- The restricted isometry constant `δ_k(Φ) = max_{|S| ≤ k} ‖Φ_S^* Φ_S - I‖_{2→2}` defined
before [KM, (1)], where `Φ_S` is the submatrix of `Φ` whose columns are indexed by `S`. -/
noncomputable def ExplicitRIP.ripConstant {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] (Φ : Matrix m n 𝕜) (k : ℕ) : ℝ :=
  ⨆ S : {S : Finset n // S.card ≤ k},
    ExplicitRIP.opNorm ((Φ.submatrix id (Subtype.val : S.1 → n))ᴴ *
      Φ.submatrix id (Subtype.val : S.1 → n) - 1)
