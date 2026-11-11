/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.DRNorm

/-!
# The discrete Rayleigh parameter of Gram submatrices

Source: [KM, Lemma 2].
-/

@[expose] public section

open scoped Matrix

/-- The parameter `ρ_k(Φ) = max_{∅ ≠ S ⊆ [n], |S| ≤ k} ‖Φ_S^* Φ_S - I‖_DR` of [KM, Lemma 2],
where `Φ_S` consists of the columns of `Φ` indexed by `S`. It is `0` when there is no such
`S`. -/
noncomputable def ExplicitRIP.rhoConstant {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] (Φ : Matrix m n 𝕜) (k : ℕ) : ℝ :=
  ⨆ S : {S : Finset n // S.Nonempty ∧ S.card ≤ k},
    ExplicitRIP.drNorm ((Φ.submatrix id (Subtype.val : S.1 → n))ᴴ *
      Φ.submatrix id (Subtype.val : S.1 → n) - 1)
