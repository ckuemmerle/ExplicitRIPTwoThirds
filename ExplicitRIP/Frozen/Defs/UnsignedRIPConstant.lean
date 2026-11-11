/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.OpNorm

/-!
# The unsigned restricted isometry constant

Source: [KM, Section 2.3, the definition of Δ_k before Theorem 4].
-/

@[expose] public section

open scoped Matrix

/-- The parameter `Δ_k(Φ) = max_{|S| ≤ k} ‖H[S]‖_op` with `H = |Φ^* Φ - I|`, using entrywise
absolute values, defined before [KM, Theorem 4]. Here `H[S]` is the principal submatrix of
`H` indexed by `S`. -/
noncomputable def ExplicitRIP.unsignedRIPConstant {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] (Φ : Matrix m n 𝕜) (k : ℕ) : ℝ :=
  ⨆ S : {S : Finset n // S.card ≤ k},
    ExplicitRIP.opNorm (((Φᴴ * Φ - 1).map fun z => ‖z‖).submatrix
      (Subtype.val : S.1 → n) (Subtype.val : S.1 → n))
