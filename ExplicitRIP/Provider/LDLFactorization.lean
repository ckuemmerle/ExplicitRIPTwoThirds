/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.LinearAlgebra.LDL.Rank

/-!
# Exact semidefinite LDLᵀ factorization

Source: [KM, proof of Theorem 1, footnote 4].

Residual positivity, the rational rank calculation, and the real Gram identity justify omission
of zero pivots and the resulting real factor. For positive semidefinite rational `G`, every
retained pivot is positive, their number is `rank G`, and the factor satisfies `Bᵀ B = G`. This
realizes the Cholesky factor in [KM, footnote 4] by exact rational LDLᵀ elimination followed by
positive real square roots.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.ldl_factorization :
    ∀ (v : ℕ) (G : Matrix (Fin v) (Fin v) ℚ), G.PosSemidef →
      (∀ k ∈ ExplicitRIP.ldlPivots G, 0 < ExplicitRIP.ldlResidual G k k k) ∧
        (ExplicitRIP.ldlPivots G).length = G.rank ∧
        (ExplicitRIP.ldlFactor G)ᵀ * ExplicitRIP.ldlFactor G = G.map (fun q : ℚ => (q : ℝ)) :=
by
  intro v G hG
  exact ⟨fun k hk => ExplicitRIP.LDL.pivot_pos G hG k hk,
    ExplicitRIP.LDL.pivots_length_eq_rank G hG,
    ExplicitRIP.LDL.factor_transpose_mul_self G hG⟩
