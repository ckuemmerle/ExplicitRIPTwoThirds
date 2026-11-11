/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.LDLResidual
public import ExplicitRIP.Frozen.Defs.LDLPivots
public import ExplicitRIP.Frozen.Defs.LDLFactor
import ExplicitRIP.Provider.LDLFactorization

/-!
# Exact LDLᵀ factorization of a positive semidefinite matrix

Source: [KM, proof of Theorem 1, footnote 4].

Exact rational symmetric elimination followed by positive real square roots realizes the
Cholesky factor described in [KM, footnote 4]. Rows corresponding to zero pivots are omitted.
-/

public section

open scoped Matrix

/-- The factorization used in [KM, footnote 4]. For a positive semidefinite rational matrix `G`,
every retained pivot of exact rational symmetric (`LDLᵀ`) elimination is positive, the
number of retained pivots is `rank G`, and the real matrix `B` built from them satisfies
`Bᵀ B = G`. Zero pivots of a positive semidefinite residual have zero rows and columns, so
omitting them is unambiguous. -/
theorem ExplicitRIP.ldl_factorization :
    ∀ (v : ℕ) (G : Matrix (Fin v) (Fin v) ℚ), G.PosSemidef →
      (∀ k ∈ ExplicitRIP.ldlPivots G, 0 < ExplicitRIP.ldlResidual G k k k) ∧
        (ExplicitRIP.ldlPivots G).length = G.rank ∧
        (ExplicitRIP.ldlFactor G)ᵀ * ExplicitRIP.ldlFactor G = G.map (fun q : ℚ => (q : ℝ)) :=
by exact ExplicitRIP.Provider.ldl_factorization
