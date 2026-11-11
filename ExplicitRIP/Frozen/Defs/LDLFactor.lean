/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.LDLResidual
public import ExplicitRIP.Frozen.Defs.LDLPivots

/-!
# The real factor from exact LDLᵀ elimination

Source: [KM, proof of Theorem 1, footnote 4].

This factor implements the Cholesky construction of [KM, footnote 4] by rational symmetric
elimination followed by positive real square roots.
-/

@[expose] public section

open scoped Matrix

/-- The real matrix `B` produced by exact rational `LDLᵀ` elimination, with zero pivots omitted.
Row `r` corresponds to the `r`-th nonzero pivot `k = (ldlPivots G)[r]` and is
`x ↦ R_k(k, x) / √d_k`, with `R_k = ldlResidual G k` and `d_k = R_k(k, k)`, using `Real.sqrt`,
the positive square root. For positive semidefinite `G`, each retained pivot is positive, this row
is `√d_k` times the transpose of the `k`-th column of the unit lower-triangular `LDLᵀ` factor, and
`Bᵀ B = G`, the Cholesky factor of [KM, footnote 4]; see `ExplicitRIP.ldl_factorization`. For other
inputs this is only a total formula (square roots of negative numbers and division by zero are
`0`). -/
noncomputable def ExplicitRIP.ldlFactor {v : ℕ} (G : Matrix (Fin v) (Fin v) ℚ) :
    Matrix (Fin (ExplicitRIP.ldlPivots G).length) (Fin v) ℝ :=
  fun r x =>
    (((ExplicitRIP.ldlResidual G ((ExplicitRIP.ldlPivots G).get r) ((ExplicitRIP.ldlPivots G).get r)
        x : ℚ) : ℝ)) /
      Real.sqrt (((ExplicitRIP.ldlResidual G ((ExplicitRIP.ldlPivots G).get r)
        ((ExplicitRIP.ldlPivots G).get r) ((ExplicitRIP.ldlPivots G).get r) : ℚ) : ℝ))
