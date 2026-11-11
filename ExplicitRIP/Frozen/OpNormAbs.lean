/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.OpNorm
import ExplicitRIP.Provider.OpNormAbs

/-!
# The spectral-norm comparison of [KM, Section 2.3]

Source: [KM, Section 2.3, the opening spectral-norm comparison].
-/

public section

open scoped Matrix

/-- Taking the entrywise absolute value of a matrix does not decrease its spectral norm:
`‖M‖_{2→2} ≤ ‖|M|‖_{2→2}` for every real or complex matrix `M`. This is the opening claim of
[KM, Section 2.3]. -/
theorem ExplicitRIP.opNorm_le_opNorm_abs :
    ∀ {𝕜 : Type} [RCLike 𝕜] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
      (M : Matrix m n 𝕜),
      ExplicitRIP.opNorm M ≤ ExplicitRIP.opNorm (M.map fun z => ‖z‖) :=
by exact ExplicitRIP.Provider.opNorm_le_opNorm_abs
