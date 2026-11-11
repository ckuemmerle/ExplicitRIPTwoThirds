/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.DRNorm
import ExplicitRIP.Provider.AbsoluteRayleigh

/-!
# [KM, (7)]: entrywise absolute values and the discrete Rayleigh norm

Source: [KM, Section 2.2, (7)].

The inequality is stated for every square matrix. In [KM, Section 2.2], it is applied to the
part above a threshold of a principal submatrix of `Φ^* Φ - I`.
-/

public section

open scoped Matrix

/-- For every square real or complex matrix `M`, `‖M‖_DR ≤ ‖|M|‖_DR`, where absolute values are
taken entrywise. This is [KM, (7)], applied there to the large-entry part `X` of a Gram
submatrix. -/
theorem ExplicitRIP.drNorm_le_drNorm_abs :
    ∀ {𝕜 : Type} [RCLike 𝕜] (ι : Type) [Fintype ι] (M : Matrix ι ι 𝕜),
      ExplicitRIP.drNorm M ≤ ExplicitRIP.drNorm (M.map fun z => ‖z‖) :=
by exact ExplicitRIP.Provider.drNorm_le_drNorm_abs
