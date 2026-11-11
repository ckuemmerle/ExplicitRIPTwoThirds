/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.OpNorm
public import ExplicitRIP.Frozen.Defs.OneToOneNorm
import ExplicitRIP.Provider.GershgorinBound

/-!
# The Gershgorin estimate of [KM, Section 2.1]

Source: [KM, Section 2.1, the Gershgorin bound before (5)].
-/

public section

open scoped Matrix

/-- If the complex matrix `M` is self-adjoint, Gershgorin's circle theorem bounds its spectral
norm by its induced `1`-norm: `‖M‖_{2→2} ≤ ‖M‖_{1→1}`. This is the unnumbered matrix-norm
bound before [KM, (5)]. -/
theorem ExplicitRIP.gershgorin_bound :
    ∀ {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ), M.IsHermitian →
      ExplicitRIP.opNorm M ≤ ExplicitRIP.oneToOneNorm M :=
by exact ExplicitRIP.Provider.gershgorin_bound
