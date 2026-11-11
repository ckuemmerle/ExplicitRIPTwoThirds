/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.OpNorm
public import ExplicitRIP.Frozen.Defs.DRNorm
import ExplicitRIP.Provider.LevDRBound

/-!
# [KM, (5)]: the logarithmic discrete Rayleigh bound

Source: [KM, Section 2.1, (5)].
-/

public section

open scoped Matrix

/-- [KM, (5)], attributed there to Lev, Theorem 2, and proved here. There is an absolute
constant `C` such that every complex matrix `M` indexed by a finite set of size `k`
satisfies `‖M‖_{2→2} ≤ C log(2k) ‖M‖_DR`. -/
theorem ExplicitRIP.lev_dr_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ),
      ExplicitRIP.opNorm M ≤ C * Real.log (2 * Fintype.card ι) * ExplicitRIP.drNorm M :=
by exact ExplicitRIP.Provider.lev_dr_bound
