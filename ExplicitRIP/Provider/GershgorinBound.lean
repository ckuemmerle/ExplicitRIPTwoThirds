/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.Gershgorin.HermitianBound

/-!
# The Gershgorin bound for a self-adjoint matrix

Source: [KM, Section 2.1, the Gershgorin bound before (5)].

The Euclidean operator norm of a complex Hermitian matrix is bounded by its maximal absolute
column sum: `‖M‖_{2→2} ≤ ‖M‖_{1→1}`.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.gershgorin_bound :
    ∀ {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ), M.IsHermitian →
      ExplicitRIP.opNorm M ≤ ExplicitRIP.oneToOneNorm M := by
  intro n _ _ M hM
  exact ExplicitRIP.Gersh.opNorm_le_oneToOneNorm_of_isHermitian hM
