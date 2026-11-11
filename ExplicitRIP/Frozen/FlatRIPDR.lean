/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.FlatConstant
public import ExplicitRIP.Frozen.Defs.RhoConstant
import ExplicitRIP.Provider.FlatRIPDR

/-!
# Lemma 2 of [KM]: flat RIP and the discrete Rayleigh norm

Source: [KM, Lemma 2].
-/

public section

open scoped Matrix

/-- [KM, Lemma 2]. If `Φ ∈ ℂ^{m×n}` has unit-norm columns, then `θ_k(Φ) ≤ ρ_{2k}(Φ) ≤ 2 θ_k(Φ)`. -/
theorem ExplicitRIP.flat_rip_dr :
    ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (Φ : Matrix m n ℂ),
      (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) → ∀ k : ℕ,
        ExplicitRIP.flatConstant Φ k ≤ ExplicitRIP.rhoConstant Φ (2 * k) ∧
          ExplicitRIP.rhoConstant Φ (2 * k) ≤ 2 * ExplicitRIP.flatConstant Φ k :=
by exact ExplicitRIP.Provider.flat_rip_dr
