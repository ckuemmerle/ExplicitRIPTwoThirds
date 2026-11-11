/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.FlatRIP.Comparison

/-!
# Proof of Lemma 2 of [KM]: flat and discrete Rayleigh parameters

Source: [KM, Lemma 2].

The finite-cut estimate in [KM, Lemma 2] includes every support of size at most `2k`. For
unit-norm complex columns, it gives `θ_k(Φ) ≤ ρ_{2k}(Φ) ≤ 2 θ_k(Φ)`.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.flat_rip_dr :
    ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (Φ : Matrix m n ℂ),
      (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) → ∀ k : ℕ,
        ExplicitRIP.flatConstant Φ k ≤ ExplicitRIP.rhoConstant Φ (2 * k) ∧
          ExplicitRIP.rhoConstant Φ (2 * k) ≤ 2 * ExplicitRIP.flatConstant Φ k := by
  intro m n _ _ _ Φ hΦ k
  exact ⟨ExplicitRIP.Flat.flatConstant_le_rhoConstant Φ k,
    ExplicitRIP.Flat.rhoConstant_le_two_mul_flatConstant Φ hΦ k⟩
