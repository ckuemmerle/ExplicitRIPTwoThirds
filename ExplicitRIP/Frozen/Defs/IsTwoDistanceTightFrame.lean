/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Two-distance tight frames

Source: [KM, Section 3, conditions (a)–(c)].
-/

@[expose] public section

open scoped Matrix

/-- A two-distance tight frame as defined in [KM, Section 3]: a matrix `F ∈ ℝ^{m × N}` for which
there exist `a, b, c ∈ ℝ` with `a ≠ b` such that (a) the diagonal entries of `Fᵀ F` all
equal `1`, (b) its off-diagonal entries all lie in `{a, b}`, and (c) `F Fᵀ = c I`. -/
def ExplicitRIP.IsTwoDistanceTightFrame {m N : Type*} [Fintype m] [Fintype N] [DecidableEq m]
    (F : Matrix m N ℝ) : Prop :=
  ∃ a b c : ℝ, a ≠ b ∧ (∀ j, (Fᵀ * F) j j = 1) ∧
    (∀ i j, i ≠ j → (Fᵀ * F) i j = a ∨ (Fᵀ * F) i j = b) ∧
    F * Fᵀ = c • (1 : Matrix m m ℝ)
