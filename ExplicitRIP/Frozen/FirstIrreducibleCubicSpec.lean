/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.FirstIrreducibleCubic
import ExplicitRIP.Provider.FirstIrreducibleCubicSpec

/-!
# The first monic irreducible cubic: specification

Source: [KM, Section 4.2, footnote 3].
-/

public section

open scoped Matrix

/-- Specification of the identification of `𝔽_p³` with `𝔽_{p³}` in [KM, footnote 3]. For every
prime `p`, `firstIrreducibleCubic p` is a monic cubic `X³ + c₂X² + c₁X + c₀` that is
irreducible over `𝔽_p`, and every monic cubic whose coefficient triple `(d₂, d₁, d₀)`
precedes `(c₂, c₁, c₀)` lexicographically, with `𝔽_p = {0, …, p - 1}`, is reducible. -/
theorem ExplicitRIP.firstIrreducibleCubic_spec :
    ∀ (p : ℕ) [Fact p.Prime], ∃ c₂ c₁ c₀ : ZMod p,
      ExplicitRIP.firstIrreducibleCubic p =
          Polynomial.X ^ 3 + Polynomial.C c₂ * Polynomial.X ^ 2 + Polynomial.C c₁ * Polynomial.X +
            Polynomial.C c₀ ∧
        Irreducible (ExplicitRIP.firstIrreducibleCubic p) ∧
        ∀ d₂ d₁ d₀ : ZMod p,
          (d₂.val < c₂.val ∨ d₂.val = c₂.val ∧
              (d₁.val < c₁.val ∨ d₁.val = c₁.val ∧ d₀.val < c₀.val)) →
          ¬ Irreducible (Polynomial.X ^ 3 + Polynomial.C d₂ * Polynomial.X ^ 2 +
            Polynomial.C d₁ * Polynomial.X + Polynomial.C d₀) :=
by exact ExplicitRIP.Provider.firstIrreducibleCubic_spec
