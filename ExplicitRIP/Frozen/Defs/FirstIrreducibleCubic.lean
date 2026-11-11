/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# The first monic irreducible cubic in lexicographic order

Source: [KM, Section 4.2, footnote 3].

The coefficient order is that of [KM, footnote 3]; adjoining a root of this cubic gives the
power-basis identification of `𝔽_p³` with `𝔽_{p³}`.
-/

@[expose] public section

open scoped Matrix

/-- The first monic irreducible cubic over `𝔽_p` in lexicographic order, as in [KM, footnote 3].
Among the cubics `X³ + c₂ X² + c₁ X + c₀` with `(c₂, c₁, c₀) ∈ {0, …, p - 1}³`, ordered
lexicographically, that is, by the base-`p` number `n = c₂ p² + c₁ p + c₀`, it is the first
one irreducible over `ZMod p`. The search is literal; its fallback value `X³` is unreachable
for every prime `p`, and the result is the lexicographically least monic irreducible cubic,
by the frozen statement `ExplicitRIP.firstIrreducibleCubic_spec`. -/
noncomputable def ExplicitRIP.firstIrreducibleCubic (p : ℕ) [Fact p.Prime] : Polynomial (ZMod p) :=
  open Classical in
  let cubic : ℕ → Polynomial (ZMod p) := fun n =>
    Polynomial.X ^ 3 + Polynomial.C ((n / p ^ 2 : ℕ) : ZMod p) * Polynomial.X ^ 2 +
      Polynomial.C ((n / p % p : ℕ) : ZMod p) * Polynomial.X + Polynomial.C ((n % p : ℕ) : ZMod p)
  match (List.range (p ^ 3)).find? (fun n => decide (Irreducible (cubic n))) with
  | some n => cubic n
  | none => Polynomial.X ^ 3
