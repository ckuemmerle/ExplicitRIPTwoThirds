/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.FirstIrreducibleCubic

/-!
# The field norm

Source: [KM, Section 4.2, footnote 3].

As in [KM, footnote 3], `(u, v, w) ∈ 𝔽_p³` is identified with `u + vX + wX²` in `𝔽_p[X]/(f)`,
where `f` is the lexicographically first monic irreducible cubic.
-/

@[expose] public section

open scoped Matrix

/-- The field norm `N : 𝔽_p³ → 𝔽_p` of [KM, Section 4.2]. With `f = firstIrreducibleCubic p` and
`θ` the root of `f` in `AdjoinRoot f = 𝔽_p[θ] = 𝔽_{p³}`, the power basis `1, θ, θ²`
identifies `𝔽_{p³}` with `𝔽_p³` as in [KM, footnote 3], and
`N(w₀, w₁, w₂) = N_{𝔽_{p³}/𝔽_p}(w₀ + w₁ θ + w₂ θ²)`. -/
noncomputable def ExplicitRIP.fieldNorm (p : ℕ) [Fact p.Prime] (w : ZMod p × ZMod p × ZMod p) :
    ZMod p :=
  Algebra.norm (ZMod p)
    (AdjoinRoot.of (ExplicitRIP.firstIrreducibleCubic p) w.1 +
      AdjoinRoot.of (ExplicitRIP.firstIrreducibleCubic p) w.2.1 *
        AdjoinRoot.root (ExplicitRIP.firstIrreducibleCubic p) +
      AdjoinRoot.of (ExplicitRIP.firstIrreducibleCubic p) w.2.2 *
        AdjoinRoot.root (ExplicitRIP.firstIrreducibleCubic p) ^ 2)
