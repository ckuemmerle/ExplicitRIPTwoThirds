/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.FieldNorm
import ExplicitRIP.Provider.FieldNormSpec

/-!
# The field norm on affine lines

Source: [KM, Section 4.2, the claim before (15), and footnote 3].

The field `𝔽_{p³}` is realized by adjoining a root of the first monic irreducible cubic in the
coefficient order of [KM, footnote 3]. Its power basis identifies it with `𝔽_p³`.
-/

public section

open scoped Matrix

/-- For every prime `p`, `𝔽_p[θ] = AdjoinRoot (firstIrreducibleCubic p)` is a field with power
basis `1, θ, θ²`, giving the identification of `𝔽_p³` with `𝔽_{p³}` in [KM, footnote 3]. The
field norm `N` is a homogeneous cubic form `F` over `𝔽_p` such that, for all `c, v ∈ 𝔽_p³`,
the coefficient of `s³` in `N(c + s v) = F(c + s v)` is `N(v)`; moreover `N(v) ≠ 0` for
`v ≠ 0`, as used just before [KM, (15)]. -/
theorem ExplicitRIP.fieldNorm_spec :
    ∀ (p : ℕ) [Fact p.Prime],
      IsField (AdjoinRoot (ExplicitRIP.firstIrreducibleCubic p)) ∧
      (∃ b : Module.Basis (Fin 3) (ZMod p) (AdjoinRoot (ExplicitRIP.firstIrreducibleCubic p)),
        ∀ i : Fin 3, b i = AdjoinRoot.root (ExplicitRIP.firstIrreducibleCubic p) ^ (i : ℕ)) ∧
      (∃ F : MvPolynomial (Fin 3) (ZMod p),
        F.IsHomogeneous 3 ∧
          (∀ w : ZMod p × ZMod p × ZMod p,
            MvPolynomial.eval ![w.1, w.2.1, w.2.2] F = ExplicitRIP.fieldNorm p w) ∧
          ∀ c v : ZMod p × ZMod p × ZMod p,
            (MvPolynomial.aeval ![Polynomial.C c.1 + Polynomial.C v.1 * Polynomial.X,
                Polynomial.C c.2.1 + Polynomial.C v.2.1 * Polynomial.X,
                Polynomial.C c.2.2 + Polynomial.C v.2.2 * Polynomial.X] F).coeff 3 =
              ExplicitRIP.fieldNorm p v) ∧
      ∀ v : ZMod p × ZMod p × ZMod p, v ≠ 0 → ExplicitRIP.fieldNorm p v ≠ 0 :=
by exact ExplicitRIP.Provider.fieldNorm_spec
