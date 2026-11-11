/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs

/-!
# Guth–Zahl line route: definitions for the trapping branch

Directional derivatives are encoded as polynomials in direction variables with
polynomial coefficients in the base point. Iterating the derivative gives the
direction jets used in the trapping recurrence.

* `DirectionPoly`
* `directionDeriv`
* `directionJet`
* `evalDirection`
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- Outer variables are the three direction coordinates; coefficients depend on x. -/
abbrev DirectionPoly (K : Type*) [Field K] := MvPolynomial (Fin 3) (Poly K)

open Classical in
/-- Differentiate only the coefficients in x, then multiply by the direction. -/
noncomputable def directionDeriv {K : Type*} [Field K]
    (H : DirectionPoly K) : DirectionPoly K :=
  ∑ i : Fin 3, MvPolynomial.X i *
    ∑ a ∈ H.support, MvPolynomial.monomial a (MvPolynomial.pderiv i (H.coeff a))

open Classical in
noncomputable def directionJet {K : Type*} [Field K] (f : Poly K) :
    ℕ → DirectionPoly K
  | 0 => MvPolynomial.C f
  | j + 1 => directionDeriv (directionJet f j)

open Classical in
noncomputable def evalDirection {K : Type*} [Field K]
    (H : DirectionPoly K) (x v : Point K) : K :=
  MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval x) H)

end ExplicitRIP.GuthZahl

end
