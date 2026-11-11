/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs
public import ExplicitRIP.Zahl.Defs

/-!
# Guth–Zahl line route: definitions for the boundary branch

This branch transports the structure theorem from affine lines over an algebraic closure
to normalized chart lines over the base field, descending the plane and split-quadric alternatives.
Chart lines have a fixed origin and direction in affine three-space. The maps
and polynomial restrictions below relate that chart to the affine-line carrier
and transport its finite families along field embeddings.

* `chartOrigin`
* `chartDirection`
* `chartLift`
* `chartFamily`
* `chartRestriction`
* `planePolynomial`
* `mapChart`
* `mapPoint`
* `mapChartFamily`
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl
open ExplicitRIP.Zahl (ChartLine)

open Classical in
def chartOrigin {K : Type*} [Field K] (l : ChartLine K) : Point K := ![0, l.s, l.t]

open Classical in
def chartDirection {K : Type*} [Field K] (l : ChartLine K) : Point K := ![1, l.u, l.v]

open Classical in
/-- The one-dimensional affine subspace with the chart line's origin and direction. -/
noncomputable def chartLift {K : Type*} [Field K] (l : ChartLine K) : Line K :=
  ⟨AffineSubspace.mk' (chartOrigin l) (Submodule.span K {chartDirection l}), by
    rw [AffineSubspace.direction_mk']
    apply finrank_span_singleton
    intro h
    have hh := congrArg (fun v : Point K => v 0) h
    simp [chartDirection] at hh⟩

open Classical in
noncomputable def chartFamily {K : Type*} [Field K] (L : Finset (ChartLine K)) :
    Finset (Line K) := L.image chartLift

open Classical in
noncomputable def chartRestriction {K : Type*} [Field K]
    (f : Poly K) (l : ChartLine K) : Polynomial K :=
  restrictLine f (chartOrigin l) (chartDirection l)

open Classical in
noncomputable def planePolynomial {K : Type*} [Field K]
    (normal : Point K) (offset : K) : Poly K :=
  (∑ j : Fin 3, MvPolynomial.C (normal j) * MvPolynomial.X j) - MvPolynomial.C offset

open Classical in
def mapChart {F K : Type*} [Field F] [Field K] (φ : F →+* K)
    (l : ChartLine F) : ChartLine K := ⟨φ l.s, φ l.t, φ l.u, φ l.v⟩

open Classical in
def mapPoint {F K : Type*} [Field F] [Field K] (φ : F →+* K)
    (x : Point F) : Point K := fun j => φ (x j)

open Classical in
noncomputable def mapChartFamily {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (L : Finset (ChartLine F)) : Finset (ChartLine K) := L.image (mapChart φ)

end ExplicitRIP.GuthZahl

end
