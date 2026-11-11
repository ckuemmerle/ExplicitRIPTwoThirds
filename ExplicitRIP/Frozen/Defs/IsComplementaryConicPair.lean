/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.SphereContact

/-!
# Pairs of complementary conic sections

Source: [KM, Section 4.1]; [Z, Definition 1.6].
-/

@[expose] public section

open scoped Matrix

/-- A pair of complementary conic sections as in [Z, Definition 1.6] and [KM, Section 4.1]: sets
`𝒞, 𝒞'` of oriented spheres, each of cardinality at least three, such that every sphere of
`𝒞` is in contact with every sphere of `𝒞'` and no two distinct spheres of the same set are
in contact. The sets are maximal: no sphere can be added to `𝒞` or to `𝒞'` while keeping
these properties. -/
def ExplicitRIP.IsComplementaryConicPair {F : Type*} [Field F] (𝒞 𝒞' : Set (F × F × F × F)) :
    Prop :=
  let good : Set (F × F × F × F) → Set (F × F × F × F) → Prop := fun A B =>
    3 ≤ A.encard ∧ 3 ≤ B.encard ∧ (∀ S ∈ A, ∀ S' ∈ B, ExplicitRIP.SphereContact S S') ∧
      (∀ S ∈ A, ∀ S' ∈ A, S ≠ S' → ¬ ExplicitRIP.SphereContact S S') ∧
      (∀ S ∈ B, ∀ S' ∈ B, S ≠ S' → ¬ ExplicitRIP.SphereContact S S')
  good 𝒞 𝒞' ∧ (∀ S, S ∉ 𝒞 → ¬ good (insert S 𝒞) 𝒞') ∧ (∀ S, S ∉ 𝒞' → ¬ good 𝒞 (insert S 𝒞'))
