/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.SphereContact

/-!
# Pencils of contacting spheres

Source: [KM, Section 4.1]; [Z, Definition 1.2].
-/

@[expose] public section

open scoped Matrix

/-- A pencil of contacting spheres as in [Z, Definition 1.2] and [KM, Section 4.1]: a set of
oriented spheres every pair of which is in contact, maximal in the sense that no further
sphere can be added while keeping this property. -/
def ExplicitRIP.IsContactPencil {F : Type*} [Field F] (P : Set (F × F × F × F)) : Prop :=
  (∀ S ∈ P, ∀ S' ∈ P, ExplicitRIP.SphereContact S S') ∧
    ∀ S, S ∉ P → ¬ ∀ S' ∈ insert S P, ∀ S'' ∈ insert S P, ExplicitRIP.SphereContact S' S''
