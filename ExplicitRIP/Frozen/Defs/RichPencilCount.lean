/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.IsContactPencil

/-!
# The number of rich pencils

Source: [KM, Section 4.1, Theorem 6(a)]; [Z, Definition 1.2].
-/

@[expose] public section

open scoped Matrix

/-- The number of `h`-rich pencils of a finite set `𝒮` of oriented spheres, as in
[Z, Definition 1.2]: pencils of contacting spheres containing at least `h` spheres of `𝒮`.
The case `h = 2` is the pencil count in [KM, Theorem 6(a)]. -/
noncomputable def ExplicitRIP.richPencilCount {F : Type*} [Field F] [Fintype F]
    (𝒮 : Finset (F × F × F × F)) (h : ℕ) : ℕ :=
  open Classical in
  {P : Set (F × F × F × F) | ExplicitRIP.IsContactPencil P ∧ h ≤ (𝒮.filter (· ∈ P)).card}.ncard
