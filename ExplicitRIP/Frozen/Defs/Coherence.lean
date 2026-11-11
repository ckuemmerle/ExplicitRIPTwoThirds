/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# The coherence

Source: [KM, Section 1, the definition of μ before (2)].
-/

@[expose] public section

open scoped Matrix

/-- The coherence `μ(Φ) = max_{i ≠ j} |⟨φ_i, φ_j⟩|` of the columns `φ_j` of `Φ`, as defined
before [KM, (2)], with `⟨φ_i, φ_j⟩ = (Φ^* Φ)_{ij}`. By convention it is `0` when `Φ` has at
most one column. -/
noncomputable def ExplicitRIP.coherence {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m]
    [Fintype n] (Φ : Matrix m n 𝕜) : ℝ :=
  ⨆ ij : {ij : n × n // ij.1 ≠ ij.2}, ‖(Φᴴ * Φ) ij.1.1 ij.1.2‖
