/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.Coherence
public import ExplicitRIP.Frozen.Defs.InducedEdgeCount
import ExplicitRIP.Provider.RIPDensityBound

/-!
# [KM, (9)]: restricted isometry from hereditary density

Source: [KM, Section 2.2, (9)].
-/

public section

open scoped Matrix

/-- [KM, (9)], with the density constant explicit. There is an absolute constant `C` such that
if `Φ` has unit-norm columns with coherence `μ`, `0 < ν < μ`, and the graph joining `i ≠ j`
when `|⟨φ_i, φ_j⟩| > ν` satisfies `e(U) ≤ c |U|^β` for every `|U| ≤ k`, where `c ≥ 0`,
`1 ≤ β ≤ 2` and `k ≥ 1`, then `δ_k ≤ C (c k^{max(1/2, β-1)} log(2k) μ + k ν)`. -/
theorem ExplicitRIP.rip_density_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (Φ : Matrix m n ℂ),
      (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) → ∀ (ν c β : ℝ) (k : ℕ),
        0 < ν → ν < ExplicitRIP.coherence Φ → 0 ≤ c → 1 ≤ β → β ≤ 2 → 1 ≤ k →
        (∀ U : Finset n, U.card ≤ k →
          (open Classical in
            (ExplicitRIP.inducedEdgeCount
              (SimpleGraph.fromRel fun i j => ν < ‖(Φᴴ * Φ) i j‖) U : ℝ)) ≤
            c * (U.card : ℝ) ^ β) →
        ExplicitRIP.ripConstant Φ k ≤
          C * (c * (k : ℝ) ^ max (1 / 2 : ℝ) (β - 1) * Real.log (2 * k) * ExplicitRIP.coherence Φ +
            k * ν) :=
by exact ExplicitRIP.Provider.rip_density_bound
