/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.Coherence
public import ExplicitRIP.Frozen.Defs.IsTwoDistanceTightFrame
import ExplicitRIP.Provider.ConstructionBarrier

/-!
# Proposition 10 of [KM]: the barrier for two-distance tight subframes

Source: [KM, Proposition 10].

The phrase “for all sufficiently large `m`” in [KM, Proposition 10] is read as eventually along
the sequence of subframes, whose row dimensions tend to infinity.
-/

public section

open scoped Matrix

/-- [KM, Proposition 10], stated for sequences. Let `F_j ∈ ℝ^{m_j × N_j}` be real two-distance
tight frames with unit-norm columns, as defined in [KM, Section 3], of coherence `μ_j`, and
let `Φ_j` be the subframe of the columns indexed by `S_j`, with `n_j = |S_j|` and `S_j`
eventually nonempty. Suppose `m_j → ∞` and `m_j / n_j → 0`. Then, for all sufficiently large
`j`, every `1 ≤ k ≤ n_j` has `δ_k(Φ_j) ≥ min {μ_j √(k - 1), 1}`. In particular, if
`μ_j ≥ C m_j^{-1/3}` eventually for some `C > 0`, then `δ_{k_j}(Φ_j) → 0` with `1 ≤ k_j ≤ n_j`
eventually requires `k_j = o(m_j^{2/3})`. -/
theorem ExplicitRIP.construction_barrier :
    ∀ (m N : ℕ → ℕ) (F : ∀ j, Matrix (Fin (m j)) (Fin (N j)) ℝ) (S : ∀ j, Finset (Fin (N j))),
      (∀ j, ExplicitRIP.IsTwoDistanceTightFrame (F j)) →
      (∀ᶠ j in Filter.atTop, (S j).Nonempty) →
      Filter.Tendsto (fun j => (m j : ℝ)) Filter.atTop Filter.atTop →
      Filter.Tendsto (fun j => (m j : ℝ) / (S j).card) Filter.atTop (nhds 0) →
      (∀ᶠ j in Filter.atTop, ∀ k : ℕ, 1 ≤ k → k ≤ (S j).card →
          min (ExplicitRIP.coherence (F j) * Real.sqrt ((k : ℝ) - 1)) 1 ≤
            ExplicitRIP.ripConstant ((F j).submatrix id (Subtype.val : S j → Fin (N j))) k) ∧
        ((∃ C : ℝ, 0 < C ∧ ∀ᶠ j in Filter.atTop,
            C * (m j : ℝ) ^ (-(1 / 3 : ℝ)) ≤ ExplicitRIP.coherence (F j)) →
          ∀ k : ℕ → ℕ, (∀ᶠ j in Filter.atTop, 1 ≤ k j ∧ k j ≤ (S j).card) →
            Filter.Tendsto (fun j => ExplicitRIP.ripConstant
                ((F j).submatrix id (Subtype.val : S j → Fin (N j))) (k j)) Filter.atTop (nhds 0) →
            (fun j => (k j : ℝ)) =o[Filter.atTop] (fun j => (m j : ℝ) ^ (2 / 3 : ℝ))) :=
by exact ExplicitRIP.Provider.construction_barrier
