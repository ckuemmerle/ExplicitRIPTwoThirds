/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.DRNorm
public import ExplicitRIP.Frozen.Defs.InducedEdgeCount
import ExplicitRIP.Provider.SubgraphDensityDR

/-!
# Lemma 3 of [KM]: discrete Rayleigh norm from induced edge counts

Source: [KM, Lemma 3].
-/

public section

open scoped Matrix

/-- [KM, Lemma 3]. If a finite simple graph on `V` satisfies `e(U) ≤ c |U|^β` for every `U ⊆ V`,
with `c ≥ 0` and `1 ≤ β ≤ 2`, then its adjacency matrix satisfies
`‖A‖_DR ≤ 2^{β+1} c |V|^{max(1/2, β-1)}`. -/
theorem ExplicitRIP.subgraph_density_dr_bound :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (c β : ℝ),
      0 ≤ c → 1 ≤ β → β ≤ 2 →
      (∀ U : Finset V, (ExplicitRIP.inducedEdgeCount G U : ℝ) ≤ c * (U.card : ℝ) ^ β) →
        ExplicitRIP.drNorm (G.adjMatrix ℝ) ≤
          2 ^ (β + 1) * c * (Fintype.card V : ℝ) ^ max (1 / 2 : ℝ) (β - 1) :=
by exact ExplicitRIP.Provider.subgraph_density_dr_bound
