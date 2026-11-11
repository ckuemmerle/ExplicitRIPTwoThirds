/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.DRNorm
public import ExplicitRIP.Frozen.Defs.InducedEdgeCount
public import ExplicitRIP.Combinatorics.DensityDR.RectangleBound

/-!
# Proof of Lemma 3 of [KM]: discrete Rayleigh norm from density

Source: [KM, Lemma 3].

Fixed-size subset averaging and an exponent split prove [KM, Lemma 3]. For `c ≥ 0` and
`1 ≤ β ≤ 2`, hereditary density `e(U) ≤ c |U|^β` gives `‖A‖_DR ≤ 2^{β+1} c |V|^{max(1/2, β-1)}`.
-/

public section

open scoped Matrix

/-- Hereditary induced-edge density controls the discrete Rayleigh norm. -/
theorem ExplicitRIP.Provider.subgraph_density_dr_bound :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (c β : ℝ),
      0 ≤ c → 1 ≤ β → β ≤ 2 →
      (∀ U : Finset V, (ExplicitRIP.inducedEdgeCount G U : ℝ) ≤ c * (U.card : ℝ) ^ β) →
        ExplicitRIP.drNorm (G.adjMatrix ℝ) ≤
          2 ^ (β + 1) * c * (Fintype.card V : ℝ) ^ max (1 / 2 : ℝ) (β - 1) := by
  intro V _ _ G _ c β hc hβ _ hdensity
  unfold ExplicitRIP.drNorm
  apply Real.iSup_le
  · intro IJ
    change ‖ExplicitRIP.Dens.rectangleSum G IJ.1.1 IJ.1.2‖ /
      Real.sqrt ((IJ.1.1.card : ℝ) * IJ.1.2.card) ≤ _
    rw [Real.norm_eq_abs,
      abs_of_nonneg (ExplicitRIP.Dens.rectangleSum_nonneg G IJ.1.1 IJ.1.2)]
    exact ExplicitRIP.Dens.rectangleSum_div_sqrt_le G c β hc (by linarith) hdensity
      IJ.1.1 IJ.1.2 IJ.2.1 IJ.2.2
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hc)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
