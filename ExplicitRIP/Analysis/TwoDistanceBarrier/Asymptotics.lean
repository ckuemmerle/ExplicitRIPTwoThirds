/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.TwoDistanceBarrier.Finite
public import ExplicitRIP.Analysis.TwoDistanceBarrier.Scaling

/-!
# The asymptotic two-thirds barrier

The finite star estimate holds eventually under the dimension-ratio
hypotheses. A coherence lower bound converts vanishing distortion into
sparsity smaller than the two-thirds power of the dimension.

Source: [KM, Proposition 10 and its proof].
-/

public section

open Filter Asymptotics
open scoped Topology Matrix

namespace ExplicitRIP.TwoDistanceBarrier

/-- The dimension ratio forces the explicit thresholds whenever a nonempty support exists. -/
theorem eventual_barrier (m N : ℕ → ℕ) (F : ∀ j, Matrix (Fin (m j)) (Fin (N j)) ℝ)
    (S : ∀ j, Finset (Fin (N j))) (hF : ∀ j, IsWeakTwoDistanceTightFrame (F j))
    (hm : Tendsto (fun j => (m j : ℝ)) atTop atTop)
    (hratio : Tendsto (fun j => (m j : ℝ) / (S j).card) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, ∀ k : ℕ, 1 ≤ k → k ≤ (S j).card →
      min (coherence (F j) * Real.sqrt ((k : ℝ) - 1)) 1 ≤
        ripConstant ((F j).submatrix id (Subtype.val : S j → Fin (N j))) k := by
  have hrow := hm.eventually_ge_atTop 8
  have hr := hratio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 200))
  filter_upwards [hrow, hr] with j hj hrj k hk hkn
  apply finite_barrier (F j) (S j) (hF j) (by exact_mod_cast hj) ?_ k hk
  have hn : (0 : ℝ) < (S j).card := by exact_mod_cast (show 0 < (S j).card by omega)
  have h := (div_lt_iff₀ hn).mp hrj
  linarith only [hj, h]

end ExplicitRIP.TwoDistanceBarrier
