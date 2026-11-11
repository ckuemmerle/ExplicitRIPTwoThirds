/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.TwoDistanceBarrier.Distances
public import ExplicitRIP.Analysis.TwoDistanceBarrier.Energy
public import ExplicitRIP.Analysis.TwoDistanceBarrier.Star

/-!
# The finite barrier for subframes of two-distance tight frames

Once the ambient dimension is at least eight and the redundancy of the
selected subframe is large, the star bound holds uniformly in the sparsity.

Source: [KM, proof of Proposition 10].
-/

public section

open scoped Matrix BigOperators

namespace ExplicitRIP.TwoDistanceBarrier

/-- Explicit sufficient thresholds for the uniform restricted-isometry lower bound. -/
theorem finite_barrier {m N : ℕ} (F : Matrix (Fin m) (Fin N) ℝ)
    (S : Finset (Fin N)) (hF : IsWeakTwoDistanceTightFrame F) (hm : 8 ≤ m)
    (hsize : 100 * ((m : ℝ) + 1) ≤ S.card) (k : ℕ) (hk : 1 ≤ k) :
    min (coherence F * Real.sqrt ((k : ℝ) - 1)) 1 ≤
      ripConstant (F.submatrix id (Subtype.val : S → Fin N)) k := by
  classical
  have hSc : 2 ≤ S.card := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have htwo : (2 : ℝ) ≤ S.card := by linarith only [hsize, hm0]
    exact_mod_cast htwo
  have hN : 2 ≤ N := hSc.trans (by simpa only [Fintype.card_fin] using S.card_le_univ)
  obtain ⟨η, hημ, hmin, hvalues⟩ := frame_distances F hF hN
  have hη := small_distance_le_half F hF hm hN η hmin
  let Φ := F.submatrix id (Subtype.val : S → Fin N)
  have hdiag (i : S) : (Φᵀ * Φ) i i = 1 := gram_diag F hF.1 i.val
  have hval (i j : S) (hij : i ≠ j) :
      (Φᵀ * Φ) i j = η ∨ |(Φᵀ * Φ) i j| = coherence F :=
    hvalues i.val j.val (fun h => hij (Subtype.ext h))
  obtain ⟨v, T, hv, hT, hlarge⟩ := exists_large_star m Φ η (coherence F)
    hdiag (RIPOneTwo.coherence_nonneg F) hημ hη hval (by
      simpa only [Fintype.card_coe] using hsize)
  apply min_sqrt_le_ripConstant Φ v T (coherence F) (RIPOneTwo.coherence_nonneg F)
    hv ?_ hlarge k hk
  intro i hi
  have hiv : i ≠ v := fun h => hv (h ▸ hi)
  simpa only [Matrix.sub_apply, Matrix.one_apply_ne hiv, sub_zero,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hT i hi

end ExplicitRIP.TwoDistanceBarrier
