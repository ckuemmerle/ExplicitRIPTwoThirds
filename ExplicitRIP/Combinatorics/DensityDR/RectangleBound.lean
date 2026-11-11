/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Combinatorics.DensityDR.Incidence
public import ExplicitRIP.Combinatorics.DensityDR.Exponents

/-!
# Hereditary edge density bounds every rectangle

Finite subset averaging bounds every rectangle by hereditary edge density.

Source: [KM, proof of Lemma 3].
-/

public section

open scoped BigOperators

namespace ExplicitRIP.Dens

variable {V : Type*} [DecidableEq V]

/-- Averaging over subsets of the larger side gives a scaled rectangle bound. -/
theorem rectangleSum_scaled_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (c β : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (hdensity : ∀ U : Finset V, (inducedEdgeCount G U : ℝ) ≤ c * (U.card : ℝ) ^ β)
    (I J : Finset V) (hI : I.Nonempty) (hIJ : I.card ≤ J.card) :
    (I.card : ℝ) * rectangleSum G I J ≤
      (J.card : ℝ) * (2 * c * (2 * (I.card : ℝ)) ^ β) := by
  have ha : 1 ≤ I.card := hI.card_pos
  have hb : 1 ≤ J.card := ha.trans hIJ
  have hterm (K : Finset V) (hK : K ∈ J.powersetCard I.card) :
      rectangleSum G I K ≤ 2 * c * (2 * (I.card : ℝ)) ^ β := by
    have hKcard := (Finset.mem_powersetCard.mp hK).2
    have hU : ((I ∪ K).card : ℝ) ≤ 2 * (I.card : ℝ) := by
      have h := Finset.card_union_le I K
      rw [hKcard] at h
      exact_mod_cast (show (I ∪ K).card ≤ 2 * I.card by omega)
    calc
      _ ≤ 2 * (inducedEdgeCount G (I ∪ K) : ℝ) :=
        rectangleSum_le_twice_inducedEdgeCount G I K
      _ ≤ 2 * (c * ((I ∪ K).card : ℝ) ^ β) :=
        mul_le_mul_of_nonneg_left (hdensity (I ∪ K)) (by norm_num)
      _ = (2 * c) * ((I ∪ K).card : ℝ) ^ β := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hU hβ) (mul_nonneg (by norm_num) hc)
  have hsum : (Nat.choose (J.card - 1) (I.card - 1) : ℝ) * rectangleSum G I J ≤
      (Nat.choose J.card I.card : ℝ) * (2 * c * (2 * (I.card : ℝ)) ^ β) := by
    calc
      _ = ∑ K ∈ J.powersetCard I.card, rectangleSum G I K :=
        (sum_powersetCard_rectangleSum G I J I.card ha).symm
      _ ≤ ∑ _K ∈ J.powersetCard I.card, 2 * c * (2 * (I.card : ℝ)) ^ β :=
        Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard]
  have hchoose : (J.card : ℝ) * (Nat.choose (J.card - 1) (I.card - 1) : ℝ) =
      (Nat.choose J.card I.card : ℝ) * (I.card : ℝ) := by
    have h := Nat.add_one_mul_choose_eq (J.card - 1) (I.card - 1)
    rw [Nat.sub_add_cancel hb, Nat.sub_add_cancel ha] at h
    exact_mod_cast h
  have hpos : (0 : ℝ) < (Nat.choose (J.card - 1) (I.card - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.sub_le_sub_right hIJ 1)
  apply le_of_mul_le_mul_left _ hpos
  calc
    _ = (I.card : ℝ) *
        ((Nat.choose (J.card - 1) (I.card - 1) : ℝ) * rectangleSum G I J) := by ring
    _ ≤ (I.card : ℝ) *
        ((Nat.choose J.card I.card : ℝ) * (2 * c * (2 * (I.card : ℝ)) ^ β)) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = ((Nat.choose J.card I.card : ℝ) * (I.card : ℝ)) *
        (2 * c * (2 * (I.card : ℝ)) ^ β) := by ring
    _ = ((J.card : ℝ) * (Nat.choose (J.card - 1) (I.card - 1) : ℝ)) *
        (2 * c * (2 * (I.card : ℝ)) ^ β) := by rw [hchoose]
    _ = _ := by ring

/-- The normalized rectangle estimate when the row set is the smaller set. -/
theorem rectangleSum_div_sqrt_le_of_card_le [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c β : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (hdensity : ∀ U : Finset V, (inducedEdgeCount G U : ℝ) ≤ c * (U.card : ℝ) ^ β)
    (I J : Finset V) (hI : I.Nonempty) (hIJ : I.card ≤ J.card) :
    rectangleSum G I J / Real.sqrt ((I.card : ℝ) * J.card) ≤
      2 ^ (β + 1) * c * (Fintype.card V : ℝ) ^ max (1 / 2 : ℝ) (β - 1) := by
  apply normalized_rectangle_le
  · exact_mod_cast (show 1 ≤ I.card from hI.card_pos)
  · exact_mod_cast hIJ
  · exact_mod_cast Finset.card_le_univ J
  · exact hc
  · exact rectangleSum_scaled_le G c β hc hβ hdensity I J hI hIJ

/-- The normalized estimate for an arbitrary nonempty rectangle. -/
theorem rectangleSum_div_sqrt_le [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c β : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (hdensity : ∀ U : Finset V, (inducedEdgeCount G U : ℝ) ≤ c * (U.card : ℝ) ^ β)
    (I J : Finset V) (hI : I.Nonempty) (hJ : J.Nonempty) :
    rectangleSum G I J / Real.sqrt ((I.card : ℝ) * J.card) ≤
      2 ^ (β + 1) * c * (Fintype.card V : ℝ) ^ max (1 / 2 : ℝ) (β - 1) := by
  rcases le_total I.card J.card with hIJ | hJI
  · exact rectangleSum_div_sqrt_le_of_card_le G c β hc hβ hdensity I J hI hIJ
  · rw [rectangleSum_comm G I J, mul_comm (I.card : ℝ) (J.card : ℝ)]
    exact rectangleSum_div_sqrt_le_of_card_le G c β hc hβ hdensity J I hJ hJI

end ExplicitRIP.Dens
