/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.HereditaryDensity.Pencils
import ExplicitRIP.Frozen.ZahlSphereContacts

/-!
# Hereditary density for two norm-graph translates

A complementary conic contains at most twelve selected points. Thus the exceptional outcome in
Zahl's two-rich dichotomy is impossible above 144 points. Smaller sets satisfy the elementary
quadratic edge bound.
-/

public section

namespace ExplicitRIP.Contact.Density

open Edges

theorem two_translate_density :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
      (T : Finset (ZMod p)), T.card ≤ 2 →
      ∀ U ⊆ selectedVertices p T, U.card ≤ p ^ 2 →
        (open Classical in (inducedEdgeCount (contactGraph p) U : ℝ)) ≤
          C * (U.card : ℝ) ^ (3 / 2 : ℝ) := by
  classical
  obtain ⟨C₀, hC₀, hZ⟩ := zahl_sphere_contacts
  refine ⟨12 + 36 * C₀, by positivity, fun p _ _ T hT U hU hsize => ?_⟩
  have hs : 0 ≤ (U.card : ℝ) := Nat.cast_nonneg _
  have hr : 0 ≤ (U.card : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hs _
  by_cases hsmall : U.card ≤ 144
  · have hsqrt : Real.sqrt U.card ≤ 12 := (Real.sqrt_le_left (by norm_num)).mpr (by
      exact_mod_cast hsmall)
    have hsq : (U.card : ℝ) ^ 2 ≤ 12 * (U.card : ℝ) ^ (3 / 2 : ℝ) := by
      rw [rpow_three_halves _ hs]
      have h := mul_le_mul_of_nonneg_right hsqrt
        (mul_nonneg (Real.sqrt_nonneg (U.card : ℝ)) hs)
      have he := congrArg (fun x : ℝ => x * U.card) (Real.sq_sqrt hs)
      nlinarith only [h, he]
    have he : (inducedEdgeCount (contactGraph p) U : ℝ) ≤ (U.card : ℝ) ^ 2 := by
      exact_mod_cast inducedEdgeCount_le_sq (contactGraph p) U
    exact he.trans (hsq.trans (mul_le_mul_of_nonneg_right (by linarith only [hC₀]) hr))
  · have htwo : (richPencilCount U 2 : ℝ) ≤ C₀ * (U.card : ℝ) ^ (3 / 2 : ℝ) := by
      rcases hZ p U hsize with h | ⟨A, B, hAB, hA, _⟩
      · exact h
      · have hcap : (U.filter (· ∈ A)).card ≤ 12 :=
          (Finset.card_le_card (Finset.filter_subset_filter _ hU)).trans
            ((conic_cap p T hAB).trans (Nat.mul_le_mul_left 6 hT))
        have hle : Real.sqrt U.card ≤ 12 := hA.trans (by exact_mod_cast hcap)
        have hcard : U.card ≤ 144 := by
          have h := (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 12)).mp hle
          exact_mod_cast h
        exact False.elim (hsmall hcard)
    have he : (inducedEdgeCount (contactGraph p) U : ℝ) ≤
        36 * (richPencilCount U 2 : ℝ) := by
      exact_mod_cast edge_count_le_rich_two p T hT U hU
    calc
      _ ≤ 36 * (C₀ * (U.card : ℝ) ^ (3 / 2 : ℝ)) :=
        he.trans (mul_le_mul_of_nonneg_left htwo (by norm_num))
      _ ≤ (12 + 36 * C₀) * (U.card : ℝ) ^ (3 / 2 : ℝ) := by
        nlinarith only [hr]

end ExplicitRIP.Contact.Density
