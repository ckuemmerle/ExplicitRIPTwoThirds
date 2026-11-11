/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Defs
import ExplicitRIP.Relative.Zahl.ThreeRich
import ExplicitRIP.Relative.Zahl.TwoRich
import ExplicitRIP.Zahl.Lie.Classification.Counting
import ExplicitRIP.Zahl.Lie.Classification.Geometry

/-!
# Zahl's sphere-contact estimates from the Heisenberg structure theorem

A conditional helper. Its premise is the Guth–Zahl structure theorem for Heisenberg lines,
which `ExplicitRIP.GuthZahl.guthZahl_heisenberg_structure` proves;
`ExplicitRIP.Zahl.sphere_contacts` applies the result below to it. The affine rich-point
estimates give the sphere-pencil bounds through the sphere–line correspondence, and the
two-ruling alternative gives a complementary conic pair. One constant covers both conclusions.
-/

public section

namespace ExplicitRIP.Zahl

/-- [Z, Theorem 1.8] in the form of `ExplicitRIP.Zahl.sphere_contacts`, assuming the
Guth–Zahl structure theorem for Heisenberg lines. -/
theorem _root_.ExplicitRIP.Relative.Zahl.sphere_contacts
    (hG10 : (open Classical in
      ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
        ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
          ∀ L : Finset (HLine (ZMod p)),
            (L.card : ℝ) ≤ c * (p : ℝ) ^ 2 →
            ∀ A : ℝ, C * Real.sqrt (L.card : ℝ) ≤ A →
              (richCount (chartImage L) 2 : ℝ) ≤ C * A * (L.card : ℝ) ∨
                (∃ normal : Point (QuadraticExtension (ZMod p)), normal ≠ 0 ∧
                  ∃ offset : QuadraticExtension (ZMod p),
                    A ≤ (((chartImage L).filter (planeContains normal offset)).card : ℝ)) ∨
                ∃ Q : SplitQuadric (QuadraticExtension (ZMod p)),
                  A ≤ (((chartImage L).filter (quadricContains Q)).card : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
      ∀ S : Finset (ZMod p × ZMod p × ZMod p × ZMod p), S.card ≤ p ^ 2 →
        (∀ h : ℕ, 3 ≤ h →
          (ExplicitRIP.richPencilCount S h : ℝ) ≤
            C * (S.card : ℝ) ^ (3 / 2 : ℝ) * (h : ℝ) ^ (-(3 / 2 : ℝ))) ∧
        ((ExplicitRIP.richPencilCount S 2 : ℝ) ≤ C * (S.card : ℝ) ^ (3 / 2 : ℝ) ∨
          ∃ C₀ C₁ : Set (ZMod p × ZMod p × ZMod p × ZMod p),
            ExplicitRIP.IsComplementaryConicPair C₀ C₁ ∧
              (open Classical in
                Real.sqrt S.card ≤ ((S.filter (· ∈ C₀)).card : ℝ) ∧
                  Real.sqrt S.card ≤ ((S.filter (· ∈ C₁)).card : ℝ))) := by
  classical
  obtain ⟨C₃, hC₃, hthree⟩ := ExplicitRIP.Relative.Zahl.exists_affine_rich_constant hG10
  obtain ⟨C₂, hC₂, htwo⟩ := ExplicitRIP.Relative.Zahl.exists_affine_two_rich_constant hG10
  have hCthree : C₃ + 1 ≤ C₃ + C₂ + 1 := by linarith only [hC₂]
  have hCtwo : C₂ + 1 ≤ C₃ + C₂ + 1 := by linarith only [hC₃]
  refine ⟨C₃ + C₂ + 1, by positivity, ?_⟩
  intro p _ _ S hn
  have hns : ¬ IsSquare (-1 : ZMod p) := zmod_neg_one_not_isSquare p
  have hchar := two_ne_zero_of_neg_one_not_isSquare hns
  let L : Finset (HLine (ZMod p)) := S.image sphereParameters
  have hcard : L.card = S.card :=
    Finset.card_image_of_injective S (parameters_injective hchar)
  have hsize : L.card ≤ p ^ 2 := by simpa only [hcard] using hn
  have himage : chartImage L = sphereImage S := by
    rw [sphereImage_eq_chartImage]
    apply congrArg chartImage
    ext l
    simp only [L, Finset.mem_image]
  have hpower : 0 ≤ (S.card : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  constructor
  · intro h hh
    have haff := hthree p L hsize h hh
    rw [himage, hcard] at haff
    have hs := rich_pencil_bound_of_affine hns S h hh C₃ hC₃.le haff
    exact hs.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCthree hpower)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · have ht := htwo p L hsize
    rw [himage, hcard] at ht
    rcases ht with hbound | ⟨Q, h0, h1, hroot0, hroot1⟩
    · left
      exact (two_rich_pencil_bound_of_affine hns S C₂ hbound).trans
        (mul_le_mul_of_nonneg_right hCtwo hpower)
    · right
      obtain ⟨C₀, C₁, hpair, hc0, hc1⟩ := complementaryConicPair_of_rulings S Q h0 h1
      exact ⟨C₀, C₁, hpair, hroot0.trans hc0, hroot1.trans hc1⟩

end ExplicitRIP.Zahl
