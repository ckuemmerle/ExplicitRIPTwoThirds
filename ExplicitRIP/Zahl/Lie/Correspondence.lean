/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Basic.Lie
public import ExplicitRIP.Zahl.Geometry.Lines

/-!
# The Lie correspondence in reflected coordinates

Normalized lines in the Heisenberg locus are exactly the canonical parameter
lines. Binary norm anisotropy gives dependence of orthogonal null vectors.
The point-pencil equations and ruling counts are transported through the
sphere-line map obtained from Zahl's map by the reflection `(X,Y,Z) ↦ (X,Y,-Z)`.
-/

public section

namespace ExplicitRIP.Zahl

variable {F : Type*} [Field F]

/-- Every normalized line in the Heisenberg locus has canonical parameters. -/
theorem linePoints_subset_heisenberg_iff (hn : ¬ IsSquare (-1 : F))
    (l : ChartLine (QuadraticExtension F)) :
    linePoints l ⊆ heisenberg ↔ ∃ h : HLine F, h.toChart = l := by
  constructor
  · intro h
    have hpoint (x : QuadraticExtension F) : linePoint l x ∈ heisenberg :=
      h ⟨x, rfl⟩
    have h0 : l.t.im = 0 := by
      simpa [heisenberg, linePoint] using hpoint 0
    have h1 : l.v.im = -(l.s.im + l.u.im) := by
      simpa [heisenberg, linePoint, h0, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one] using hpoint 1
    have hm1 : -l.v.im = l.s.im - l.u.im := by
      simpa [heisenberg, linePoint, h0, sub_eq_add_neg, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one] using hpoint (-1)
    have hi : l.v.re = l.s.re - l.u.im := by
      simpa [heisenberg, linePoint, h0, sub_eq_add_neg] using
        hpoint (⟨0, 1⟩ : QuadraticExtension F)
    have hu : l.u.im = 0 := by
      apply (mul_eq_zero.mp (show (2 : F) * l.u.im = 0 by
        linear_combination h1 + hm1)).resolve_left
        (two_ne_zero_of_neg_one_not_isSquare hn)
    have hvi : l.v.im = -l.s.im := by linear_combination h1 - hu
    have hvr : l.v.re = l.s.re := by linear_combination hi - hu
    refine ⟨⟨l.t.re, l.u.re, l.s.re, l.s.im⟩, ?_⟩
    apply ChartLine.ext_of_coefficients
    · exact QuadraticAlgebra.ext rfl rfl
    · apply QuadraticAlgebra.ext
      · rfl
      · exact h0.symm
    · apply QuadraticAlgebra.ext
      · rfl
      · exact hu.symm
    · apply QuadraticAlgebra.ext
      · exact hvr.symm
      · exact hvi.symm
  · rintro ⟨h, rfl⟩
    exact h.linePoints_subset_heisenberg

/-- A nonzero null vector and an orthogonal null vector are proportional. -/
theorem null_orthogonal_dependent (hn : ¬ IsSquare (-1 : F))
    (a b c d A B C D : F)
    (hv : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0)
    (hqv : c ^ 2 + d ^ 2 = a * b)
    (hqu : C ^ 2 + D ^ 2 = A * B)
    (horth : 2 * (c * C + d * D) = a * B + A * b) :
    ∃ t : F, A = t * a ∧ B = t * b ∧ C = t * c ∧ D = t * d := by
  by_cases hb : b = 0
  · obtain ⟨hc, hd⟩ := (sum_sq_eq_zero_iff hn c d).mp (by
      simpa only [hb, mul_zero] using hqv)
    have ha : a ≠ 0 := by simpa only [hb, hc, hd, ne_self_iff_false, or_false] using hv
    have hB : B = 0 := by
      have hprod : a * B = 0 := by simpa only [hb, hc, hd, zero_mul, add_zero,
        mul_zero] using horth.symm
      exact (mul_eq_zero.mp hprod).resolve_left ha
    obtain ⟨hC, hD⟩ := (sum_sq_eq_zero_iff hn C D).mp (by
      simpa only [hB, mul_zero] using hqu)
    refine ⟨A / a, ?_, ?_, ?_, ?_⟩
    · field_simp
    · simp only [hb, hB, mul_zero]
    · simp only [hc, hC, mul_zero]
    · simp only [hd, hD, mul_zero]
  · have hnorm : (b * C - B * c) ^ 2 + (b * D - B * d) ^ 2 = 0 := by
      linear_combination b ^ 2 * hqu - b * B * horth + B ^ 2 * hqv
    obtain ⟨hC, hD⟩ := (sum_sq_eq_zero_iff hn _ _).mp hnorm
    have hprod : (A * b - a * B) * b = 0 := by
      linear_combination -b * horth + 2 * c * hC + 2 * d * hD + 2 * B * hqv
    have hA := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hb)
    refine ⟨B / b, ?_, ?_, ?_, ?_⟩
    · field_simp
      linear_combination hA
    · field_simp
    · field_simp
      linear_combination hC
    · field_simp
      linear_combination hD

/-- The three parameter equations for the pencil through a Heisenberg point. -/
theorem mem_pointPencil_iff (w : Point (QuadraticExtension F)) (hw : w ∈ heisenberg)
    (S : Sphere F) :
    S ∈ pointPencil w ↔
      (sphereParameters S).c = (w 1).re - (sphereParameters S).b * (w 0).re ∧
      (sphereParameters S).d = (w 1).im - (sphereParameters S).b * (w 0).im ∧
      (sphereParameters S).a = (w 2).re -
        (sphereParameters S).c * (w 0).re - (sphereParameters S).d * (w 0).im := by
  change w ∈ linePoints (sphereLine S) ↔ _
  rw [mem_linePoints_iff]
  constructor
  · rintro ⟨hY, hZ⟩
    have hYr := congrArg QuadraticAlgebra.re hY
    have hYi := congrArg QuadraticAlgebra.im hY
    have hZr := congrArg QuadraticAlgebra.re hZ
    simp [sphereLine, HLine.toChart] at hYr hYi hZr
    refine ⟨?_, ?_, ?_⟩
    · linear_combination -hYr
    · linear_combination -hYi
    · linear_combination -hZr
  · rintro ⟨hc, hd, ha⟩
    have hH := hw
    simp [heisenberg] at hH
    constructor
    · apply QuadraticAlgebra.ext <;> simp [sphereLine, HLine.toChart]
      · linear_combination -hc
      · linear_combination -hd
    · apply QuadraticAlgebra.ext <;> simp [sphereLine, HLine.toChart]
      · linear_combination -ha
      · linear_combination hH + (w 0).re * hd - (w 0).im * hc

open Classical in
/-- Ruling counts equal the cardinalities of their sphere preimages. -/
theorem rulingCount_sphereImage {F : Type*} [Field F]
    [Fact (¬ IsSquare (-1 : F))] (S : Finset (Sphere F))
    (Q : SplitQuadric (QuadraticExtension F)) (side : Bool) :
    rulingCount Q side (sphereImage S) =
      (S.filter (fun s => inRuling Q side (sphereLine s))).card := by
  rw [rulingCount, sphereImage, Finset.filter_image]
  exact Finset.card_image_of_injective _
    (sphereLine_injective (two_ne_zero_of_neg_one_not_isSquare Fact.out))

end ExplicitRIP.Zahl
