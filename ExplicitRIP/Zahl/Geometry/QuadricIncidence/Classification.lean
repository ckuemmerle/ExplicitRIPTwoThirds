/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Geometry.QuadricIncidence.Kernels

/-!
# Classification of lines contained in a split quadric

In characteristic different from two, evaluations at zero, one and minus one
make the entire homogeneous matrix pencil singular. Its common kernel puts
the line in one of the two rulings.
-/

public section

namespace ExplicitRIP.Zahl.Geometry.QuadricIncidence

theorem quadricContains_of_inRuling {K : Type*} [Field K]
    (Q : SplitQuadric K) (side : Bool) (l : ChartLine K)
    (hl : inRuling Q side l) : quadricContains Q l := by
  obtain ⟨a, ha, h⟩ := hl
  intro w hw
  apply det_eq_zero_of_mem_rulingSpace side a ha (Q (homogenize w))
  cases side
  · exact (Rulings.mem_leftSpace_iff _ _).mpr (h w hw)
  · exact (Rulings.mem_rightSpace_iff _ _).mpr (h w hw)

end ExplicitRIP.Zahl.Geometry.QuadricIncidence

namespace ExplicitRIP.Zahl

open Polynomial

/-- The contained lines are exactly the lines in the two kernel rulings. -/
theorem quadricContains_iff_inRuling {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (Q : SplitQuadric K) (l : ChartLine K) :
    quadricContains Q l ↔ inRuling Q false l ∨ inRuling Q true l := by
  constructor
  · intro hl
    let A := Q (Rulings.lineMap l ![1, 0])
    let B := Q (Rulings.lineMap l ![0, 1])
    have hmap (x : K) : Q (homogenize (linePoint l x)) = A + x • B := by
      rw [Rulings.homogenize_linePoint_eq]
      have hx : (![1, x] : Fin 2 → K) = ![1, 0] + x • ![0, 1] := by
        ext i
        fin_cases i
        · change (1 : K) = 1 + x * 0
          ring
        · change x = 0 + x * 1
          ring
      rw [hx, map_add, map_smul, map_add, map_smul]
    have hA0 : A ≠ 0 := by
      intro hzero
      have h : Rulings.lineMap l ![1, 0] = 0 :=
        Q.injective (hzero.trans Q.map_zero.symm)
      exact one_ne_zero (congrFun h 0)
    have hval (x : K) :
        (A 0 + x * B 0) * (A 3 + x * B 3) -
          (A 1 + x * B 1) * (A 2 + x * B 2) = 0 := by
      have hx := hl (linePoint l x) ⟨x, rfl⟩
      simpa only [quadricValue, hmap, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hx
    have hA := hval 0
    simp only [zero_mul, add_zero] at hA
    have hplus := hval 1
    simp only [one_mul] at hplus
    have hminus := hval (-1)
    simp only [neg_one_mul] at hminus
    have hB : B 0 * B 3 - B 1 * B 2 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left h2
      change (2 : K) * (B 0 * B 3 - B 1 * B 2) = 0
      linear_combination hplus + hminus - 2 * hA
    have hAB : A 0 * B 3 + B 0 * A 3 - A 1 * B 2 - B 1 * A 2 = 0 := by
      linear_combination hplus - hA - hB
    obtain ⟨side, a, ha, hleft, hright⟩ :=
      Geometry.QuadricIncidence.exists_common_rulingSpace A B hA0 hA hB hAB
    have hruling : inRuling Q side l := by
      refine ⟨a, ha, ?_⟩
      rintro w ⟨x, rfl⟩
      have hx : Q (homogenize (linePoint l x)) ∈ Rulings.rulingSpace side a := by
        rw [hmap]
        exact (Rulings.rulingSpace side a).add_mem hleft
          ((Rulings.rulingSpace side a).smul_mem x hright)
      cases side
      · exact (Rulings.mem_leftSpace_iff _ _).mp hx
      · exact (Rulings.mem_rightSpace_iff _ _).mp hx
    cases side
    · exact Or.inl hruling
    · exact Or.inr hruling
  · rintro (h | h)
    · exact Geometry.QuadricIncidence.quadricContains_of_inRuling Q false l h
    · exact Geometry.QuadricIncidence.quadricContains_of_inRuling Q true l h

end ExplicitRIP.Zahl
