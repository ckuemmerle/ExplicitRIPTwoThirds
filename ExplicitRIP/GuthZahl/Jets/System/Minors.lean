/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Jets.Defs

/-!
# Three minors of a pair of directions

The three two-by-two minors detect independent vectors in three coordinates.
Over a field, their nonvanishing is expressed by a linear combination equal to one.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl
namespace JetSystem


/-- The minors in the coordinate pairs `(0,1)`, `(0,2)`, and `(1,2)`. -/
def directionMinors {K : Type*} [CommRing K] (v w : Point K) : Fin 3 → K :=
  ![v 0 * w 1 - v 1 * w 0, v 0 * w 2 - v 2 * w 0,
    v 1 * w 2 - v 2 * w 1]

theorem directionMinors_zero_left {K : Type*} [CommRing K] (w : Point K) :
    directionMinors 0 w = 0 := by
  ext i
  fin_cases i <;> simp [directionMinors]

theorem directionMinors_zero_right {K : Type*} [CommRing K] (v : Point K) :
    directionMinors v 0 = 0 := by
  ext i
  fin_cases i <;> simp [directionMinors]

theorem directionMinors_smul {K : Type*} [CommRing K] (v : Point K) (a : K) :
    directionMinors v (a • v) = 0 := by
  ext i
  fin_cases i <;> simp [directionMinors] <;> ring

theorem exists_smul_of_directionMinors_eq_zero {K : Type*} [Field K]
    (v w : Point K) (hv : v ≠ 0) (hm : directionMinors v w = 0) :
    ∃ a : K, w = a • v := by
  have h01 : v 0 * w 1 = v 1 * w 0 :=
    sub_eq_zero.mp (congrFun hm 0)
  have h02 : v 0 * w 2 = v 2 * w 0 :=
    sub_eq_zero.mp (congrFun hm 1)
  have h12 : v 1 * w 2 = v 2 * w 1 :=
    sub_eq_zero.mp (congrFun hm 2)
  have hmul : ∀ i j : Fin 3, v i * w j = v j * w i := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals first | rfl | exact h01 | exact h01.symm | exact h02 |
      exact h02.symm | exact h12 | exact h12.symm
  have hv' : ¬ ∀ i, v i = 0 := fun h => hv (funext h)
  obtain ⟨i, hi⟩ := not_forall.mp hv'
  refine ⟨w i / v i, ?_⟩
  ext j
  change w j = (w i / v i) * v j
  rw [div_mul_eq_mul_div₀, eq_div_iff hi]
  calc
    w j * v i = v i * w j := mul_comm _ _
    _ = v j * w i := hmul i j
    _ = w i * v j := mul_comm _ _

theorem exists_multipliers_iff_ne_zero {K : Type*} [Field K] (m : Fin 3 → K) :
    (∃ u : Fin 3 → K, ∑ i, u i * m i = 1) ↔ m ≠ 0 := by
  constructor
  · rintro ⟨u, hu⟩ hm
    have h01 : (0 : K) = 1 := by
      simpa only [hm, Pi.zero_apply, mul_zero, Finset.sum_const_zero] using hu
    exact zero_ne_one h01
  · intro hm
    have hm' : ¬ ∀ i, m i = 0 := fun h => hm (funext h)
    obtain ⟨i, hi⟩ := not_forall.mp hm'
    refine ⟨fun j => if j = i then (m i)⁻¹ else 0, ?_⟩
    rw [Finset.sum_eq_single i]
    · change (if i = i then (m i)⁻¹ else 0) * m i = 1
      rw [ite_eq_left rfl, inv_mul_cancel₀ hi]
    · intro j _ hji
      simp only [hji, ite_false, zero_mul]
    · intro hi'
      exact (hi' (Finset.mem_univ i)).elim

theorem independent_directions_iff_exists_multipliers {K : Type*} [Field K]
    (v w : Point K) :
    (v ≠ 0 ∧ w ≠ 0 ∧ (¬ ∃ a : K, w = a • v)) ↔
      ∃ u : Fin 3 → K, ∑ i, u i * directionMinors v w i = 1 := by
  rw [exists_multipliers_iff_ne_zero]
  constructor
  · rintro ⟨hv, _, hnot⟩ hm
    exact hnot (exists_smul_of_directionMinors_eq_zero v w hv hm)
  · intro hm
    refine ⟨?_, ?_, ?_⟩
    · intro hv
      apply hm
      rw [hv, directionMinors_zero_left]
    · intro hw
      apply hm
      rw [hw, directionMinors_zero_right]
    · rintro ⟨a, ha⟩
      apply hm
      rw [ha, directionMinors_smul]

end JetSystem
end ExplicitRIP.GuthZahl

end
