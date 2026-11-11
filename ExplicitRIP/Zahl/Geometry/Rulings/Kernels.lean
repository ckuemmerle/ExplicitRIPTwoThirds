/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Geometry.Rulings.Homogeneous

/-!
# Linear kernels for the two rulings

Each nonzero two-coordinate kernel vector cuts out a two-dimensional space of
matrices. The homogeneous subspace of a line in that ruling is exactly this
space after applying the split-quadric coordinate equivalence.
-/

@[expose] public section

namespace ExplicitRIP.Zahl.Rulings

variable {K : Type*} [Field K]

/-- The two linear equations defining a fixed ruling line. -/
def rulingMap (side : Bool) (a : Fin 2 → K) : (Fin 4 → K) →ₗ[K] (Fin 2 → K) where
  toFun v := if side then
    ![v 0 * a 0 + v 1 * a 1, v 2 * a 0 + v 3 * a 1]
    else ![a 0 * v 0 + a 1 * v 2, a 0 * v 1 + a 1 * v 3]
  map_add' v w := by cases side <;> ext i <;> fin_cases i <;> simp <;> ring
  map_smul' c v := by cases side <;> ext i <;> fin_cases i <;> simp <;> ring

/-- The homogeneous matrix subspace with a specified left or right kernel. -/
def rulingSpace (side : Bool) (a : Fin 2 → K) : Submodule K (Fin 4 → K) :=
  LinearMap.ker (rulingMap side a)

theorem mem_leftSpace_iff (a : Fin 2 → K) (v : Fin 4 → K) :
    v ∈ rulingSpace false a ↔
      a 0 * v 0 + a 1 * v 2 = 0 ∧ a 0 * v 1 + a 1 * v 3 = 0 := by
  simp [rulingSpace, rulingMap, funext_iff, Fin.forall_fin_two]

theorem mem_rightSpace_iff (a : Fin 2 → K) (v : Fin 4 → K) :
    v ∈ rulingSpace true a ↔
      v 0 * a 0 + v 1 * a 1 = 0 ∧ v 2 * a 0 + v 3 * a 1 = 0 := by
  simp [rulingSpace, rulingMap, funext_iff, Fin.forall_fin_two]

theorem coord_one_ne_zero (a : Fin 2 → K) (ha : a ≠ 0) (h₀ : a 0 = 0) : a 1 ≠ 0 := by
  intro h₁
  apply ha
  ext i
  fin_cases i <;> assumption

theorem rulingMap_surjective (side : Bool) (a : Fin 2 → K) (ha : a ≠ 0) :
    Function.Surjective (rulingMap side a) := by
  intro v
  by_cases h₀ : a 0 = 0
  · have h₁ := coord_one_ne_zero a ha h₀
    cases side
    · refine ⟨![0, 0, v 0 / a 1, v 1 / a 1], ?_⟩
      ext i; fin_cases i <;> simp [rulingMap, h₁, mul_div_cancel₀]
    · refine ⟨![0, v 0 / a 1, 0, v 1 / a 1], ?_⟩
      ext i; fin_cases i <;> simp [rulingMap, h₁]
  · cases side
    · refine ⟨![v 0 / a 0, v 1 / a 0, 0, 0], ?_⟩
      ext i; fin_cases i <;> simp [rulingMap, h₀, mul_div_cancel₀]
    · refine ⟨![v 0 / a 0, 0, v 1 / a 0, 0], ?_⟩
      ext i; fin_cases i <;> simp [rulingMap, h₀]

theorem finrank_rulingSpace (side : Bool) (a : Fin 2 → K) (ha : a ≠ 0) :
    Module.finrank K (rulingSpace side a) = 2 := by
  have h := (rulingMap side a).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (rulingMap_surjective side a ha)] at h
  simp only [finrank_top, Module.finrank_fin_fun] at h
  change 2 + Module.finrank K (rulingSpace side a) = 4 at h
  omega

theorem exists_map_lineSpace_eq (Q : SplitQuadric K) (side : Bool) (l : ChartLine K)
    (hl : inRuling Q side l) :
    ∃ a : Fin 2 → K, a ≠ 0 ∧ (lineSpace l).map Q.toLinearMap = rulingSpace side a := by
  obtain ⟨a, ha, h⟩ := hl
  refine ⟨a, ha, ?_⟩
  have hle : lineSpace l ≤ (rulingSpace side a).comap Q.toLinearMap := by
    apply lineSpace_le_of_homogenize_mem
    intro x
    have hx := h (linePoint l x) ⟨x, rfl⟩
    change Q (homogenize (linePoint l x)) ∈ rulingSpace side a
    cases side
    · exact (mem_leftSpace_iff _ _).mpr hx
    · exact (mem_rightSpace_iff _ _).mpr hx
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.map_le_iff_le_comap.mpr hle
  · rw [Q.finrank_map_eq, finrank_lineSpace, finrank_rulingSpace side a ha]

end ExplicitRIP.Zahl.Rulings
