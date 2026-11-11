/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Defs

/-!
# Homogeneous subspaces of normalized chart lines

A chart line determines a two-dimensional subspace of homogeneous coordinates.
Its nonzero intersections are exactly the determinant predicate `Coplanar`.
-/

@[expose] public section

namespace ExplicitRIP.Zahl.Rulings

variable {K : Type*} [Field K]

/-- The homogeneous parameterization of a normalized chart line. -/
def lineMap (l : ChartLine K) : (Fin 2 → K) →ₗ[K] (Fin 4 → K) where
  toFun a := ![a 0, a 1, a 0 * l.s + a 1 * l.u, a 0 * l.t + a 1 * l.v]
  map_add' a b := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by ext i; fin_cases i <;> simp <;> ring

/-- The homogeneous two-dimensional subspace of a chart line. -/
def lineSpace (l : ChartLine K) : Submodule K (Fin 4 → K) :=
  LinearMap.range (lineMap l)

theorem lineMap_injective (l : ChartLine K) : Function.Injective (lineMap l) := by
  intro a b h
  ext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1

theorem finrank_lineSpace (l : ChartLine K) : Module.finrank K (lineSpace l) = 2 := by
  rw [lineSpace, LinearMap.finrank_range_of_inj (lineMap_injective l)]
  exact Module.finrank_fin_fun K

theorem mem_lineSpace_iff (l : ChartLine K) (w : Fin 4 → K) :
    w ∈ lineSpace l ↔
      w 2 = w 0 * l.s + w 1 * l.u ∧ w 3 = w 0 * l.t + w 1 * l.v := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨h₂, h₃⟩
    refine ⟨![w 0, w 1], ?_⟩
    ext i
    fin_cases i <;> simp [lineMap, h₂, h₃]

theorem homogenize_linePoint_eq (l : ChartLine K) (x : K) :
    homogenize (linePoint l x) = lineMap l ![1, x] := by
  ext i
  fin_cases i <;> simp [homogenize, linePoint, lineMap, mul_comm]

theorem lineSpace_le_of_homogenize_mem (l : ChartLine K)
    (P : Submodule K (Fin 4 → K))
    (h : ∀ x : K, homogenize (linePoint l x) ∈ P) : lineSpace l ≤ P := by
  have h₀ : lineMap l ![1, 0] ∈ P := by
    rw [← homogenize_linePoint_eq]
    exact h 0
  have h₁ : lineMap l ![0, 1] ∈ P := by
    have he : (![0, 1] : Fin 2 → K) = ![1, 1] - ![1, 0] := by
      ext i; fin_cases i <;> simp
    rw [he, map_sub]
    exact P.sub_mem (by rw [← homogenize_linePoint_eq]; exact h 1) h₀
  rintro _ ⟨a, rfl⟩
  have he : a = a 0 • ![1, 0] + a 1 • ![0, 1] := by
    ext i; fin_cases i <;> simp
  rw [he, map_add, map_smul, map_smul]
  exact P.add_mem (P.smul_mem _ h₀) (P.smul_mem _ h₁)

theorem lineSpace_injective : Function.Injective (lineSpace (K := K)) := by
  intro l m h
  have h₀ : lineMap l ![1, 0] ∈ lineSpace m := h ▸ ⟨![1, 0], rfl⟩
  have h₁ : lineMap l ![0, 1] ∈ lineSpace m := h ▸ ⟨![0, 1], rfl⟩
  rw [mem_lineSpace_iff] at h₀ h₁
  simp only [lineMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, one_mul, zero_mul,
    add_zero, zero_add] at h₀ h₁
  cases l
  cases m
  simp_all only

theorem coplanar_iff_nonzero_mem (l m : ChartLine K) :
    Coplanar l m ↔ ∃ w : Fin 4 → K, w ≠ 0 ∧ w ∈ lineSpace l ∧ w ∈ lineSpace m := by
  let M : Matrix (Fin 2) (Fin 2) K :=
    !![l.s - m.s, l.u - m.u; l.t - m.t, l.v - m.v]
  have hdet : Coplanar l m ↔ M.det = 0 := by
    simp only [Coplanar, M, Matrix.det_fin_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm (l.u - m.u) (l.t - m.t)]
  rw [hdet, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨a, ha, hMa⟩
    refine ⟨lineMap l a, ?_, ⟨a, rfl⟩, ?_⟩
    · intro hzero
      exact ha (lineMap_injective l (hzero.trans (map_zero (lineMap l)).symm))
    · have h₀ := congrFun hMa 0
      have h₁ := congrFun hMa 1
      simp only [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h₀ h₁
      rw [mem_lineSpace_iff]
      change (a 0 * l.s + a 1 * l.u = a 0 * m.s + a 1 * m.u) ∧
        (a 0 * l.t + a 1 * l.v = a 0 * m.t + a 1 * m.v)
      constructor
      · linear_combination h₀
      · linear_combination h₁
  · rintro ⟨w, hw, hl, hm⟩
    obtain ⟨a, rfl⟩ := hl
    refine ⟨a, ?_, ?_⟩
    · intro ha
      exact hw (ha ▸ map_zero (lineMap l))
    · rw [mem_lineSpace_iff] at hm
      change (a 0 * l.s + a 1 * l.u = a 0 * m.s + a 1 * m.u) ∧
        (a 0 * l.t + a 1 * l.v = a 0 * m.t + a 1 * m.v) at hm
      ext i
      fin_cases i <;>
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply]
      · change (l.s - m.s) * a 0 + (l.u - m.u) * a 1 = 0
        linear_combination hm.1
      · change (l.t - m.t) * a 0 + (l.v - m.v) * a 1 = 0
        linear_combination hm.2

end ExplicitRIP.Zahl.Rulings
