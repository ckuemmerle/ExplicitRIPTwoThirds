/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Boundary.Defs

/-!
# Coordinates for three skew projective lines

Three pairwise disjoint two-dimensional subspaces of a four-dimensional
vector space can be sent to the two coordinate blocks and their diagonal.
-/

public section

namespace ExplicitRIP.GuthZahl.Boundary.Descent

variable {K : Type*} [Field K]

/-- Two disjoint planes in four-dimensional vector space are complementary. -/
theorem isCompl_of_finrank_two (A B : Submodule K (Fin 4 → K))
    (hA : Module.finrank K A = 2) (hB : Module.finrank K B = 2)
    (hAB : Disjoint A B) : IsCompl A B := by
  refine ⟨hAB, ?_⟩
  rw [codisjoint_iff]
  apply Submodule.eq_top_of_finrank_eq
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hAB.eq_bot, finrank_bot, hA, hB, add_zero] at h
  simpa only [Module.finrank_fin_fun] using h

/-- A common coordinate frame for three pairwise skew projective lines. -/
theorem exists_skew_frame (A B C : Submodule K (Fin 4 → K))
    (hA : Module.finrank K A = 2) (hB : Module.finrank K B = 2)
    (hC : Module.finrank K C = 2)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    ∃ E : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K),
      (∀ x, E x ∈ A ↔ x 2 = 0 ∧ x 3 = 0) ∧
      (∀ x, E x ∈ B ↔ x 0 = 0 ∧ x 1 = 0) ∧
      (∀ x, E x ∈ C ↔ x 0 = x 2 ∧ x 1 = x 3) := by
  classical
  let hcomp := isCompl_of_finrank_two A B hA hB hAB
  let c : (Fin 2 → K) ≃ₗ[K] C := LinearEquiv.ofFinrankEq _ _ (by
    simpa only [Module.finrank_fin_fun] using hC.symm)
  let a : (Fin 2 → K) →ₗ[K] (Fin 4 → K) :=
    (A.projection B hcomp).comp (C.subtype.comp c.toLinearMap)
  let b : (Fin 2 → K) →ₗ[K] (Fin 4 → K) :=
    (B.projection A hcomp.symm).comp (C.subtype.comp c.toLinearMap)
  have ha_mem (u : Fin 2 → K) : a u ∈ A := Submodule.projection_apply_mem _ _
  have hb_mem (u : Fin 2 → K) : b u ∈ B := Submodule.projection_apply_mem _ _
  have hab (u : Fin 2 → K) : a u + b u = (c u : Fin 4 → K) :=
    Submodule.projection_add_projection_eq_self hcomp _
  have ha : Function.Injective a := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    have hm : (c u : Fin 4 → K) ∈ B :=
      (Submodule.projection_apply_eq_zero_iff hcomp).mp hu
    have hz : (c u : Fin 4 → K) = 0 :=
      (Submodule.disjoint_def.mp hBC) _ hm (c u).property
    exact c.injective (Subtype.ext (hz.trans (by simp)))
  have hb : Function.Injective b := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    have hm : (c u : Fin 4 → K) ∈ A :=
      (Submodule.projection_apply_eq_zero_iff hcomp.symm).mp hu
    have hz : (c u : Fin 4 → K) = 0 :=
      (Submodule.disjoint_def.mp hAC) _ hm (c u).property
    exact c.injective (Subtype.ext (hz.trans (by simp)))
  let left : (Fin 4 → K) →ₗ[K] (Fin 2 → K) :=
    LinearMap.pi fun i => LinearMap.proj (if i = 0 then 0 else 1)
  let right : (Fin 4 → K) →ₗ[K] (Fin 2 → K) :=
    LinearMap.pi fun i => LinearMap.proj (if i = 0 then 2 else 3)
  let T : (Fin 4 → K) →ₗ[K] (Fin 4 → K) := a.comp left + b.comp right
  have hT (x : Fin 4 → K) : T x = a ![x 0, x 1] + b ![x 2, x 3] := by
    have hl : left x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    have hr : right x = ![x 2, x 3] := by ext i; fin_cases i <;> rfl
    change a (left x) + b (right x) = _
    rw [hl, hr]
  have hprojA (x : Fin 4 → K) :
      A.projection B hcomp (T x) = a ![x 0, x 1] := by
    rw [hT, map_add, Submodule.projection_apply_of_mem_left hcomp (ha_mem _),
      Submodule.projection_apply_of_mem_right hcomp (hb_mem _), add_zero]
  have hprojB (x : Fin 4 → K) :
      B.projection A hcomp.symm (T x) = b ![x 2, x 3] := by
    rw [hT, map_add, Submodule.projection_apply_of_mem_right hcomp.symm (ha_mem _),
      Submodule.projection_apply_of_mem_left hcomp.symm (hb_mem _), zero_add]
  have hTinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hl : (![x 0, x 1] : Fin 2 → K) = 0 := ha (by
      rw [← hprojA, hx, map_zero, map_zero])
    have hr : (![x 2, x 3] : Fin 2 → K) = 0 := hb (by
      rw [← hprojB, hx, map_zero, map_zero])
    ext i
    fin_cases i
    · exact congrFun hl 0
    · exact congrFun hl 1
    · exact congrFun hr 0
    · exact congrFun hr 1
  let E := LinearEquiv.ofInjectiveEndo T hTinj
  refine ⟨E, ?_, ?_, ?_⟩
  · intro x
    change T x ∈ A ↔ _
    rw [← Submodule.projection_apply_eq_zero_iff hcomp.symm, hprojB,
      b.map_eq_zero_iff hb]
    simp only [funext_iff, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.zero_apply]
  · intro x
    change T x ∈ B ↔ _
    rw [← Submodule.projection_apply_eq_zero_iff hcomp, hprojA,
      a.map_eq_zero_iff ha]
    simp only [funext_iff, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.zero_apply]
  · intro x
    have hd (u : Fin 2 → K) : E ![u 0, u 1, u 0, u 1] = (c u : Fin 4 → K) := by
      change T _ = _
      rw [hT]
      change a ![u 0, u 1] + b ![u 0, u 1] = _
      have hu : (![u 0, u 1] : Fin 2 → K) = u := by
        ext i
        fin_cases i <;> rfl
      rw [hu]
      exact hab u
    constructor
    · intro hx
      obtain ⟨u, hu⟩ := c.surjective ⟨E x, hx⟩
      have he : E ![u 0, u 1, u 0, u 1] = E x := (hd u).trans (congrArg Subtype.val hu)
      have heq := E.injective he
      rw [← heq]
      exact ⟨rfl, rfl⟩
    · rintro ⟨h0, h1⟩
      have heq : x = ![x 0, x 1, x 0, x 1] := by
        ext i
        fin_cases i
        · rfl
        · rfl
        · exact h0.symm
        · exact h1.symm
      have hx' : E x = (c ![x 0, x 1] : Fin 4 → K) :=
        (congrArg E heq).trans (hd ![x 0, x 1])
      rw [hx']
      exact (c _).property

end ExplicitRIP.GuthZahl.Boundary.Descent

end
