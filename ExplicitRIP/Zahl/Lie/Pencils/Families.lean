/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Lie.Pencils.Affine

/-!
# Point and direction pencils

The direction fibers and the lines through a Heisenberg point are affine null
lines. Their explicit parameters also distinguish the indexing points and
separate finite point pencils from direction pencils.
-/

@[expose] public section

namespace ExplicitRIP.Zahl

variable {F : Type*} [Field F]

/-- Every fixed direction fiber is a maximal contact pencil. -/
theorem directionPencil_isContactPencil (hn : ¬ IsSquare (-1 : F))
    (v : F × F × F) : ExplicitRIP.IsContactPencil (directionPencil v) := by
  have h2 := two_ne_zero_of_neg_one_not_isSquare hn
  let S : Sphere F := parametersSphere ⟨0, v.1, v.2.1, v.2.2⟩
  let T : Sphere F := parametersSphere ⟨1, v.1, v.2.1, v.2.2⟩
  have hS : sphereParameters S = ⟨0, v.1, v.2.1, v.2.2⟩ :=
    sphereParameters_parametersSphere h2 _
  have hT : sphereParameters T = ⟨1, v.1, v.2.1, v.2.2⟩ :=
    sphereParameters_parametersSphere h2 _
  have hlin (t : F) : sphereParameters (S + t • (T - S)) =
      ⟨t, v.1, v.2.1, v.2.2⟩ := by
    rw [sphereParameters_affine, hS, hT]
    simp only [sub_zero, mul_one, zero_add, sub_self, mul_zero, add_zero]
  have hEq : directionPencil v = affinePencil S T := by
    ext U
    constructor
    · rintro ⟨hb, hc, hd⟩
      refine ⟨(sphereParameters U).a, parameters_injective h2 ?_⟩
      rw [hlin]
      exact HLine.ext rfl hb.symm hc.symm hd.symm
    · rintro ⟨t, rfl⟩
      change (sphereParameters _).b = _ ∧ (sphereParameters _).c = _ ∧
        (sphereParameters _).d = _
      rw [hlin]
      exact ⟨rfl, rfl, rfl⟩
  rw [hEq]
  apply affinePencil_isContactPencil hn S T
  · intro heq
    have ha := congrArg (fun U : Sphere F => (sphereParameters U).a) heq
    rw [hS, hT] at ha
    exact zero_ne_one ha
  · rw [sphereContact_iff_parameters, hS, hT]
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), add_zero, mul_zero]

/-- The sphere through `w` whose line parameter `b` is prescribed. -/
def pointSphere (w : Point (QuadraticExtension F)) (b : F) : Sphere F :=
  parametersSphere
    ⟨(w 2).re - ((w 1).re - b * (w 0).re) * (w 0).re -
        ((w 1).im - b * (w 0).im) * (w 0).im,
      b, (w 1).re - b * (w 0).re, (w 1).im - b * (w 0).im⟩

theorem sphereParameters_pointSphere (h2 : (2 : F) ≠ 0)
    (w : Point (QuadraticExtension F)) (b : F) :
    sphereParameters (pointSphere w b) =
      ⟨(w 2).re - ((w 1).re - b * (w 0).re) * (w 0).re -
        ((w 1).im - b * (w 0).im) * (w 0).im,
       b, (w 1).re - b * (w 0).re, (w 1).im - b * (w 0).im⟩ :=
  sphereParameters_parametersSphere h2 _

theorem pointSphere_mem_pointPencil (h2 : (2 : F) ≠ 0)
    (w : Point (QuadraticExtension F)) (hw : w ∈ heisenberg) (b : F) :
    pointSphere w b ∈ pointPencil w := by
  rw [mem_pointPencil_iff w hw, sphereParameters_pointSphere h2]
  exact ⟨rfl, rfl, rfl⟩

theorem pointSphere_injective (h2 : (2 : F) ≠ 0)
    (w : Point (QuadraticExtension F)) : Function.Injective (pointSphere w) := by
  intro b c h
  have hb := congrArg (fun U : Sphere F => (sphereParameters U).b) h
  simpa only [sphereParameters_pointSphere h2] using hb

theorem pointPencil_eq_range (h2 : (2 : F) ≠ 0)
    (w : Point (QuadraticExtension F)) (hw : w ∈ heisenberg) :
    pointPencil w = Set.range (pointSphere w) := by
  ext S
  constructor
  · intro hS
    obtain ⟨hc, hd, ha⟩ := (mem_pointPencil_iff w hw S).mp hS
    refine ⟨(sphereParameters S).b, parameters_injective h2 ?_⟩
    rw [sphereParameters_pointSphere h2]
    apply HLine.ext
    · dsimp
      rw [← hc, ← hd]
      exact ha.symm
    · rfl
    · exact hc.symm
    · exact hd.symm
  · rintro ⟨b, rfl⟩
    exact pointSphere_mem_pointPencil h2 w hw b

/-- The explicit point family is an affine line with parameter `b`. -/
theorem pointSphere_affine (w : Point (QuadraticExtension F)) (b : F) :
    pointSphere w b = pointSphere w 0 + b • (pointSphere w 1 - pointSphere w 0) := by
  apply Prod.ext
  · dsimp [pointSphere, parametersSphere]
    ring
  apply Prod.ext
  · dsimp [pointSphere, parametersSphere]
    ring
  apply Prod.ext <;> dsimp [pointSphere, parametersSphere] <;> ring

theorem pointPencil_eq_affinePencil (h2 : (2 : F) ≠ 0)
    (w : Point (QuadraticExtension F)) (hw : w ∈ heisenberg) :
    pointPencil w = affinePencil (pointSphere w 0) (pointSphere w 1) := by
  rw [pointPencil_eq_range h2 w hw]
  unfold affinePencil
  congr 1
  funext b
  exact pointSphere_affine w b

/-- The lines through a Heisenberg point give a maximal contact pencil. -/
theorem pointPencil_isContactPencil (hn : ¬ IsSquare (-1 : F))
    (w : Point (QuadraticExtension F)) (hw : w ∈ heisenberg) :
    ExplicitRIP.IsContactPencil (pointPencil w) := by
  have h2 := two_ne_zero_of_neg_one_not_isSquare hn
  rw [pointPencil_eq_affinePencil h2 w hw]
  apply affinePencil_isContactPencil hn
  · intro heq
    exact zero_ne_one (pointSphere_injective h2 w heq)
  · rw [sphereContact_iff_parameters, sphereParameters_pointSphere h2,
      sphereParameters_pointSphere h2]
    dsimp
    ring

/-- Two points of the Heisenberg locus with equal pencils coincide. -/
theorem pointPencil_injOn (h2 : (2 : F) ≠ 0) :
    Set.InjOn (pointPencil : Point (QuadraticExtension F) → Set (Sphere F)) heisenberg := by
  intro w hw z hz hp
  have hmem (b : F) : pointSphere w b ∈ pointPencil z := by
    rw [← hp]
    exact pointSphere_mem_pointPencil h2 w hw b
  have h0 := (mem_pointPencil_iff z hz _).mp (hmem 0)
  have h1 := (mem_pointPencil_iff z hz _).mp (hmem 1)
  simp only [sphereParameters_pointSphere h2, zero_mul, sub_zero] at h0
  simp only [sphereParameters_pointSphere h2, one_mul] at h1
  have hXr : (w 0).re = (z 0).re := by linear_combination h0.1 - h1.1
  have hXi : (w 0).im = (z 0).im := by linear_combination h0.2.1 - h1.2.1
  have hX : w 0 = z 0 := QuadraticAlgebra.ext hXr hXi
  have hY : w 1 = z 1 := QuadraticAlgebra.ext h0.1 h0.2.1
  have hZr : (w 2).re = (z 2).re := by
    rw [hXr, hXi] at h0
    linear_combination h0.2.2
  have hZi : (w 2).im = (z 2).im := by
    change (w 2).im = (w 0 * star (w 1)).im at hw
    change (z 2).im = (z 0 * star (z 1)).im at hz
    rw [hX, hY] at hw
    exact hw.trans hz.symm
  funext j
  fin_cases j
  · exact hX
  · exact hY
  · exact QuadraticAlgebra.ext hZr hZi

/-- A finite point pencil cannot be a fixed direction fiber. -/
theorem pointPencil_ne_directionPencil (h2 : (2 : F) ≠ 0)
    (w : Point (QuadraticExtension F)) (hw : w ∈ heisenberg) (v : F × F × F) :
    pointPencil w ≠ directionPencil v := by
  intro heq
  have h0 := pointSphere_mem_pointPencil h2 w hw 0
  have h1 := pointSphere_mem_pointPencil h2 w hw 1
  rw [heq] at h0 h1
  change (sphereParameters _).b = v.1 ∧ _ at h0 h1
  rw [sphereParameters_pointSphere h2] at h0 h1
  exact zero_ne_one (h0.1.trans h1.1.symm)

end ExplicitRIP.Zahl
