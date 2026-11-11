/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Defs

/-!
# Basic identities for the Lie correspondence

The coordinate inverses, the contact determinant, the bilinear forms, Heisenberg containment,
cardinalities and the anisotropy of the binary norm.
-/

public section

namespace ExplicitRIP.Zahl

variable {F : Type*} [Field F]

theorem quadraticExtension_card [Fintype F] :
    Fintype.card (QuadraticExtension F) = Fintype.card F ^ 2 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd (-1 : F) 0),
    Fintype.card_prod, pow_two]

theorem two_ne_zero_of_neg_one_not_isSquare (hn : ¬ IsSquare (-1 : F)) :
    (2 : F) ≠ 0 := by
  intro h
  apply hn
  refine ⟨1, ?_⟩
  have hh : (-1 : F) = 1 := by linear_combination -h
  simpa using hh

/-- Change of sphere coordinates, with its exact inverse. -/
theorem parametersSphere_sphereParameters (h2 : (2 : F) ≠ 0) (S : Sphere F) :
    parametersSphere (sphereParameters S) = S := by
  rcases S with ⟨x, y, z, r⟩
  apply Prod.ext
  · simp [parametersSphere, sphereParameters]
  apply Prod.ext
  · simp [parametersSphere, sphereParameters]
  apply Prod.ext <;> dsimp [parametersSphere, sphereParameters] <;>
    field_simp [h2] <;> ring

theorem sphereParameters_parametersSphere (h2 : (2 : F) ≠ 0) (l : HLine F) :
    sphereParameters (parametersSphere l) = l := by
  rcases l with ⟨a, b, c, d⟩
  simp only [parametersSphere, sphereParameters, neg_neg]
  congr 1 <;> field_simp [h2] <;> ring

theorem parameters_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (sphereParameters : Sphere F → HLine F) :=
  Function.LeftInverse.injective (parametersSphere_sphereParameters h2)

theorem HLine.toChart_injective :
    Function.Injective (HLine.toChart : HLine F → ChartLine (QuadraticExtension F)) := by
  intro l m h
  have hs := congrArg ChartLine.s h
  have ht := congrArg ChartLine.t h
  have hu := congrArg ChartLine.u h
  have hc := congrArg QuadraticAlgebra.re hs
  have hd := congrArg QuadraticAlgebra.im hs
  have ha := congrArg QuadraticAlgebra.re ht
  have hb := congrArg QuadraticAlgebra.re hu
  cases l
  cases m
  simp_all [HLine.toChart]

theorem sphereLine_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (sphereLine : Sphere F → ChartLine (QuadraticExtension F)) :=
  HLine.toChart_injective.comp (parameters_injective h2)

/-- The determinant is exactly the sphere-contact quadratic of [KM, Section 4.1]. -/
theorem sphere_contact_determinant (S T : Sphere F) :
    ((sphereLine S).s - (sphereLine T).s) *
        ((sphereLine S).v - (sphereLine T).v) -
      ((sphereLine S).t - (sphereLine T).t) *
        ((sphereLine S).u - (sphereLine T).u) =
      algebraMap F (QuadraticExtension F)
        ((S.1 - T.1) ^ 2 + (S.2.1 - T.2.1) ^ 2 +
          (S.2.2.1 - T.2.2.1) ^ 2 - (S.2.2.2 - T.2.2.2) ^ 2) := by
  apply QuadraticAlgebra.ext <;>
    simp [sphereLine, sphereParameters, HLine.toChart, pow_two] <;> ring

theorem sphereContact_iff_coplanar (S T : Sphere F) :
    ExplicitRIP.SphereContact S T ↔ Coplanar (sphereLine S) (sphereLine T) := by
  unfold Coplanar
  rw [sphere_contact_determinant]
  rw [map_eq_zero_iff _ (algebraMap F (QuadraticExtension F)).injective]
  exact sub_eq_zero.symm

theorem correctedLieMap_kleinForm (q q' : Fin 6 → F) :
    kleinForm (correctedLieMap q) (correctedLieMap q') =
      -algebraMap F (QuadraticExtension F) (lieForm q q') := by
  apply QuadraticAlgebra.ext <;>
    simp [kleinForm, correctedLieMap, lieForm] <;> ring

theorem sphereLieCoordinates_self (S : Sphere F) :
    lieForm (sphereLieCoordinates S) (sphereLieCoordinates S) = 0 := by
  simp [lieForm, sphereLieCoordinates]
  ring

theorem correctedLieMap_sphereLieCoordinates (S : Sphere F) :
    correctedLieMap (sphereLieCoordinates S) = chartPlucker (sphereLine S) := by
  funext j
  fin_cases j <;> apply QuadraticAlgebra.ext <;>
    simp [correctedLieMap, sphereLieCoordinates, chartPlucker,
      sphereLine, sphereParameters, HLine.toChart, pow_two] <;> ring

/-- Every chosen line lies in the Heisenberg group. -/
theorem HLine.linePoints_subset_heisenberg (l : HLine F) :
    linePoints l.toChart ⊆ heisenberg := by
  rintro w ⟨t, rfl⟩
  simp [heisenberg, linePoint, HLine.toChart]
  ring

theorem chartImage_card (L : Finset (HLine F)) : (chartImage L).card = L.card := by
  classical
  exact Finset.card_image_of_injective L HLine.toChart_injective

theorem sphereImage_card (h2 : (2 : F) ≠ 0) (S : Finset (Sphere F)) :
    (sphereImage S).card = S.card := by
  classical
  exact Finset.card_image_of_injective S (sphereLine_injective h2)

open Classical in
theorem sphereImage_eq_chartImage (S : Finset (Sphere F)) :
    sphereImage S = chartImage (S.image sphereParameters) := by
  simp only [sphereImage, chartImage, Finset.image_image]
  rfl

/-- Anisotropy of the binary norm; the only nonsquare-dependent algebraic step. -/
theorem sum_sq_eq_zero_iff (hn : ¬ IsSquare (-1 : F)) (c d : F) :
    c ^ 2 + d ^ 2 = 0 ↔ c = 0 ∧ d = 0 := by
  have : Fact (¬ IsSquare (-1 : F)) := ⟨hn⟩
  have hnorm : (⟨c, d⟩ : QuadraticExtension F).norm = c ^ 2 + d ^ 2 := by
    simp [QuadraticAlgebra.norm_def]
    ring
  constructor
  · intro h
    have hz : (⟨c, d⟩ : QuadraticExtension F) = 0 :=
      QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp (hnorm.trans h)
    simpa using QuadraticAlgebra.ext_iff.mp hz
  · rintro ⟨rfl, rfl⟩
    simp

open Classical in
/-- Every subfamily of a chart image is the chart image of a subfamily. -/
theorem exists_chartImage_subfamily {F : Type*} [Field F] (L : Finset (HLine F))
    {S : Finset (ChartLine (QuadraticExtension F))} (hS : S ⊆ chartImage L) :
    ∃ T ⊆ L, chartImage T = S :=
  Finset.subset_image_iff.mp hS

end ExplicitRIP.Zahl
