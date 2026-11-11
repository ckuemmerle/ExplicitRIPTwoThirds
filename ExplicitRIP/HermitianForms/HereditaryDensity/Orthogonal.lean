/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.HereditaryDensity.Quadratic

/-!
# Orthogonal planes in the contact space

The four-dimensional contact space has two-dimensional orthogonal complements of planes. This
supplies the plane geometry for the complementary conics described in [KM, Section 4.1].
-/

public section
namespace ExplicitRIP.Edges

variable {F : Type*} [Field F]

open Module Submodule

theorem mb_add_left (x y z : V4 F) : mb (x + y) z = mb x z + mb y z := by
  dsimp [mb]; ring

theorem mb_add_right (x y z : V4 F) : mb x (y + z) = mb x y + mb x z := by
  dsimp [mb]; ring

theorem mb_smul_left (t : F) (x y : V4 F) : mb (t • x) y = t * mb x y := by
  dsimp [mb]; ring

theorem mb_smul_right (t : F) (x y : V4 F) : mb x (t • y) = t * mb x y := by
  dsimp [mb]; ring

theorem mem_orthogonal_pair {u w v : V4 F} (hu : mb u v = 0) (hw : mb w v = 0) :
    v ∈ minkForm.orthogonal (span F ({u, w} : Set (V4 F))) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro x hx
  rcases mem_span_pair.mp hx with ⟨a, b, rfl⟩
  change mb (a • u + b • w) v = 0
  rw [mb_add_left, mb_smul_left, mb_smul_left, hu, hw, mul_zero, mul_zero, add_zero]

/-- Two independent vectors exhaust the common orthogonal plane of another independent pair. -/
theorem orth_pair_span {u w a b c : V4 F}
    (huw : LinearIndependent F ![u, w]) (hab : LinearIndependent F ![a, b])
    (hua : mb u a = 0) (hwb : mb w b = 0) (hub : mb u b = 0) (hwa : mb w a = 0)
    (huc : mb u c = 0) (hwc : mb w c = 0) :
    ∃ α β : F, c = α • a + β • b := by
  let W := span F ({u, w} : Set (V4 F))
  let A := span F ({a, b} : Set (V4 F))
  have hrange (v₁ v₂ : V4 F) : Set.range ![v₁, v₂] = ({v₁, v₂} : Set (V4 F)) := by
    ext v
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hW : finrank F W = 2 := by
    have he : span F (Set.range ![u, w]) = W := congrArg (span F) (hrange u w)
    have hd := congrArg (fun S : Submodule F (V4 F) => finrank F S) he
    exact hd.symm.trans (finrank_span_eq_card huw)
  have hA : finrank F A = 2 := by
    have he : span F (Set.range ![a, b]) = A := congrArg (span F) (hrange a b)
    have hd := congrArg (fun S : Submodule F (V4 F) => finrank F S) he
    exact hd.symm.trans (finrank_span_eq_card hab)
  have horth : finrank F (minkForm.orthogonal W) = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal minkForm_nondegenerate, hW]
    simp only [V4, Module.finrank_prod, Module.finrank_self]
  have hle : A ≤ minkForm.orthogonal W := by
    apply span_le.mpr
    intro x hx
    rcases hx with rfl | rfl
    · exact mem_orthogonal_pair hua hwa
    · exact mem_orthogonal_pair hub hwb
  have heq : A = minkForm.orthogonal W := Submodule.eq_of_le_of_finrank_eq hle (hA.trans horth.symm)
  have hc : c ∈ A := by
    rw [heq]
    exact mem_orthogonal_pair huc hwc
  rcases mem_span_pair.mp hc with ⟨α, β, h⟩
  exact ⟨α, β, h.symm⟩

/-- Four contact equations imply orthogonality of the two differences. -/
theorem mb_sub_eq_zero_of_contacts (h2 : (2 : F) ≠ 0) {x x' y y' : V4 F}
    (hxy : SphereContact x y) (hx'y : SphereContact x' y)
    (hxy' : SphereContact x y') (hx'y' : SphereContact x' y') :
    mb (x' - x) (y' - y) = 0 := by
  have h1 := (contact_iff _ _).mp hxy
  have h2' := (contact_iff _ _).mp hx'y
  have h3 := (contact_iff _ _).mp hxy'
  have h4 := (contact_iff _ _).mp hx'y'
  apply (mul_eq_zero.mp (show 2 * mb (x' - x) (y' - y) = 0 from ?_)).resolve_left h2
  dsimp [mq, mb] at *
  linear_combination h2' + h3 - h1 - h4

end ExplicitRIP.Edges
