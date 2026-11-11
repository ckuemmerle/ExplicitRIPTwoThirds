/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.SphereContact
public import ExplicitRIP.HermitianForms.LightCone.Coordinates
public import ExplicitRIP.HermitianForms.HostSRG.Common

/-!
# Quadratic contact geometry

The quadratic contact equation in the sphere coordinates `(x, y, z, r)` of [KM, Section 4.1]
identifies adjacency in the Hermitian-forms model of `VO₄⁻(p)` with contact of oriented spheres.
-/

@[expose] public section

namespace ExplicitRIP.Edges

abbrev V4 (F : Type*) := F × F × F × F

section Field
variable {F : Type*} [Field F]

/-- The quadratic form whose null differences express contact. -/
def mq (x : V4 F) : F := x.1 ^ 2 + x.2.1 ^ 2 + x.2.2.1 ^ 2 - x.2.2.2 ^ 2

/-- The symmetric bilinear form associated with `mq`. -/
def mb (x y : V4 F) : F :=
  x.1 * y.1 + x.2.1 * y.2.1 + x.2.2.1 * y.2.2.1 - x.2.2.2 * y.2.2.2

theorem contact_iff (x y : V4 F) : SphereContact x y ↔ mq (x - y) = 0 := by
  exact sub_eq_zero.symm

@[simp] theorem mq_zero : mq (0 : V4 F) = 0 := by simp [mq]
@[simp] theorem mq_neg (x : V4 F) : mq (-x) = mq x := by simp [mq]
theorem mq_sub_comm (x y : V4 F) : mq (x - y) = mq (y - x) := by
  rw [← mq_neg, neg_sub]

theorem contact_refl (x : V4 F) : SphereContact x x := by
  rw [contact_iff, sub_self, mq_zero]

theorem contact_symm {x y : V4 F} (h : SphereContact x y) : SphereContact y x := by
  rwa [contact_iff, mq_sub_comm, ← contact_iff]

theorem mb_comm (x y : V4 F) : mb x y = mb y x := by dsimp [mb]; ring

theorem mq_add (x y : V4 F) : mq (x + y) = mq x + 2 * mb x y + mq y := by
  dsimp [mq, mb]; ring

theorem mq_sub (x y : V4 F) : mq (x - y) = mq x - 2 * mb x y + mq y := by
  dsimp [mq, mb]; ring

theorem mq_smul (t : F) (x : V4 F) : mq (t • x) = t ^ 2 * mq x := by
  dsimp [mq]; ring

def minkForm : LinearMap.BilinForm F (V4 F) :=
  LinearMap.mk₂ F mb
    (by intros; dsimp [mb]; ring)
    (by intros; dsimp [mb]; ring)
    (by intros; dsimp [mb]; ring)
    (by intros; dsimp [mb]; ring)

@[simp] theorem minkForm_apply (x y : V4 F) : minkForm x y = mb x y := rfl

theorem minkForm_isSymm : (minkForm (F := F)).IsSymm := by
  constructor
  intro x y
  exact mb_comm x y

theorem minkForm_nondegenerate : (minkForm (F := F)).Nondegenerate := by
  have hrefl : LinearMap.IsRefl (minkForm (F := F)) := minkForm_isSymm.isRefl
  apply hrefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  have h1 := hx (1, 0, 0, 0)
  have h2 := hx (0, 1, 0, 0)
  have h3 := hx (0, 0, 1, 0)
  have h4 := hx (0, 0, 0, 1)
  simp only [minkForm_apply, mb, mul_one, mul_zero, zero_add, add_zero, sub_zero,
    zero_sub, neg_eq_zero] at h1 h2 h3 h4
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

/-- The affine line through `x` in direction `y - x`. -/
def lineSet (x y : V4 F) : Set (V4 F) := {z | ∃ t : F, z = x + t • (y - x)}

theorem left_mem_lineSet (x y : V4 F) : x ∈ lineSet x y := ⟨0, by simp⟩
theorem right_mem_lineSet (x y : V4 F) : y ∈ lineSet x y := ⟨1, by simp⟩

theorem contact_of_mem_lineSet {x y z w : V4 F} (hxy : SphereContact x y)
    (hz : z ∈ lineSet x y) (hw : w ∈ lineSet x y) : SphereContact z w := by
  rcases hz with ⟨s, rfl⟩
  rcases hw with ⟨t, rfl⟩
  rw [contact_iff]
  have he : (x + s • (y - x)) - (x + t • (y - x)) = (s - t) • (y - x) := by
    module
  rw [he, mq_smul, mq_sub_comm, (contact_iff x y).mp hxy, mul_zero]

end Field

section Prime
variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

theorem mq_sphereCoords (x : V4 (ZMod p)) :
    mq (sphereCoords p x) = -Hfsrg.quad p x := by
  dsimp [mq, sphereCoords, Hfsrg.quad]
  field_simp [Trace.two_ne_zero p]
  ring

theorem adj_iff_sphereContact (x y : V4 (ZMod p)) :
    (hermitianGraph p).Adj x y ↔ x ≠ y ∧ SphereContact (sphereCoords p x) (sphereCoords p y) := by
  rw [Hfsrg.adj_iff, contact_iff]
  have he : sphereCoords p x - sphereCoords p y = sphereCoords p (x - y) :=
    (map_sub (LightCone.sphereEquiv p) x y).symm
  rw [he, mq_sphereCoords, neg_eq_zero]

end Prime
end ExplicitRIP.Edges
