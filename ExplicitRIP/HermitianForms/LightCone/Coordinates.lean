/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.Defs.SphereCoords
public import ExplicitRIP.HermitianForms.TracePairing.Basic
public import ExplicitRIP.HermitianForms.RankOne.Basic

/-!
# Sphere coordinates and their inverse

The sphere map identifies the Hermitian-forms model of `VO₄⁻(p)` with the contact-coordinate
model of [KM, Section 4.1]. In these coordinates the trace pairing is twice the ordinary dot
product, and the determinant is `r² - x² - y² - z²`.
-/

@[expose] public section

namespace ExplicitRIP.LightCone

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- The ordinary dot product on the four sphere coordinates. -/
def dot (x y : ZMod p × ZMod p × ZMod p × ZMod p) : ZMod p :=
  x.1 * y.1 + x.2.1 * y.2.1 + x.2.2.1 * y.2.2.1 + x.2.2.2 * y.2.2.2

/-- The inverse of the sphere-coordinate change recovers `(a, b₁, b₂, c)`. -/
def sphereEquiv :
    (ZMod p × ZMod p × ZMod p × ZMod p) ≃ₗ[ZMod p]
      (ZMod p × ZMod p × ZMod p × ZMod p) where
  map_add' := by intros; ext <;> dsimp [sphereCoords] <;> ring
  map_smul' := by intros; ext <;> dsimp [sphereCoords] <;> ring
  toFun := sphereCoords p
  invFun x := (x.2.2.2 + x.2.2.1, x.1, x.2.1, x.2.2.2 - x.2.2.1)
  left_inv K := by
    dsimp [sphereCoords]
    ext <;> field_simp [Trace.two_ne_zero p] <;> ring
  right_inv x := by
    dsimp [sphereCoords]
    ext <;> field_simp [Trace.two_ne_zero p] <;> ring

@[simp]
theorem sphereEquiv_apply (K : ZMod p × ZMod p × ZMod p × ZMod p) :
    sphereEquiv p K = sphereCoords p K := rfl

@[simp]
theorem sphereCoords_zero : sphereCoords p 0 = 0 := by
  simp only [sphereCoords, sub_self, zero_add, zero_div, Prod.zero_eq_mk]

/-- Doubling sphere coordinates is a bijection on the whole vertex space. -/
def frequencyEquiv :
    (ZMod p × ZMod p × ZMod p × ZMod p) ≃
      (ZMod p × ZMod p × ZMod p × ZMod p) :=
  (sphereEquiv p).toEquiv.trans (Equiv.smulRight (Trace.two_ne_zero p))

@[simp]
theorem frequencyEquiv_apply (K : ZMod p × ZMod p × ZMod p × ZMod p) :
    frequencyEquiv p K = (2 : ZMod p) • sphereCoords p K := rfl

@[simp]
theorem frequencyEquiv_zero : frequencyEquiv p 0 = 0 := by
  rw [frequencyEquiv_apply, sphereCoords_zero, smul_zero]

theorem sphereCoords_radius_add_height (K : ZMod p × ZMod p × ZMod p × ZMod p) :
    (sphereCoords p K).2.2.2 + (sphereCoords p K).2.2.1 = K.1 := by
  dsimp only [sphereCoords]
  field_simp [Trace.two_ne_zero p]
  ring

theorem sphereCoords_radius_sub_height (K : ZMod p × ZMod p × ZMod p × ZMod p) :
    (sphereCoords p K).2.2.2 - (sphereCoords p K).2.2.1 = K.2.2.2 := by
  dsimp only [sphereCoords]
  field_simp [Trace.two_ne_zero p]
  ring

theorem tracePairing_eq_dot (H K : ZMod p × ZMod p × ZMod p × ZMod p) :
    tracePairing p H K = 2 * dot p (sphereCoords p H) (sphereCoords p K) := by
  dsimp only [tracePairing, dot, sphereCoords]
  field_simp [Trace.two_ne_zero p]
  ring

theorem hermitian_det_eq_sphereCoords (K : ZMod p × ZMod p × ZMod p × ZMod p) :
    (hermitianMatrix p K).det =
      ⟨(sphereCoords p K).2.2.2 ^ 2 - (sphereCoords p K).1 ^ 2 -
        (sphereCoords p K).2.1 ^ 2 - (sphereCoords p K).2.2.1 ^ 2, 0⟩ := by
  rw [Rank1.hermitian_det]
  apply QuadraticAlgebra.ext
  · dsimp only [sphereCoords]
    field_simp [Trace.two_ne_zero p]
    ring
  · rfl

omit [Fact (p % 4 = 3)] in
theorem dot_smul_right (x y : ZMod p × ZMod p × ZMod p × ZMod p) (c : ZMod p) :
    dot p x (c • y) = c * dot p x y := by
  change x.1 * (c * y.1) + x.2.1 * (c * y.2.1) +
      x.2.2.1 * (c * y.2.2.1) + x.2.2.2 * (c * y.2.2.2) =
    c * (x.1 * y.1 + x.2.1 * y.2.1 + x.2.2.1 * y.2.2.1 + x.2.2.2 * y.2.2.2)
  ring

end ExplicitRIP.LightCone
