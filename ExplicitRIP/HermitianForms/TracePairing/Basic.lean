/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.Defs.HermitianMatrix
public import ExplicitRIP.HermitianForms.Defs.TracePairing

/-!
# The coordinate trace pairing

The trace of the product of two Hermitian matrices defines a symmetric nondegenerate bilinear
form on their four base-field coordinates.
-/

@[expose] public section

namespace ExplicitRIP.Trace

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- Multiplication of the two Hermitian matrices gives the coordinate pairing. -/
theorem matrix_trace_mul (H K : ZMod p × ZMod p × ZMod p × ZMod p) :
    (hermitianMatrix p H * hermitianMatrix p K).trace = ⟨tracePairing p H K, 0⟩ := by
  rw [Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  apply QuadraticAlgebra.ext <;> dsimp [hermitianMatrix, tracePairing] <;> ring

/-- The trace pairing bundled as a bilinear form on the four coordinates. -/
def form : LinearMap.BilinForm (ZMod p) (ZMod p × ZMod p × ZMod p × ZMod p) :=
  LinearMap.mk₂ (ZMod p) (tracePairing p)
    (by
      intro H K L
      dsimp [tracePairing]
      ring)
    (by
      intro r H K
      dsimp [tracePairing]
      ring)
    (by
      intro H K L
      dsimp [tracePairing]
      ring)
    (by
      intro r H K
      dsimp [tracePairing]
      ring)

@[simp]
theorem form_apply (H K : ZMod p × ZMod p × ZMod p × ZMod p) :
    form p H K = tracePairing p H K := rfl

theorem form_isSymm : (form p).IsSymm := by
  constructor
  intro H K
  change tracePairing p H K = tracePairing p K H
  dsimp only [tracePairing]
  ring

/-- The modulus assumption implies that the weight of each off-diagonal coordinate is nonzero. -/
theorem two_ne_zero : (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hd
  have hpmod : p % 4 = 3 := Fact.out
  omega

theorem form_separatingLeft : (form p).SeparatingLeft := by
  intro H hH
  have ha : H.1 = 0 := by
    simpa only [form_apply, tracePairing, mul_one, mul_zero, add_zero] using hH (1, 0, 0, 0)
  have hb₁ : 2 * H.2.1 = 0 := by
    simpa only [form_apply, tracePairing, mul_one, mul_zero, zero_add, add_zero]
      using hH (0, 1, 0, 0)
  have hb₂ : 2 * H.2.2.1 = 0 := by
    simpa only [form_apply, tracePairing, mul_one, mul_zero, zero_add, add_zero]
      using hH (0, 0, 1, 0)
  have hc : H.2.2.2 = 0 := by
    simpa only [form_apply, tracePairing, mul_one, mul_zero, zero_add, add_zero]
      using hH (0, 0, 0, 1)
  have hb₁' : H.2.1 = 0 := (mul_eq_zero.mp hb₁).resolve_left (two_ne_zero p)
  have hb₂' : H.2.2.1 = 0 := (mul_eq_zero.mp hb₂).resolve_left (two_ne_zero p)
  exact Prod.ext ha (Prod.ext hb₁' (Prod.ext hb₂' hc))

theorem form_nondegenerate : (form p).Nondegenerate :=
  (form_isSymm p).isRefl.nondegenerate_iff_separatingLeft.mpr (form_separatingLeft p)

end ExplicitRIP.Trace
