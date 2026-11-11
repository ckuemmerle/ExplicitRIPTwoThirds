/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Jets.System.Equations

/-!
# A fixed integer polynomial system for two jet directions

The directional coefficient equations and one minor equation give a single
presentation that works over every field, including characteristic two.
-/

public section

namespace ExplicitRIP.GuthZahl
open Classical in
/-- Six direction coordinates and three multipliers for the three minors. The last equation is
u0*m01 + u1*m02 + u2*m12 = 1. -/
theorem fixed_integer_jet_system (r : ℕ) :
    ∃ F : Fin (2 * (r + 1) + 1) → MvPolynomial (JetIndex r ⊕ Fin 9) ℤ,
      ∀ (K : Type*) [Field K] (J : JetIndex r → K),
        JetTwoDirections J ↔ ∃ y : Fin 9 → K, ∀ i,
          MvPolynomial.eval₂ (Int.castRingHom K) (Sum.elim J y) (F i) = 0 := by
  refine ⟨JetSystem.equations r, ?_⟩
  intro K _ J
  constructor
  · rintro ⟨v, w, hv, hw, hnot, hvJ, hwJ⟩
    obtain ⟨u, hu⟩ :=
      (JetSystem.independent_directions_iff_exists_multipliers v w).mp ⟨hv, hw, hnot⟩
    let y : Fin 9 → K := Fin.append v (Fin.append w u)
    refine ⟨y, ?_⟩
    intro i
    by_cases hfirst : i.val < r + 1
    · rw [JetSystem.equations, ite_eq_left hfirst, JetSystem.eval_directionPolynomial]
      simpa only [y, JetSystem.firstDirectionIndex, Fin.append_left] using
        hvJ i.val (Nat.le_of_lt_succ hfirst)
    · by_cases hsecond : i.val < 2 * (r + 1)
      · rw [JetSystem.equations, ite_eq_right hfirst, ite_eq_left hsecond,
          JetSystem.eval_directionPolynomial]
        simpa only [y, JetSystem.secondDirectionIndex, Fin.append_right,
          Fin.append_left] using hwJ (i.val - (r + 1)) (by omega)
      · rw [JetSystem.equations, ite_eq_right hfirst, ite_eq_right hsecond,
          JetSystem.eval_independencePolynomial]
        simp only [y, JetSystem.firstDirectionIndex, JetSystem.secondDirectionIndex,
          JetSystem.multiplierIndex, Fin.append_left, Fin.append_right, hu, sub_self]
  · rintro ⟨y, hy⟩
    let v : Point K := fun i => y (JetSystem.firstDirectionIndex i)
    let w : Point K := fun i => y (JetSystem.secondDirectionIndex i)
    have hlast := hy ⟨2 * (r + 1), by omega⟩
    rw [JetSystem.equations_last, JetSystem.eval_independencePolynomial,
      sub_eq_zero] at hlast
    obtain ⟨hv, hw, hnot⟩ :=
      (JetSystem.independent_directions_iff_exists_multipliers v w).mpr
        ⟨fun i => y (JetSystem.multiplierIndex i), hlast⟩
    refine ⟨v, w, hv, hw, hnot, ?_, ?_⟩
    · intro j hj
      have h := hy ⟨j, by omega⟩
      rw [JetSystem.equations_first r ⟨j, Nat.lt_succ_of_le hj⟩,
        JetSystem.eval_directionPolynomial] at h
      exact h
    · intro j hj
      have h := hy ⟨r + 1 + j, by omega⟩
      rw [JetSystem.equations_second r ⟨j, Nat.lt_succ_of_le hj⟩,
        JetSystem.eval_directionPolynomial] at h
      exact h

end ExplicitRIP.GuthZahl

end
