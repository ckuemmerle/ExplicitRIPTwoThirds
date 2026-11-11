/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Jets.Defs
import ExplicitRIP.GuthZahl.Jets.Constructible
import ExplicitRIP.GuthZahl.Jets.Fiber
import ExplicitRIP.GuthZahl.Jets.Hasse
import ExplicitRIP.GuthZahl.Jets.NormalForm.Transport
import ExplicitRIP.GuthZahl.Jets.System

/-!
# Uniform Boolean normal forms for two tangent directions

A constructible projection over the integers yields one finite list of tests
before any field is chosen. Applying this to the fixed jet system and pulling
the tests back along the finite jet gives a degree bound uniform in the field
and its characteristic.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- The projection of a fixed integer polynomial system has a finite Boolean description that works
over every algebraically closed field. -/
theorem fixed_integer_system_elimination {σ τ : Type*} [Finite σ] [Finite τ]
    (k : ℕ) (F : Fin k → MvPolynomial (σ ⊕ τ) ℤ) :
    ∃ J : ℕ, ∃ q : Fin J → MvPolynomial σ ℤ, ∃ B : Set (Fin J → Bool),
      ∀ (K : Type*) [Field K] [IsAlgClosed K] (x : σ → K),
        (∃ y : τ → K, ∀ i,
          MvPolynomial.eval₂ (Int.castRingHom K) (Sum.elim x y) (F i) = 0) ↔
        integerZeroPattern q x ∈ B := by
  obtain ⟨J, q, B, hB⟩ :=
    integer_constructible_boolean _ (integer_equation_image_constructible k F)
  refine ⟨J, q, B, ?_⟩
  intro K _ _ x
  exact (integer_projection_at_algClosed_point k F x).symm.trans
    (hB (integerEvaluationPrime x))

open Classical in
/-- A fixed finite jet condition has a bounded Boolean polynomial description. There is no
characteristic dependence in M. Coefficient tangency avoids factorial inverses. -/
theorem two_flecnode_normal_form (r : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (K : Type*) [Field K] [IsAlgClosed K] (f : Poly K),
      ∃ J ≤ M, ∃ qs : Fin J → Poly K, ∃ B : Set (Fin J → Bool),
        (∀ j, (qs j).totalDegree ≤ M * (f.totalDegree + 1)) ∧
        ∀ x, TwoTangentDirections f x r ↔ zeroPattern qs x ∈ B := by
  obtain ⟨F, hF⟩ := fixed_integer_jet_system r
  obtain ⟨J, q, B, hB⟩ := fixed_integer_system_elimination (2 * (r + 1) + 1) F
  let D := Finset.univ.sup (fun j => (q j).totalDegree)
  let M := max 1 (max J D)
  have hpos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hJ : J ≤ M := (le_max_left J D).trans (le_max_right 1 (max J D))
  have hD : D ≤ M := (le_max_right J D).trans (le_max_right 1 (max J D))
  refine ⟨M, hpos, ?_⟩
  intro K _ _ f
  refine ⟨J, hJ, (fun j => jetPullback r f (q j)), B, ?_, ?_⟩
  · intro j
    have hj : (q j).totalDegree ≤ D :=
      Finset.le_sup (f := fun i => (q i).totalDegree) (Finset.mem_univ j)
    exact (jetPullback_spec r f (q j)).1.trans
      (Nat.mul_le_mul (hj.trans hD) (Nat.le_succ f.totalDegree))
  · intro x
    rw [Jets.NormalForm.two_tangent_directions_iff_jet,
      Jets.NormalForm.zeroPattern_jetPullback]
    exact (hF K (finiteJet r f x)).trans (hB K (finiteJet r f x))

end ExplicitRIP.GuthZahl

end
