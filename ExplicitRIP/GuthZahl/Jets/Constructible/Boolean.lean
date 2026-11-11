/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma

/-!
# Finite Boolean descriptions of constructible subsets of prime spectra

Enumerate all the equations and inequalities in a finite constructible
description. The acceptance set records the disjunction of its pieces.
-/

public section

namespace ExplicitRIP.GuthZahl.Constructible

open Classical in
/-- Membership in a constructible subset of a prime spectrum is determined by
the membership pattern of finitely many ring elements in the prime ideal. -/
theorem exists_boolean_description {R : Type*} [CommSemiring R]
    (S : Set (PrimeSpectrum R)) (hS : Topology.IsConstructible S) :
    ∃ J : ℕ, ∃ q : Fin J → R, ∃ B : Set (Fin J → Bool),
      ∀ P : PrimeSpectrum R,
        P ∈ S ↔ (fun j => decide (q j ∈ P.asIdeal)) ∈ B := by
  obtain ⟨D, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hS
  -- In each piece, `none` indexes the inequality and `some i` the i-th equation.
  let ι := Σ C : D, Option (Fin C.val.n)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let q₀ : ι → R := fun ⟨C, i⟩ => i.elim C.val.f C.val.g
  let q := q₀ ∘ e.symm
  have hq (C : D) (i : Option (Fin C.val.n)) :
      q (e ⟨C, i⟩) = i.elim C.val.f C.val.g := by
    change q₀ (e.symm (e ⟨C, i⟩)) = _
    rw [e.symm_apply_apply]
  let B : Set (Fin (Fintype.card ι) → Bool) :=
    {b | ∃ C : D, b (e ⟨C, none⟩) = false ∧ ∀ i, b (e ⟨C, some i⟩) = true}
  refine ⟨Fintype.card ι, q, B, ?_⟩
  intro P
  have hmem (C : PrimeSpectrum.BasicConstructibleSetData R) :
      P ∈ C.toSet ↔ (∀ i, C.g i ∈ P.asIdeal) ∧ C.f ∉ P.asIdeal := by
    simp only [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff,
      PrimeSpectrum.mem_zeroLocus, Set.range_subset_iff, Set.singleton_subset_iff,
      SetLike.mem_coe]
  have hD : P ∈ D.toSet ↔ ∃ C ∈ D, P ∈ C.toSet := by
    simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion, exists_prop]
  rw [hD]
  constructor
  · rintro ⟨C, hC, hP⟩
    obtain ⟨hg, hf⟩ := (hmem C).mp hP
    refine ⟨⟨C, hC⟩, ?_, ?_⟩
    · change decide (q (e ⟨⟨C, hC⟩, none⟩) ∈ P.asIdeal) = false
      rw [hq]
      exact decide_eq_false_iff_not.mpr hf
    · intro i
      change decide (q (e ⟨⟨C, hC⟩, some i⟩) ∈ P.asIdeal) = true
      rw [hq]
      exact decide_eq_true_eq.mpr (hg i)
  · rintro ⟨C, hf, hg⟩
    refine ⟨C.val, C.property, (hmem C.val).mpr ⟨?_, ?_⟩⟩
    · intro i
      have hi : decide (q (e ⟨C, some i⟩) ∈ P.asIdeal) = true := hg i
      rw [hq] at hi
      exact decide_eq_true_eq.mp hi
    · change decide (q (e ⟨C, none⟩) ∈ P.asIdeal) = false at hf
      rw [hq] at hf
      exact decide_eq_false_iff_not.mp hf

end ExplicitRIP.GuthZahl.Constructible

end
