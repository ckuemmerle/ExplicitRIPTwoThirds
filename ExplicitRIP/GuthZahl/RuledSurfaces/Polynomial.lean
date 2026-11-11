/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Basic.Restriction
public import ExplicitRIP.GuthZahl.Basic.PrincipalOpen

/-!
# Polynomial consequences of irreducible hypersurfaces

The Nullstellensatz is used only through Mathlib's proved radical-ideal
identity. Vanishing on an irreducible hypersurface, or on a nonempty principal
open in it, forces polynomial divisibility.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- An irreducible polynomial over a field has positive total degree. -/
theorem totalDegree_pos_of_irreducible {f : Poly K} (hf : Irreducible f) :
    0 < f.totalDegree := by
  by_contra h
  have heq : f = MvPolynomial.C (f.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_not_pos h)
  have hc : f.coeff 0 ≠ 0 := by
    intro hc
    apply hf.ne_zero
    rw [heq, hc, map_zero]
  exact hf.not_isUnit (heq.symm ▸ (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C)

/-- The zero locus of the principal ideal agrees with the literal hypersurface. -/
theorem zeroLocus_span_singleton (f : Poly K) :
    MvPolynomial.zeroLocus K (Ideal.span ({f} : Set (Poly K))) =
      {x : Point K | MvPolynomial.eval x f = 0} := by
  rw [MvPolynomial.zeroLocus_span]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq,
    MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id]

/-- A polynomial vanishing on a principal open is divisible by its irreducible equation. -/
theorem dvd_of_eval_eq_zero_on_principalOpen [IsAlgClosed K] {f g q : Poly K}
    (hf : Irreducible f) (hg : ¬ f ∣ g)
    (hq : ∀ x ∈ principalOpen f g, MvPolynomial.eval x q = 0) : f ∣ q := by
  have hprod : f ∣ g * q := by
    apply dvd_of_vanishes_on_irreducible _ _ hf
    intro x hx
    rw [map_mul]
    by_cases hgx : MvPolynomial.eval x g = 0
    · rw [hgx, zero_mul]
    · rw [hq x ⟨hx, hgx⟩, mul_zero]
  exact (hf.prime.dvd_mul.mp hprod).resolve_left hg

/-- Two allowable principal opens intersect. -/
theorem principalOpen_mul_nonempty [IsAlgClosed K] {f g h : Poly K}
    (hf : Irreducible f) (hg : ¬ f ∣ g) (hh : ¬ f ∣ h) :
    (principalOpen f (g * h)).Nonempty :=
  principalOpen_nonempty _ _ hf (fun hgh => (hf.prime.dvd_mul.mp hgh).elim hg hh)

/-- A nonplane irreducible polynomial dividing a polynomial of degree at most two
has degree exactly two. -/
theorem totalDegree_eq_two_of_dvd {f q : Poly K} (hf : Irreducible f)
    (hnonplane : f.totalDegree ≠ 1) (hdiv : f ∣ q) (hq : q ≠ 0)
    (hdegree : q.totalDegree ≤ 2) : f.totalDegree = 2 := by
  have hpos := totalDegree_pos_of_irreducible hf
  have hle := (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hq).trans hdegree
  omega

end ExplicitRIP.GuthZahl.RuledSurfaces
end
