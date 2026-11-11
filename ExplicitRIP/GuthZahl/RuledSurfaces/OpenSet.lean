/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.Polynomial

/-!
# Principal opens and finite line families

A nonempty principal open of a nonplane irreducible hypersurface cannot be
covered by finitely many affine lines. In particular, the literal double-ruling
hypothesis forces infinitely many algebraically contained lines.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- Every affine line lies on a nonzero polynomial of total degree one. -/
theorem exists_linear_equation (L : Line K) [Infinite K] :
    ∃ q : Poly K, q.totalDegree = 1 ∧ LineOn q L := by
  classical
  obtain ⟨a, v, ha, hv, hv0, hparam⟩ := exists_line_parametrization L
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  obtain ⟨j, hji⟩ := exists_ne i
  let q : Poly K := MvPolynomial.C (v i) * (MvPolynomial.X j - MvPolynomial.C (a j)) -
    MvPolynomial.C (v j) * (MvPolynomial.X i - MvPolynomial.C (a i))
  have hcoeff : q.coeff (Finsupp.single j 1) = v i := by
    simp only [q, mul_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_X, MvPolynomial.coeff_C,
      ↓reduceIte, mul_one]
    have hj0 : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single j 1 := by
      exact Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
    have hij : Finsupp.single i (1 : ℕ) ≠ Finsupp.single j 1 := by
      exact fun h => hji ((Finsupp.single_left_inj one_ne_zero).mp h).symm
    simp only [hj0, hij, ↓reduceIte, mul_zero, sub_zero]
  have hdegree : q.totalDegree = 1 := by
    apply le_antisymm
    · apply (MvPolynomial.totalDegree_sub _ _).trans
      apply max_le
      · apply (MvPolynomial.totalDegree_mul _ _).trans
        simpa only [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X] using
          MvPolynomial.totalDegree_sub_C_le (MvPolynomial.X j : Poly K) (a j)
      · apply (MvPolynomial.totalDegree_mul _ _).trans
        simpa only [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X] using
          MvPolynomial.totalDegree_sub_C_le (MvPolynomial.X i : Poly K) (a i)
    · have hm : Finsupp.single j 1 ∈ q.support := MvPolynomial.mem_support_iff.mpr
        (hcoeff.trans_ne hi)
      simpa only [Finsupp.sum_single_index, mul_one] using MvPolynomial.le_totalDegree hm
  refine ⟨q, hdegree, (lineOn_iff_eval_eq_zero q L).2 ?_⟩
  intro x hx
  obtain ⟨t, rfl⟩ := (hparam x).1 hx
  simp only [q, map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A nonplane irreducible equation cannot divide an affine linear equation. -/
theorem not_dvd_of_totalDegree_eq_one {f q : Poly K} (hf : Irreducible f)
    (hnonplane : f.totalDegree ≠ 1) (hq : q.totalDegree = 1) : ¬ f ∣ q := by
  intro hdiv
  have hq0 : q ≠ 0 := by
    intro hz
    rw [hz, MvPolynomial.totalDegree_zero] at hq
    exact Nat.zero_ne_one hq
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hq0
  have hpos := totalDegree_pos_of_irreducible hf
  rw [hq] at hle
  exact hnonplane (by omega)

/-- A finite product of polynomials not divisible by an irreducible equation
is itself not divisible by that equation. -/
theorem not_dvd_finset_prod {ι : Type*} (s : Finset ι) (qs : ι → Poly K)
    {f : Poly K} (hf : Irreducible f) (hqs : ∀ i ∈ s, ¬ f ∣ qs i) :
    ¬ f ∣ ∏ i ∈ s, qs i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty, isUnit_iff_dvd_one] using hf.not_isUnit
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    intro hdiv
    rcases hf.prime.dvd_mul.mp hdiv with h | h
    · exact hqs i (Finset.mem_insert_self i s) h
    · exact ih (fun j hj => hqs j (Finset.mem_insert_of_mem hj)) h

/-- A principal open contains a point outside the zero sets of finitely many
polynomials not divisible by its irreducible equation. -/
theorem exists_mem_principalOpen_forall_eval_ne_zero [IsAlgClosed K]
    {f g : Poly K} (hf : Irreducible f) (hg : ¬ f ∣ g)
    {ι : Type*} (s : Finset ι) (qs : ι → Poly K)
    (hqs : ∀ i ∈ s, ¬ f ∣ qs i) :
    ∃ x ∈ principalOpen f g, ∀ i ∈ s, MvPolynomial.eval x (qs i) ≠ 0 := by
  obtain ⟨x, hxf, hxg⟩ := principalOpen_mul_nonempty hf hg (not_dvd_finset_prod s qs hf hqs)
  rw [map_mul, mul_ne_zero_iff] at hxg
  refine ⟨x, ⟨hxf, hxg.1⟩, ?_⟩
  have hp := hxg.2
  rw [map_prod, Finset.prod_ne_zero_iff] at hp
  exact hp

/-- No finite collection of lines covers a principal open on a nonplane irreducible surface. -/
theorem exists_mem_principalOpen_forall_not_mem_line [IsAlgClosed K]
    {f g : Poly K} (hf : Irreducible f) (hg : ¬ f ∣ g)
    (hnonplane : f.totalDegree ≠ 1) (Ls : Finset (Line K)) :
    ∃ x ∈ principalOpen f g, ∀ L ∈ Ls, x ∉ L.1 := by
  classical
  choose qs hdegree hline using fun L : Line K => exists_linear_equation L
  obtain ⟨x, hx, hxqs⟩ := exists_mem_principalOpen_forall_eval_ne_zero hf hg Ls qs
    (fun L _ => not_dvd_of_totalDegree_eq_one hf hnonplane (hdegree L))
  refine ⟨x, hx, fun L hL hxL => ?_⟩
  exact hxqs L hL (eval_eq_zero_of_lineOn (hline L) hxL)

/-- A nonplane doubly ruled irreducible surface has infinitely many contained lines. -/
theorem infinite_lines_of_doublyRuled [IsAlgClosed K] {f : Poly K}
    (hf : Irreducible f) (hruled : DoublyRuled f) (hnonplane : f.totalDegree ≠ 1) :
    {L : Line K | LineOn f L}.Infinite := by
  classical
  intro hfinite
  obtain ⟨g, hg, -, hruled⟩ := hruled
  obtain ⟨x, hx, hxLs⟩ := exists_mem_principalOpen_forall_not_mem_line hf hg hnonplane
    hfinite.toFinset
  obtain ⟨L, M, -, hxL, -, hL, -⟩ := hruled x hx
  exact hxLs L (hfinite.mem_toFinset.mpr hL) hxL

end ExplicitRIP.GuthZahl.RuledSurfaces
end
