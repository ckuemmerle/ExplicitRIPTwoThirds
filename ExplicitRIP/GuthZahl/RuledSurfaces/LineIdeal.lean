/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Basic.Restriction

/-!
# The prime ideal of an affine line

The ideal consists of polynomials whose restrictions to the line vanish.
Normalized coordinate equations give two generators, independently of any
intersection-degree estimate.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- The ideal of polynomials algebraically vanishing on a line. -/
noncomputable def lineIdeal (L : Line K) : Ideal (Poly K) where
  carrier := {f | LineOn f L}
  zero_mem' := by
    intro a ha v hv
    exact map_zero _
  add_mem' := by
    intro f g hf hg a ha v hv
    rw [restrictLine_add, hf a ha v hv, hg a ha v hv, add_zero]
  smul_mem' := by
    intro f g hg a ha v hv
    change restrictLine (f * g) a v = 0
    rw [restrictLine_mul, hg a ha v hv, mul_zero]

@[simp]
theorem mem_lineIdeal (L : Line K) (f : Poly K) : f ∈ lineIdeal L ↔ LineOn f L := Iff.rfl

instance lineIdeal_isPrime [Infinite K] (L : Line K) : (lineIdeal L).IsPrime where
  ne_top' := by
    intro h
    have h1 : LineOn (1 : Poly K) L := by
      change (1 : Poly K) ∈ lineIdeal L
      rw [h]
      exact Submodule.mem_top
    obtain ⟨a, ha⟩ := line_nonempty L
    have hz := eval_eq_zero_of_lineOn h1 ha
    rw [map_one] at hz
    exact one_ne_zero hz
  mem_or_mem' := by
    intro f g hfg
    exact (lineOn_mul_iff f g L).1 hfg

/-- The normalized affine equation in coordinate `j` for a parametrized line. -/
noncomputable def lineRelation (a v : Point K) (i j : Fin 3) : Poly K :=
  MvPolynomial.X j - MvPolynomial.C (a j) -
    MvPolynomial.C (v j / v i) * (MvPolynomial.X i - MvPolynomial.C (a i))

@[simp]
theorem eval_lineRelation (a v x : Point K) (i j : Fin 3) :
    MvPolynomial.eval x (lineRelation a v i j) =
      x j - a j - (v j / v i) * (x i - a i) := by
  simp only [lineRelation, map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]

/-- The distinguished coordinate equation is zero. -/
theorem lineRelation_self (a v : Point K) (i : Fin 3) (hi : v i ≠ 0) :
    lineRelation a v i i = 0 := by
  simp only [lineRelation, div_self hi, map_one, one_mul, sub_self]

/-- Each normalized coordinate relation vanishes algebraically on its line. -/
theorem lineRelation_mem [Infinite K] {L : Line K} {a v : Point K}
    (ha : a ∈ L.1) (hv : v ∈ L.1.direction) (i j : Fin 3) (hi : v i ≠ 0) :
    lineRelation a v i j ∈ lineIdeal L := by
  have hv0 : v ≠ 0 := fun h => hi (congrFun h i)
  apply (lineOn_iff_eval_eq_zero _ L).2
  intro x hx
  obtain ⟨t, rfl⟩ := (mem_line_iff_exists_smul ha hv hv0 x).1 hx
  rw [eval_lineRelation]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
  field_simp
  ring

/-- Two normalized coordinate equations generate the ideal of a line. -/
theorem lineIdeal_eq_span_relations [Infinite K] {L : Line K} {a v : Point K}
    (ha : a ∈ L.1) (hv : v ∈ L.1.direction) (i : Fin 3) (hi : v i ≠ 0) :
    lineIdeal L = Ideal.span (lineRelation a v i '' {j : Fin 3 | j ≠ i}) := by
  let I : Ideal (Poly K) := Ideal.span (lineRelation a v i '' {j : Fin 3 | j ≠ i})
  have hrel (j : Fin 3) : Ideal.Quotient.mk I (lineRelation a v i j) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    by_cases hji : j = i
    · rw [hji, lineRelation_self a v i hi]
      exact I.zero_mem
    · exact Ideal.subset_span ⟨j, hji, rfl⟩
  let cHom : K →+* (Poly K) ⧸ I := (Ideal.Quotient.mk I).comp MvPolynomial.C
  let z : (Poly K) ⧸ I :=
    Ideal.Quotient.mk I (MvPolynomial.C ((v i)⁻¹) * (MvPolynomial.X i - MvPolynomial.C (a i)))
  have hvar (j : Fin 3) :
      cHom (a j) + cHom (v j) * z = Ideal.Quotient.mk I (MvPolynomial.X j) := by
    have hj := hrel j
    simp only [lineRelation, map_sub, map_mul, div_eq_mul_inv, map_mul] at hj
    dsimp only [cHom, z, RingHom.coe_comp, Function.comp_apply]
    rw [map_mul, map_sub]
    linear_combination -hj
  have hcomm (f : Poly K) :
      Polynomial.eval₂ cHom z (restrictLine f a v) = Ideal.Quotient.mk I f := by
    induction f using MvPolynomial.induction_on with
    | C c =>
      rw [restrictLine_C, Polynomial.eval₂_C]
      rfl
    | add f g hf hg =>
      rw [restrictLine_add, Polynomial.eval₂_add, hf, hg, map_add]
    | mul_X f j hf =>
      rw [restrictLine_mul, Polynomial.eval₂_mul, hf, restrictLine_X,
        Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_X, hvar, map_mul]
  apply le_antisymm
  · intro f hf
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← hcomm, hf a ha v hv, Polynomial.eval₂_zero]
  · apply Ideal.span_le.mpr
    rintro q ⟨j, hj, rfl⟩
    exact lineRelation_mem ha hv i j hi

/-- The prime ideal of an affine line has height at most two. -/
theorem height_lineIdeal_le_two [Infinite K] (L : Line K) : (lineIdeal L).height ≤ 2 := by
  obtain ⟨a, v, ha, hv, hv0, -⟩ := exists_line_parametrization L
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hgen := lineIdeal_eq_span_relations ha hv i hi
  have hproper : Ideal.span (lineRelation a v i '' {j : Fin 3 | j ≠ i}) ≠ ⊤ :=
    hgen ▸ (lineIdeal_isPrime L).ne_top
  rw [hgen]
  apply (Ideal.height_span_le_encard_of_span_ne_top hproper).trans
  apply (Set.encard_image_le _ _).trans
  have hs : {j : Fin 3 | j ≠ i} = Set.univ \ {i} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
  rw [hs, Set.encard_sdiff_singleton_of_mem (Set.mem_univ i), Set.encard_univ]
  norm_num

/-- The ideal of a line determines the line. -/
theorem lineIdeal_injective [Infinite K] : Function.Injective (lineIdeal (K := K)) := by
  intro L M hLM
  apply line_eq_of_le
  obtain ⟨a, v, ha, hv, hv0, -⟩ := exists_line_parametrization M
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  intro x hx
  apply (mem_line_iff_exists_smul ha hv hv0 x).2
  refine ⟨(x i - a i) / v i, ?_⟩
  funext j
  have hq : lineRelation a v i j ∈ lineIdeal L :=
    hLM.symm ▸ lineRelation_mem ha hv i j hi
  have heq := eval_eq_zero_of_lineOn hq hx
  rw [eval_lineRelation, sub_eq_zero] at heq
  change a j + ((x i - a i) / v i) * v j = x j
  have hcomm : ((x i - a i) / v i) * v j = (v j / v i) * (x i - a i) := by ring
  rw [hcomm, ← heq]
  exact add_sub_cancel _ _

end ExplicitRIP.GuthZahl.RuledSurfaces
end
