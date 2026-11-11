/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Basic.Restriction

/-!
# Affine coordinate charts for lines

A line with nonzero direction in coordinate `i` has a unique parametrization
whose base coordinate is zero and whose `i`th direction coordinate is one.
These are the three standard charts used for algebraic incidence conditions.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- The affine line with given base point and nonzero direction. -/
noncomputable def lineThrough (a v : Point K) (hv : v ≠ 0) : Line K :=
  ⟨AffineSubspace.mk' a (Submodule.span K {v}), by
    rw [AffineSubspace.direction_mk']
    exact finrank_span_singleton hv⟩

@[simp]
theorem mem_lineThrough (a v x : Point K) (hv : v ≠ 0) :
    x ∈ (lineThrough a v hv).1 ↔ ∃ t : K, a + t • v = x := by
  rw [lineThrough, AffineSubspace.mem_mk', Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    change t • v = x - a at ht
    rw [ht]
    abel
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    change t • v = x - a
    rw [← ht]
    abel

/-- A line is recovered from any base point and nonzero direction on it. -/
theorem lineThrough_eq {L : Line K} {a v : Point K}
    (ha : a ∈ L.1) (hv : v ∈ L.1.direction) (hv0 : v ≠ 0) :
    lineThrough a v hv0 = L := by
  apply Subtype.ext
  change AffineSubspace.mk' a (Submodule.span K {v}) = L.1
  rw [← eq_span_singleton_of_mem_of_finrank_eq_one L.2 hv hv0]
  exact AffineSubspace.mk'_eq ha

/-- Every line belongs to one of the three normalized coordinate charts. -/
theorem exists_normalized_parametrization (L : Line K) :
    ∃ (i : Fin 3) (a v : Point K), a i = 0 ∧ v i = 1 ∧
      a ∈ L.1 ∧ v ∈ L.1.direction ∧
      ∀ x : Point K, x ∈ L.1 ↔ x = a + x i • v := by
  obtain ⟨a, v, ha, hv, hv0, -⟩ := exists_line_parametrization L
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  let a' : Point K := a - (a i / v i) • v
  let v' : Point K := (v i)⁻¹ • v
  have hai : a' i = 0 := by
    dsimp only [a', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ _ hi, sub_self]
  have hvi : v' i = 1 := by
    dsimp only [v', Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hi
  have ha' : a' ∈ L.1 := by
    have := AffineSubspace.vadd_mem_of_mem_direction
      (L.1.direction.smul_mem (-(a i / v i)) hv) ha
    simpa only [a', vadd_eq_add, neg_smul, sub_eq_add_neg, add_comm] using this
  have hv' : v' ∈ L.1.direction := L.1.direction.smul_mem _ hv
  have hv'0 : v' ≠ 0 := by
    intro hz
    have hz' := congrFun hz i
    rw [hvi, Pi.zero_apply] at hz'
    exact one_ne_zero hz'
  refine ⟨i, a', v', hai, hvi, ha', hv', fun x => ?_⟩
  rw [mem_line_iff_exists_smul ha' hv' hv'0]
  constructor
  · rintro ⟨t, ht⟩
    have hti := congrFun ht i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hai, hvi, mul_one, zero_add] at hti
    rw [← hti]
    exact ht.symm
  · intro hx
    exact ⟨x i, hx.symm⟩

/-- In a fixed normalized chart, the base point and direction are uniquely determined. -/
theorem normalized_parametrization_unique {L : Line K} (i : Fin 3)
    {a v b w : Point K} (hai : a i = 0) (hvi : v i = 1)
    (hbi : b i = 0) (hwi : w i = 1)
    (ha : a ∈ L.1) (hv : v ∈ L.1.direction)
    (hb : b ∈ L.1) (hw : w ∈ L.1.direction) : a = b ∧ v = w := by
  have hv0 : v ≠ 0 := by
    intro hz
    exact one_ne_zero (hvi.symm.trans (congrFun hz i))
  obtain ⟨t, ht⟩ := (mem_line_iff_exists_smul ha hv hv0 b).1 hb
  have hti := congrFun ht i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hai, hbi, hvi, mul_one,
    zero_add] at hti
  have hab : a = b := by simpa only [hti, zero_smul, add_zero] using ht
  have hwspan := hw
  rw [eq_span_singleton_of_mem_of_finrank_eq_one L.2 hv hv0] at hwspan
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwspan
  have hci := congrFun hc i
  simp only [Pi.smul_apply, smul_eq_mul, hvi, hwi, mul_one] at hci
  exact ⟨hab, by simpa only [hci, one_smul] using hc⟩

end ExplicitRIP.GuthZahl.RuledSurfaces
end
