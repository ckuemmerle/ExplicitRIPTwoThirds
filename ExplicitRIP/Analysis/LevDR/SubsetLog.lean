/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.LevDR.PrefixLog
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Fin

/-! All-subset estimates and sorting of nonnegative coefficients. -/

public section

open scoped BigOperators

namespace ExplicitRIP.Lev

/-- Reindex a finite sum through an enumeration, extending by zero beyond its length. -/
theorem sum_zero_extension {J M : Type*} [AddCommMonoid M]
    (s : Finset J) (e : Fin s.card ≃ s) (g : J → M) :
    (∑ i ∈ Finset.range s.card,
      if hi : i < s.card then g (e ⟨i, hi⟩) else 0) = ∑ j ∈ s, g j := by
  classical
  rw [Finset.sum_range]
  calc
    (∑ i : Fin s.card, if hi : (i : ℕ) < s.card then g (e ⟨i, hi⟩) else 0) =
        ∑ i : Fin s.card, g (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [i.isLt, dite_true]
    _ = ∑ j : s, g j := e.sum_comp (fun j : s => g j)
    _ = ∑ j ∈ s, g j := Finset.sum_coe_sort s g

end ExplicitRIP.Lev

/-- All-subset square-root bounds imply logarithmic control of arbitrary nonnegative weights. -/
theorem ExplicitRIP.Lev.norm_nonneg_weighted_sum_le_log_of_subset_bounds
    {J : Type*} (s : Finset J) (v : J → ℂ) (a : J → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ j ∈ s, 0 ≤ a j)
    (hsubset : ∀ u : Finset J, u ⊆ s →
      ‖∑ j ∈ u, v j‖ ≤ C * Real.sqrt (u.card : ℝ)) :
    ‖∑ j ∈ s, (a j : ℂ) * v j‖ ≤
      C * Real.sqrt (1 + Real.log (s.card : ℝ)) *
        Real.sqrt (∑ j ∈ s, (a j) ^ 2) :=
by
  classical
  let f : Fin s.card → ℝ := fun i => -a (s.equivFin.symm i)
  let e : Fin s.card ≃ s := (Tuple.sort f).trans s.equivFin.symm
  have horder : Antitone (fun i : Fin s.card => a (e i)) := by
    intro i j hij
    have h := Tuple.monotone_sort f hij
    change -a (e i) ≤ -a (e j) at h
    exact neg_le_neg_iff.mp h
  let A : ℕ → ℝ := fun i => if hi : i < s.card then a (e ⟨i, hi⟩) else 0
  let V : ℕ → ℂ := fun i => if hi : i < s.card then v (e ⟨i, hi⟩) else 0
  have hA (i : ℕ) (_hi : i ≤ s.card) : 0 ≤ A i := by
    dsimp only [A]
    split_ifs with hi
    · exact ha _ (e ⟨i, hi⟩).property
    · exact le_rfl
  have hmono (i : ℕ) (hi : i < s.card) : A (i + 1) ≤ A i := by
    by_cases hn : i + 1 < s.card
    · simpa only [A, hi, hn, dite_true] using
        horder (show (⟨i, hi⟩ : Fin s.card) ≤ ⟨i + 1, hn⟩ from Nat.le_succ i)
    · simpa only [A, hi, hn, dite_true, dite_false] using ha _ (e ⟨i, hi⟩).property
  have hzero : A s.card = 0 := by simp only [A, lt_self_iff_false, dite_false]
  have hprefix (k : ℕ) (hk : k ≤ s.card) :
      ‖∑ i ∈ Finset.range k, V i‖ ≤ C * Real.sqrt (k : ℝ) := by
    let E : {i // i ∈ Finset.range k} ↪ J :=
      { toFun := fun i => (e ⟨i.val, (Finset.mem_range.mp i.property).trans_le hk⟩).val
        inj' := by
          intro i j hij
          have he : e ⟨i.val, (Finset.mem_range.mp i.property).trans_le hk⟩ =
              e ⟨j.val, (Finset.mem_range.mp j.property).trans_le hk⟩ := Subtype.ext hij
          have hfin := e.injective he
          exact Subtype.ext (congrArg Fin.val hfin) }
    let u := (Finset.range k).attach.map E
    have hus : u ⊆ s := by
      intro j hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
      exact (e ⟨i.val, (Finset.mem_range.mp i.property).trans_le hk⟩).property
    have hcard : u.card = k := by
      simp only [u, Finset.card_map, Finset.card_attach, Finset.card_range]
    have hsum : (∑ j ∈ u, v j) = ∑ i ∈ Finset.range k, V i := by
      rw [Finset.sum_map]
      calc
        (∑ i ∈ (Finset.range k).attach, v (E i)) =
            ∑ i ∈ (Finset.range k).attach, V i.val := by
          apply Finset.sum_congr rfl
          intro i _
          have hi : i.val < s.card := (Finset.mem_range.mp i.property).trans_le hk
          simp only [V, hi, dite_true]
          rfl
        _ = ∑ i ∈ Finset.range k, V i := Finset.sum_attach _ _
    simpa only [hsum, hcard] using hsubset u hus
  have hweighted : (∑ i ∈ Finset.range s.card, (A i : ℂ) * V i) =
      ∑ j ∈ s, (a j : ℂ) * v j := by
    calc
      (∑ i ∈ Finset.range s.card, (A i : ℂ) * V i) =
          ∑ i ∈ Finset.range s.card,
            if hi : i < s.card then (a (e ⟨i, hi⟩) : ℂ) * v (e ⟨i, hi⟩) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [A, V, Finset.mem_range.mp hi, dite_true]
      _ = ∑ j ∈ s, (a j : ℂ) * v j :=
        sum_zero_extension s e (fun j => (a j : ℂ) * v j)
  have hsquares : (∑ i ∈ Finset.range s.card, (A i) ^ 2) =
      ∑ j ∈ s, (a j) ^ 2 := by
    calc
      (∑ i ∈ Finset.range s.card, (A i) ^ 2) =
          ∑ i ∈ Finset.range s.card,
            if hi : i < s.card then (a (e ⟨i, hi⟩)) ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [A, Finset.mem_range.mp hi, dite_true]
      _ = ∑ j ∈ s, (a j) ^ 2 := sum_zero_extension s e (fun j => (a j) ^ 2)
  simpa only [hweighted, hsquares] using
    norm_weighted_sum_le_log_of_prefix_bounds s.card V A C hC hA hmono hzero hprefix
