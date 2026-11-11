/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Basic
public import ExplicitRIP.GuthZahl.Interpolation

/-!
# Interpolation and rich-point loss for polynomial removal

A finite line family has a nonzero common vanishing polynomial of degree at most four
times the square root of its size. Removing the contained lines loses at most the
polynomial's degree many rich points on each remaining line.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- A finite line family has a nonzero vanishing polynomial of degree at most `ceil(sqrt(6n))`. The
empty family admits the polynomial `1`. -/
theorem interpolation_sqrt {K : Type*} [Field K] (Ls : Finset (Line K)) :
    ∃ f : Poly K, f ≠ 0 ∧ (f.totalDegree : ℝ) ≤ 4 * Real.sqrt Ls.card ∧
      ∀ L ∈ Ls, LineOn f L := by
  by_cases hLs : Ls = ∅
  · subst Ls
    refine ⟨1, one_ne_zero, ?_, ?_⟩
    · simp only [MvPolynomial.totalDegree_one, Nat.cast_zero, Finset.card_empty,
        Real.sqrt_zero, mul_zero, le_refl]
    · intro L hL
      exact False.elim (Finset.notMem_empty L hL)
  let d : ℕ := ⌈Real.sqrt (6 * (Ls.card : ℝ))⌉₊
  have hsq : 6 * Ls.card ≤ d ^ 2 := by
    have hreal : 6 * (Ls.card : ℝ) ≤ (d : ℝ) ^ 2 := by
      calc
        _ = Real.sqrt (6 * (Ls.card : ℝ)) ^ 2 :=
          (Real.sq_sqrt (by positivity)).symm
        _ ≤ (d : ℝ) ^ 2 := by
          gcongr
          exact Nat.le_ceil _
    exact_mod_cast hreal
  have hchoose : 6 * Nat.choose (d + 3) 3 = (d + 1) * (d + 2) * (d + 3) := by
    calc
      _ = (d + 1).ascFactorial 3 := by
        simpa only [show Nat.factorial 3 = 6 from rfl] using
          (Nat.ascFactorial_eq_factorial_mul_choose d 3).symm
      _ = _ := by
        simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
        ring
  have hd : Ls.card * (d + 1) < Nat.choose (d + 3) 3 := by
    apply (Nat.mul_lt_mul_left (by decide : 0 < 6)).mp
    rw [hchoose]
    calc
      6 * (Ls.card * (d + 1)) = (6 * Ls.card) * (d + 1) := by ring
      _ ≤ d ^ 2 * (d + 1) := Nat.mul_le_mul_right _ hsq
      _ < ((d + 2) * (d + 3)) * (d + 1) :=
        mul_lt_mul_of_pos_right (by nlinarith only [Nat.zero_le d]) (Nat.succ_pos d)
      _ = (d + 1) * (d + 2) * (d + 3) := by ring
  have hcard : (1 : ℝ) ≤ Ls.card := by
    exact_mod_cast (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hLs))
  have hsqrt : Real.sqrt (6 * (Ls.card : ℝ)) ≤ 3 * Real.sqrt Ls.card := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 3 ^ 2)
      (Nat.cast_nonneg Ls.card)
  have hdegree : (d : ℝ) ≤ 4 * Real.sqrt Ls.card := by
    calc
      _ ≤ Real.sqrt (6 * (Ls.card : ℝ)) + 1 :=
        (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
      _ ≤ 3 * Real.sqrt Ls.card + Real.sqrt Ls.card :=
        add_le_add hsqrt (Real.one_le_sqrt.mpr hcard)
      _ = _ := by ring
  obtain ⟨f, hf, hfd, hlines⟩ := polynomial_interpolation Ls d hd
  exact ⟨f, hf, (Nat.cast_le.mpr hfd).trans hdegree, hlines⟩

open Classical in
/-- Removal of contained lines costs at most deg f rich points on an outside line. -/
theorem rich_points_after_polynomial_removal {K : Type*} [Field K]
    (Ls : Finset (Line K)) (f : Poly K) (L : Line K)
    (hL : L ∈ Ls) (hout : ¬ LineOn f L) :
    (richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard ≤
      (richPoints (Ls.filter (fun M => ¬ LineOn f M)) 2 ∩
        (L.1 : Set (Point K))).ncard + f.totalDegree := by
  let remaining := Ls.filter (fun M => ¬ LineOn f M)
  let zeros : Set (Point K) := {x | x ∈ L.1 ∧ MvPolynomial.eval x f = 0}
  have hLremaining : L ∈ remaining := Finset.mem_filter.mpr ⟨hL, hout⟩
  obtain ⟨hzeros, hbound⟩ :=
    line_hypersurface_bound f L (Finset.mem_filter.mp hLremaining).2
  have hremaining : (richPoints remaining 2 ∩ (L.1 : Set (Point K))).Finite :=
    (richPoints_finite remaining 2 le_rfl).inter_of_left _
  have hsubset : richPoints Ls 2 ∩ (L.1 : Set (Point K)) ⊆
      (richPoints remaining 2 ∩ (L.1 : Set (Point K))) ∪ zeros := by
    intro x hx
    by_cases hzero : MvPolynomial.eval x f = 0
    · exact Or.inr ⟨hx.2, hzero⟩
    · refine Or.inl ⟨?_, hx.2⟩
      change 2 ≤ (remaining.filter (fun M => x ∈ M.1)).card
      have hxrich := hx.1
      change 2 ≤ (Ls.filter (fun M => x ∈ M.1)).card at hxrich
      apply hxrich.trans
      apply Finset.card_le_card
      intro M hM
      obtain ⟨hMs, hxM⟩ := Finset.mem_filter.mp hM
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hMs, ?_⟩, hxM⟩
      intro hMf
      have heval := congrArg (Polynomial.eval (0 : K))
        (hMf x hxM 0 (Submodule.zero_mem _))
      rw [eval_restrictLine] at heval
      exact hzero (by simpa only [zero_smul, add_zero, Polynomial.eval_zero] using heval)
  calc
    _ ≤ ((richPoints remaining 2 ∩ (L.1 : Set (Point K))) ∪ zeros).ncard :=
      Set.ncard_le_ncard hsubset (hremaining.union hzeros)
    _ ≤ (richPoints remaining 2 ∩ (L.1 : Set (Point K))).ncard + zeros.ncard :=
      Set.ncard_union_le _ _
    _ ≤ _ := Nat.add_le_add_left hbound _

end ExplicitRIP.GuthZahl

end
