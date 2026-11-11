/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Contagion.Defs
import ExplicitRIP.GuthZahl.Contagion.Patterns
import ExplicitRIP.GuthZahl.Components.CommonLineCounts
import ExplicitRIP.GuthZahl.Components.Factors.Degree

/-!
# Contagion for finite Boolean polynomial conditions

More accepted lines than the exceptional-line bound force the surface's generic
zero pattern to be accepted. The resulting principal open proves contagion.
For bounded Boolean data, the constant `4 * b ^ 2 + 1` supplies strict slack
for both the line count and the number of accepted points on each line.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- A Boolean condition holding at sufficiently many points on sufficiently many contained lines
holds on a nonempty principal open of the irreducible surface. -/
theorem boolean_condition_contagion {K : Type*} [Field K] [IsAlgClosed K]
    {J : ℕ} (f : Poly K) (hf : Irreducible f) (qs : Fin J → Poly K)
    (B : Set (Fin J → Bool)) (Ls : Finset (Line K))
    (hcard : 2 * f.totalDegree * (∑ j, (qs j).totalDegree) < Ls.card)
    (hLs : ∀ L ∈ Ls, LineOn f L ∧
      ((∑ j, (qs j).totalDegree : ℕ) : ℕ∞) <
        {x : Point K | x ∈ L.1 ∧ zeroPattern qs x ∈ B}.encard) :
    ∃ g : Poly K, ¬ f ∣ g ∧ (principalOpen f g).Nonempty ∧
      ∀ x ∈ principalOpen f g, zeroPattern qs x ∈ B := by
  have hsurface : surfaceGenericPattern f qs ∈ B := by
    by_contra hnot
    have hfilter :
        Ls.filter (fun L => lineGenericPattern qs L ≠ surfaceGenericPattern f qs) = Ls := by
      apply Finset.filter_eq_self.mpr
      intro L hL heq
      apply hnot
      rw [← heq]
      exact line_generic_pattern_accepted qs B L (hLs L hL).2
    have hbound := surface_exceptional_lines_bound f hf qs Ls
      (fun L hL => (hLs L hL).1)
    rw [hfilter] at hbound
    exact (not_le_of_gt hcard) hbound
  obtain ⟨g, hfg, hnonempty, hpattern⟩ := surface_generic_pattern_open f hf qs
  refine ⟨g, hfg, hnonempty, ?_⟩
  intro x hx
  rw [hpattern x hx]
  exact hsurface

open Classical in
/-- For at most `b` tests of degree at most `b * (deg f + 1)`, the constant `4 * b² + 1` gives
explicit line and point thresholds for Boolean contagion. -/
theorem bounded_boolean_contagion {K : Type*} [Field K] [IsAlgClosed K]
    (b J : ℕ) (hb : 0 < b) (hJ : J ≤ b)
    (f : Poly K) (hf : Irreducible f) (qs : Fin J → Poly K)
    (hdeg : ∀ j, (qs j).totalDegree ≤ b * (f.totalDegree + 1))
    (B : Set (Fin J → Bool)) (Ls : Finset (Line K))
    (hcard : (4 * b ^ 2 + 1) * f.totalDegree ^ 2 ≤ Ls.card)
    (hLs : ∀ L ∈ Ls, LineOn f L ∧
      (((4 * b ^ 2 + 1) * f.totalDegree : ℕ) : ℕ∞) ≤
        {x : Point K | x ∈ L.1 ∧ zeroPattern qs x ∈ B}.encard) :
    ∃ g : Poly K, ¬ f ∣ g ∧ (principalOpen f g).Nonempty ∧
      ∀ x ∈ principalOpen f g, zeroPattern qs x ∈ B := by
  have hd : 1 ≤ f.totalDegree := Factors.one_le_totalDegree_of_irreducible hf
  have hsum : (∑ j, (qs j).totalDegree) ≤ 2 * b ^ 2 * f.totalDegree := by
    calc
      _ ≤ ∑ _j : Fin J, b * (f.totalDegree + 1) :=
        Finset.sum_le_sum (fun j _ => hdeg j)
      _ = J * (b * (f.totalDegree + 1)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ b * (b * (f.totalDegree + 1)) := Nat.mul_le_mul_right _ hJ
      _ ≤ b * (b * (2 * f.totalDegree)) :=
        Nat.mul_le_mul_left b (Nat.mul_le_mul_left b (by omega))
      _ = 2 * b ^ 2 * f.totalDegree := by ring
  have hpoint : (∑ j, (qs j).totalDegree) < (4 * b ^ 2 + 1) * f.totalDegree := by
    apply hsum.trans_lt
    apply Nat.mul_lt_mul_of_pos_right _ hd
    exact (Nat.mul_lt_mul_of_pos_right (by decide : 2 < 4) (pow_pos hb 2)).trans
      (Nat.lt_succ_self _)
  have hlines : 2 * f.totalDegree * (∑ j, (qs j).totalDegree) <
      (4 * b ^ 2 + 1) * f.totalDegree ^ 2 := by
    calc
      _ ≤ 2 * f.totalDegree * (2 * b ^ 2 * f.totalDegree) :=
        Nat.mul_le_mul_left _ hsum
      _ = 4 * b ^ 2 * f.totalDegree ^ 2 := by ring
      _ < (4 * b ^ 2 + 1) * f.totalDegree ^ 2 :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (pow_pos hd 2)
  apply boolean_condition_contagion f hf qs B Ls (hlines.trans_le hcard)
  intro L hL
  exact ⟨(hLs L hL).1,
    (ENat.natCast_lt_natCast.mpr hpoint).trans_le (hLs L hL).2⟩

end ExplicitRIP.GuthZahl

end
