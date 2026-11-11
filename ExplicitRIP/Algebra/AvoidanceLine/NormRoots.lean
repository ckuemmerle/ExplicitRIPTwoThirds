/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Algebra.AvoidanceLine.Restriction
public import ExplicitRIP.Frozen.Defs.FieldNorm
import ExplicitRIP.Algebra.FieldNorm

/-!
# Intersections of a line with a translated norm graph

The cubic norm gives a nonvanishing leading coefficient when the projected line direction is
nonzero.

Source: [KM, Section 4.2 and proof of Lemma 7(a)].
-/

@[expose] public section

noncomputable section

namespace ExplicitRIP.Avline

open Polynomial
open scoped Matrix

/-- The three coordinates used by the norm polynomial specification. -/
def coordinates {K : Type*} (w : K × K × K) : Fin 3 → K :=
  ![w.1, w.2.1, w.2.2]

theorem coordinates_add_smul {K : Type*} [CommSemiring K]
    (a b : K × K × K) (t : K) :
    coordinates (a + t • b) = fun i => coordinates a i + coordinates b i * t := by
  funext i
  fin_cases i
  · exact congrArg (fun z => a.1 + z) (mul_comm t b.1)
  · exact congrArg (fun z => a.2.1 + z) (mul_comm t b.2.1)
  · exact congrArg (fun z => a.2.2 + z) (mul_comm t b.2.2)

/-- Each translated norm graph contributes at most three parameters on a nonconstant line. -/
theorem norm_line_card_le (p : ℕ) [Fact p.Prime]
    (a b : ZMod p × ZMod p × ZMod p) (c d τ : ZMod p)
    (hbd : b ≠ 0 ∨ d ≠ 0) :
    (Finset.univ.filter (fun t : ZMod p =>
      ExplicitRIP.fieldNorm p (a + t • b) + τ = c + t * d)).card ≤ 3 := by
  classical
  by_cases hb : b = 0
  · have hd : d ≠ 0 := hbd.resolve_left (not_not.mpr hb)
    apply le_trans (b := 1) _ (by decide)
    apply Finset.card_le_one.mpr
    intro s hs t ht
    have hs' := (Finset.mem_filter.mp hs).2
    have ht' := (Finset.mem_filter.mp ht).2
    rw [hb, smul_zero, add_zero] at hs' ht'
    exact mul_right_cancel₀ hd (add_left_cancel (hs'.symm.trans ht'))
  · obtain ⟨F, hF, _, heval⟩ := (ExplicitRIP.FieldNorm.algebra_spec p).2.2.1
    change ∀ w : ZMod p × ZMod p × ZMod p,
      MvPolynomial.eval (coordinates w) F = ExplicitRIP.fieldNorm p w at heval
    let q : (ZMod p)[X] := restrictLine F (coordinates a) (coordinates b) + C τ -
      affinePolynomial c d
    have hqdeg : q.natDegree ≤ 3 := by
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · exact natDegree_add_le_of_degree_le (restrictLine_natDegree_le hF _ _)
          (by simp only [natDegree_C]; decide)
      · exact (affinePolynomial_natDegree_le c d).trans (by decide)
    have hcoeff : q.coeff 3 = ExplicitRIP.fieldNorm p b := by
      dsimp only [q]
      rw [coeff_sub, coeff_add, restrictLine_coeff hF,
        coeff_eq_zero_of_natDegree_lt ((affinePolynomial_natDegree_le c d).trans_lt
          (by decide))]
      simp only [coeff_C, OfNat.ofNat_ne_zero, ite_false, add_zero, sub_zero]
      exact heval b
    have hq : q ≠ 0 := by
      intro hzero
      have h := (ExplicitRIP.FieldNorm.algebra_spec p).2.2.2.2 b hb
      apply h
      rw [← hcoeff, hzero, coeff_zero]
    have heq (t : ZMod p) : q.eval t = 0 ↔
        ExplicitRIP.fieldNorm p (a + t • b) + τ = c + t * d := by
      dsimp only [q]
      rw [eval_sub, eval_add, eval_C, eval_restrictLine, eval_affinePolynomial,
        ← coordinates_add_smul, heval]
      rw [sub_eq_zero, mul_comm d t]
    have hset : (Finset.univ.filter (fun t : ZMod p =>
        ExplicitRIP.fieldNorm p (a + t • b) + τ = c + t * d)) =
        Finset.univ.filter (fun t : ZMod p => q.eval t = 0) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, heq]
    rw [hset]
    apply le_trans (card_le_degree_of_subset_roots (p := q) ?_) hqdeg
    intro t ht
    exact (mem_roots hq).mpr ((Finset.mem_filter.mp ht).2)

end ExplicitRIP.Avline

end

end
