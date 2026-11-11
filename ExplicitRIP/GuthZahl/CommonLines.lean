/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.CommonLines.Coordinates
public import ExplicitRIP.GuthZahl.CommonLines.Elimination
public import ExplicitRIP.GuthZahl.CommonLines.Planar

/-!
# Common lines on relatively prime surfaces

Choose linear coordinates that project the finite family to distinct affine
graphs. A nonzero eliminant has degree at most twice the product of the surface
degrees. A generic plane slice and univariate root counting bound the number of
graphs, hence the number of original lines. This quantitative bound over algebraically
closed fields is used in the component counts and contagion argument.
`RuledSurfaces/CommonLines` instead proves qualitative finiteness over any infinite
field, using minimal primes; the ruled-surface classification uses that result.
-/

public section

namespace ExplicitRIP.GuthZahl

theorem common_surface_lines_bound {K : Type*} [Field K] [IsAlgClosed K]
    (f g : Poly K) (hf : f ≠ 0) (hg : g ≠ 0) (hcop : IsRelPrime f g)
    (Ls : Finset (Line K)) (hLs : ∀ L ∈ Ls, LineOn f L ∧ LineOn g L) :
    Ls.card ≤ 2 * f.totalDegree * g.totalDegree := by
  classical
  by_cases hfd : f.totalDegree = 0
  · have hEmpty : Ls = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun L hL =>
      CommonLines.not_lineOn_of_totalDegree_eq_zero hf hfd L (hLs L hL).1
    simp only [hEmpty, Finset.card_empty, Nat.zero_le]
  by_cases hgd : g.totalDegree = 0
  · have hEmpty : Ls = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun L hL =>
      CommonLines.not_lineOn_of_totalDegree_eq_zero hg hgd L (hLs L hL).2
    simp only [hEmpty, Finset.card_empty, Nat.zero_le]
  obtain ⟨e, a, v, hav, hinj⟩ := CommonLines.exists_separating_coordinates Ls
  let F := CommonLines.pullback e.symm.toLinearMap f
  let G := CommonLines.pullback e.symm.toLinearMap g
  have hF : F ≠ 0 := CommonLines.pullback_ne_zero e.symm hf
  have hG : G ≠ 0 := CommonLines.pullback_ne_zero e.symm hg
  have hFG : IsRelPrime F G := CommonLines.isRelPrime_pullback e.symm hcop
  have hdG : 0 < G.totalDegree := by
    dsimp only [G]
    rw [CommonLines.totalDegree_pullback]
    exact Nat.pos_of_ne_zero hgd
  obtain ⟨R, hR, hdR, hvanish⟩ := CommonLines.exists_common_zero_eliminant F G hF hG hFG hdG
  have hgraphs : ∀ (L : Ls) t, MvPolynomial.eval ![t, e (a L) 2 + t * e (v L) 2] R = 0 := by
    intro L t
    have hx : a L + t • v L ∈ L.val.val :=
      CommonLines.line_add_smul_mem L.val (hav L).1 (hav L).2.1 t
    have hxF : MvPolynomial.eval (e (a L + t • v L)) F = 0 := by
      simpa only [F, CommonLines.eval_pullback, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply] using
        eval_eq_zero_of_lineOn (hLs L.val L.property).1 hx
    have hxG : MvPolynomial.eval (e (a L + t • v L)) G = 0 := by
      simpa only [G, CommonLines.eval_pullback, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply] using
        eval_eq_zero_of_lineOn (hLs L.val L.property).2 hx
    have htail : (fun i : Fin 2 => e (a L + t • v L) i.succ) =
        ![t, e (a L) 2 + t * e (v L) 2] := by
      ext i
      fin_cases i
      · change e (a L + t • v L) 1 = t
        simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          (hav L).2.2.1, (hav L).2.2.2, mul_one, zero_add]
      · change e (a L + t • v L) 2 = e (a L) 2 + t * e (v L) 2
        simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← htail]
    exact hvanish _ hxF hxG
  calc
    Ls.card = Fintype.card Ls := (Fintype.card_coe Ls).symm
    _ ≤ R.totalDegree := CommonLines.card_le_totalDegree_of_graphs
      (fun L => e (a L) 2) (fun L => e (v L) 2) hinj R hR hgraphs
    _ ≤ 2 * F.totalDegree * G.totalDegree := hdR
    _ = 2 * f.totalDegree * g.totalDegree := by
      simp only [F, G, CommonLines.totalDegree_pullback]

end ExplicitRIP.GuthZahl
end
