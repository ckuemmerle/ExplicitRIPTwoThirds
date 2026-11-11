/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs

/-!
# Total degree of products of irreducible factors

Nonzero products have additive total degree, and an irreducible polynomial over a field
has positive total degree.
-/

public section

namespace ExplicitRIP.GuthZahl
namespace Factors

theorem totalDegree_prod {K : Type*} [Field K] {ι : Type*}
    (s : Finset ι) (f : ι → Poly K) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).totalDegree = ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, MvPolynomial.totalDegree_one, Finset.sum_empty]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      MvPolynomial.totalDegree_mul_of_isDomain
        (hf i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

theorem one_le_totalDegree_of_irreducible {K : Type*} [Field K]
    {f : Poly K} (hf : Irreducible f) : 1 ≤ f.totalDegree := by
  apply Nat.pos_of_ne_zero
  intro hd
  have hconst := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
  have hc0 : f.coeff 0 ≠ 0 := by
    intro h
    apply hf.ne_zero
    rw [hconst, h, map_zero]
  apply hf.not_isUnit
  rw [hconst]
  exact (isUnit_iff_ne_zero.mpr hc0).map MvPolynomial.C

end Factors
end ExplicitRIP.GuthZahl

end
