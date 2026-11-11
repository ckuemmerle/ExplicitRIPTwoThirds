/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.HostSRG.Coordinates

/-!
# Fibers of the quadratic norm

The norm from `𝔽_p[i]` to `𝔽_p` is surjective, and each nonzero fiber has `p + 1` elements.
This supplies the norm-fiber counts for the degree and common-neighbor parameters of the
Hermitian-forms model of `VO₄⁻(p)` in [KM, Section 3].
-/

@[expose] public section

namespace ExplicitRIP.Hfsrg

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

noncomputable instance extensionFintype : Fintype (Extension p) :=
  Fintype.ofEquiv (ZMod p × ZMod p) (QuadraticAlgebra.equivProd (-1) 0).symm

omit [Fact (p % 4 = 3)] in
theorem card_extension : Fintype.card (Extension p) = p ^ 2 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd (-1 : ZMod p) 0)]
  simp [sq]

theorem algebra_norm_eq (z : Extension p) :
    Algebra.norm (ZMod p) z = QuadraticAlgebra.norm z := by
  change (DistribSMul.toLinearMap (ZMod p) (Extension p) z).det = _
  exact QuadraticAlgebra.det_toLinearMap_eq_norm z

theorem norm_surjective : Function.Surjective (QuadraticAlgebra.norm (R := ZMod p)
    (a := -1) (b := 0)) := by
  intro t
  obtain ⟨z, hz⟩ := FiniteField.norm_surjective (ZMod p) (Extension p) t
  exact ⟨z, by simpa only [algebra_norm_eq] using hz⟩

theorem units_norm_surjective : Function.Surjective
    (Units.map (QuadraticAlgebra.norm (R := ZMod p) (a := -1) (b := 0))) := by
  intro t
  obtain ⟨z, hz⟩ := norm_surjective p t.val
  have hz0 : z ≠ 0 := by
    intro h
    apply t.ne_zero
    simpa only [h, QuadraticAlgebra.norm_zero] using hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext hz⟩

theorem card_norm_kernel :
    Nat.card (Units.map (QuadraticAlgebra.norm (R := ZMod p) (a := -1) (b := 0))).ker =
      p + 1 := by
  have h := Subgroup.card_ker_mul_card_of_surjective (units_norm_surjective p)
  have hK : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hE : Nat.card (Extension p) = p ^ 2 := by
    rw [Nat.card_eq_fintype_card, card_extension]
  rw [Nat.card_units, Nat.card_units, hK, hE] at h
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hsq : 1 ≤ p ^ 2 := by nlinarith
  have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have hsubsq : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel hsq
  apply Nat.eq_of_mul_eq_mul_right (show 0 < p - 1 by omega)
  rw [h]
  nlinarith

/-- Passing from a nonzero norm fiber to the corresponding fiber on units. -/
noncomputable def normFiberUnitsEquiv (t : ZMod p) (ht : t ≠ 0) :
    {z : Extension p // QuadraticAlgebra.norm z = t} ≃
      {u : (Extension p)ˣ // Units.map QuadraticAlgebra.norm u = Units.mk0 t ht} where
  toFun z := ⟨Units.mk0 z.val (by
    intro hz
    apply ht
    simpa only [hz, QuadraticAlgebra.norm_zero] using z.property.symm),
    Units.ext z.property⟩
  invFun u := ⟨u.val.val, congrArg Units.val u.property⟩
  left_inv _ := rfl
  right_inv _ := Subtype.ext (Units.ext rfl)

theorem card_norm_fiber (t : ZMod p) (ht : t ≠ 0) :
    Fintype.card {z : Extension p // QuadraticAlgebra.norm z = t} = p + 1 := by
  classical
  rw [Fintype.card_eq_nat_card]
  trans Nat.card (Units.map (QuadraticAlgebra.norm (R := ZMod p) (a := -1) (b := 0))).ker
  · exact Nat.card_congr ((normFiberUnitsEquiv p t ht).trans
      (MonoidHom.fiberEquivKerOfSurjective (units_norm_surjective p) (Units.mk0 t ht)))
  · exact card_norm_kernel p

theorem card_sq_add_sq (t : ZMod p) :
    Fintype.card {z : ZMod p × ZMod p // z.1 ^ 2 + z.2 ^ 2 = t} =
      if t = 0 then 1 else p + 1 := by
  classical
  by_cases ht : t = 0
  · subst t
    have he : {z : ZMod p × ZMod p // z.1 ^ 2 + z.2 ^ 2 = 0} ≃
        {z : ZMod p × ZMod p // z = 0} :=
      Equiv.subtypeEquivRight (fun z => by
        rw [Rank1.sum_sq_eq_zero_iff]
        exact ⟨fun h => Prod.ext h.1 h.2,
          fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩)
    rw [Fintype.card_congr he]
    simp
  · rw [ite_eq_right ht, ← card_norm_fiber p t ht]
    exact Fintype.card_congr ((QuadraticAlgebra.equivProd (-1 : ZMod p) 0).symm.subtypeEquiv
      (fun z => (norm_mk p z.1 z.2).symm ▸ Iff.rfl))

end ExplicitRIP.Hfsrg
