/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Geometry.Rulings.Incidence

/-!
# The two rulings of a split quadric

Ruling membership is exclusive. Distinct lines in one ruling are projectively
skew, while lines in opposite rulings are projectively coplanar, including
intersection at infinity.
-/

public section

namespace ExplicitRIP.Zahl

open Polynomial

/-- A chart line cannot belong to both rulings. -/
theorem not_inRuling_both {K : Type*} [Field K]
    (Q : SplitQuadric K) (l : ChartLine K) :
    ¬ (inRuling Q false l ∧ inRuling Q true l) := by
  rintro ⟨hl, hr⟩
  obtain ⟨a, ha, hleft⟩ := Rulings.exists_map_lineSpace_eq Q false l hl
  obtain ⟨b, hb, hright⟩ := Rulings.exists_map_lineSpace_eq Q true l hr
  exact Rulings.not_leftSpace_le_rightSpace a b ha hb (hleft.symm.trans hright).le

/-- Distinct lines in the same ruling are not projectively coplanar. -/
theorem not_coplanar_of_same_ruling {K : Type*} [Field K]
    (Q : SplitQuadric K) (side : Bool) (l m : ChartLine K)
    (hl : inRuling Q side l) (hm : inRuling Q side m) (hlm : l ≠ m) :
    ¬ Coplanar l m := by
  intro hcop
  obtain ⟨a, ha, hla⟩ := Rulings.exists_map_lineSpace_eq Q side l hl
  obtain ⟨b, hb, hmb⟩ := Rulings.exists_map_lineSpace_eq Q side m hm
  obtain ⟨w, hw, hwl, hwm⟩ := (Rulings.coplanar_iff_nonzero_mem l m).mp hcop
  have hQw : Q w ≠ 0 := fun h ↦ hw (Q.injective (h.trans Q.map_zero.symm))
  have hQa : Q w ∈ Rulings.rulingSpace side a := hla ▸ ⟨w, hwl, rfl⟩
  have hQb : Q w ∈ Rulings.rulingSpace side b := hmb ▸ ⟨w, hwm, rfl⟩
  have he := Rulings.rulingSpace_eq_of_nonzero_mem side a b ha hb (Q w) hQw hQa hQb
  apply hlm
  apply Rulings.lineSpace_injective
  apply Submodule.map_injective_of_injective (f := Q.toLinearMap) Q.injective
  exact hla.trans (he.trans hmb.symm)

/-- Lines in opposite rulings are projectively coplanar. -/
theorem coplanar_of_opposite_ruling {K : Type*} [Field K]
    (Q : SplitQuadric K) (side : Bool) (l m : ChartLine K)
    (hl : inRuling Q side l) (hm : inRuling Q (!side) m) :
    Coplanar l m := by
  obtain ⟨a, ha, hla⟩ := Rulings.exists_map_lineSpace_eq Q side l hl
  obtain ⟨b, hb, hmb⟩ := Rulings.exists_map_lineSpace_eq Q (!side) m hm
  obtain ⟨v, hv, hva, hvb⟩ := Rulings.exists_nonzero_mem_opposite side a b ha hb
  rw [← hla] at hva
  rw [← hmb] at hvb
  obtain ⟨w, hwl, hw⟩ := hva
  obtain ⟨z, hzm, hz⟩ := hvb
  have hwz : w = z := Q.injective (hw.trans hz.symm)
  apply (Rulings.coplanar_iff_nonzero_mem l m).mpr
  refine ⟨w, ?_, hwl, hwz.symm ▸ hzm⟩
  intro hzero
  apply hv
  rw [← hw, hzero, map_zero]

end ExplicitRIP.Zahl
