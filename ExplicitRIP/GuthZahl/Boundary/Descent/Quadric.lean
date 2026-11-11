/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Boundary.Descent.Chart

/-!
# Descent of a split-quadric equation

The coordinate frame of a skew triple is constructed over the base field.
Over the extension field, uniqueness identifies its determinant equation
with the original split quadric up to a nonzero scalar.
-/

public section

namespace ExplicitRIP.GuthZahl.Boundary.Descent

open ExplicitRIP.Zahl (ChartLine)

variable {F K : Type*} [Field F] [Field K]

theorem quadric_descends_of_skew_triple (φ : F →+* K) (h2 : (2 : F) ≠ 0)
    (Q : Zahl.SplitQuadric K) (a b c : ChartLine F)
    (hab : Disjoint (chartPlane a) (chartPlane b))
    (hac : Disjoint (chartPlane a) (chartPlane c))
    (hbc : Disjoint (chartPlane b) (chartPlane c))
    (ha : Zahl.quadricContains Q (mapChart φ a))
    (hb : Zahl.quadricContains Q (mapChart φ b))
    (hc : Zahl.quadricContains Q (mapChart φ c)) :
    ∃ Q₀ : Zahl.SplitQuadric F, ∀ l : ChartLine F,
      Zahl.quadricContains Q (mapChart φ l) → Zahl.quadricContains Q₀ l := by
  classical
  have h2K : (2 : K) ≠ 0 := by
    intro h
    apply h2
    apply φ.injective
    simpa only [map_ofNat, map_zero] using h
  obtain ⟨E, hEA, hEB, hEC⟩ := exists_skew_frame (chartPlane a) (chartPlane b) (chartPlane c)
    (finrank_chartPlane a) (finrank_chartPlane b) (finrank_chartPlane c) hab hac hbc
  let E' := extendEquiv φ E
  let T := E'.trans Q
  have hspan (l : ChartLine F) (hl : Zahl.quadricContains Q (mapChart φ l))
      (u v : Fin 4 → F) (hu : E u ∈ chartPlane l) (hv : E v ∈ chartPlane l)
      (s t : K) : determinantFour (T
        (s • (fun i => φ (u i)) + t • (fun i => φ (v i)))) = 0 := by
    apply chartPlane_zero h2K Q (mapChart φ l) hl
    change extendEquiv φ E (s • (fun i => φ (u i)) + t • (fun i => φ (v i))) ∈ _
    rw [map_add, map_smul, map_smul, extendEquiv_apply, extendEquiv_apply]
    exact (chartPlane (mapChart φ l)).add_mem
      ((chartPlane (mapChart φ l)).smul_mem s (map_mem_chartPlane φ l hu))
      ((chartPlane (mapChart φ l)).smul_mem t (map_mem_chartPlane φ l hv))
  have hleft (s t : K) : determinantFour (T ![s, t, 0, 0]) = 0 := by
    have h := hspan a ha ![1, 0, 0, 0] ![0, 1, 0, 0]
      ((hEA _).mpr ⟨rfl, rfl⟩) ((hEA _).mpr ⟨rfl, rfl⟩) s t
    have heq : s • (fun i => φ ((![1, 0, 0, 0] : Fin 4 → F) i)) +
        t • (fun i => φ ((![0, 1, 0, 0] : Fin 4 → F) i)) = ![s, t, 0, 0] := by
      ext i; fin_cases i <;> simp
    rwa [heq] at h
  have hright (s t : K) : determinantFour (T ![0, 0, s, t]) = 0 := by
    have h := hspan b hb ![0, 0, 1, 0] ![0, 0, 0, 1]
      ((hEB _).mpr ⟨rfl, rfl⟩) ((hEB _).mpr ⟨rfl, rfl⟩) s t
    have heq : s • (fun i => φ ((![0, 0, 1, 0] : Fin 4 → F) i)) +
        t • (fun i => φ ((![0, 0, 0, 1] : Fin 4 → F) i)) = ![0, 0, s, t] := by
      ext i; fin_cases i <;> simp
    rwa [heq] at h
  have hdiag (s t : K) : determinantFour (T ![s, t, s, t]) = 0 := by
    have h := hspan c hc ![1, 0, 1, 0] ![0, 1, 0, 1]
      ((hEC _).mpr ⟨rfl, rfl⟩) ((hEC _).mpr ⟨rfl, rfl⟩) s t
    have heq : s • (fun i => φ ((![1, 0, 1, 0] : Fin 4 → F) i)) +
        t • (fun i => φ ((![0, 1, 0, 1] : Fin 4 → F) i)) = ![s, t, s, t] := by
      ext i; fin_cases i <;> simp
    rwa [heq] at h
  obtain ⟨r, hr, hT⟩ := determinantFour_comp_eq_scalar T hleft hright hdiag
  refine ⟨E.symm, ?_⟩
  intro l hl w hw
  obtain ⟨t, rfl⟩ := hw
  have hw : Zahl.homogenize (Zahl.linePoint l t) ∈ chartPlane l := by
    refine ⟨![1, t], ?_⟩
    rw [homogeneousLineMap_chart]
    ext i; fin_cases i <;> simp [Zahl.homogenize, Zahl.linePoint, mul_comm]
  let y := E.symm (Zahl.homogenize (Zahl.linePoint l t))
  have hz : determinantFour (T (fun i => φ (y i))) = 0 := by
    change determinantFour (Q (extendEquiv φ E (fun i => φ (y i)))) = 0
    rw [extendEquiv_apply]
    change determinantFour (Q (fun i => φ (E (E.symm _) i))) = 0
    rw [E.apply_symm_apply]
    exact chartPlane_zero h2K Q (mapChart φ l) hl _ (map_mem_chartPlane φ l hw)
  rw [hT] at hz
  have hz' := (mul_eq_zero.mp hz).resolve_left hr
  change determinantFour y = 0
  apply φ.injective
  simpa only [determinantFour, map_sub, map_mul, map_zero] using hz'

end ExplicitRIP.GuthZahl.Boundary.Descent

end
