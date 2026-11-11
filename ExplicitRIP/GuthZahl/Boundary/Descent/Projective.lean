/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Boundary.Descent.Frame
public import ExplicitRIP.GuthZahl.RuledSurfaces.AffineGeometry

/-!
# Homogeneous coordinates for affine line parametrizations

Skewness of actual affine lines includes distinct directions. Consequently
their homogeneous two-dimensional spans are disjoint.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.Boundary.Descent

variable {K : Type*} [Field K]

/-- Homogeneous parametrization from an affine origin and direction. -/
def homogeneousLineMap (a v : Point K) : (Fin 2 → K) →ₗ[K] (Fin 4 → K) where
  toFun u := Fin.cons (u 0) (u 0 • a + u 1 • v)
  map_add' u w := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (u 0 + w 0) * a j + (u 1 + w 1) * v j =
        (u 0 * a j + u 1 * v j) + (w 0 * a j + w 1 * v j)
      ring
  map_smul' c u := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (c * u 0) * a j + (c * u 1) * v j =
        c * (u 0 * a j + u 1 * v j)
      ring

/-- A nonzero affine direction gives an injective homogeneous parametrization. -/
theorem homogeneousLineMap_injective (a v : Point K) (hv : v ≠ 0) :
    Function.Injective (homogeneousLineMap a v) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  have h0 : u 0 = 0 := congrFun hu 0
  have hs : u 1 • v = 0 := by
    ext i
    have h := congrFun hu i.succ
    simpa only [homogeneousLineMap, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.cons_succ, h0, zero_smul, zero_add, Pi.zero_apply] using h
  have h1 : u 1 = 0 := (smul_eq_zero.mp hs).resolve_right hv
  ext i
  fin_cases i <;> assumption

/-- The homogeneous span of an affine line has dimension two. -/
theorem finrank_range_homogeneousLineMap (a v : Point K) (hv : v ≠ 0) :
    Module.finrank K (LinearMap.range (homogeneousLineMap a v)) = 2 := by
  rw [LinearMap.finrank_range_of_inj (homogeneousLineMap_injective a v hv)]
  exact Module.finrank_fin_fun K

/-- Affine points on a parametrized line lift to its homogeneous span. -/
theorem homogenize_mem_range {L : Line K} {a v : Point K}
    (ha : a ∈ L.1) (hv : v ∈ L.1.direction) (hv0 : v ≠ 0)
    {x : Point K} (hx : x ∈ L.1) :
    Zahl.homogenize x ∈ LinearMap.range (homogeneousLineMap a v) := by
  obtain ⟨t, rfl⟩ := (mem_line_iff_exists_smul ha hv hv0 x).mp hx
  refine ⟨![1, t], ?_⟩
  change Fin.cons 1 (1 • a + t • v) = Zahl.homogenize (a + t • v)
  rw [one_smul]
  ext i
  fin_cases i <;> rfl

/-- The homogeneous spans of skew affine lines have zero intersection. -/
theorem disjoint_ranges_of_not_coplanar {L M : Line K}
    {a v b w : Point K} (ha : a ∈ L.1) (hv : v ∈ L.1.direction) (hv0 : v ≠ 0)
    (hb : b ∈ M.1) (hw : w ∈ M.1.direction) (hw0 : w ≠ 0)
    (hLM : ¬ Coplanar L M) :
    Disjoint (LinearMap.range (homogeneousLineMap a v))
      (LinearMap.range (homogeneousLineMap b w)) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨u, rfl⟩ ⟨z, heq⟩
  by_contra hx
  have h0 : z 0 = u 0 := congrFun heq 0
  have ht : z 0 • b + z 1 • w = u 0 • a + u 1 • v := by
    ext i
    exact congrFun heq i.succ
  by_cases hu : u 0 = 0
  · have hvec : u 1 • v = z 1 • w := by
      simpa only [h0, hu, zero_smul, zero_add] using ht.symm
    have hne : u 1 • v ≠ 0 := by
      intro hz
      apply hx
      change (Fin.cons (u 0) (u 0 • a + u 1 • v) : Fin 4 → K) = 0
      rw [hu, zero_smul, zero_add, hz]
      ext i
      fin_cases i <;> rfl
    have hLv : u 1 • v ∈ L.1.direction := L.1.direction.smul_mem _ hv
    have hMv : u 1 • v ∈ M.1.direction := hvec ▸ M.1.direction.smul_mem _ hw
    exact hLM (RuledSurfaces.coplanar_of_direction_eq
      ((eq_span_singleton_of_mem_of_finrank_eq_one L.2 hLv hne).trans
        (eq_span_singleton_of_mem_of_finrank_eq_one M.2 hMv hne).symm))
  · have hp : a + (u 1 / u 0) • v = b + (z 1 / u 0) • w := by
      ext i
      have h := congrFun ht i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0] at h ⊢
      field_simp
      linear_combination -h
    have hL : a + (u 1 / u 0) • v ∈ L.1 :=
      (mem_line_iff_exists_smul ha hv hv0 _).mpr ⟨_, rfl⟩
    have hM : a + (u 1 / u 0) • v ∈ M.1 := hp ▸
      (mem_line_iff_exists_smul hb hw hw0 _).mpr ⟨_, rfl⟩
    exact hLM (RuledSurfaces.coplanar_of_mem_of_ne hL hM
      (RuledSurfaces.ne_of_not_coplanar hLM))

/-- Three skew actual affine lines lie on the zero set of a split quadric. -/
theorem exists_splitQuadric_of_skew_triple (A B C : Line K)
    (hAB : ¬ Coplanar A B) (hAC : ¬ Coplanar A C) (hBC : ¬ Coplanar B C) :
    ∃ Q : Zahl.SplitQuadric K,
      (∀ x ∈ A.1, Zahl.quadricValue Q x = 0) ∧
      (∀ x ∈ B.1, Zahl.quadricValue Q x = 0) ∧
      (∀ x ∈ C.1, Zahl.quadricValue Q x = 0) := by
  obtain ⟨a, v, ha, hv, hv0, _⟩ := exists_line_parametrization A
  obtain ⟨b, w, hb, hw, hw0, _⟩ := exists_line_parametrization B
  obtain ⟨c, z, hc, hz, hz0, _⟩ := exists_line_parametrization C
  obtain ⟨E, hEA, hEB, hEC⟩ := exists_skew_frame
    (LinearMap.range (homogeneousLineMap a v))
    (LinearMap.range (homogeneousLineMap b w))
    (LinearMap.range (homogeneousLineMap c z))
    (finrank_range_homogeneousLineMap a v hv0)
    (finrank_range_homogeneousLineMap b w hw0)
    (finrank_range_homogeneousLineMap c z hz0)
    (disjoint_ranges_of_not_coplanar ha hv hv0 hb hw hw0 hAB)
    (disjoint_ranges_of_not_coplanar ha hv hv0 hc hz hz0 hAC)
    (disjoint_ranges_of_not_coplanar hb hw hw0 hc hz hz0 hBC)
  refine ⟨E.symm, ?_, ?_, ?_⟩
  · intro x hx
    have h := (hEA (E.symm (Zahl.homogenize x))).mp (by
      rw [E.apply_symm_apply]
      exact homogenize_mem_range ha hv hv0 hx)
    simp only [Zahl.quadricValue, h.1, h.2, mul_zero, sub_self]
  · intro x hx
    have h := (hEB (E.symm (Zahl.homogenize x))).mp (by
      rw [E.apply_symm_apply]
      exact homogenize_mem_range hb hw hw0 hx)
    simp only [Zahl.quadricValue, h.1, h.2, zero_mul, sub_self]
  · intro x hx
    have h := (hEC (E.symm (Zahl.homogenize x))).mp (by
      rw [E.apply_symm_apply]
      exact homogenize_mem_range hc hz hz0 hx)
    simp only [Zahl.quadricValue, h.1, h.2, mul_comm, sub_self]

end ExplicitRIP.GuthZahl.Boundary.Descent

end
