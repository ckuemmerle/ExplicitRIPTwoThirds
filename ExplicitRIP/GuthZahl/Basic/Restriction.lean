/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Basic.Geometry

/-!
# Polynomial restrictions to affine lines

Affine substitution does not increase total degree. Evaluation and affine changes of the
line parameter connect polynomial restrictions with geometric intersections.
-/

public section

namespace ExplicitRIP.GuthZahl

variable {K : Type*} [Field K]

theorem restrictLine_natDegree_le {K : Type*} [Field K]
    (f : Poly K) (a v : Point K) : (restrictLine f a v).natDegree ≤ f.totalDegree := by
  classical
  unfold restrictLine
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  refine le_trans (Finset.sum_le_sum ?_) (MvPolynomial.le_totalDegree hd)
  intro i _
  apply (Polynomial.natDegree_pow_le).trans
  have hlinear : (Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp only [Polynomial.natDegree_C]; exact Nat.zero_le _
    · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  simpa only [mul_one] using Nat.mul_le_mul_left (d i) hlinear

theorem eval_restrictLine {K : Type*} [Field K] (f : Poly K)
    (a v : Point K) (t : K) :
    Polynomial.eval t (restrictLine f a v) = MvPolynomial.eval (a + t • v) f := by
  have h : (Polynomial.evalRingHom t).comp
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun j => Polynomial.C (a j) + Polynomial.C (v j) * Polynomial.X)) =
      MvPolynomial.eval (a + t • v) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C,
        Polynomial.coe_evalRingHom, Polynomial.eval_C]
    · intro j
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X,
        Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm]
  exact DFunLike.congr_fun h f

theorem restrictLine_affine_reparam {K : Type*} [Field K] (f : Poly K)
    (a v : Point K) (s c : K) :
    restrictLine f (a + s • v) (c • v) =
      (restrictLine f a v).comp (Polynomial.C s + Polynomial.C c * Polynomial.X) := by
  have h : MvPolynomial.eval₂Hom Polynomial.C
        (fun j => Polynomial.C ((a + s • v) j) + Polynomial.C ((c • v) j) * Polynomial.X) =
      (Polynomial.compRingHom (Polynomial.C s + Polynomial.C c * Polynomial.X)).comp
        (MvPolynomial.eval₂Hom Polynomial.C
          (fun j => Polynomial.C (a j) + Polynomial.C (v j) * Polynomial.X)) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C,
        Polynomial.coe_compRingHom_apply, Polynomial.C_comp]
    · intro j
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X',
        Polynomial.coe_compRingHom_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Polynomial.C_comp, Polynomial.X_comp, map_add, map_mul]
      ring
  exact DFunLike.congr_fun h f

theorem line_exists_base_direction {K : Type*} [Field K] (L : Line K) :
    ∃ a ∈ L.1, ∃ v ∈ L.1.direction, v ≠ (0 : Point K) := by
  have hd : L.1.direction ≠ ⊥ := by
    intro h
    have he := congrArg (fun S : Submodule K (Point K) => Module.finrank K S) h
    exact Nat.one_ne_zero (L.2.symm.trans (he.trans (finrank_bot K (Point K))))
  have hL : L.1 ≠ ⊥ := by
    intro h
    exact hd ((congrArg AffineSubspace.direction h).trans
      (AffineSubspace.direction_bot K (Point K) (Point K)))
  obtain ⟨a, ha⟩ := (AffineSubspace.nonempty_iff_ne_bot L.1).mpr hL
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hd
  exact ⟨a, ha, v, hv, hv0⟩

theorem lineOn_iff_restrictLine_eq_zero {K : Type*} [Field K] (f : Poly K)
    (L : Line K) (a : Point K) (ha : a ∈ L.1) (v : Point K)
    (hv : v ∈ L.1.direction) (hv0 : v ≠ 0) :
    LineOn f L ↔ restrictLine f a v = 0 := by
  refine ⟨fun h => h a ha v hv, ?_⟩
  intro h b hb w hw
  obtain ⟨s, hs⟩ := (mem_line_iff_exists_smul ha hv hv0 b).mp hb
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one L.2 hv hv0
  rw [hspan] at hw
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  rw [← hs, ← hc, restrictLine_affine_reparam, h, Polynomial.zero_comp]

theorem line_hypersurface_bound {K : Type*} [Field K] (f : Poly K) (L : Line K)
    (h : ¬ LineOn f L) :
    {x : Point K | x ∈ L.1 ∧ MvPolynomial.eval x f = 0}.Finite ∧
      {x : Point K | x ∈ L.1 ∧ MvPolynomial.eval x f = 0}.ncard ≤ f.totalDegree := by
  classical
  obtain ⟨a, ha, v, hv, hv0⟩ := line_exists_base_direction L
  have hq : restrictLine f a v ≠ 0 :=
    fun hq => h ((lineOn_iff_restrictLine_eq_zero f L a ha v hv hv0).mpr hq)
  let R := (restrictLine f a v).roots.toFinset
  let φ : K → Point K := fun t => a + t • v
  have hsub : {x : Point K | x ∈ L.1 ∧ MvPolynomial.eval x f = 0} ⊆
      φ '' (R : Set K) := by
    intro x hx
    obtain ⟨t, ht⟩ := (mem_line_iff_exists_smul ha hv hv0 x).mp hx.1
    refine ⟨t, ?_, ht⟩
    change t ∈ (restrictLine f a v).roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq, Polynomial.IsRoot,
      eval_restrictLine, ht]
    exact hx.2
  have hfin := R.finite_toSet.image φ
  refine ⟨hfin.subset hsub, ?_⟩
  calc
    _ ≤ (φ '' (R : Set K)).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ (R : Set K).ncard := Set.ncard_image_le R.finite_toSet
    _ = R.card := Set.ncard_coe_finset R
    _ ≤ (restrictLine f a v).roots.card := Multiset.toFinset_card_le _
    _ ≤ (restrictLine f a v).natDegree := Polynomial.card_roots' _
    _ ≤ f.totalDegree := restrictLine_natDegree_le f a v

@[simp]
theorem restrictLine_C (c : K) (a v : Point K) :
    restrictLine (MvPolynomial.C c) a v = Polynomial.C c :=
  MvPolynomial.eval₂Hom_C _ _ _

@[simp]
theorem restrictLine_X (i : Fin 3) (a v : Point K) :
    restrictLine (MvPolynomial.X i) a v =
      Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X :=
  MvPolynomial.eval₂Hom_X' _ _ _

@[simp]
theorem restrictLine_add (f g : Poly K) (a v : Point K) :
    restrictLine (f + g) a v = restrictLine f a v + restrictLine g a v :=
  map_add _ _ _

@[simp]
theorem restrictLine_mul (f g : Poly K) (a v : Point K) :
    restrictLine (f * g) a v = restrictLine f a v * restrictLine g a v :=
  map_mul _ _ _

/-- Algebraic containment implies vanishing at every point of the line. -/
theorem eval_eq_zero_of_lineOn {f : Poly K} {L : Line K} (h : LineOn f L)
    {a : Point K} (ha : a ∈ L.1) : MvPolynomial.eval a f = 0 := by
  have he := congrArg (Polynomial.eval (0 : K)) (h a ha 0 L.1.direction.zero_mem)
  simpa only [eval_restrictLine, zero_smul, add_zero, Polynomial.eval_zero] using he

/-- Over an infinite field, pointwise vanishing on a line is algebraic containment. -/
theorem lineOn_iff_eval_eq_zero [Infinite K] (f : Poly K) (L : Line K) :
    LineOn f L ↔ ∀ x ∈ L.1, MvPolynomial.eval x f = 0 := by
  refine ⟨fun h x hx => eval_eq_zero_of_lineOn h hx, ?_⟩
  intro h a ha v hv
  apply Polynomial.funext
  intro t
  rw [eval_restrictLine, Polynomial.eval_zero]
  apply h
  simpa only [vadd_eq_add, add_comm] using
    AffineSubspace.vadd_mem_of_mem_direction (L.1.direction.smul_mem t hv) ha

/-- A line contained in a product is contained in one factor. -/
theorem lineOn_mul_iff [Infinite K] (f g : Poly K) (L : Line K) :
    LineOn (f * g) L ↔ LineOn f L ∨ LineOn g L := by
  obtain ⟨a, v, ha, hv, hv0, -⟩ := exists_line_parametrization L
  rw [lineOn_iff_restrictLine_eq_zero _ _ _ ha _ hv hv0,
    lineOn_iff_restrictLine_eq_zero _ _ _ ha _ hv hv0,
    lineOn_iff_restrictLine_eq_zero _ _ _ ha _ hv hv0, restrictLine_mul, mul_eq_zero]

/-- Containment is preserved when the defining polynomial is multiplied. -/
theorem lineOn_of_dvd {f g : Poly K} (hfg : f ∣ g) {L : Line K}
    (hf : LineOn f L) : LineOn g L := by
  obtain ⟨q, rfl⟩ := hfg
  intro a ha v hv
  change (MvPolynomial.eval₂Hom Polynomial.C
    (fun j => Polynomial.C (a j) + Polynomial.C (v j) * Polynomial.X)) (f * q) = 0
  rw [map_mul]
  change restrictLine f a v * restrictLine q a v = 0
  rw [hf a ha v hv, zero_mul]

/-- Associated polynomials contain exactly the same lines. -/
theorem lineOn_iff_of_associated {f g : Poly K} (h : Associated f g) (L : Line K) :
    LineOn f L ↔ LineOn g L :=
  ⟨lineOn_of_dvd h.dvd, lineOn_of_dvd h.symm.dvd⟩

theorem restrictLine_monomial_natDegree_le (m : Fin 3 →₀ ℕ) (c : K) (a v : Point K) :
    (restrictLine (MvPolynomial.monomial m c) a v).natDegree ≤ m.sum (fun _ e => e) := by
  classical
  rw [restrictLine, MvPolynomial.eval₂Hom_monomial]
  calc
    _ ≤ (Polynomial.C c).natDegree +
        (m.prod fun i e =>
          (Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) ^ e).natDegree :=
      Polynomial.natDegree_mul_le
    _ = (m.prod fun i e =>
          (Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) ^ e).natDegree := by
      rw [Polynomial.natDegree_C, zero_add]
    _ ≤ m.sum (fun _ e => e) := by
      apply (Polynomial.natDegree_prod_le _ _).trans
      apply Finset.sum_le_sum
      intro i _hi
      apply (Polynomial.natDegree_pow_le).trans
      have h : (Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X).natDegree ≤ 1 := by
        apply Polynomial.natDegree_add_le_of_degree_le
        · simp only [Polynomial.natDegree_C, zero_le]
        · exact (Polynomial.natDegree_mul_le).trans (by
            simp only [Polynomial.natDegree_C, Polynomial.natDegree_X, zero_add, le_refl])
      simpa only [mul_one] using Nat.mul_le_mul_left (m i) h

end ExplicitRIP.GuthZahl

end
