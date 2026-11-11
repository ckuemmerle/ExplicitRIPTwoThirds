/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Boundary.Descent.Projective

/-!
# Extension of homogeneous coordinates

An invertible coordinate matrix over the base field stays invertible after
applying a field homomorphism to its coefficients.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.Boundary.Descent

variable {F K : Type*} [Field F] [Field K]

/-- Entrywise coefficient extension of an endomorphism in four coordinates. -/
noncomputable def extendLinear (φ : F →+* K) (f : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) :
    (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
  Matrix.toLin' (φ.mapMatrix (LinearMap.toMatrix' f))

theorem extendLinear_comp (φ : F →+* K)
    (f g : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) :
    extendLinear φ (f.comp g) = (extendLinear φ f).comp (extendLinear φ g) := by
  simp only [extendLinear, LinearMap.toMatrix'_comp, map_mul, Matrix.toLin'_mul]

theorem extendLinear_id (φ : F →+* K) :
    extendLinear φ (LinearMap.id : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) = LinearMap.id := by
  simp only [extendLinear, LinearMap.toMatrix'_id, map_one, Matrix.toLin'_one]

/-- Extension of an invertible homogeneous coordinate transformation. -/
noncomputable def extendEquiv (φ : F →+* K) (E : Zahl.SplitQuadric F) :
    Zahl.SplitQuadric K :=
  { extendLinear φ E.toLinearMap with
    invFun := extendLinear φ E.symm.toLinearMap
    left_inv := fun x => by
      change (extendLinear φ E.symm.toLinearMap).comp (extendLinear φ E.toLinearMap) x = x
      rw [← extendLinear_comp]
      have h : E.symm.toLinearMap.comp E.toLinearMap = LinearMap.id := by
        exact LinearMap.ext (fun v => E.symm_apply_apply v)
      rw [h, extendLinear_id, LinearMap.id_apply]
    right_inv := fun x => by
      change (extendLinear φ E.toLinearMap).comp (extendLinear φ E.symm.toLinearMap) x = x
      rw [← extendLinear_comp]
      have h : E.toLinearMap.comp E.symm.toLinearMap = LinearMap.id := by
        exact LinearMap.ext (fun v => E.apply_symm_apply v)
      rw [h, extendLinear_id, LinearMap.id_apply] }

theorem extendEquiv_apply (φ : F →+* K) (E : Zahl.SplitQuadric F) (v : Fin 4 → F) :
    extendEquiv φ E (fun i => φ (v i)) = fun i => φ (E v i) := by
  ext i
  change Matrix.mulVec (φ.mapMatrix (LinearMap.toMatrix' E.toLinearMap))
    (fun j => φ (v j)) i = _
  calc
    _ = φ (Matrix.mulVec (LinearMap.toMatrix' E.toLinearMap) v i) :=
      (RingHom.map_mulVec φ (LinearMap.toMatrix' E.toLinearMap) v i).symm
    _ = φ (E v i) := congrArg φ (congrFun
      (congrArg (fun f : (Fin 4 → F) →ₗ[F] (Fin 4 → F) => f v)
        (Matrix.toLin'_toMatrix' E.toLinearMap)) i)

theorem map_homogeneousLineMap (φ : F →+* K) (a v : Point F) (u : Fin 2 → F) :
    (fun i => φ (homogeneousLineMap a v u i)) =
      homogeneousLineMap (mapPoint φ a) (mapPoint φ v) (fun i => φ (u i)) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change φ (u 0 * a j + u 1 * v j) = _
    simp only [map_add, map_mul]
    rfl

theorem map_mem_range_homogeneousLineMap (φ : F →+* K) (a v : Point F)
    {x : Fin 4 → F} (hx : x ∈ LinearMap.range (homogeneousLineMap a v)) :
    (fun i => φ (x i)) ∈ LinearMap.range (homogeneousLineMap (mapPoint φ a) (mapPoint φ v)) := by
  obtain ⟨u, rfl⟩ := hx
  exact ⟨fun i => φ (u i), (map_homogeneousLineMap φ a v u).symm⟩

end ExplicitRIP.GuthZahl.Boundary.Descent

end
