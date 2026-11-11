/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.RichPencilCount
public import ExplicitRIP.Frozen.Defs.IsComplementaryConicPair
public import ExplicitRIP.Algebra.ZModNonsquare
public import ExplicitRIP.GuthZahl.Defs

/-!
# Coordinates and finite counts for the Zahl correspondence

Definitions for the sphere–line correspondence of [Z, Section 2]: sphere parameters, the
quadratic extension `F[i]`, chart lines and their incidences, the sphere–line map, rich points
and counts, pencils, split quadrics and finite means. The coordinates use Zahl's map followed
by the ambient reflection `(X,Y,Z) ↦ (X,Y,-Z)`.
-/

@[expose] public section

namespace ExplicitRIP.Zahl

abbrev Sphere (F : Type*) := F × F × F × F

-- Points of affine 3-space: the same type as `ExplicitRIP.GuthZahl.Point`.
export ExplicitRIP.GuthZahl (Point)

abbrev QuadraticExtension (F : Type*) [Field F] := QuadraticAlgebra F (-1) 0

/-- A line in the affine chart with first direction coordinate one. -/
structure ChartLine (K : Type*) where
  s : K
  t : K
  u : K
  v : K
  deriving DecidableEq

def linePoint {K : Type*} [CommRing K] (l : ChartLine K) (x : K) : Point K :=
  ![x, l.s + l.u * x, l.t + l.v * x]

def linePoints {K : Type*} [CommRing K] (l : ChartLine K) : Set (Point K) :=
  Set.range (linePoint l)

def Parallel {K : Type*} (l m : ChartLine K) : Prop := l.u = m.u ∧ l.v = m.v

/-- The determinant criterion for projective intersection, including parallel lines. -/
def Coplanar {K : Type*} [CommRing K] (l m : ChartLine K) : Prop :=
  (l.s - m.s) * (l.v - m.v) - (l.t - m.t) * (l.u - m.u) = 0

def Intersects {K : Type*} [CommRing K] (l m : ChartLine K) : Prop :=
  (linePoints l ∩ linePoints m).Nonempty

/-- Literal Heisenberg line parameters `(a,b,c,d)`. -/
structure HLine (F : Type*) where
  a : F
  b : F
  c : F
  d : F
  deriving DecidableEq

def HLine.toChart {F : Type*} [Field F] (l : HLine F) :
    ChartLine (QuadraticExtension F) :=
  ⟨⟨l.c, l.d⟩, algebraMap F _ l.a, algebraMap F _ l.b, ⟨l.c, -l.d⟩⟩

/-- Sphere parameters `(a,b,c,d) = (z+r,r-z,-x,-y)` for the reflected sphere–line map. -/
def sphereParameters {F : Type*} [Field F] (S : Sphere F) : HLine F :=
  ⟨S.2.2.1 + S.2.2.2, S.2.2.2 - S.2.2.1, -S.1, -S.2.1⟩

def parametersSphere {F : Type*} [Field F] (l : HLine F) : Sphere F :=
  (-l.c, -l.d, (l.a - l.b) / 2, (l.a + l.b) / 2)

def sphereLine {F : Type*} [Field F] (S : Sphere F) :
    ChartLine (QuadraticExtension F) := (sphereParameters S).toChart

def heisenberg {F : Type*} [Field F] : Set (Point (QuadraticExtension F)) :=
  {w | (w 2).im = (w 0 * star (w 1)).im}

noncomputable def chartImage {F : Type*} [Field F] (L : Finset (HLine F)) :
    Finset (ChartLine (QuadraticExtension F)) := by
  classical
  exact L.image HLine.toChart

noncomputable def sphereImage {F : Type*} [Field F] (S : Finset (Sphere F)) :
    Finset (ChartLine (QuadraticExtension F)) := by
  classical
  exact S.image sphereLine

noncomputable def richPoints {K : Type*} [CommRing K]
    (L : Finset (ChartLine K)) (k : ℕ) : Set (Point K) := by
  classical
  exact {w | k ≤ (L.filter (fun l => w ∈ linePoints l)).card}

noncomputable def richCount {K : Type*} [CommRing K]
    (L : Finset (ChartLine K)) (k : ℕ) : ℕ := (richPoints L k).ncard

noncomputable def bichromaticPoints {K : Type*} [CommRing K]
    (R B : Finset (ChartLine K)) : Set (Point K) :=
  {w | (∃ l ∈ R, w ∈ linePoints l) ∧ ∃ l ∈ B, w ∈ linePoints l}

def pointPencil {F : Type*} [Field F] (w : Point (QuadraticExtension F)) :
    Set (Sphere F) := {S | w ∈ linePoints (sphereLine S)}

def directionPencil {F : Type*} [Field F] (v : F × F × F) : Set (Sphere F) :=
  {S | (sphereParameters S).b = v.1 ∧ (sphereParameters S).c = v.2.1 ∧
    (sphereParameters S).d = v.2.2}

noncomputable def parallelRichCount {F : Type*} [Field F]
    (S : Finset (Sphere F)) (k : ℕ) : ℕ := by
  classical
  exact {v : F × F × F | k ≤ (S.filter (· ∈ directionPencil v)).card}.ncard

def planeContains {K : Type*} [Field K] (normal : Point K) (offset : K)
    (l : ChartLine K) : Prop :=
  ∀ w ∈ linePoints l, (∑ j : Fin 3, normal j * w j) = offset

abbrev SplitQuadric (K : Type*) [Field K] :=
  (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)

def homogenize {K : Type*} [Zero K] [One K] (w : Point K) : Fin 4 → K :=
  ![1, w 0, w 1, w 2]

/-- A smooth split projective quadric intersected with the chosen affine chart. -/
def quadricValue {K : Type*} [Field K] (Q : SplitQuadric K) (w : Point K) : K :=
  let v := Q (homogenize w)
  v 0 * v 3 - v 1 * v 2

def quadricContains {K : Type*} [Field K] (Q : SplitQuadric K)
    (l : ChartLine K) : Prop := ∀ w ∈ linePoints l, quadricValue Q w = 0

/-- Left-kernel and right-kernel descriptions of the two rulings. -/
def inRuling {K : Type*} [Field K] (Q : SplitQuadric K)
    (side : Bool) (l : ChartLine K) : Prop :=
  ∃ a : Fin 2 → K, a ≠ 0 ∧ ∀ w ∈ linePoints l,
    let v := Q (homogenize w)
    if side then v 0 * a 0 + v 1 * a 1 = 0 ∧ v 2 * a 0 + v 3 * a 1 = 0
    else a 0 * v 0 + a 1 * v 2 = 0 ∧ a 0 * v 1 + a 1 * v 3 = 0

noncomputable def rulingCount {K : Type*} [Field K] (Q : SplitQuadric K)
    (side : Bool) (L : Finset (ChartLine K)) : ℕ := by
  classical
  exact (L.filter (inRuling Q side)).card

def commonContacts {F : Type*} [Field F] (A : Set (Sphere F)) : Set (Sphere F) :=
  {S | ∀ T ∈ A, ExplicitRIP.SphereContact S T}

section

variable {F : Type*} [Field F]

noncomputable instance quadraticExtensionFintype [Fintype F] :
    Fintype (QuadraticExtension F) :=
  Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd (-1 : F) 0).symm

instance quadraticExtensionCharP (p : ℕ) [CharP F p] :
    CharP (QuadraticExtension F) p :=
  charP_of_injective_algebraMap (algebraMap F (QuadraticExtension F)).injective p

/-- The two bilinear forms, with the coordinate order used by Zahl. -/
def lieForm (q q' : Fin 6 → F) : F :=
  2 * q 1 * q' 1 + 2 * q 2 * q' 2 + 2 * q 3 * q' 3 -
    q 0 * q' 4 - q 4 * q' 0 - 2 * q 5 * q' 5

def kleinForm {K : Type*} [CommRing K] (q q' : Fin 6 → K) : K :=
  q 0 * q' 3 + q 3 * q' 0 + q 1 * q' 4 + q 4 * q' 1 +
    q 2 * q' 5 + q 5 * q' 2

/-- Zahl's map followed by the ambient reflection `(X,Y,Z) ↦ (X,Y,-Z)`. -/
def correctedLieMap (q : Fin 6 → F) : Fin 6 → QuadraticExtension F :=
  ![algebraMap F _ (q 0), algebraMap F _ (q 3 + q 5),
    ⟨q 1, -q 2⟩, algebraMap F _ (q 4),
    algebraMap F _ (q 5 - q 3), ⟨-q 1, -q 2⟩]

def sphereLieCoordinates (S : Sphere F) : Fin 6 → F :=
  ![1, -S.1, -S.2.1, -S.2.2.1,
    S.1 ^ 2 + S.2.1 ^ 2 + S.2.2.1 ^ 2 - S.2.2.2 ^ 2, S.2.2.2]

def chartPlucker {K : Type*} [CommRing K] (l : ChartLine K) : Fin 6 → K :=
  ![1, l.u, l.v, l.s * l.v - l.t * l.u, l.t, -l.s]

def affinePencil (S T : Sphere F) : Set (Sphere F) :=
  Set.range (fun t : F => S + t • (T - S))

end

open Polynomial

/-- The literal univariate restriction of a split-quadric equation to a chart line. -/
noncomputable def quadricRestriction {K : Type*} [Field K] (Q : SplitQuadric K)
    (l : ChartLine K) : Polynomial K :=
  let a := Q ![1, 0, l.s, l.t]
  let b := Q ![0, 1, l.u, l.v]
  let f := fun j : Fin 4 => C (a j) + C (b j) * X
  f 0 * f 3 - f 1 * f 2

/-- The zero predicate of a literal affine hypersurface polynomial. -/
def surfaceZero {K : Type*} [Field K]
    (f : MvPolynomial (Fin 3) K) (w : Point K) : Prop :=
  MvPolynomial.eval w f = 0

/-- Literal pointwise containment of a chart line in an affine hypersurface. -/
def hypersurfaceContains {K : Type*} [Field K]
    (f : MvPolynomial (Fin 3) K) (l : ChartLine K) : Prop :=
  ∀ w ∈ linePoints l, surfaceZero f w

/-- A nonempty principal-open part of the hypersurface has two distinct lines
through each point. For an irreducible polynomial over an algebraically closed
field, this is the line case of the nonempty-open doubly-ruled condition of [GZ, Section 3]. -/
def doublyRuledHypersurface {K : Type*} [Field K]
    (f : MvPolynomial (Fin 3) K) : Prop :=
  ∃ g : MvPolynomial (Fin 3) K,
    (∃ w : Point K, surfaceZero f w ∧ MvPolynomial.eval w g ≠ 0) ∧
      ∀ w : Point K, surfaceZero f w → MvPolynomial.eval w g ≠ 0 →
        ∃ v₁ v₂ : Point K, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧
          (¬ ∃ a : K, v₂ = a • v₁) ∧
            ∀ t : K, surfaceZero f (w + t • v₁) ∧
              surfaceZero f (w + t • v₂)

/-- Literal finite average; the empty average is zero. -/
noncomputable def finiteMean {α : Type*} (Ω : Finset α) (f : α → ℝ) : ℝ :=
  Finset.expect Ω f

/-- The zero color class of a coloring of the elements of a finite set. -/
noncomputable def colorSample {α : Type*} (L : Finset α) {k : ℕ}
    (χ : ↥L → Fin k) : Finset α := by
  classical
  exact (L.attach.filter (fun l => (χ l).val = 0)).image Subtype.val

end ExplicitRIP.Zahl
