/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Carriers for the line-only Guth–Zahl structure theorem

Definitions used by the formalization of the line case of [GZ, Theorem 3.8], on which
[Z, Theorem 1.8] rests. The library theorem `ExplicitRIP.Zahl.sphere_contacts` proves
the case used in [KM, Theorem 6], from which the frozen statement
`ExplicitRIP.zahl_sphere_contacts` is proved.

* `Point K = Fin 3 → K` and `Poly K = MvPolynomial (Fin 3) K`;
* `Line K`: actual affine lines (one-dimensional affine subspaces), so different parametrizations
  of one line are never counted twice;
* `restrictLine f a v`: the univariate polynomial `t ↦ f (a + t v)`;
* `LineOn f L`: algebraic containment (the restriction vanishes identically for every base point
  and direction of `L`); over a finite field this is stronger than vanishing at rational points;
* `richPoints Ls r`: the points lying on at least `r` lines of a finite family;
* `principalOpen f g`, `DoublyRuled f`: two distinct contained lines through every point of a
  nonempty principal open subset of the hypersurface `f = 0`;
* `TangentToOrder`, `TwoTangentDirections`: coefficient tangency (no factorial inverses);
* `zeroPattern`: the Boolean zero pattern of a finite polynomial family.

The algebraic containment and coefficient-tangency predicates are meaningful over finite
fields as well as infinite fields.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl

abbrev Point (K : Type*) := Fin 3 → K
abbrev Poly (K : Type*) [CommSemiring K] := MvPolynomial (Fin 3) K

/-- Actual affine lines, not multiply-counted parametrizations. -/
abbrev Line (K : Type*) [Field K] :=
  { L : AffineSubspace K (Point K) // Module.finrank K L.direction = 1 }

/-- Coplanarity includes parallel lines; equivalently, projective completions meet. -/
def Coplanar {K : Type*} [Field K] (L M : Line K) : Prop :=
  ∃ P : AffineSubspace K (Point K), Module.finrank K P.direction = 2 ∧ L.1 ≤ P ∧ M.1 ≤ P

/-- The polynomial `f(a + t v)` in an indeterminate `t`. -/
noncomputable def restrictLine {K : Type*} [Field K]
    (f : Poly K) (a v : Point K) : Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun j => Polynomial.C (a j) + Polynomial.C (v j) * Polynomial.X) f

/-- Scheme-independent algebraic containment of an affine line in a hypersurface. -/
def LineOn {K : Type*} [Field K] (f : Poly K) (L : Line K) : Prop :=
  ∀ a ∈ L.1, ∀ v ∈ L.1.direction, restrictLine f a v = 0

/-- Points incident to at least `r` distinct lines in a finite set. -/
noncomputable def richPoints {K : Type*} [Field K] (Ls : Finset (Line K)) (r : ℕ) :
    Set (Point K) :=
  open Classical in {x | r ≤ (Ls.filter (fun L => x ∈ L.1)).card}

/-- A principal open subset of a hypersurface, in classical point language. -/
def principalOpen {K : Type*} [Field K] (f g : Poly K) : Set (Point K) :=
  {x | MvPolynomial.eval x f = 0 ∧ MvPolynomial.eval x g ≠ 0}

/-- Two geometrically different lines through each point of a nonempty principal open. -/
def DoublyRuled {K : Type*} [Field K] (f : Poly K) : Prop :=
  ∃ g : Poly K, ¬ f ∣ g ∧ (principalOpen f g).Nonempty ∧
    ∀ x ∈ principalOpen f g,
      ∃ L M : Line K, L ≠ M ∧ x ∈ L.1 ∧ x ∈ M.1 ∧ LineOn f L ∧ LineOn f M

/-- Tangency to order at least `r` along the direction `v`, expressed by coefficients. -/
def TangentToOrder {K : Type*} [Field K] (f : Poly K) (x v : Point K) (r : ℕ) : Prop :=
  ∀ j ≤ r, (restrictLine f x v).coeff j = 0

/-- The line-only two-flecnode condition. The two directions are not proportional. -/
def TwoTangentDirections {K : Type*} [Field K] (f : Poly K) (x : Point K) (r : ℕ) : Prop :=
  ∃ v w : Point K, v ≠ 0 ∧ w ≠ 0 ∧ (¬ ∃ a : K, w = a • v) ∧
    TangentToOrder f x v r ∧ TangentToOrder f x w r

/-- The Boolean zero pattern of a finite polynomial family. -/
noncomputable def zeroPattern {K : Type*} [Field K] {J : ℕ}
    (qs : Fin J → Poly K) (x : Point K) : Fin J → Bool :=
  open Classical in fun j => decide (MvPolynomial.eval x (qs j) = 0)

end ExplicitRIP.GuthZahl
end
