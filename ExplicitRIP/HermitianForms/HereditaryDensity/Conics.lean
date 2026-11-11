/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.HereditaryDensity.Pencils
public import ExplicitRIP.HermitianForms.HereditaryDensity.Orthogonal
public import ExplicitRIP.Frozen.Defs.IsComplementaryConicPair

/-!
# Complementary contact conics

The geometric consequences here are derived from the maximality predicate for complementary
conics, described in [KM, Section 4.1]. They support density estimates obtained by removing
vertices on conics from the sphere-map image of the Hermitian norm-graph selection.
-/

public section
namespace ExplicitRIP.Edges

section Field
variable {F : Type*} [Field F]

omit [Field F] in
theorem exists_three_of_encard {A : Set (V4 F)} (hA : 3 ≤ A.encard) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  obtain ⟨B, hBA, hB⟩ := Set.exists_subset_encard_eq hA
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Set.encard_eq_three.mp hB
  exact ⟨x, hBA (by simp), y, hBA (by simp), z, hBA (by simp), hxy, hxz, hyz⟩

theorem complementary_symm {A B : Set (V4 F)} (h : IsComplementaryConicPair A B) :
    IsComplementaryConicPair B A := by
  have flip {C D : Set (V4 F)}
      (hc : 3 ≤ C.encard ∧ 3 ≤ D.encard ∧
        (∀ x ∈ C, ∀ y ∈ D, SphereContact x y) ∧
        (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ¬SphereContact x y) ∧
        (∀ x ∈ D, ∀ y ∈ D, x ≠ y → ¬SphereContact x y)) :
      3 ≤ D.encard ∧ 3 ≤ C.encard ∧
        (∀ x ∈ D, ∀ y ∈ C, SphereContact x y) ∧
        (∀ x ∈ D, ∀ y ∈ D, x ≠ y → ¬SphereContact x y) ∧
        (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ¬SphereContact x y) :=
    ⟨hc.2.1, hc.1, fun _ hx _ hy => contact_symm (hc.2.2.1 _ hy _ hx),
      hc.2.2.2.2, hc.2.2.2.1⟩
  exact ⟨flip h.1, fun z hz hg => h.2.2 z hz (flip hg),
    fun z hz hg => h.2.1 z hz (flip hg)⟩

/-- Three collinear, pairwise noncontacting parameters have no common contact. -/
theorem not_contact_third_on_line {x y z : V4 F} {c : F}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hxy : ¬SphereContact x y)
    (hzx : SphereContact z x) (hzy : SphereContact z y) :
    ¬SphereContact z (x + c • (y - x)) := by
  intro hz3
  have h1 := (contact_iff _ _).mp hzx
  have h2 := (contact_iff _ _).mp hzy
  have h3 := (contact_iff _ _).mp hz3
  have he : mq (z - (x + c • (y - x))) =
      (1 - c) * mq (z - x) + c * mq (z - y) + c * (c - 1) * mq (y - x) := by
    dsimp [mq]; ring
  rw [h1, h2, h3, mul_zero, mul_zero, zero_add, zero_add] at he
  have hq : mq (y - x) = 0 :=
    (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero hc0 (sub_ne_zero.mpr hc1))
  exact hxy ((contact_iff _ _).mpr ((mq_sub_comm x y).trans hq))

/-- A common contact forces three pairwise noncontacting points to span a plane. -/
theorem independent_differences {x y z q : V4 F}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hn : ¬SphereContact x y)
    (hqx : SphereContact q x) (hqy : SphereContact q y) (hqz : SphereContact q z) :
    LinearIndependent F ![y - x, z - x] := by
  rw [LinearIndependent.pair_iff' (sub_ne_zero.mpr hxy.symm)]
  intro c hc
  have hz : z = x + c • (y - x) := by rw [hc]; abel
  have hc0 : c ≠ 0 := by intro h; rw [h, zero_smul, add_zero] at hz; exact hxz hz.symm
  have hc1 : c ≠ 1 := by
    intro hc
    apply hyz
    calc
      y = x + (y - x) := by abel
      _ = z := by simpa only [hc, one_smul] using hz.symm
  exact not_contact_third_on_line hc0 hc1 hn hqx hqy (hz ▸ hqz)

theorem contact_of_three_and_orth {x x' y y' : V4 F}
    (hxy : SphereContact x y) (hx'y : SphereContact x' y)
    (hxy' : SphereContact x y') (horth : mb (x' - x) (y' - y) = 0) :
    SphereContact x' y' := by
  rw [contact_iff]
  have h1 := (contact_iff _ _).mp hxy
  have h2 := (contact_iff _ _).mp hx'y
  have h3 := (contact_iff _ _).mp hxy'
  dsimp [mq, mb] at *
  linear_combination h2 + h3 - h1 - 2 * horth

end Field

section Prime
variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
variable {A B : Set (V4 (ZMod p))}

omit [Fact (p % 4 = 3)] in
theorem complementary_independent (h : IsComplementaryConicPair A B)
    {x y z : V4 (ZMod p)} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    LinearIndependent (ZMod p) ![y - x, z - x] := by
  obtain ⟨q, hq, _, _, _, _, _, _, _⟩ := exists_three_of_encard h.1.2.1
  exact independent_differences hxy hxz hyz (h.1.2.2.2.1 x hx y hy hxy)
    (contact_symm (h.1.2.2.1 x hx q hq)) (contact_symm (h.1.2.2.1 y hy q hq))
    (contact_symm (h.1.2.2.1 z hz q hq))

/-- Maximality identifies each member of a complementary pair as the full common-contact family. -/
theorem mem_of_forall_contact (h : IsComplementaryConicPair A B) {z : V4 (ZMod p)}
    (hz : ∀ x ∈ A, SphereContact x z) : z ∈ B := by
  by_contra hn
  apply h.2.2 z hn
  have hnon (w : V4 (ZMod p)) (hw : w ∈ B) (hzw : z ≠ w) : ¬SphereContact z w := by
    intro hzwc
    obtain ⟨x, hx, y, hy, _, _, hxy, _, _⟩ := exists_three_of_encard h.1.1
    have hxline := mem_lineSet_of_contact p hzw hzwc (contact_symm (hz x hx))
      (contact_symm (h.1.2.2.1 x hx w hw))
    have hyline := mem_lineSet_of_contact p hzw hzwc (contact_symm (hz y hy))
      (contact_symm (h.1.2.2.1 y hy w hw))
    exact h.1.2.2.2.1 x hx y hy hxy (contact_of_mem_lineSet hzwc hxline hyline)
  refine ⟨h.1.1, h.1.2.1.trans (Set.encard_mono (Set.subset_insert _ _)), ?_, h.1.2.2.2.1, ?_⟩
  · intro x hx y hy
    rcases hy with rfl | hy
    · exact hz x hx
    · exact h.1.2.2.1 x hx y hy
  · intro x hx y hy hxy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · exact hnon y hy hxy
    · exact fun hc => hnon x hx hxy.symm (contact_symm hc)
    · exact h.1.2.2.2.2 x hx y hy hxy

/-- Three distinct contacts on one complementary conic force membership in the other. -/
theorem mem_of_three_contacts (h : IsComplementaryConicPair A B)
    {x₁ x₂ x₃ z : V4 (ZMod p)} (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hx₃ : x₃ ∈ A)
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (hz₁ : SphereContact x₁ z) (hz₂ : SphereContact x₂ z) (hz₃ : SphereContact x₃ z) : z ∈ B := by
  obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, hy12, hy13, hy23⟩ := exists_three_of_encard h.1.2.1
  have hc := h.1.2.2.1
  have h2 := Trace.two_ne_zero p
  have hlinX := complementary_independent p h hx₁ hx₂ hx₃ h12 h13 h23
  have hlinY := complementary_independent p (complementary_symm h) hy₁ hy₂ hy₃ hy12 hy13 hy23
  have ho (x : V4 (ZMod p)) (hx : x ∈ A) (y : V4 (ZMod p)) (hy : y ∈ B) :
      mb (x - x₁) (y - y₁) = 0 :=
    mb_sub_eq_zero_of_contacts h2 (hc x₁ hx₁ y₁ hy₁) (hc x hx y₁ hy₁)
      (hc x₁ hx₁ y hy) (hc x hx y hy)
  obtain ⟨α, β, he⟩ := orth_pair_span hlinX hlinY
    (ho x₂ hx₂ y₂ hy₂) (ho x₃ hx₃ y₃ hy₃) (ho x₂ hx₂ y₃ hy₃) (ho x₃ hx₃ y₂ hy₂)
    (mb_sub_eq_zero_of_contacts h2 (hc x₁ hx₁ y₁ hy₁) (hc x₂ hx₂ y₁ hy₁) hz₁ hz₂)
    (mb_sub_eq_zero_of_contacts h2 (hc x₁ hx₁ y₁ hy₁) (hc x₃ hx₃ y₁ hy₁) hz₁ hz₃)
  apply mem_of_forall_contact p h
  intro x hx
  apply contact_of_three_and_orth (hc x₁ hx₁ y₁ hy₁) (hc x hx y₁ hy₁) hz₁
  rw [he, mb_add_right, mb_smul_right, mb_smul_right, ho x hx y₂ hy₂, ho x hx y₃ hy₃,
    mul_zero, mul_zero, add_zero]

open Classical in
theorem card_contacts_le_two (h : IsComplementaryConicPair A B) {z : V4 (ZMod p)}
    (hz : z ∉ B) (S : Finset (V4 (ZMod p))) (hS : (↑S : Set _) ⊆ A) :
    (S.filter (fun x => SphereContact x z)).card ≤ 2 := by
  classical
  by_contra hn
  obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, h12, h13, h23⟩ := Finset.two_lt_card.mp (by omega :
    2 < (S.filter (fun x => SphereContact x z)).card)
  exact hz (mem_of_three_contacts p h (hS (Finset.mem_filter.mp hx₁).1)
    (hS (Finset.mem_filter.mp hx₂).1) (hS (Finset.mem_filter.mp hx₃).1) h12 h13 h23
    (Finset.mem_filter.mp hx₁).2 (Finset.mem_filter.mp hx₂).2 (Finset.mem_filter.mp hx₃).2)

end Prime
end ExplicitRIP.Edges
