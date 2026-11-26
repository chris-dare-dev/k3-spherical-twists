/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.IntersectingWalls
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.ConeHNStrict

/-!
# Cuts at a strict phase and phase gaps in the cases with a known answer

Mathlib has no triangulated category with a slicing yet, so the slicing is a variable here, as in
`ConeCutModel`.

* A cone on zero truncates compatibly at a strict cut.
* The phase gap of the two charges `1` and `i` at the phases `0` and `1/2`: some `ε ∈ (0, 1/8)`
  works, and the charge `1` on the ray of phase `0` is not moved.
-/

namespace K3TwistsTest.IntersectingWallsModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open scoped ZeroObject

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- A cone on zero has cut composite zero at a strict cut, so it truncates compatibly. -/
example (s : Slicing C) (t : ℝ) (E : C) {E₁ : C} {ι : E₁ ⟶ E}
    (hι : (s.gtProp C t).IsCoreflection ι) :
    ∃ (a : (0 : C) ⟶ E₁) (b : E₁ ⟶ E₁),
      Triangle.mk a b (ι ≫ 0) ∈ distTriang C ∧ a ≫ ι = 0 ∧ b ≫ ι = ι ≫ 𝟙 E :=
  s.exists_truncation_triangle_of_gtProp (contractible_distinguished₁ E)
    (s.gtProp_of_isZero C (isZero_zero C) t) hι hι

/-- The phase gap of the charges `1` and `i` at the phases `0` and `1/2`. -/
example : ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 8 ∧
    (∀ z ∈ ({1, Complex.I} : Set ℂ), ∀ φ ∈ ({0, 1 / 2} : Finset ℝ), ∀ m ψ : ℝ, 0 < m →
      z = (m : ℂ) * Complex.exp ((Real.pi * ψ : ℝ) * Complex.I) → |ψ - φ| < 2 * ε → ψ = φ) ∧
    ∀ φ ∈ ({0, 1 / 2} : Finset ℝ), ∀ φ' ∈ ({0, 1 / 2} : Finset ℝ), φ ≠ φ' →
      2 * ε < |φ - φ'| :=
  Complex.exists_phaseGap _ (Set.toFinite _) _

end K3TwistsTest.IntersectingWallsModel
