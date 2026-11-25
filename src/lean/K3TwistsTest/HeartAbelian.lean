/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Heart
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Hearts are abelian: instances

* The heart of Mathlib's canonical t-structure on the derived category `D(A)` of an abelian
  category is abelian, by the general theorem (not by identifying it with `A`).
* The heart `P((a, a+1])` of any slicing is abelian, and a morphism of it has a kernel and a
  cokernel there.
* In the heart of any slicing, `(P(a+1), P((a, a+1)))` is a torsion pair, so `P(a+1)` is a
  torsion class and the thin interval `P((a, a+1))` a torsion-free class.
* In the heart `P((0, 1])` of a prestability condition, `P(1)` is a Serre class (the kernel of
  `Im Z`), closed under subobjects, quotients and extensions.
* The converse of the tilting theorem applies to the hearts of one slicing at base points
  `a ≤ b ≤ a + 1`; the hypotheses of `heart_eq_of_le` hold for the t-structure of `σ` itself.

Built by `lake test`.
-/

noncomputable section

namespace HeartAbelianModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

section Derived

universe w v u

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The heart of the canonical t-structure on `D(A)` is abelian. -/
example : Abelian (DerivedCategory.TStructure.t (C := A)).heart.FullSubcategory :=
  DerivedCategory.TStructure.t.heartFullSubcategoryAbelian

end Derived

section Slicing

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (s : Slicing C) (a : ℝ)

example : Abelian (s.HeartCat C a) := inferInstance

example {X Y : s.HeartCat C a} (f : X ⟶ Y) : HasKernel f := inferInstance

example {X Y : s.HeartCat C a} (f : X ⟶ Y) : HasCokernel f := inferInstance

example : Abelian.IsTorsionClass (s.heartTop C a) :=
  (s.torsionTheory_heartTop C a).isTorsionClass

example : Abelian.IsTorsionFreeClass (s.heartFree C a) :=
  (s.torsionTheory_heartTop C a).isTorsionFreeClass

example {θ : ℝ} (h₁ : a ≤ θ) (h₂ : θ ≤ a + 1) :
    Abelian.IsTorsionClass (s.heartAbove C a θ) :=
  (s.torsionTheory_heartAbove C h₁ h₂).isTorsionClass

end Slicing

section Charge

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  {Λ : Type*} [AddCommGroup Λ] {v : K₀ C →+ Λ} (σ : PreStabilityCondition.WithClassMap C v)

/-- The weight of `P((0, 1])` is `Im Z`. -/
example (E : C) : σ.heartWeight 0 (K₀.of C E) = (σ.charge E).im := by
  simp [PreStabilityCondition.WithClassMap.heartWeight, PreStabilityCondition.WithClassMap.charge,
    classOf]

example : (σ.slicing.heartTop C 0).IsSerreClass := σ.isSerreClass_heartTop 0

example {X Y : σ.slicing.HeartCat C 0} (f : X ⟶ Y) [Mono f]
    (hY : σ.slicing.P (0 + 1) Y.obj) : σ.slicing.P (0 + 1) X.obj :=
  have := σ.isSerreClass_heartTop 0
  (σ.slicing.heartTop C 0).prop_of_mono f hY

/-- The hypotheses of `heart_eq_of_le` are met by the t-structure of `σ` itself. -/
example : (σ.slicing.toTStructure C 0).heart = σ.slicing.heartProp C 0 :=
  σ.heart_eq_of_le _ le_rfl (σ.slicing.toTStructure C 0).le_zero_le fun E hE hEZ => σ.charge_mem_of_heartProp
      ((σ.slicing.toTStructure_mem_heart_iff C 0 E).1 hE) hEZ

end Charge

section Tilt

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (s : Slicing C) {a b : ℝ}

/-- The heart at `b ∈ [a, a+1]` is the tilt of the heart at `a`. -/
example (h₁ : a ≤ b) (h₂ : b ≤ a + 1) (E : C) :
    (s.toTStructure C b).heart E ↔ (s.toTStructure C a).le 0 E ∧ (s.toTStructure C a).ge (-1) E ∧
      (s.toTStructure C b).le 0 (((s.toTStructure C a).truncGE 0).obj E) ∧
      (s.toTStructure C b).ge 0 (((s.toTStructure C a).truncLT 0).obj E) :=
  TStructure.mem_heart_iff_of_le (s.toTStructure_le_neg_one_le C h₂) (s.toTStructure_le_le C h₁) E

/-- The torsion pair of that tilt, in the abelian category `P((a, a+1])`. -/
example (h₁ : a ≤ b) (h₂ : b ≤ a + 1) :
    Abelian.TorsionTheory (((s.toTStructure C b).le 0).inverseImage (s.heartProp C a).ι)
      (((s.toTStructure C b).ge 1).inverseImage (s.heartProp C a).ι) :=
  TStructure.torsionTheory_of_le (H := s.HeartCat C a) (s.toTStructure_le_neg_one_le C h₂)
    (s.toTStructure_le_le C h₁)

end Tilt

end HeartAbelianModel

end
