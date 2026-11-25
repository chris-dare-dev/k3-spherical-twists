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

end Charge

end HeartAbelianModel

end
