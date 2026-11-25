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

end Slicing

end HeartAbelianModel

end
