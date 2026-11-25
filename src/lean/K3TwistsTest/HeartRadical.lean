/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.HeartRadical

/-!
# The radical and the charge function on the heart: instances

* For any slicing, every object of the heart `P((a, a+1])` has a largest subobject of phase
  `a + 1`, with no chain condition, and the inclusion of `P(a+1)` is a left adjoint.
* For a prestability condition, the interval class of `P(1)` on the subobjects of an object of
  `P((0, 1])` is hereditary, the radical of a subobject is cut out by the radical of the object,
  and `Im Z`, `-Re Z` are the rank and degree of a charge function on its subobjects.

Built by `lake test`.
-/

noncomputable section

namespace HeartRadicalModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

section Slicing

variable (s : Slicing C) (a : ℝ)

example (R : s.HeartCat C a) :
    ∃ t : Subobject R, IsGreatest {A : Subobject R | s.heartTop C a (A : s.HeartCat C a)} t :=
  s.exists_isGreatest_heartTop C a R

example : (s.heartTop C a).ι.IsLeftAdjoint := s.isLeftAdjoint_ι_heartTop C a

/-- `P(a+1)` is closed under quotients and extensions in the heart of any slicing. -/
example : (s.heartTop C a).IsClosedUnderQuotients := inferInstance

example : (s.heartTop C a).IsClosedUnderExtensions := inferInstance

end Slicing

section Charge

variable {Λ : Type*} [AddCommGroup Λ] {v : K₀ C →+ Λ}
  (σ : PreStabilityCondition.WithClassMap C v)

example (R : σ.slicing.HeartCat C 0) :
    ((σ.slicing.heartTop C 0).intervalClass R).Hereditary :=
  σ.intervalClass_heartTop_hereditary 0 R

/-- The radical of every subobject of an object of `P((0, 1])`, from the radical of the object. -/
example (R : σ.slicing.HeartCat C 0) (A : Subobject R) :
    ∃ t : Subobject R, IsGreatest
      {B : Subobject R | B ≤ A ∧ σ.slicing.heartTop C 0 (B : σ.slicing.HeartCat C 0)} t := by
  obtain ⟨t, ht⟩ := σ.slicing.exists_isGreatest_heartTop C 0 R
  exact ⟨A ⊓ t, σ.isGreatest_inf_heartTop 0 ht A⟩

example (X : σ.slicing.HeartCat C 0) (A : Subobject X) :
    (σ.heartChargeFunction X).rk A = (σ.charge (A : σ.slicing.HeartCat C 0).obj).im :=
  rfl

example (X : σ.slicing.HeartCat C 0) : IsModularLattice (Subobject X) :=
  σ.isModularLattice_subobject_heart X

end Charge

end HeartRadicalModel

end
