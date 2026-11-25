/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.TStructure

/-!
# The t-structure of a slicing: interface checks

For any slicing `s` and `a ∈ ℝ`:

* the heart of `s.toTStructure a` is the half-open interval `P((a, a+1])`, and the full
  subcategory `s.HeartCat a` is its heart in Mathlib's sense (`TStructure.Heart`);
* a semistable object of phase `a + 1` is in the heart and one of phase `a` is in the heart at
  `a - 1`: the heart is half-open on the left;
* the open interval `P((a, a+1))` lies in the heart; shifting by `n` moves the heart at `a` to the
  heart at `a + n`;
* every object is `t`-bounded.

Built by `lake test`.
-/

namespace SlicingHeartModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (s : Slicing C) (a : ℝ)

example : (s.toTStructure C a).heart = s.gtProp C a ⊓ s.leProp C (a + 1) :=
  s.toTStructure_heart C a

example : (s.toTStructure C a).ιHeart (H := s.HeartCat C a) = (s.heartProp C a).ι :=
  rfl

example {E : C} (hE : s.P (a + 1) E) : (s.toTStructure C a).heart E := by
  rw [Slicing.toTStructure_mem_heart_iff]
  exact s.heartProp_of_semistable C hE (by linarith) le_rfl

example {E : C} (hE : s.P a E) : (s.toTStructure C (a - 1)).heart E := by
  rw [Slicing.toTStructure_mem_heart_iff]
  exact s.heartProp_of_semistable C hE (by linarith) (by linarith)

example {E : C} (hE : s.intervalProp C a (a + 1) E) : (s.toTStructure C a).heart E := by
  rw [Slicing.toTStructure_mem_heart_iff]
  exact s.intervalProp_le_heartProp C a E hE

example {E : C} (n : ℤ) (hE : (s.toTStructure C a).heart E) :
    (s.toTStructure C (a + n)).heart (E⟦n⟧) := by
  rw [Slicing.toTStructure_mem_heart_iff] at hE ⊢
  exact s.heartProp_shift C a E n hE

example (E : C) : (s.toTStructure C a).bounded E :=
  s.toTStructure_bounded C a E

end SlicingHeartModel
