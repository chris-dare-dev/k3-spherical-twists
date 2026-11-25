/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Algebra.Homology.DerivedCategory.AbelianHeart

/-!
# Window dévissage: test models

* **The identity functor.** The window condition holds on every pair of objects for every
  window, so window dévissage, full faithfulness on the extension closure and the essential image
  apply to any family of objects of any pretriangulated category.
* **The model `vect → ⟨S⟩`.** For one object `S` with no shifted self-morphisms in nonzero
  degrees and a triangulated functor `F` bijective on `End(S)` with `Hom(F S, (F S)⟦n⟧) = 0` for
  `n = ±1`, the window `[0, 1]` holds on `{S}`, so `F` is fully faithful on the extension closure
  of `S` with essential image the extension closure of `F S`. This is the model of the functor
  `V ↦ V ⊗ S` out of graded vector spaces, which Mathlib cannot build as a triangulated functor;
  the check is on the hypotheses it would satisfy.
* **The standard heart.** `singleFunctor C 0 : C ⥤ D(C)` satisfies the heart-type fields, so for
  every family `Σ` of simple objects of an abelian category `C`, the objects `A` whose complex
  `A[0]` is in the extension closure of the `S[0]`, `S ∈ Σ`, form a Serre class of `C`; and the
  abelian corollary applies to the identity functor of `D(C)` on the family `Σ[0]`.

Built by `lake test`.
-/

universe w

namespace ExtComparisonModel

open CategoryTheory Limits Pretriangulated

section Identity

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

/-- Window dévissage for the identity functor, in every window. -/
example (a b : ℤ) {X Y : C} (hX : P.extensionClosure X) (hY : P.extensionClosure Y) :
    (𝟭 C).IsExtWindow a b X Y :=
  Functor.isExtWindow_of_extensionClosure (fun S T _ _ ↦ Functor.isExtWindow_id a b S T) hX hY

/-- Full faithfulness of the identity on the extension closure, from window data in `[0, 1]`. -/
noncomputable example : (P.extensionClosure.ι ⋙ 𝟭 C).FullyFaithful :=
  Functor.fullyFaithfulOfIsExtWindow (a := 0) (b := 1) le_rfl zero_le_one
    fun S T _ _ ↦ Functor.isExtWindow_id 0 1 S T

/-- The essential image of the identity on the extension closure. -/
example : P.extensionClosure.map (𝟭 C) = (P.map (𝟭 C)).extensionClosure :=
  Functor.map_extensionClosure_eq (a := 0) (b := 1) (by norm_num) le_rfl
    fun S T _ _ ↦ Functor.isExtWindow_id 0 1 S T

end Identity

section Exceptional

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] {S : C}
  (hS : ∀ n : ℤ, n ≠ 0 → ∀ f : S ⟶ S⟦n⟧, f = 0)
  (hFS : ∀ n : ℤ, n ≠ 0 → -1 ≤ n → n ≤ 1 → ∀ g : F.obj S ⟶ (F.obj S)⟦n⟧, g = 0)
  (h0 : Function.Bijective (F.map : (S ⟶ S) → (F.obj S ⟶ F.obj S)))

include hS hFS h0

theorem window_singleton :
    ∀ ⦃X Y : C⦄, (· = S) X → (· = S) Y → F.IsExtWindow 0 1 X Y := by
  rintro X Y rfl rfl
  exact .of_vanishing hS (fun n hn ha hb ↦ hFS n hn (by lia) hb) h0

/-- `F` is fully faithful on the extension closure of `S`. -/
noncomputable example :
    (ObjectProperty.extensionClosure (· = S)).ι ⋙ F |>.FullyFaithful :=
  F.fullyFaithfulOfIsExtWindow le_rfl zero_le_one (window_singleton F hS hFS h0)

/-- Its essential image there is the extension closure of `F S`. -/
example : (ObjectProperty.extensionClosure (· = S)).map F =
    (ObjectProperty.map (· = S) F).extensionClosure :=
  F.map_extensionClosure_eq (by norm_num) le_rfl (window_singleton F hS hFS h0)

end Exceptional

section Heart

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{w} C]
  (Q : ObjectProperty C) (hQ : ∀ X, Q X → Simple X)

include hQ

/-- In the standard heart, the objects whose complex lies in the extension closure of a family
of simple objects form a Serre class. -/
example : ObjectProperty.IsSerreClass (fun A : C ↦
    (Q.map (DerivedCategory.singleFunctor C 0)).extensionClosure
      ((DerivedCategory.singleFunctor C 0).obj A)) :=
  (DerivedCategory.abelianHeartHypotheses_singleFunctor C).isSerreClass_extensionClosure
    fun _ ⟨X, hX, ⟨e⟩⟩ ↦ ⟨X, hQ X hX, ⟨e⟩⟩

/-- The abelian corollary of window dévissage for the identity functor of `D(C)`. -/
example : ObjectProperty.IsSerreClass (fun A : C ↦
    ∃ X, (Q.map (DerivedCategory.singleFunctor C 0)).extensionClosure X ∧
      Nonempty ((𝟭 (DerivedCategory C)).obj X ≅ (DerivedCategory.singleFunctor C 0).obj A)) :=
  (DerivedCategory.abelianHeartHypotheses_singleFunctor C).isSerreClass_image (a := 0) (b := 1)
    (by norm_num) le_rfl (fun S T _ _ ↦ Functor.isExtWindow_id 0 1 S T)
    fun _ ⟨X, hX, ⟨e⟩⟩ ↦ ⟨X, hQ X hX, ⟨e⟩⟩

end Heart

end ExtComparisonModel
