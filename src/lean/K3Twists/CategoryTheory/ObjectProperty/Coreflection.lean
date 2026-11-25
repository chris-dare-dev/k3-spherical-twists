/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Coreflections into a class of objects

Let `P` be a class of objects of a category `C` and `R : C`. A morphism `ε : D ⟶ R` is a
*coreflection of `R` into `P`* (`P.IsCoreflection ε`) when `D` lies in `P` and every morphism
from an object of `P` to `R` factors uniquely through `ε`: the object `D` represents the functor
`Hom(-, R)` on `P`, with counit `ε`. In the torsion theory of an abelian category, with `P` a
torsion class, `ε` is the inclusion of the torsion radical `t(R) ⊆ R`.

This is the value at `R` of the partial right adjoint of the inclusion `P.ι` (Mathlib's
`Functor.partialRightAdjoint`): `R` has a coreflection exactly when
`P.ι.rightAdjointObjIsDefined R` (`rightAdjointObjIsDefined_ι_iff`), and every object has one
exactly when `P.ι` is a left adjoint (`isLeftAdjoint_ι_iff`).

## Main results

* `IsCoreflection.lift`, `IsCoreflection.hom_ext`: the universal property;
* `IsCoreflection.isoOfIsCoreflection`: two coreflections of `R` are isomorphic over `R`;
* `IsCoreflection.rightAdjointObjIsDefined`, `isCoreflection_partialRightAdjoint`: coreflections
  are the partial right adjoint of `P.ι`;
* `coreflectiveι`: if every object has a coreflection, `P.ι` is coreflective.

The abelian statements (the counit is a monomorphism, its image is the largest subobject in `P`,
existence on Noetherian objects) are in
`K3Twists/CategoryTheory/Abelian/TorsionTheory/Radical.lean`.

## Tags

coreflection, coreflective subcategory, representing object, partial adjoint, radical
-/

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- `ε : D ⟶ R` is a *coreflection of `R` into `P`*: `D` lies in `P`, and composition with `ε`
is a bijection `Hom(A, D) ≃ Hom(A, R)` for every `A` in `P`. -/
structure IsCoreflection {D R : C} (ε : D ⟶ R) : Prop where
  /-- The representing object lies in `P`. -/
  prop : P D
  /-- Every morphism from an object of `P` to `R` factors uniquely through `ε`. -/
  bijective : ∀ ⦃A : C⦄, P A → Function.Bijective fun g : A ⟶ D => g ≫ ε

namespace IsCoreflection

variable {P} {D R : C} {ε : D ⟶ R} (h : P.IsCoreflection ε)
include h

/-- The factorization of `f : A ⟶ R`, `A` in `P`, through the coreflection. -/
noncomputable def lift {A : C} (hA : P A) (f : A ⟶ R) : A ⟶ D :=
  (Equiv.ofBijective _ (h.bijective hA)).symm f

@[reassoc (attr := simp)]
theorem lift_comp {A : C} (hA : P A) (f : A ⟶ R) : h.lift hA f ≫ ε = f :=
  Equiv.ofBijective_apply_symm_apply _ (h.bijective hA) f

theorem hom_ext {A : C} (hA : P A) {g g' : A ⟶ D} (w : g ≫ ε = g' ≫ ε) : g = g' :=
  (h.bijective hA).1 w

theorem eq_lift {A : C} (hA : P A) {f : A ⟶ R} {g : A ⟶ D} (w : g ≫ ε = f) : g = h.lift hA f :=
  h.hom_ext hA (by simp [w])

/-- **Uniqueness.** Two coreflections of `R` into `P` are isomorphic over `R`. -/
noncomputable def isoOfIsCoreflection {D' : C} {ε' : D' ⟶ R} (h' : P.IsCoreflection ε') :
    D ≅ D' where
  hom := h'.lift h.prop ε
  inv := h.lift h'.prop ε'
  hom_inv_id := h.hom_ext h.prop (by simp)
  inv_hom_id := h'.hom_ext h'.prop (by simp)

@[reassoc (attr := simp)]
theorem isoOfIsCoreflection_hom_comp {D' : C} {ε' : D' ⟶ R} (h' : P.IsCoreflection ε') :
    (h.isoOfIsCoreflection h').hom ≫ ε' = ε := by
  simp [isoOfIsCoreflection]

/-- Precomposing a coreflection with an isomorphism gives a coreflection. -/
theorem iso_comp [P.IsClosedUnderIsomorphisms] {D' : C} (e : D' ≅ D) :
    P.IsCoreflection (e.hom ≫ ε) := by
  refine ⟨P.prop_of_iso e.symm h.prop, fun A hA => ?_⟩
  have he : Function.Bijective fun g : A ⟶ D' => g ≫ e.hom :=
    ⟨fun g g' w => by simpa using congrArg (· ≫ e.inv) w,
      fun g => ⟨g ≫ e.inv, by simp⟩⟩
  convert (h.bijective hA).comp he using 1
  funext g
  simp

/-- A coreflection gives a representing object of `Hom(P.ι -, R)`. -/
noncomputable def representableBy :
    (P.ι.op ⋙ yoneda.obj R).RepresentableBy (⟨D, h.prop⟩ : P.FullSubcategory) where
  homEquiv {X} := P.fullyFaithfulι.homEquiv.trans (Equiv.ofBijective _ (h.bijective X.property))
  homEquiv_comp f g := by
    change (f ≫ g).hom ≫ ε = f.hom ≫ g.hom ≫ ε
    simp

/-- A coreflection is the value of the partial right adjoint of `P.ι`: the partial right adjoint
is defined at `R`. -/
theorem rightAdjointObjIsDefined : P.ι.rightAdjointObjIsDefined R :=
  h.representableBy.isRepresentable

end IsCoreflection

variable {P}

/-- The counit of the partial right adjoint of `P.ι` is a coreflection. -/
theorem isCoreflection_partialRightAdjoint (Y : P.ι.PartialRightAdjointSource) :
    P.IsCoreflection (P.ι.partialRightAdjointHomEquiv (𝟙 (P.ι.partialRightAdjointObj Y))) := by
  refine ⟨(P.ι.partialRightAdjointObj Y).property, fun A hA => ?_⟩
  let A' : P.FullSubcategory := ⟨A, hA⟩
  have key : ∀ g : A ⟶ (P.ι.partialRightAdjointObj Y).obj,
      g ≫ P.ι.partialRightAdjointHomEquiv (𝟙 (P.ι.partialRightAdjointObj Y)) =
        P.ι.partialRightAdjointHomEquiv (homMk g : A' ⟶ P.ι.partialRightAdjointObj Y) := by
    intro g
    have := P.ι.partialRightAdjointHomEquiv_comp (𝟙 (P.ι.partialRightAdjointObj Y))
      (homMk g : A' ⟶ P.ι.partialRightAdjointObj Y)
    rw [Category.comp_id] at this
    exact this.symm
  refine ⟨fun g g' w => ?_, fun f => ?_⟩
  · simp only [key] at w
    exact congrArg InducedCategory.Hom.hom (P.ι.partialRightAdjointHomEquiv.injective w)
  · refine ⟨((P.ι.partialRightAdjointHomEquiv (X := A') (Y := Y)).symm f).hom, ?_⟩
    simp only [key]
    exact (P.ι.partialRightAdjointHomEquiv (X := A') (Y := Y)).apply_symm_apply f

/-- `R` has a coreflection into `P` exactly when the partial right adjoint of `P.ι` is defined
at `R`. -/
theorem rightAdjointObjIsDefined_ι_iff {R : C} :
    P.ι.rightAdjointObjIsDefined R ↔ ∃ (D : C) (ε : D ⟶ R), P.IsCoreflection ε :=
  ⟨fun h => ⟨_, _, isCoreflection_partialRightAdjoint ⟨R, h⟩⟩,
    fun ⟨_, _, h⟩ => h.rightAdjointObjIsDefined⟩

/-- Every object has a coreflection into `P` exactly when the inclusion `P.ι` is a left
adjoint. -/
theorem isLeftAdjoint_ι_iff :
    P.ι.IsLeftAdjoint ↔ ∀ R : C, ∃ (D : C) (ε : D ⟶ R), P.IsCoreflection ε := by
  rw [Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top]
  refine ⟨fun h R => rightAdjointObjIsDefined_ι_iff.1 (by simp [h]), fun h => ?_⟩
  ext R
  simpa using rightAdjointObjIsDefined_ι_iff.2 (h R)

/-- If every object has a coreflection into `P`, the inclusion `P.ι` is coreflective. -/
@[instance_reducible]
noncomputable def coreflectiveι (h : ∀ R : C, ∃ (D : C) (ε : D ⟶ R), P.IsCoreflection ε) :
    Coreflective P.ι :=
  haveI := isLeftAdjoint_ι_iff.2 h
  { R := P.ι.rightAdjoint
    adj := Adjunction.ofIsLeftAdjoint P.ι }

end CategoryTheory.ObjectProperty
