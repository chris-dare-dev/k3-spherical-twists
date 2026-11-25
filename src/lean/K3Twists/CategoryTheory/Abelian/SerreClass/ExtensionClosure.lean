/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Simple

/-!
# The extension closure of simple objects is a Serre class

In an abelian category, `ObjectProperty.abelianExtensionClosure P` is the smallest property of
objects that contains `P` and the zero objects and is closed under extensions: if
`0 → X₁ → X₂ → X₃ → 0` is short exact and `X₁`, `X₃` have it, so does `X₂`. Its objects are the
objects with a finite filtration whose subquotients are in `P`.

When every object of `P` is simple, the closure is a **Serre class**
(`ObjectProperty.isSerreClass_abelianExtensionClosure`): it is also closed under subobjects and
quotients. The proof is by induction on the closure. For a subobject `A ⊆ X₂` of an extension
`0 → X₁ → X₂ → X₃ → 0`, the image `A₃` of `A` in `X₃` is a subobject of `X₃` and the kernel
`A₁` of `A → A₃` a subobject of `X₁`, and `0 → A₁ → A → A₃ → 0` is short exact; quotients are
dual. A subobject of a simple object is zero or the whole object.

## Main definitions

* `ObjectProperty.abelianExtensionClosure`: the extension closure in an abelian category.

## Main results

* `ObjectProperty.abelianExtensionClosure_of_mono`, `ObjectProperty.abelianExtensionClosure_of_epi`:
  closure under subobjects and quotients when `P` consists of simple objects.
* `ObjectProperty.isSerreClass_abelianExtensionClosure`: the closure is a Serre class.

## Tags

Serre class, extension closure, simple object, finite length
-/

universe v u

open CategoryTheory Limits ZeroObject

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The **extension closure** of a property of objects of an abelian category: the smallest
property that contains `P` and the zero objects and is closed under extensions. -/
inductive abelianExtensionClosure (P : ObjectProperty C) : ObjectProperty C
  /-- Objects of `P` are in the closure. -/
  | of_prop {X : C} (hX : P X) : abelianExtensionClosure P X
  /-- Zero objects are in the closure. -/
  | of_isZero {X : C} (hX : IsZero X) : abelianExtensionClosure P X
  /-- The middle term of a short exact sequence with outer terms in the closure. -/
  | ext (S : ShortComplex C) (hS : S.ShortExact) (h₁ : abelianExtensionClosure P S.X₁)
      (h₃ : abelianExtensionClosure P S.X₃) : abelianExtensionClosure P S.X₂

variable (P : ObjectProperty C)

theorem le_abelianExtensionClosure : P ≤ P.abelianExtensionClosure :=
  fun _ hX ↦ .of_prop hX

/-- The closure is closed under isomorphisms: `0 → X → Y → 0 → 0` is short exact. -/
theorem abelianExtensionClosure_of_iso {X Y : C} (e : X ≅ Y)
    (hX : P.abelianExtensionClosure X) : P.abelianExtensionClosure Y := by
  have hS : (ShortComplex.mk e.hom (0 : Y ⟶ 0) comp_zero).ShortExact :=
    .mk' ((ShortComplex.exact_iff_epi _ rfl).2 inferInstance) inferInstance
      ((isZero_zero C).epi _)
  exact .ext _ hS hX (.of_isZero (isZero_zero C))

instance : P.abelianExtensionClosure.IsClosedUnderIsomorphisms where
  of_iso e hX := P.abelianExtensionClosure_of_iso e hX

instance : P.abelianExtensionClosure.ContainsZero where
  exists_zero := ⟨0, isZero_zero C, .of_isZero (isZero_zero C)⟩

instance : P.abelianExtensionClosure.IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := .ext _ hS h₁ h₃

/-- The closure is the smallest property containing `P` and the zero objects that is closed
under extensions. -/
theorem abelianExtensionClosure_le {Q : ObjectProperty C} [Q.ContainsZero]
    [Q.IsClosedUnderIsomorphisms] [Q.IsClosedUnderExtensions] (h : P ≤ Q) :
    P.abelianExtensionClosure ≤ Q := by
  intro X hX
  induction hX with
  | of_prop hX => exact h _ hX
  | of_isZero hX => exact Q.prop_of_isZero hX
  | ext S hS _ _ h₁ h₃ => exact Q.prop_X₂_of_shortExact hS h₁ h₃

variable {P}

/-- **Closure under subobjects**, when `P` consists of simple objects. -/
theorem abelianExtensionClosure_of_mono (hP : ∀ X, P X → Simple X) {B : C}
    (hB : P.abelianExtensionClosure B) {A : C} (i : A ⟶ B) [Mono i] :
    P.abelianExtensionClosure A := by
  induction hB generalizing A with
  | @of_prop X hB =>
    have := hP _ hB
    by_cases hi : i = 0
    · subst hi
      exact .of_isZero (IsZero.of_mono_zero A X)
    · have := (Simple.mono_isIso_iff_nonzero i).2 hi
      exact P.abelianExtensionClosure_of_iso (asIso i).symm (.of_prop hB)
  | of_isZero hB => exact .of_isZero (IsZero.of_mono i hB)
  | ext S hS _ _ ih₁ ih₃ =>
    have := hS.mono_f
    have := hS.epi_g
    let p := factorThruImage (i ≫ S.g)
    have h₃ : P.abelianExtensionClosure (image (i ≫ S.g)) := ih₃ (image.ι (i ≫ S.g))
    have hk : (kernel.ι p ≫ i) ≫ S.g = 0 :=
      calc (kernel.ι p ≫ i) ≫ S.g = kernel.ι p ≫ p ≫ image.ι (i ≫ S.g) := by simp [p]
        _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]
    have : Mono (hS.exact.lift (kernel.ι p ≫ i) hk) := by
      have : Mono (hS.exact.lift (kernel.ι p ≫ i) hk ≫ S.f) := by
        rw [hS.exact.lift_f]
        infer_instance
      exact mono_of_mono _ S.f
    have h₁ : P.abelianExtensionClosure (kernel p) := ih₁ (hS.exact.lift (kernel.ι p ≫ i) hk)
    have hSA : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
      .mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p)) inferInstance inferInstance
    exact .ext _ hSA h₁ h₃

/-- **Closure under quotients**, when `P` consists of simple objects. -/
theorem abelianExtensionClosure_of_epi (hP : ∀ X, P X → Simple X) {B : C}
    (hB : P.abelianExtensionClosure B) {Q : C} (p : B ⟶ Q) [Epi p] :
    P.abelianExtensionClosure Q := by
  induction hB generalizing Q with
  | @of_prop X hB =>
    have := hP _ hB
    by_cases hp : p = 0
    · subst hp
      exact .of_isZero (IsZero.of_epi_zero X Q)
    · have := isIso_of_epi_of_ne_zero hp
      exact P.abelianExtensionClosure_of_iso (asIso p) (.of_prop hB)
  | of_isZero hB => exact .of_isZero (IsZero.of_epi p hB)
  | ext S hS _ _ ih₁ ih₃ =>
    have := hS.mono_f
    have := hS.epi_g
    let m := image.ι (S.f ≫ p)
    have h₁ : P.abelianExtensionClosure (image (S.f ≫ p)) := ih₁ (factorThruImage (S.f ≫ p))
    have hk : S.f ≫ p ≫ cokernel.π m = 0 := by
      rw [← Category.assoc, ← congrArg (fun x ↦ x ≫ cokernel.π m) (image.fac (S.f ≫ p)),
        Category.assoc, cokernel.condition, comp_zero]
    have : Epi (hS.exact.desc (p ≫ cokernel.π m) hk) := by
      have : Epi (S.g ≫ hS.exact.desc (p ≫ cokernel.π m) hk) := by
        rw [hS.exact.g_desc]
        infer_instance
      exact epi_of_epi S.g _
    have h₃ : P.abelianExtensionClosure (cokernel m) := ih₃ (hS.exact.desc (p ≫ cokernel.π m) hk)
    have hSQ : (ShortComplex.mk m (cokernel.π m) (cokernel.condition m)).ShortExact :=
      .mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel m)) inferInstance
        inferInstance
    exact .ext _ hSQ h₁ h₃

/-- **The extension closure of simple objects is a Serre class.** -/
theorem isSerreClass_abelianExtensionClosure (hP : ∀ X, P X → Simple X) :
    P.abelianExtensionClosure.IsSerreClass where
  prop_of_mono f _ hY := abelianExtensionClosure_of_mono hP hY f
  prop_of_epi f _ hX := abelianExtensionClosure_of_epi hP hX f

end CategoryTheory.ObjectProperty
