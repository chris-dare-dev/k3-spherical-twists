/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Subobjects along a fully faithful functor

A functor `G : C ⥤ D` that preserves monomorphisms sends a subobject `A ↪ X` to the subobject
`G A ↪ G X` (`CategoryTheory.Functor.mapSubobject`). If `G` is fully faithful, this map reflects
the order. If moreover every subobject of `G X` is the image of a monomorphism into `X` up to
isomorphism, the map is an order isomorphism `Subobject X ≃o Subobject (G X)`
(`CategoryTheory.Functor.subobjectOrderIso`).

This is how a realization functor identifies subobject lattices: a fully faithful exact functor
whose essential image is closed under subobjects (a Serre subcategory) carries the lattice of
subobjects of an object onto that of its image.

## Main definitions

* `CategoryTheory.Functor.mapSubobject`: `mk f ↦ mk (G.map f)`.
* `CategoryTheory.Functor.subobjectOrderIso`: the order isomorphism.

## Main results

* `CategoryTheory.Functor.mapSubobject_le_mapSubobject_iff`: a fully faithful functor reflects the
  order of subobjects.
* `CategoryTheory.Functor.underlyingMapSubobjectIso`: the underlying object of the image of a
  subobject `P` is `G P`; `CategoryTheory.Subobject.mapObjUnderlyingIso`: the same for the image
  under a monomorphism.
-/

namespace CategoryTheory

open Limits

namespace Subobject

variable {C : Type*} [Category C]

/-- The underlying object of the image `(map f).obj N` of a subobject under a monomorphism `f` is
the underlying object of `N`. -/
noncomputable def mapObjUnderlyingIso {X Y : C} (f : X ⟶ Y) [Mono f] (N : Subobject X) :
    (((Subobject.map f).obj N : Subobject Y) : C) ≅ (N : C) :=
  (Subobject.isoOfEq _ _ (by
    have h : (Subobject.map f).obj (Subobject.mk N.arrow) = Subobject.mk (N.arrow ≫ f) := rfl
    rwa [Subobject.mk_arrow] at h)).trans (Subobject.underlyingIso (N.arrow ≫ f))

end Subobject

namespace Functor

variable {C D : Type*} [Category C] [Category D] (G : C ⥤ D) [G.PreservesMonomorphisms]

/-- The image of a subobject `mk f` of `X` under a functor preserving monomorphisms, the
subobject `mk (G.map f)` of `G X`. -/
noncomputable def mapSubobject (X : C) : Subobject X → Subobject (G.obj X) :=
  Subobject.lift (fun _ f _ ↦ Subobject.mk (G.map f)) fun _ _ f g _ _ i w ↦
    Subobject.mk_eq_mk_of_comm _ _ (G.mapIso i) (by simp [← G.map_comp, w])

@[simp]
lemma mapSubobject_mk {X A : C} (f : A ⟶ X) [Mono f] :
    G.mapSubobject X (Subobject.mk f) = Subobject.mk (G.map f) :=
  rfl

lemma mapSubobject_eq_mk {X : C} (P : Subobject X) :
    G.mapSubobject X P = Subobject.mk (G.map P.arrow) := by
  have h : G.mapSubobject X (Subobject.mk P.arrow) = Subobject.mk (G.map P.arrow) := rfl
  rwa [Subobject.mk_arrow] at h

/-- The underlying object of the image of a subobject `P` is `G P`. -/
noncomputable def underlyingMapSubobjectIso {X : C} (P : Subobject X) :
    ((G.mapSubobject X P : Subobject (G.obj X)) : D) ≅ G.obj (P : C) :=
  (Subobject.isoOfEq _ _ (G.mapSubobject_eq_mk P)).trans (Subobject.underlyingIso (G.map P.arrow))

lemma mapSubobject_mono {X : C} {P P' : Subobject X} (h : P ≤ P') :
    G.mapSubobject X P ≤ G.mapSubobject X P' := by
  induction P using Subobject.ind with | h f =>
  induction P' using Subobject.ind with | h g =>
  simp only [mapSubobject_mk]
  exact Subobject.mk_le_mk_of_comm (G.map (Subobject.ofMkLEMk f g h))
    (by rw [← G.map_comp, Subobject.ofMkLEMk_comp])

variable [G.Full] [G.Faithful]

/-- **A fully faithful functor reflects the order of subobjects.** -/
theorem mapSubobject_le_mapSubobject_iff {X : C} (P P' : Subobject X) :
    G.mapSubobject X P ≤ G.mapSubobject X P' ↔ P ≤ P' := by
  refine ⟨fun h ↦ ?_, G.mapSubobject_mono⟩
  induction P using Subobject.ind with | h f =>
  induction P' using Subobject.ind with | h g =>
  simp only [mapSubobject_mk] at h
  refine Subobject.mk_le_mk_of_comm (G.preimage (Subobject.ofMkLEMk _ _ h)) (G.map_injective ?_)
  rw [G.map_comp, G.map_preimage, Subobject.ofMkLEMk_comp]

/-- **Subobjects along a fully faithful functor.** If `G` is fully faithful, preserves
monomorphisms, and every subobject of `G X` comes from a monomorphism into `X` up to isomorphism,
then `P ↦ G P` is an order isomorphism `Subobject X ≃o Subobject (G X)`. -/
noncomputable def subobjectOrderIso (X : C)
    (hG : ∀ ⦃Y : D⦄ (f : Y ⟶ G.obj X) [Mono f],
      ∃ (Z : C) (g : Z ⟶ X) (_ : Mono g) (e : G.obj Z ≅ Y), e.hom ≫ f = G.map g) :
    Subobject X ≃o Subobject (G.obj X) :=
  RelIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (G.mapSubobject X) (G.mapSubobject_le_mapSubobject_iff))
    fun S ↦ by
      obtain ⟨Z, g, _, e, he⟩ := hG S.arrow
      refine ⟨Subobject.mk g, ?_⟩
      change G.mapSubobject X (Subobject.mk g) = S
      rw [mapSubobject_mk, ← Subobject.mk_arrow S]
      exact Subobject.mk_eq_mk_of_comm _ _ e he

lemma subobjectOrderIso_apply (X : C)
    (hG : ∀ ⦃Y : D⦄ (f : Y ⟶ G.obj X) [Mono f],
      ∃ (Z : C) (g : Z ⟶ X) (_ : Mono g) (e : G.obj Z ≅ Y), e.hom ≫ f = G.map g)
    (P : Subobject X) : G.subobjectOrderIso X hG P = G.mapSubobject X P :=
  rfl

end Functor

end CategoryTheory
