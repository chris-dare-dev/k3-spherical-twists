/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Abelian.TorsionTheory.Saturation
import K3Twists.CategoryTheory.Subobject.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Transport of saturation and radicals along an equivalence

Let `G : C ⥤ D` be an equivalence of abelian categories carrying a class of objects `P` of `C` to
a class `P'` of `D` (`P' (G X) ↔ P X`). For an object `R` of `C`, `G` identifies the subobjects
of `R` with those of `G R` (`CategoryTheory.Functor.subobjectOrderIsoOfIsEquivalence`), and a
subquotient `b / a` lies in `P` exactly when `G b / G a` lies in `P'`
(`CategoryTheory.ObjectProperty.subQ_mapSubobject_iff`): an equivalence preserves cokernels.
So the order isomorphism matches the interval classes of `P` and `P'`, and the transport theorem of
the order layer (`IntervalClass.sat_map`) gives:

* `ObjectProperty.mapSubobject_intervalClass_sat`: `G (Sat_P a) = Sat_{P'} (G a)`;
* `ObjectProperty.mapSubobject_intervalClass_rad`: `G (t_P R) = t_{P'} (G R)`.

This is the categorical form of the transport of the torsion part `t` and of the saturation
`Sat` along an equivalence that carries one class to the other; the order layer has it for order
isomorphisms of lattices that match interval classes.

## Main definitions

* `CategoryTheory.Functor.subobjectOrderIsoOfIsEquivalence`: subobjects along an equivalence.

## Main results

* `CategoryTheory.ObjectProperty.subQ_mapSubobject_iff`
* `CategoryTheory.ObjectProperty.mapSubobject_intervalClass_sat`
* `CategoryTheory.ObjectProperty.mapSubobject_intervalClass_rad`

## Tags

torsion class, radical, saturation, equivalence of categories, transport
-/

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

namespace Functor

variable (G : C ⥤ D) [G.IsEquivalence]

omit [Abelian D] in
/-- Every subobject of `G R` comes from a subobject of `R`. -/
lemma exists_of_mono_of_isEquivalence (R : C) ⦃Y : D⦄ (f : Y ⟶ G.obj R) [Mono f] :
    ∃ (Z : C) (g : Z ⟶ R) (_ : Mono g) (e : G.obj Z ≅ Y), e.hom ≫ f = G.map g := by
  let e := G.objObjPreimageIso Y
  refine ⟨G.objPreimage Y, G.preimage (e.hom ≫ f), ?_, e, (G.map_preimage _).symm⟩
  exact G.mono_of_mono_map (by rw [G.map_preimage]; infer_instance)

/-- **An equivalence identifies subobject lattices**: `P ↦ G P`, an order isomorphism
`Subobject R ≃o Subobject (G R)`. -/
noncomputable def subobjectOrderIsoOfIsEquivalence (R : C) :
    Subobject R ≃o Subobject (G.obj R) :=
  G.subobjectOrderIso R (G.exists_of_mono_of_isEquivalence R)

lemma subobjectOrderIsoOfIsEquivalence_apply (R : C) (P : Subobject R) :
    G.subobjectOrderIsoOfIsEquivalence R P = G.mapSubobject R P :=
  rfl

/-- An equivalence carries Noetherian objects to Noetherian objects. -/
lemma isNoetherianObject_obj (R : C) [IsNoetherianObject R] : IsNoetherianObject (G.obj R) := by
  rw [isNoetherianObject_iff_not_strictMono]
  intro f hf
  exact not_strictMono_of_wellFoundedGT _
    ((G.subobjectOrderIsoOfIsEquivalence R).symm.strictMono.comp hf)

end Functor

namespace ObjectProperty

variable {P : ObjectProperty C} {P' : ObjectProperty D} [P.IsClosedUnderIsomorphisms]
  [P'.IsClosedUnderIsomorphisms] (G : C ⥤ D) [G.IsEquivalence]

/-- **An equivalence carrying `P` to `P'` matches the subquotient predicates**: `b / a` lies in `P`
exactly when `G b / G a` lies in `P'`. -/
theorem subQ_mapSubobject_iff (hP : ∀ X, P' (G.obj X) ↔ P X) {R : C} (a b : Subobject R) :
    P'.SubQ (G.mapSubobject R a) (G.mapSubobject R b) ↔ P.SubQ a b := by
  induction a using Subobject.ind with | h f =>
  induction b using Subobject.ind with | h g =>
  simp only [Functor.mapSubobject_mk]
  by_cases hle : Subobject.mk f ≤ Subobject.mk g
  · have hu : Subobject.ofMkLEMk f g hle ≫ g = f := Subobject.ofMkLEMk_comp hle
    have hGu : G.map (Subobject.ofMkLEMk f g hle) ≫ G.map g = G.map f := by
      rw [← G.map_comp, hu]
    rw [subQ_mk_iff _ hGu, subQ_mk_iff _ hu, ← hP]
    exact ⟨fun h ↦ P'.prop_of_iso (PreservesCokernel.iso G _).symm h,
      fun h ↦ P'.prop_of_iso (PreservesCokernel.iso G _) h⟩
  · have hle' : ¬Subobject.mk (G.map f) ≤ Subobject.mk (G.map g) := by
      rwa [← Functor.mapSubobject_mk, ← Functor.mapSubobject_mk,
        G.mapSubobject_le_mapSubobject_iff]
    exact ⟨fun h ↦ absurd h.le hle', fun h ↦ absurd h.le hle⟩

variable [P.ContainsZero] [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
  [P'.ContainsZero] [P'.IsClosedUnderQuotients] [P'.IsClosedUnderExtensions]

/-- **Transport of the saturation** along an equivalence carrying `P` to `P'`:
`G (Sat_P a) = Sat_{P'} (G a)` on a Noetherian object. -/
theorem mapSubobject_intervalClass_sat (hP : ∀ X, P' (G.obj X) ↔ P X) {R : C}
    [IsNoetherianObject R] (a : Subobject R) :
    have := G.isNoetherianObject_obj R
    G.mapSubobject R ((P.intervalClass R).sat a) =
      (P'.intervalClass (G.obj R)).sat (G.mapSubobject R a) :=
  have := G.isNoetherianObject_obj R
  (P.intervalClass R).sat_map (P'.intervalClass (G.obj R))
    (G.subobjectOrderIsoOfIsEquivalence R) (fun a b ↦ subQ_mapSubobject_iff G hP a b) a

/-- **Transport of the radical** along an equivalence carrying `P` to `P'`: `G (t_P R)` is
`t_{P'} (G R)`, the largest subobject of `G R` in `P'`, on a Noetherian object. -/
theorem mapSubobject_intervalClass_rad (hP : ∀ X, P' (G.obj X) ↔ P X) (R : C)
    [IsNoetherianObject R] :
    have := G.isNoetherianObject_obj R
    G.mapSubobject R (P.intervalClass R).rad = (P'.intervalClass (G.obj R)).rad := by
  have := G.isNoetherianObject_obj R
  have h := mapSubobject_intervalClass_sat G hP (⊥ : Subobject R)
  have hbot : G.mapSubobject R ⊥ = ⊥ := (G.subobjectOrderIsoOfIsEquivalence R).map_bot
  rw [hbot] at h
  exact h

end ObjectProperty

end CategoryTheory
