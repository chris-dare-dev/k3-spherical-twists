/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Abelian.TorsionTheory.Radical
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Coreflections into a shifted class: the radical after a tilt represents `Ext¹`

Let `C` be a category with a shift by an additive group `A`, `P` a class of objects of `C`
closed under isomorphisms, and `a : A`. The shifted class `P.shift a` (Mathlib's
`ObjectProperty.shift`) consists of the objects `X` with `X⟦a⟧` in `P`; for `A = ℤ` and `a = 1`
it is the class `P[-1]`. A coreflection into a class (`ObjectProperty.IsCoreflection`: a morphism
from an object of the class through which every morphism from the class factors uniquely) can be
computed after shifting, because the shift is an equivalence:

* `isCoreflection_shift_iff`: `ε : X ⟶ R` is a coreflection of `R` into `P.shift a` exactly
  when `ε⟦a⟧'` is a coreflection of `R⟦a⟧` into `P`;
* `isCoreflection_shift_iff_homEquiv`, **the radical after a tilt represents `Ext¹`**: for an
  adjunction `⟦b⟧ ⊣ ⟦a⟧` (for `b + a = 0`, Mathlib's `(shiftEquiv' C b a h).toAdjunction`), a
  morphism `ε : U⟦b⟧ ⟶ K` is a coreflection of `K` into `P.shift a` exactly when its adjoint
  `η : U ⟶ K⟦a⟧` is a coreflection of `K⟦a⟧` into `P`. That is, `U` lies in `P` and composition
  with `η` is a bijection `Hom(X, U) ≃ Hom(X, K⟦a⟧)` for every `X` in `P`: `η` represents
  `Hom(-, K⟦a⟧)` on `P`;
* `exists_isCoreflection_shift_iff`: `K` has a coreflection into `P.shift a` exactly when the
  functor `Hom(-, K⟦a⟧)` on `P` is representable.

In a pretriangulated category take `a = 1` and `b = -1`. For `X` and `K` in a heart,
`Hom(X, K⟦1⟧)` is `Ext¹(X, K)`. So the coreflection of `K` into `P[-1]` is `U[-1] ⟶ K` for the
object `U` of `P` that represents `Ext¹(-, K)` on `P`, and conversely. In a heart that contains
`K` and `P[-1]`, and in which `P[-1]` is closed under quotients, this coreflection is the radical
of `K`, its largest subobject in `P[-1]` (`isCoreflection_arrow_iff`). Only the shift adjunction
and the definitions enter; no exactness is used.

Both statements come from `isCoreflection_inverseImage_iff`: a fully faithful functor
`F : C ⥤ D` whose essential image contains a class `Q` closed under isomorphisms identifies the
coreflections into `Q.inverseImage F` with the coreflections into `Q`, and from its form for an
adjoint equivalence, `isCoreflection_inverseImage_iff_homEquiv`. For the inclusion of a full
subcategory, such as a heart (`TStructure.ιHeart`), it says that coreflections into a class that
lies in the subcategory are the same in the subcategory and in `C`;
`isCoreflection_inverseImage_shift_iff` combines this with the shift.

## Main results

* **A single brick** (`isCoreflection_biproductDesc_basis`). Let `C` be `k`-linear with finite
  biproducts, `S` an object whose endomorphisms are the multiples of `𝟙 S`, and `e₁, …, e_m` a
  basis of `Hom(S, R)`. Then `⨁_{j < m} S ⟶ R` with components `e_j` is a coreflection of `R`
  into `addClosure S`, the objects isomorphic to a finite biproduct of copies of `S`. With
  `R = K⟦1⟧`, its adjoint is a coreflection of `K` into `(addClosure S)[-1]`
  (`isCoreflection_shift_addClosure`); if the shift is additive, so is `⨁_{j < m} S⟦-1⟧ ⟶ K`,
  with components the basis of `Hom(S⟦-1⟧, K) = Ext¹(S, K)` adjoint to the `e_j`: the radical
  is `S[-1] ⊗ Ext¹(S, K)` (`isCoreflection_desc_shift_addClosure`).
* **A representing object** (`IsCoreflection.homLinearEquiv`). If `η : U ⟶ R` is a coreflection
  into `P`, composition with `η` is a `k`-linear isomorphism `Hom(X, U) ≃ Hom(X, R)` for every
  `X` in `P`, natural in `X` (`IsCoreflection.homLinearEquiv_comp`), so equivariant for
  precomposition by `End(X)` (`IsCoreflection.homLinearEquiv_smul`); and `U` is unique up to a
  unique isomorphism over `R` (`IsCoreflection.isoOfIsCoreflection`,
  `IsCoreflection.eq_isoOfIsCoreflection_hom`). For `R = K⟦1⟧` and an object `G` of `P`,
  for instance a projective generator of a Serre subcategory `P` of a heart, the coreflection of
  `K` into `P[-1]` is `U[-1]` with `Hom(G, U) ≅ Ext¹(G, K)` as right `End(G)`-modules.
* **Transport across an autoequivalence** (`isCoreflection_shift_of_equivalence`). If an
  autoequivalence `Φ` carries `P` to `P.shift a`, the adjoint `Φ D ⟶ K` of a coreflection
  `D ⟶ Φ⁻¹ K` into `P` is a coreflection of `K` into `P.shift a`: the new radical is the image of
  the old one, and `(Φ D)⟦a⟧` represents `Hom(-, K⟦a⟧)` on `P`.
* **Existence from a chain condition** (`exists_isCoreflection_shift_of_isNoetherianObject`). If
  `ι : B ⥤ C` is fully faithful from an abelian category, the objects of `P.shift a` lie in its
  essential image, and the inverse image of `P.shift a` in `B` contains zero and is closed under
  quotients and extensions, then every Noetherian object `K` of `B` has a radical `D ↪ K` for
  `P.shift a`, and `(ι D)⟦a⟧` represents `Hom(-, (ι K)⟦a⟧)` on `P`.

## Scope

The coreflection statements hold for every object `K`. That `K` receives no nonzero morphism
from `P` is what puts `K` into the tilted heart, where a coreflection into a class closed under
subobjects or quotients is a monomorphism and the largest subobject in the class
(`IsCoreflection.mono_of_subobjects`, `IsCoreflection.mono_of_quotients`,
`IsCoreflection.isGreatest`).

For a Serre subcategory `P = Filt(S₁, …, S_l)` of a heart `A` with a projective generator `G`,
tilted across the longest element `w₀` of a finite Weyl group, nothing here constructs the
representing object unconditionally. If the twist `F_{w₀}` carries `P` to `P[-1]` (as
`F_{w₀} S_i ≅ S_{π i}[-1]` and exactness give), `isCoreflection_shift_of_equivalence` reduces it
to the coreflection of `F_{w₀}⁻¹ K` into `P`, computed in `A`. That exists when `F_{w₀}⁻¹ K` is
Noetherian in `A` (`exists_isGreatest_subobject`), which the library does not show for the
hearts of interest; or, for every object, from the torsion triangle of
`TStructure.exists_distTriang_heart_of_le` for the t-structure with heart `F_{w₀} A[1]`, which
needs that t-structure (the image of a t-structure under an exact autoequivalence), the
inclusion of aisles it asks for, and the identification of its torsion class `A ∩ F_{w₀} A[1]`
with `P`. The route through modules needs an equivalence of `P` with the finitely generated
right modules over `End(G)`, which Mathlib does not have for an abelian category of finite length
with a projective generator.

## References

* D. Happel, I. Reiten and S. O. Smalø, *Tilting in abelian categories and quasitilted
  algebras*, Mem. Amer. Math. Soc. 120 (1996), no. 575, Chapter I (tilting at a torsion pair).

## Tags

coreflection, radical, shift, tilt, heart, representing object, Ext, brick
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-! ### Composition with a fixed morphism -/

/-- Composition with `f` is bijective on the morphisms out of `A` exactly when it is bijective on
the morphisms out of an isomorphic object `A'`. -/
theorem bijective_comp_iff_of_iso {A A' X R : C} (e : A ≅ A') (f : X ⟶ R) :
    Function.Bijective (fun g : A ⟶ X => g ≫ f) ↔
      Function.Bijective (fun g : A' ⟶ X => g ≫ f) := by
  have key : (fun g : A ⟶ X => g ≫ f) ∘ e.homFromEquiv.symm =
      e.homFromEquiv.symm ∘ fun g : A' ⟶ X => g ≫ f := by
    funext g
    simp
  rw [← Equiv.bijective_comp e.homFromEquiv.symm (fun g : A ⟶ X => g ≫ f), key,
    Equiv.comp_bijective]

/-- Precomposing with an isomorphism does not change being a coreflection into a class closed
under isomorphisms. -/
theorem isCoreflection_iso_comp_iff {P : ObjectProperty C} [P.IsClosedUnderIsomorphisms]
    {D D' R : C} (e : D' ≅ D) (ε : D ⟶ R) :
    P.IsCoreflection (e.hom ≫ ε) ↔ P.IsCoreflection ε :=
  ⟨fun h => by simpa using h.iso_comp e.symm, fun h => h.iso_comp e⟩

/-! ### Fully faithful functors -/

section FullyFaithful

variable {D : Type*} [Category D] (F : C ⥤ D) [F.Full] [F.Faithful]

/-- For a fully faithful functor `F`, composition with `F.map ε` is bijective on the morphisms
out of `F.obj A` exactly when composition with `ε` is bijective on the morphisms out of `A`. -/
theorem bijective_comp_map_iff {A X R : C} (ε : X ⟶ R) :
    Function.Bijective (fun g : F.obj A ⟶ F.obj X => g ≫ F.map ε) ↔
      Function.Bijective (fun g : A ⟶ X => g ≫ ε) := by
  let hF := Functor.FullyFaithful.ofFullyFaithful F
  have key : (fun g : F.obj A ⟶ F.obj X => g ≫ F.map ε) ∘ hF.homEquiv =
      hF.homEquiv ∘ fun g : A ⟶ X => g ≫ ε := by
    funext g
    simp [hF]
  rw [← Equiv.bijective_comp hF.homEquiv (fun g : F.obj A ⟶ F.obj X => g ≫ F.map ε), key,
    Equiv.comp_bijective]

variable {F} {Q : ObjectProperty D}

/-- A fully faithful functor reflects coreflections: if `F.map ε` is a coreflection into `Q`,
then `ε` is a coreflection into the inverse image of `Q`. -/
theorem IsCoreflection.of_map {X R : C} {ε : X ⟶ R} (h : Q.IsCoreflection (F.map ε)) :
    (Q.inverseImage F).IsCoreflection ε :=
  ⟨h.prop, fun _ hA => (bijective_comp_map_iff F ε).1 (h.bijective hA)⟩

/-- A fully faithful functor preserves coreflections into the inverse image of a class `Q`
closed under isomorphisms whose objects lie in its essential image. -/
theorem IsCoreflection.map [Q.IsClosedUnderIsomorphisms] (hQ : Q ≤ F.essImage) {X R : C}
    {ε : X ⟶ R} (h : (Q.inverseImage F).IsCoreflection ε) : Q.IsCoreflection (F.map ε) := by
  refine ⟨h.prop, fun B hB => ?_⟩
  obtain ⟨A, ⟨e⟩⟩ := hQ B hB
  rw [← bijective_comp_iff_of_iso e]
  exact (bijective_comp_map_iff F ε).2 (h.bijective (Q.prop_of_iso e.symm hB))

variable (F) in
/-- **Coreflections in a full subcategory.** Let `F : C ⥤ D` be fully faithful and `Q` a class of
objects of `D`, closed under isomorphisms, whose objects lie in the essential image of `F`. Then
`ε` is a coreflection into the inverse image of `Q` in `C` exactly when `F.map ε` is a
coreflection into `Q`. For the inclusion of a heart: a coreflection into a class inside the heart
can be computed in the heart or in the ambient category. -/
theorem isCoreflection_inverseImage_iff [Q.IsClosedUnderIsomorphisms] (hQ : Q ≤ F.essImage)
    {X R : C} (ε : X ⟶ R) :
    (Q.inverseImage F).IsCoreflection ε ↔ Q.IsCoreflection (F.map ε) :=
  ⟨IsCoreflection.map hQ, IsCoreflection.of_map⟩

end FullyFaithful

/-! ### Adjoints -/

section Adjunction

variable {D : Type*} [Category D] {L : D ⥤ C} {G : C ⥤ D} (adj : L ⊣ G) [L.Full] [L.Faithful]
  [G.Full] [G.Faithful] {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]

/-- **Coreflections and adjoints.** Let `L ⊣ G` be an adjunction between fully faithful functors
(an adjoint equivalence), and `Q` a class of objects of `D`, closed under isomorphisms, whose
objects lie in the essential image of `G`. A morphism `ε : L U ⟶ K` is a coreflection of `K` into
the inverse image of `Q` exactly when its adjoint `U ⟶ G K` is a coreflection of `G K` into
`Q`. -/
theorem isCoreflection_inverseImage_iff_homEquiv (hQ : Q ≤ G.essImage) {U : D} {K : C}
    (ε : L.obj U ⟶ K) :
    (Q.inverseImage G).IsCoreflection ε ↔ Q.IsCoreflection (adj.homEquiv U K ε) := by
  rw [isCoreflection_inverseImage_iff G hQ, Adjunction.homEquiv_unit]
  exact (isCoreflection_iso_comp_iff (asIso (adj.unit.app U)) _).symm

end Adjunction

/-! ### Shifted classes -/

section Shift

variable {A : Type*} [AddGroup A] [HasShift C A] (P : ObjectProperty C)
  [P.IsClosedUnderIsomorphisms]

/-- **Coreflections into a shifted class.** `ε : X ⟶ R` is a coreflection of `R` into
`P.shift a`, the objects `Y` with `Y⟦a⟧` in `P`, exactly when `ε⟦a⟧'` is a coreflection of
`R⟦a⟧` into `P`. -/
theorem isCoreflection_shift_iff (a : A) {X R : C} (ε : X ⟶ R) :
    (P.shift a).IsCoreflection ε ↔ P.IsCoreflection (ε⟦a⟧') :=
  isCoreflection_inverseImage_iff (shiftFunctor C a)
    (fun Y _ => Functor.EssSurj.mem_essImage _ Y) ε

/-- **The radical after a tilt represents `Ext¹`.** Let `adj : ⟦b⟧ ⊣ ⟦a⟧` be an adjunction
between shifts (for `b + a = 0`, `(shiftEquiv' C b a h).toAdjunction`; in a pretriangulated
category, `a = 1` and `b = -1`). A morphism `ε : U⟦b⟧ ⟶ K` is a coreflection of `K` into the
shifted class `P.shift a` exactly when its adjoint `η : U ⟶ K⟦a⟧` is a coreflection of `K⟦a⟧`
into `P`: `U` lies in `P`, and composition with `η` is a bijection `Hom(X, U) ≃ Hom(X, K⟦a⟧)` for
every `X` in `P`. For `a = 1` and `X`, `K` in a heart, `Hom(X, K⟦1⟧) = Ext¹(X, K)`, so the
radical of `K` for `P[-1]` is `U[-1]`, where `U` represents `Ext¹(-, K)` on `P`. No exactness is
used. -/
theorem isCoreflection_shift_iff_homEquiv {a b : A} (adj : shiftFunctor C b ⊣ shiftFunctor C a)
    {U K : C} (ε : U⟦b⟧ ⟶ K) :
    (P.shift a).IsCoreflection ε ↔ P.IsCoreflection (adj.homEquiv U K ε) :=
  isCoreflection_inverseImage_iff_homEquiv adj (fun Y _ => Functor.EssSurj.mem_essImage _ Y) ε

/-- **The radical after a tilt from a representing object.** For an adjunction `adj : ⟦b⟧ ⊣ ⟦a⟧`
and `η : U ⟶ K⟦a⟧`, the adjoint `U⟦b⟧ ⟶ K` of `η` is a coreflection of `K` into `P.shift a`
exactly when `η` is a coreflection of `K⟦a⟧` into `P`, that is, when `η` represents
`Hom(-, K⟦a⟧)` on `P`. -/
theorem isCoreflection_shift_homEquiv_symm_iff {a b : A}
    (adj : shiftFunctor C b ⊣ shiftFunctor C a) {U K : C} (η : U ⟶ K⟦a⟧) :
    (P.shift a).IsCoreflection ((adj.homEquiv U K).symm η) ↔ P.IsCoreflection η := by
  rw [isCoreflection_shift_iff_homEquiv P adj, Equiv.apply_symm_apply]

/-- **The radical after a tilt exists exactly when `Ext¹` is representable.** An object `K` has
a coreflection into `P.shift a` exactly when the functor `Hom(-, K⟦a⟧)` on `P`,
`P.ι.op ⋙ yoneda.obj (K⟦a⟧)`, is representable; for `a = 1` this is `Ext¹(-, K)` on `P`. -/
theorem exists_isCoreflection_shift_iff (a : A) (K : C) :
    (∃ (D : C) (ε : D ⟶ K), (P.shift a).IsCoreflection ε) ↔
      (P.ι.op ⋙ yoneda.obj (K⟦a⟧)).IsRepresentable := by
  refine Iff.trans ?_ (rightAdjointObjIsDefined_ι_iff (P := P) (R := K⟦a⟧)).symm
  refine ⟨fun ⟨_, ε, h⟩ => ⟨_, _, (isCoreflection_shift_iff P a ε).1 h⟩, fun ⟨_, η, h⟩ => ?_⟩
  have adj : shiftFunctor C (-a) ⊣ shiftFunctor C a :=
    (shiftEquiv' C (-a) a (neg_add_cancel a)).toAdjunction
  exact ⟨_, _, (isCoreflection_shift_homEquiv_symm_iff P adj η).2 h⟩

/-- **The radical across an autoequivalence.** Let `Φ : C ≌ C` carry `P` to `P.shift a`: `X⟦a⟧`
lies in `P` exactly when `Φ⁻¹ X` does (for the twist across the longest element of a finite Weyl
group and `a = 1`, `Φ` maps `P` to `P[-1]`). If `ε' : D ⟶ Φ⁻¹ K` is a coreflection of `Φ⁻¹ K`
into `P`, then its adjoint `Φ D ⟶ K` is a coreflection of `K` into `P.shift a`; so, by
`isCoreflection_shift_iff`, `(Φ D)⟦a⟧` represents `Hom(-, K⟦a⟧)` on `P`. -/
theorem isCoreflection_shift_of_equivalence (Φ : C ≌ C) {a : A}
    (hΦ : ∀ X, P (X⟦a⟧) ↔ P (Φ.inverse.obj X)) {D K : C} {ε' : D ⟶ Φ.inverse.obj K}
    (h : P.IsCoreflection ε') :
    (P.shift a).IsCoreflection ((Φ.toAdjunction.homEquiv D K).symm ε') := by
  have hP : P.shift a = P.inverseImage Φ.inverse := funext fun X => propext (hΦ X)
  rw [hP, isCoreflection_inverseImage_iff_homEquiv Φ.toAdjunction
    (fun Y _ => Functor.EssSurj.mem_essImage _ Y), Equiv.apply_symm_apply]
  exact h

/-- **Coreflections into a shifted class, in a full subcategory.** Let `ι : B ⥤ C` be fully
faithful (for instance the inclusion of a heart) and let the objects of `P.shift a` lie in its
essential image. A morphism `ε` of `B` is a coreflection into the inverse image of `P.shift a` in
`B` exactly when `(ι.map ε)⟦a⟧'` is a coreflection into `P`. -/
theorem isCoreflection_inverseImage_shift_iff {B : Type*} [Category B] (ι : B ⥤ C) [ι.Full]
    [ι.Faithful] (a : A) (hP : P.shift a ≤ ι.essImage) {X R : B} (ε : X ⟶ R) :
    ((P.shift a).inverseImage ι).IsCoreflection ε ↔ P.IsCoreflection ((ι.map ε)⟦a⟧') := by
  rw [isCoreflection_inverseImage_iff ι hP, isCoreflection_shift_iff]

end Shift

/-! ### A representing object -/

namespace IsCoreflection

variable {P : ObjectProperty C} {U R : C} {η : U ⟶ R}

/-- **Uniqueness of the representing object.** The isomorphism between two coreflections of `R`
into `P` is the only morphism between them over `R`. -/
theorem eq_isoOfIsCoreflection_hom (h : P.IsCoreflection η) {U' : C} {η' : U' ⟶ R}
    (h' : P.IsCoreflection η') {φ : U ⟶ U'} (w : φ ≫ η' = η) :
    φ = (h.isoOfIsCoreflection h').hom :=
  h'.hom_ext h.prop (by simp [w])

section Linear

variable (k : Type w) [Semiring k] [Preadditive C] [Linear k C] (h : P.IsCoreflection η)

/-- For a coreflection `η : U ⟶ R` into `P` and an object `X` of `P`, composition with `η` is a
`k`-linear isomorphism `Hom(X, U) ≃ Hom(X, R)`. For `R = K⟦1⟧` it identifies `Hom(X, U)` with
`Ext¹(X, K)`. -/
noncomputable def homLinearEquiv {X : C} (hX : P X) : (X ⟶ U) ≃ₗ[k] (X ⟶ R) :=
  LinearEquiv.ofBijective (Linear.rightComp k X η) (h.bijective hX)

@[simp]
theorem homLinearEquiv_apply {X : C} (hX : P X) (g : X ⟶ U) :
    h.homLinearEquiv k hX g = g ≫ η :=
  rfl

/-- The isomorphism `Hom(X, U) ≃ Hom(X, R)` is natural in `X` in `P`. -/
theorem homLinearEquiv_comp {X Y : C} (hX : P X) (hY : P Y) (a : X ⟶ Y) (g : Y ⟶ U) :
    h.homLinearEquiv k hX (a ≫ g) = a ≫ h.homLinearEquiv k hY g := by
  simp

/-- The isomorphism `Hom(X, U) ≃ Hom(X, R)` commutes with precomposition by endomorphisms of `X`:
it is an isomorphism of right `End(X)`-modules. -/
theorem homLinearEquiv_smul {X : C} (hX : P X) (r : (End X)ᵐᵒᵖ) (g : X ⟶ U) :
    h.homLinearEquiv k hX (r • g) = r • h.homLinearEquiv k hX g := by
  rw [homLinearEquiv_apply, homLinearEquiv_apply]
  exact Category.assoc _ _ _

end Linear

end IsCoreflection

/-! ### A single brick -/

section Brick

/-- Composition with `η` is bijective on the morphisms out of a biproduct when it is bijective on
the morphisms out of each summand. -/
theorem bijective_comp_biproduct [HasZeroMorphisms C] {J : Type*} {f : J → C} [HasBiproduct f]
    {X R : C} (η : X ⟶ R) (h : ∀ j, Function.Bijective fun g : f j ⟶ X => g ≫ η) :
    Function.Bijective fun g : ⨁ f ⟶ X => g ≫ η := by
  refine ⟨fun g g' w => biproduct.hom_ext' _ _ fun j => (h j).1 ?_, fun t => ?_⟩
  · simpa using congrArg (biproduct.ι f j ≫ ·) w
  · choose g hg using fun j => (h j).2 (biproduct.ι f j ≫ t)
    exact ⟨biproduct.desc g, biproduct.hom_ext' _ _ fun j => by simpa using hg j⟩

variable [Preadditive C] [HasFiniteBiproducts C]

/-- `add(S)`: the objects isomorphic to a finite biproduct `S ⊞ ⋯ ⊞ S` of copies of `S`. -/
def addClosure (S : C) : ObjectProperty C :=
  fun X => ∃ n : ℕ, Nonempty (X ≅ ⨁ fun _ : Fin n => S)

instance (S : C) : (addClosure S).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨n, ⟨e'⟩⟩ => ⟨n, ⟨e.symm ≪≫ e'⟩⟩

theorem addClosure_biproduct (S : C) (n : ℕ) : addClosure S (⨁ fun _ : Fin n => S) :=
  ⟨n, ⟨Iso.refl _⟩⟩

variable {k : Type w} [Semiring k] [Linear k C]

/-- Let the endomorphisms of `S` be the multiples of `𝟙 S` and `e` a basis of `Hom(S, R)`. Then
composition with `(e_j) : ⨁_j S ⟶ R` is bijective on the morphisms out of `S`: a morphism
`S ⟶ ⨁_j S` is a family of scalars, and it goes to their combination of the `e_j`. -/
theorem bijective_comp_biproductDesc_basis {S R : C}
    (hS : ∀ f : S ⟶ S, ∃ c : k, f = c • 𝟙 S) {m : ℕ} (e : Module.Basis (Fin m) k (S ⟶ R)) :
    Function.Bijective fun g : S ⟶ ⨁ (fun _ : Fin m => S) => g ≫ biproduct.desc fun j => e j := by
  have key : ∀ c : Fin m → k,
      biproduct.lift (fun j => c j • 𝟙 S) ≫ biproduct.desc (fun j => e j) = e.equivFun.symm c := by
    intro c
    simp [biproduct.lift_desc]
  refine ⟨fun g g' w => ?_, fun t => ⟨biproduct.lift fun j => e.equivFun t j • 𝟙 S,
    (key (e.equivFun t)).trans (e.equivFun.symm_apply_apply t)⟩⟩
  choose c hc using fun j => hS (g ≫ biproduct.π _ j)
  choose c' hc' using fun j => hS (g' ≫ biproduct.π _ j)
  have hg : g = biproduct.lift fun j => c j • 𝟙 S :=
    biproduct.hom_ext _ _ fun j => by simp [hc]
  have hg' : g' = biproduct.lift fun j => c' j • 𝟙 S :=
    biproduct.hom_ext _ _ fun j => by simp [hc']
  have hcc : c = c' := e.equivFun.symm.injective (by rw [← key, ← key, ← hg, ← hg']; exact w)
  rw [hg, hg', hcc]

/-- **The coreflection at a single brick.** Let `C` be `k`-linear with finite biproducts, `S` an
object whose endomorphisms are the multiples of `𝟙 S`, and `e` a basis of `Hom(S, R)` with `m`
elements. Then `(e_j) : ⨁_{j < m} S ⟶ R` is a coreflection of `R` into `addClosure S`: every
morphism from a finite biproduct of copies of `S` to `R` factors uniquely through it. -/
theorem isCoreflection_biproductDesc_basis {S R : C}
    (hS : ∀ f : S ⟶ S, ∃ c : k, f = c • 𝟙 S) {m : ℕ} (e : Module.Basis (Fin m) k (S ⟶ R)) :
    (addClosure S).IsCoreflection (biproduct.desc fun j => e j) := by
  refine ⟨addClosure_biproduct S m, fun X hX => ?_⟩
  obtain ⟨n, ⟨i⟩⟩ := hX
  rw [bijective_comp_iff_of_iso i]
  exact bijective_comp_biproduct _ fun _ => bijective_comp_biproductDesc_basis hS e

variable [HasShift C ℤ] (adj : shiftFunctor C (-1 : ℤ) ⊣ shiftFunctor C (1 : ℤ))

/-- **The radical at a single brick.** Let `S` be as in `isCoreflection_biproductDesc_basis`, `e`
a basis of `Hom(S, K⟦1⟧)` (which is `Ext¹(S, K)` in a heart), and `adj : ⟦-1⟧ ⊣ ⟦1⟧` (for
instance `(shiftEquiv' C (-1) 1 _).toAdjunction`). The adjoint `(⨁_j S)⟦-1⟧ ⟶ K` of
`(e_j) : ⨁_j S ⟶ K⟦1⟧` is a coreflection of `K` into `(addClosure S)[-1]`. -/
theorem isCoreflection_shift_addClosure {S K : C} (hS : ∀ f : S ⟶ S, ∃ c : k, f = c • 𝟙 S)
    {m : ℕ} (e : Module.Basis (Fin m) k (S ⟶ K⟦(1 : ℤ)⟧)) :
    ((addClosure S).shift (1 : ℤ)).IsCoreflection
      ((adj.homEquiv _ K).symm (biproduct.desc fun j => e j)) :=
  (isCoreflection_shift_homEquiv_symm_iff _ adj _).2 (isCoreflection_biproductDesc_basis hS e)

/-- **The radical at a single brick is `S[-1] ⊗ Ext¹(S, K)`.** Let `S` be as in
`isCoreflection_biproductDesc_basis`, the shift by `-1` additive, `adj : ⟦-1⟧ ⊣ ⟦1⟧`, and `e` a
basis of `Hom(S, K⟦1⟧)`. Then `⨁_j S⟦-1⟧ ⟶ K`, whose components are the adjoints
`S⟦-1⟧ ⟶ K` of the `e_j` (a basis of `Hom(S⟦-1⟧, K)`), is a coreflection of `K` into
`(addClosure S)[-1]`. -/
theorem isCoreflection_desc_shift_addClosure [(shiftFunctor C (-1 : ℤ)).Additive] {S K : C}
    (hS : ∀ f : S ⟶ S, ∃ c : k, f = c • 𝟙 S) {m : ℕ}
    (e : Module.Basis (Fin m) k (S ⟶ K⟦(1 : ℤ)⟧)) :
    ((addClosure S).shift (1 : ℤ)).IsCoreflection
      (biproduct.desc (f := fun _ : Fin m => S⟦(-1 : ℤ)⟧) fun j =>
        (adj.homEquiv S K).symm (e j)) := by
  have key : (biproduct.desc (f := fun _ : Fin m => S⟦(-1 : ℤ)⟧) fun j =>
      (adj.homEquiv S K).symm (e j)) =
      ((shiftFunctor C (-1 : ℤ)).mapBiproduct fun _ : Fin m => S).inv ≫
        (adj.homEquiv _ K).symm (biproduct.desc fun j => e j) := by
    refine biproduct.hom_ext' _ _ fun j => ?_
    simp only [biproduct.ι_desc, Functor.mapBiproduct_inv, biproduct.ι_desc_assoc,
      Adjunction.homEquiv_counit, ← Functor.map_comp_assoc]
  rw [key]
  exact (isCoreflection_shift_addClosure adj hS e).iso_comp
    ((shiftFunctor C (-1 : ℤ)).mapBiproduct fun _ : Fin m => S).symm

end Brick

/-! ### Existence from a chain condition -/

section Abelian

variable {A : Type*} [AddGroup A] [HasShift C A] {B : Type*} [Category B] [Abelian B]
  (ι : B ⥤ C) [ι.Full] [ι.Faithful] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]

/-- **Existence of the radical and of the representing object from a chain condition.** Let
`ι : B ⥤ C` be fully faithful from an abelian category (the inclusion of a tilted heart), let the
objects of `P.shift a` lie in its essential image, and let the inverse image of `P.shift a` in
`B` contain zero and be closed under quotients and extensions. Then every Noetherian object `K`
of `B` has a radical `ε : D ↪ K` for `P.shift a`, and `(ι.map ε)⟦a⟧ : (ι D)⟦a⟧ ⟶ (ι K)⟦a⟧`
represents `Hom(-, (ι K)⟦a⟧)` on `P`. -/
theorem exists_isCoreflection_shift_of_isNoetherianObject (a : A) (hP : P.shift a ≤ ι.essImage)
    [((P.shift a).inverseImage ι).ContainsZero]
    [((P.shift a).inverseImage ι).IsClosedUnderQuotients]
    [((P.shift a).inverseImage ι).IsClosedUnderExtensions] (K : B) [IsNoetherianObject K] :
    ∃ (D : B) (ε : D ⟶ K), Mono ε ∧ ((P.shift a).inverseImage ι).IsCoreflection ε ∧
      P.IsCoreflection ((ι.map ε)⟦a⟧') := by
  obtain ⟨t, ht⟩ := exists_isGreatest_subobject (P := (P.shift a).inverseImage ι) K
  have h := isCoreflection_of_isGreatest ht
  exact ⟨_, t.arrow, inferInstance, h, (isCoreflection_inverseImage_shift_iff P ι a hP _).1 h⟩

end Abelian

end CategoryTheory.ObjectProperty
