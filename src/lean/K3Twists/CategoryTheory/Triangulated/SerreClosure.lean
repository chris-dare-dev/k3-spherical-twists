/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Logic.Relation

/-!
# The thick closure of a Serre preimage

Let `F : C ⥤ A` be a homological functor from a pretriangulated category to an abelian category
and `P` a Serre class of `A`. The objects `X` with `P (F (X⟦n⟧))` for every `n : ℤ`
(`Functor.serrePreimage F P`) form a thick subcategory of `C`: it is triangulated (it contains
zero and is stable under shifts and under extensions by distinguished triangles), closed under
isomorphisms and closed under retracts. For `P = IsZero` it is the kernel of `F`
(`Functor.homologicalKernel`, Verdier, *Des catégories dérivées des catégories abéliennes*).

Twist words are then handled by thickness, with no induction on letters through exact
sequences in `A`. A spherical twist `T_S` at a centre `S` sits in the evaluation triangle
`Hom•(S, E) ⊗ S → E → T_S E` (Seidel–Thomas, arXiv:math/0001043, §2), and its inverse in the
coevaluation triangle; in either, one end is the previous object and the other a finite sum of
shifts of `S`.

## Main results

* `Functor.serrePreimage`, with instances: triangulated, closed under isomorphisms, stable under
  retracts. `Functor.serrePreimage_inf`: `D_{P ⊓ Q} = D_P ⊓ D_Q`.
* `ObjectProperty.prop_iff_of_trW`: two-out-of-three along a morphism whose cone lies in a
  triangulated `K`.
* The Verdier form. `ObjectProperty.IsWordModulo K Φ`: `Φ` is a composite of letters, each
  joined to the identity by a natural transformation, in either direction, whose components
  have cones in `K`. Such a word preserves `K` and its complement
  (`ObjectProperty.IsWordModulo.prop_iff`) and acts as the identity on every localization of
  `C` at `K`, that is on every functor `L` that inverts `K.trW` (`IsWordModulo.nonempty_iso`):
  `Φ ⋙ L ≅ L`. A homological functor inverts the cones in its kernel
  (`Functor.homologicalKernel_trW_isInvertedBy`), so a word whose letters have centres with
  zero image in every degree leaves every `F (X⟦n⟧)` unchanged up to isomorphism
  (`ObjectProperty.IsWordModulo.nonempty_iso_obj_shift`).
* Words on objects. `ObjectProperty.LetterStep Q X Y`: `Y` is the middle vertex of a
  distinguished triangle whose two ends are `X` and an object of `Q`, in either order.
  `ObjectProperty.shiftSums 𝒮`: finite products of shifts of objects of `𝒮`, the third
  vertices of twists at centres in `𝒮`. A chain of letter steps
  (`Relation.ReflTransGen (LetterStep (shiftSums 𝒮))`) preserves every thick `K ⊇ 𝒮`
  (`ObjectProperty.prop_iff_of_reflTransGen`).
* The Serre-preimage theorem (`Functor.prop_obj_shift_of_reflTransGen`): if `F` is homological,
  `P` a Serre class, `F (E⟦j⟧) ∈ P` and `F (S⟦j⟧) ∈ P` for every `j` and every centre `S`, then
  `F (Y⟦i⟧) ∈ P` for every `i` and every object `Y` reached from `E` by letters at the centres.
  Every prefix of a word is such a `Y`. Since `P` is any Serre class containing the inputs, `Y`
  lands in the Serre class they generate.
* The derived category of an abelian category `A` with `F = H⁰`: the complexes whose cohomology
  lies in a Serre class `P` form a thick subcategory of `D(A)`
  (`DerivedCategory.mem_serrePreimage_homologyFunctor_iff`), which contains `X[0]` exactly when
  `X ∈ P` (`DerivedCategory.singleFunctor_mem_serrePreimage_iff`).

## The heart cohomology of a stability condition

The intended `F` is `π ∘ H⁰_𝒜` for the heart `𝒜 = P((0, 1])` of a stability condition and the
Serre quotient `π : 𝒜 → 𝒜/P(1)`. Neither is in Mathlib: the heart of a t-structure is not yet
shown to be abelian, nor `H⁰` homological, and Serre quotients are not constructed. The results
here take any homological `F`, so `π ∘ H⁰_𝒜` is an input, not a field of a structure. The quotient
can also be avoided: a Serre class `𝒫` of `𝒜/P(1)` has the preimage `π⁻¹ 𝒫`, a Serre class of
`𝒜` containing `P(1)`, and `π H⁰_𝒜 (Y) ∈ 𝒫` iff `H⁰_𝒜 (Y) ∈ π⁻¹ 𝒫`; so `F = H⁰_𝒜` with the
Serre class `π⁻¹ 𝒫` gives the same subcategory. The derived category of an abelian category,
with its standard heart, is the instance from objects Mathlib has.

## Not formalized

For finitely many simples `T` of a bounded heart, `thick(T)` is the Serre preimage of `Filt(T)`,
the objects with all composition factors in `T`. The inclusion `thick(T) ⊆ D_{Filt(T)}` is the
thickness above, once `Filt(T)` is known to be a Serre class; the reverse inclusion needs the
truncation triangles of the heart and its cohomology functors. The intersection
`thick(S_I) ∩ thick(S_J) = thick(S_{I ∩ J})` then follows from `Functor.serrePreimage_inf` and
`Filt(S_I) ∩ Filt(S_J) = Filt(S_{I ∩ J})`, which is Jordan–Hölder in a length category. Neither
Serre property of `Filt(T)` nor Jordan–Hölder for abelian length categories is in Mathlib.
-/

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject

variable {C A : Type*} [Category* C] [HasShift C ℤ] [Category* A]

namespace Functor

variable (F : C ⥤ A) (P Q : ObjectProperty A)

/-- **The Serre preimage** `D_P = {X : ∀ n, P (F (X⟦n⟧))}` of a property `P` of `A` under
`F : C ⥤ A`. -/
def serrePreimage : ObjectProperty C := fun X ↦ ∀ n : ℤ, P (F.obj (X⟦n⟧))

lemma mem_serrePreimage_iff [F.ShiftSequence ℤ] [P.IsClosedUnderIsomorphisms] (X : C) :
    F.serrePreimage P X ↔ ∀ n : ℤ, P ((F.shift n).obj X) :=
  forall_congr' fun n ↦ P.prop_iff_of_iso ((F.isoShift n).app X)

/-- The Serre preimage of the zero objects is the homological kernel. -/
lemma serrePreimage_isZero : F.serrePreimage (IsZero (C := A)) = F.homologicalKernel := rfl

variable {P Q} in
lemma serrePreimage_mono (h : P ≤ Q) : F.serrePreimage P ≤ F.serrePreimage Q :=
  fun _ hX n ↦ h _ (hX n)

lemma serrePreimage_inf : F.serrePreimage (P ⊓ Q) = F.serrePreimage P ⊓ F.serrePreimage Q := by
  ext X
  exact ⟨fun h ↦ ⟨fun n ↦ (h n).1, fun n ↦ (h n).2⟩, fun h n ↦ ⟨h.1 n, h.2 n⟩⟩

lemma homologicalKernel_le_serrePreimage [P.ContainsZero] [P.IsClosedUnderIsomorphisms] :
    F.homologicalKernel ≤ F.serrePreimage P :=
  fun _ hX n ↦ P.prop_of_isZero (hX n)

instance [P.IsClosedUnderIsomorphisms] : (F.serrePreimage P).IsClosedUnderIsomorphisms where
  of_iso e hX n := P.prop_of_iso ((shiftFunctor C n ⋙ F).mapIso e) (hX n)

variable [Abelian A] [P.IsSerreClass]

/-- **The Serre preimage is retract-closed**: a retract of `X` maps to a subobject of `F (X⟦n⟧)`
for each `n`. -/
instance : (F.serrePreimage P).IsStableUnderRetracts where
  of_retract h hY n := P.prop_of_mono (h.map (shiftFunctor C n ⋙ F)).i (hY n)

variable [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [F.IsHomological]

/-- **The Serre preimage is triangulated**: the middle term of `F` applied to a shifted
distinguished triangle is in `P` when both ends are, by exactness and the Serre property. -/
instance : (F.serrePreimage P).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C,
    fun n ↦ P.prop_of_isZero ((shiftFunctor C n ⋙ F).map_isZero (isZero_zero C))⟩
  toIsStableUnderShift := ⟨fun a ↦ ⟨fun X hX b ↦
    P.prop_of_iso (F.mapIso ((shiftFunctorAdd C a b).app X)) (hX (a + b))⟩⟩
  toIsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ n ↦
      P.prop_X₂_of_exact (F.map_distinguished_exact _ (Triangle.shift_distinguished T hT n))
        (h₁ n) (h₃ n))

/-- A homological functor inverts every morphism whose cone lies in its kernel. -/
lemma homologicalKernel_trW_isInvertedBy : F.homologicalKernel.trW.IsInvertedBy F := by
  intro X Y f hf
  let := ShiftSequence.tautological F ℤ
  have h := (F.mem_homologicalKernel_trW_iff f).1 hf 0
  exact (NatIso.isIso_map_iff (F.isoShiftZero ℤ) f).1 h

end Functor

variable [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A]

namespace ObjectProperty

variable (K : ObjectProperty C)

/-- **Two out of three along `K.trW`.** If the cone of `f : X ⟶ Y` lies in a triangulated `K`
closed under isomorphisms, then `X ∈ K ↔ Y ∈ K`. -/
lemma prop_iff_of_trW [K.IsTriangulated] [K.IsClosedUnderIsomorphisms] {X Y : C} {f : X ⟶ Y}
    (hf : K.trW f) : K X ↔ K Y := by
  obtain ⟨Z, g, h, hT, hZ⟩ := hf
  exact ⟨fun hX ↦ K.ext_of_isTriangulatedClosed₂ _ hT hX hZ,
    fun hY ↦ K.ext_of_isTriangulatedClosed₁ _ hT hY hZ⟩

/-! ### The Verdier form -/

/-- **Words modulo `K`.** The composites of letters, a letter being an endofunctor `Ψ` with a
natural transformation `𝟭 ⟶ Ψ` or `Ψ ⟶ 𝟭` whose components have their cones in `K`. A twist
at a centre in a thick `K` is a letter through its evaluation triangle, whose cone is a finite
sum of shifts of the centre; its inverse is a letter through the coevaluation triangle. -/
inductive IsWordModulo : (C ⥤ C) → Prop
  | id : IsWordModulo (𝟭 C)
  | comp_unit {Φ Ψ : C ⥤ C} (hΦ : IsWordModulo Φ) (η : 𝟭 C ⟶ Ψ)
      (hη : ∀ X, K.trW (η.app X)) : IsWordModulo (Φ ⋙ Ψ)
  | comp_counit {Φ Ψ : C ⥤ C} (hΦ : IsWordModulo Φ) (ε : Ψ ⟶ 𝟭 C)
      (hε : ∀ X, K.trW (ε.app X)) : IsWordModulo (Φ ⋙ Ψ)

variable {K}

/-- **Words preserve `K`**, and its complement: `X ∈ K ↔ Φ X ∈ K`. -/
lemma IsWordModulo.prop_iff [K.IsTriangulated] [K.IsClosedUnderIsomorphisms] {Φ : C ⥤ C}
    (hΦ : K.IsWordModulo Φ) (X : C) : K X ↔ K (Φ.obj X) := by
  induction hΦ with
  | id => rfl
  | comp_unit _ η hη ih => exact ih.trans (K.prop_iff_of_trW (hη _))
  | comp_counit _ ε hε ih => exact ih.trans (K.prop_iff_of_trW (hε _)).symm

/-- A functor that inverts `K.trW` turns a natural transformation with cones in `K` into a
natural isomorphism. -/
lemma nonempty_iso_of_trW {E : Type*} [Category* E] {L : C ⥤ E} (hL : K.trW.IsInvertedBy L)
    {Φ Ψ : C ⥤ C} (η : Φ ⟶ Ψ) (hη : ∀ X, K.trW (η.app X)) : Nonempty (Φ ⋙ L ≅ Ψ ⋙ L) := by
  have : ∀ X, IsIso ((Functor.whiskerRight η L).app X) := fun X ↦ hL _ (hη X)
  have : IsIso (Functor.whiskerRight η L) := NatIso.isIso_of_isIso_app _
  exact ⟨asIso (Functor.whiskerRight η L)⟩

/-- **The Verdier form.** A word modulo `K` acts as the identity on every localization at `K`:
for every functor `L` inverting `K.trW` (for instance the Verdier quotient `C ⥤ C/K`),
`Φ ⋙ L ≅ L`. -/
lemma IsWordModulo.nonempty_iso {E : Type*} [Category* E] {L : C ⥤ E}
    (hL : K.trW.IsInvertedBy L) {Φ : C ⥤ C} (hΦ : K.IsWordModulo Φ) : Nonempty (Φ ⋙ L ≅ L) := by
  induction hΦ with
  | id => exact ⟨Functor.leftUnitor L⟩
  | @comp_unit Φ Ψ _ η hη ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨u⟩ := nonempty_iso_of_trW hL η hη
    exact ⟨Functor.associator Φ Ψ L ≪≫ Functor.isoWhiskerLeft Φ u.symm ≪≫
      Functor.isoWhiskerLeft Φ (Functor.leftUnitor L) ≪≫ e⟩
  | @comp_counit Φ Ψ _ ε hε ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨u⟩ := nonempty_iso_of_trW hL ε hε
    exact ⟨Functor.associator Φ Ψ L ≪≫ Functor.isoWhiskerLeft Φ u ≪≫
      Functor.isoWhiskerLeft Φ (Functor.leftUnitor L) ≪≫ e⟩

/-- **Words with centres in the kernel of a homological functor** leave every `F (X⟦n⟧)`
unchanged up to isomorphism: appending a twist at a centre with zero image in every degree
preserves each cohomology object. -/
lemma IsWordModulo.nonempty_iso_obj_shift (F : C ⥤ A) [F.IsHomological] {Φ : C ⥤ C}
    (hΦ : F.homologicalKernel.IsWordModulo Φ) (X : C) (n : ℤ) :
    Nonempty (F.obj ((Φ.obj X)⟦n⟧) ≅ F.obj (X⟦n⟧)) := by
  have hL : F.homologicalKernel.trW.IsInvertedBy (shiftFunctor C n ⋙ F) := fun _ _ f hf ↦
    F.homologicalKernel_trW_isInvertedBy _ (hf.shift n)
  obtain ⟨e⟩ := hΦ.nonempty_iso hL
  exact ⟨e.app X⟩

/-! ### Words on objects -/

/-- **One letter.** `Y` is the middle vertex of a distinguished triangle `U ⟶ Y ⟶ V ⟶ U⟦1⟧`
whose two ends are, in either order, `X` and an object of `Q`. For a twist at a centre `S`,
`Q` holds the finite sums of shifts of `S` (`shiftSums`): the evaluation triangle, rotated, is
`E ⟶ T_S E ⟶ (Hom•(S, E) ⊗ S)⟦1⟧ ⟶ E⟦1⟧`, and the coevaluation triangle of `T_S⁻¹` has `E` as
its last vertex. -/
def LetterStep (Q : ObjectProperty C) (X Y : C) : Prop :=
  ∃ T ∈ distTriang C, Nonempty (T.obj₂ ≅ Y) ∧
    ((Nonempty (T.obj₁ ≅ X) ∧ Q T.obj₃) ∨ (Q T.obj₁ ∧ Nonempty (T.obj₃ ≅ X)))

/-- Finite products (equivalently, biproducts) of shifts of objects of `𝒮`, up to
isomorphism. -/
def shiftSums (𝒮 : ObjectProperty C) : ObjectProperty C := fun X ↦
  ∃ (k : ℕ) (S : Fin k → C) (n : Fin k → ℤ), (∀ i, 𝒮 (S i)) ∧
    Nonempty (X ≅ ∏ᶜ fun i ↦ (S i)⟦n i⟧)

/-- A triangulated `K` closed under isomorphisms contains the finite sums of shifts of its
objects. -/
lemma shiftSums_le [K.IsTriangulated] [K.IsClosedUnderIsomorphisms] {𝒮 : ObjectProperty C}
    (h : 𝒮 ≤ K) : shiftSums 𝒮 ≤ K := by
  rintro X ⟨k, S, n, hS, ⟨e⟩⟩
  exact K.prop_of_iso e.symm (K.prop_pi _ fun i ↦ K.le_shift (n i) _ (h _ (hS i)))

/-- **A letter step preserves `K`**, and its complement, when the third vertex lies in `K`. -/
lemma prop_iff_of_letterStep [K.IsTriangulated] [K.IsClosedUnderIsomorphisms]
    {Q : ObjectProperty C} (hQ : Q ≤ K) {X Y : C} (h : LetterStep Q X Y) : K X ↔ K Y := by
  obtain ⟨T, hT, ⟨e₂⟩, h⟩ := h
  rw [← K.prop_iff_of_iso e₂]
  rcases h with ⟨⟨e₁⟩, h₃⟩ | ⟨h₁, ⟨e₃⟩⟩
  · rw [← K.prop_iff_of_iso e₁]
    exact ⟨fun h ↦ K.ext_of_isTriangulatedClosed₂ _ hT h (hQ _ h₃),
      fun h ↦ K.ext_of_isTriangulatedClosed₁ _ hT h (hQ _ h₃)⟩
  · rw [← K.prop_iff_of_iso e₃]
    exact ⟨fun h ↦ K.ext_of_isTriangulatedClosed₂ _ hT (hQ _ h₁) h,
      fun h ↦ K.ext_of_isTriangulatedClosed₃ _ hT (hQ _ h₁) h⟩

/-- **Words preserve every thick subcategory containing their centres.** Along any chain of
letter steps at centres in `𝒮 ≤ K`, membership in `K` is constant. -/
lemma prop_iff_of_reflTransGen [K.IsTriangulated] [K.IsClosedUnderIsomorphisms]
    {𝒮 : ObjectProperty C} (h𝒮 : 𝒮 ≤ K) {X Y : C}
    (h : Relation.ReflTransGen (LetterStep (shiftSums 𝒮)) X Y) : K X ↔ K Y := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (prop_iff_of_letterStep (shiftSums_le h𝒮) hs)

end ObjectProperty

namespace Functor

variable (F : C ⥤ A) [F.IsHomological] (P : ObjectProperty A) [P.IsSerreClass]

/-- **The Serre-preimage theorem for twist words.** Let `F` be homological and `P` a Serre class
of `A` containing `F (E⟦j⟧)` and `F (S⟦j⟧)` for every `j : ℤ` and every centre `S ∈ 𝒮`. Then
`F (Y⟦i⟧) ∈ P` for every `i` and every `Y` reached from `E` by letters at the centres; every prefix
of a word is such a `Y`. -/
theorem prop_obj_shift_of_reflTransGen {𝒮 : ObjectProperty C}
    (h𝒮 : ∀ S, 𝒮 S → ∀ j : ℤ, P (F.obj (S⟦j⟧))) {E Y : C} (hE : ∀ j : ℤ, P (F.obj (E⟦j⟧)))
    (h : Relation.ReflTransGen (ObjectProperty.LetterStep (ObjectProperty.shiftSums 𝒮)) E Y)
    (i : ℤ) : P (F.obj (Y⟦i⟧)) :=
  (ObjectProperty.prop_iff_of_reflTransGen (K := F.serrePreimage P) h𝒮 h).1 hE i

end Functor

end CategoryTheory

namespace DerivedCategory

open CategoryTheory Limits

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] (P : ObjectProperty A)
  [P.IsClosedUnderIsomorphisms]

/-- In the derived category, the Serre preimage under `H⁰` is the class of complexes whose
cohomology lies in `P` in every degree. For a Serre class `P` it is thick. -/
lemma mem_serrePreimage_homologyFunctor_iff (X : DerivedCategory A) :
    (homologyFunctor A 0).serrePreimage P X ↔ ∀ n : ℤ, P ((homologyFunctor A n).obj X) :=
  (homologyFunctor A 0).mem_serrePreimage_iff P X

/-- An object of `A`, placed in degree zero, lies in the Serre preimage of a Serre class `P`
exactly when it lies in `P`. -/
lemma singleFunctor_mem_serrePreimage_iff [P.IsSerreClass] (X : A) :
    (homologyFunctor A 0).serrePreimage P ((singleFunctor A 0).obj X) ↔ P X := by
  rw [mem_serrePreimage_homologyFunctor_iff]
  refine ⟨fun h ↦ P.prop_of_iso ((singleFunctorCompHomologyFunctorIso A 0).app X) (h 0),
    fun h n ↦ ?_⟩
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact P.prop_of_isZero (isZero_of_isGE _ 0 n hn)
  · exact P.prop_of_iso ((singleFunctorCompHomologyFunctorIso A 0).app X).symm h
  · exact P.prop_of_isZero (isZero_of_isLE _ 0 n hn)

end DerivedCategory
