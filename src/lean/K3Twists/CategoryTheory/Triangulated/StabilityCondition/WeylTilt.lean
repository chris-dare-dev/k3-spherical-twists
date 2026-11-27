/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.Coxeter.GeometricRepresentation
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Slicing.Artin
import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-!
# Weyl-indexed galleries of tilts

Let `A` be the heart of a t-structure on a triangulated category, `S_i` spherical objects that
are simple in `A`, and `T_i` their twists. For a word `ω = [i₁, …, i_k]` put
`F_ω = T_{i₁} ∘ ⋯ ∘ T_{i_k}` and `T_ω := A ∩ F_ω A[1]`. One induction on the word gives the whole
gallery `A, F_{i₁} A, F_{i₁ i₂} A, …` (`WeylGalleryHypotheses.gallery_step`):

* `F_ω A = ⟨T_ω^⊥ ∩ A, T_ω[-1]⟩`, the lower tilt of `A` at the torsion class `T_ω`;
* if the class `ω(α_i)` of `F_ω S_i` is a positive root, then `F_ω S_i` is simple in `F_ω A`, lies
  in `A ∩ T_ω^⊥`, and `T_{ω i} = Filt(T_ω ∪ {F_ω S_i})`;
* if the classes `α_i` are linearly independent and `u i` is root-positive with `u(α_i) = α_j`,
  then `F_{u i} S_i ≅ S_j[-1]`; at the reduced words of the longest element `w₀`, with
  `w₀(α_i) = -α_{π i}`, this is `F_{w₀} S_i ≅ S_{π i}[-1]`
  (`WeylGalleryHypotheses.F_obj_iso_shift`, `WeylGalleryHypotheses.longest_obj_iso_shift`).

The words are root-positive words (`BilinearForm.IsRootPositive`): every prefix root
`s_{i₁} ⋯ s_{i_{j-1}}(α_{i_j})` is a nonempty sum of simple roots. By Tits' positivity theorem
these are exactly the reduced words of the Weyl group; that theorem is not formalized
(`CoxeterMatrix.CoxeterPositivity`), so the induction is on root-positive words, which for an
explicit word is a finite computation (`CoxeterMatrix.longestWordA`).

## Inputs

Mathlib has hearts of t-structures as properties of objects but no theory of their tilts, and
no spherical twist functors. The structure `WeylGalleryHypotheses` takes:

* a t-structure `t` with heart `A`, and a `TwistConjugation.Configuration`: spherical objects
  `S_i`, autoequivalences `T_i`, the link `[T_i] = τ(S_i)` and the conjugation formula
  `T_{Φ S} ≅ Φ T_S Φ⁻¹` (Seidel–Thomas, arXiv:math/0001043, Lemma 2.11);
* **the sign of the class**: a class map `cl`, additive on triangles, along which `T_i` acts by
  the reflection in `cl(S_i)`, and a cone containing the class of every nonzero object of `A` and
  no pair `v, -v` (for a stability function `Z` on `A`, the classes with `Z` in the upper half
  plane or on the negative real axis);
* **the simple tilt**: `T_i A = ⟨S_i^⊥ ∩ A, S_i[-1]⟩`, the lower tilt of `A` at `Filt(S_i)`; this
  is the `2`-Calabi–Yau case, where `T_S S ≅ S[-1]`;
* **tilt composition**: if `X` is simple in the lower tilt `B` of `A` at a torsion class `T` and
  lies in `T^⊥ ∩ A`, the lower tilt of `B` at `Filt(X)` is the lower tilt of `A` at
  `Filt(T ∪ {X})`, again a torsion class;
* **`C` Serre in `A`**: a class `hull` containing the `S_i` and stable under the `T_i` (the
  thick subcategory they generate) whose objects in `A` lie in `Filt(S)`. When the extension
  closure `C` of the `S_i` is a Serre subcategory of `A`, this holds for that thick subcategory.

Tilt composition and the Serre condition are statements about hearts of bounded t-structures:
the hearts between `A[-1]` and `A` are the tilts of `A` at its torsion classes (Happel, Reiten
and Smalø, *Tilting in abelian categories and quasitilted algebras*, Mem. Amer. Math. Soc. 575;
Woolf, arXiv:0909.0552), and the tilt of `A^♭_T` at a simple object of `T^⊥ ∩ A` is again such a
heart. The simple tilt is a statement about twists in the `2`-Calabi–Yau case. Tilts are defined
here as properties of objects (`WeylGallery.lowerTilt`), with no claim that they are hearts;
once hearts of t-structures are abelian categories in the library, tilt composition and the
Serre condition become lemmas.

## Real objects

There is no instance of `WeylGalleryHypotheses` from geometry: it needs the derived category of a
K3 surface as a triangulated category with a heart, and spherical twist functors, and Mathlib has
neither (twist functors need a dg or Fourier–Mukai enhancement). The fields with no geometric
instance are therefore `conf` (the twists), the simple-tilt field `image_heart_eq_lowerTilt` and
tilt composition `lowerTilt_lowerTilt_eq`. The class-level half of every statement here, which
is what the induction feeds on, is instantiated from real classes in
`AlgebraicGeometry/Surface/K3/EllipticWithSection/WeylGallery.lean`, the `A₂` configuration
`𝒪_X[1]`, `𝒪_C` on the Mukai lattice of an elliptic K3 surface with a section.

## Corollaries

* **The Garside bound** (`WeylGalleryHypotheses.heartOf_flatten_le_window`): if a positive word is
  a concatenation of `m` root-positive words (for instance `Δ^k x₁ ⋯ x_l` with `m = k + l`), then
  `F A` lies in the window `[A[-m], A]`: every object of `F A` has a finite filtration with
  factors in `A[-j]`, `0 ≤ j ≤ m`. So `A[-(k+m)] ≤ F A ≤ A` for `F = Δ^k x₁ ⋯ x_m`.
* **The left edge** is the dual theorem (`WeylGalleryHypotheses.heart_eq_lowerTilt_image_symm`):
  read from `F_ω⁻¹ A`, the same gallery is a chain of lower tilts that ends at `A`, the last one
  at `F_ω⁻¹ T_ω`. Its upper-tilt form `F_ω⁻¹ A = ⟨F[1], ⊥F ∩ A⟩` needs Happel–Reiten–Smalø
  inversion and is not stated.
* **Path independence** (`WeylGalleryHypotheses.heartOf_eq_of_eq`): two words with the same image
  in the Artin group give the same heart. It uses only the braid relations of the configuration;
  Matsumoto's theorem (reduced words of one element are related by braid moves) is not
  formalized, so the hypothesis is equality in the Artin group.
* **Each step is the twist along the new simple object**
  (`WeylGalleryHypotheses.twist_F_obj`): `τ(F_ω S_i) = [F_{ω i}] [F_ω]⁻¹`, by the conjugation
  formula, so `F_{ω i} A = T_{F_ω S_i}(F_ω A)` (`WeylGalleryHypotheses.image_heartOf_of_twist`).

## Conventions

`F_ω` is `TriEquiv.ofWord`, which applies the rightmost letter first, and `ω` acts on classes by
`BilinearForm.reflectWord` in the same order. The image of a property under an autoequivalence
is `X ∈ Φ(P) ↔ Φ⁻¹ X ∈ P` (`WeylGallery.image`), as for slicings (`TriEquiv.act`). A heart
`B` with `A[-1] ≤ B ≤ A` is the lower tilt `⟨T^⊥ ∩ A, T[-1]⟩` (objects `X` with a distinguished
triangle `F → X → T'[-1] → F[1]`), not the upper tilt `⟨F[1], T⟩ = ⟨T^⊥ ∩ A, T[-1]⟩[1]`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CoxeterSystem
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
open ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace WeylGallery

/-! ### Filtrations, tilts, simple objects and torsion classes -/

/-- The objects isomorphic to `X`. -/
def isoClass (X : C) : ObjectProperty C := fun Y => Nonempty (Y ≅ X)

instance (X : C) : (isoClass X).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨e'⟩ => ⟨e.symm ≪≫ e'⟩

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
theorem isoClass_self (X : C) : isoClass X X := ⟨Iso.refl X⟩

instance : ObjectProperty.IsClosedUnderIsomorphisms (IsZero (C := C)) where
  of_iso e h := h.of_iso e.symm

instance isClosedUnderIsomorphisms_sup (P Q : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [Q.IsClosedUnderIsomorphisms] : (P ⊔ Q).IsClosedUnderIsomorphisms where
  of_iso e h := h.imp (P.prop_of_iso e) (Q.prop_of_iso e)

instance isClosedUnderIsomorphisms_inf (P Q : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [Q.IsClosedUnderIsomorphisms] : (P ⊓ Q).IsClosedUnderIsomorphisms where
  of_iso e h := ⟨P.prop_of_iso e h.1, Q.prop_of_iso e h.2⟩

instance isClosedUnderIsomorphisms_extensionProductIter (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (n : ℕ) :
    (P.extensionProductIter n).IsClosedUnderIsomorphisms := by
  cases n with
  | zero => rw [ObjectProperty.extensionProductIter_zero]; infer_instance
  | succ n => rw [ObjectProperty.extensionProductIter_succ]; infer_instance

/-- `Filt(P)`: the objects with a finite filtration by distinguished triangles whose factors
satisfy `P` or are zero. -/
def filtration (P : ObjectProperty C) : ObjectProperty C :=
  fun X => ∃ n, (P ⊔ IsZero).extensionProductIter n X

instance (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    (filtration P).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨n, h⟩ => ⟨n, ObjectProperty.prop_of_iso _ e h⟩

theorem le_filtration (P : ObjectProperty C) : P ≤ filtration P :=
  fun _ h => ⟨0, Or.inl h⟩

theorem filtration_of_isZero (P : ObjectProperty C) {X : C} (h : IsZero X) : filtration P X :=
  ⟨0, Or.inr h⟩

theorem filtration_mono {P Q : ObjectProperty C} (h : P ≤ Q) : filtration P ≤ filtration Q :=
  fun X ⟨n, hX⟩ =>
    ⟨n, ObjectProperty.monotone_extensionProductIter (sup_le_sup_right h IsZero) n X hX⟩

/-- `Filt(P)` is closed under extensions. -/
theorem extensionProduct_filtration_le [IsTriangulated C] (P : ObjectProperty C) :
    ObjectProperty.extensionProduct (filtration P) (filtration P) ≤ filtration P := by
  rintro X ⟨Y, Z, f, g, h, hT, ⟨a, hY⟩, ⟨b, hZ⟩⟩
  refine ⟨a + 1 + b, ?_⟩
  rw [ObjectProperty.extensionProductIter_add _ (n' := a) rfl]
  exact ⟨Y, Z, f, g, h, hT, hY, hZ⟩

/-- `Filt` is idempotent. -/
theorem filtration_le_filtration [IsTriangulated C] {P Q : ObjectProperty C}
    (h : Q ≤ filtration P) : filtration Q ≤ filtration P := by
  rintro X ⟨n, hX⟩
  induction n generalizing X with
  | zero => exact Or.elim hX (fun h' => h X h') (fun h' => filtration_of_isZero P h')
  | succ n ih =>
    rw [ObjectProperty.extensionProductIter_succ] at hX
    obtain ⟨Y, Z, f, g, h', hT, hY, hZ⟩ := hX
    exact extensionProduct_filtration_le P X
      ⟨Y, Z, f, g, h', hT, Or.elim hY (fun h'' => h Y h'') (fun h'' => filtration_of_isZero P h''),
        ih _ hZ⟩

/-- The lower tilt `⟨T^⊥ ∩ A, T[-1]⟩` of `A` at `T`: the objects `X` with a distinguished triangle
`F → X → T'[-1] → F[1]`, where `F ∈ A` receives no nonzero map from `T` and `T' ∈ T`. -/
def lowerTilt (A T : ObjectProperty C) : ObjectProperty C :=
  ObjectProperty.extensionProduct (A ⊓ T.rightOrthogonal) (T.shift (1 : ℤ))

instance (A T : ObjectProperty C) : (lowerTilt A T).IsClosedUnderIsomorphisms := by
  unfold lowerTilt; infer_instance

/-- The nonzero objects. -/
def nonzero : ObjectProperty C := fun X => ¬IsZero X

instance : (nonzero (C := C)).IsClosedUnderIsomorphisms where
  of_iso e h h' := h (h'.of_iso e)

/-- `X` is simple in `H`: a nonzero object of `H` that is not an extension of two nonzero
objects of `H`. In a heart, distinguished triangles with all three vertices in the heart are
the short exact sequences, so this is simplicity in the abelian sense. -/
def IsSimpleIn (H : ObjectProperty C) (X : C) : Prop :=
  H X ∧ ¬IsZero X ∧ ¬ObjectProperty.extensionProduct (H ⊓ nonzero) (H ⊓ nonzero) X

/-- A torsion class of `A`, in triangulated terms: a class of objects of `A`, closed under
isomorphisms and extensions, containing the zero objects, and containing every quotient in `A`
of each of its objects. -/
structure IsTorsionClass (A T : ObjectProperty C) : Prop where
  le : T ≤ A
  isClosedUnderIsomorphisms : T.IsClosedUnderIsomorphisms
  prop_of_isZero : ∀ X, IsZero X → T X
  ext : ∀ ⦃X₁ X₂ X₃ : C⦄ (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : X₃ ⟶ X₁⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C → T X₁ → T X₃ → T X₂
  quot : ∀ ⦃X₁ X₂ X₃ : C⦄ (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : X₃ ⟶ X₁⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C → A X₁ → T X₂ → A X₃ → T X₃

/-! ### Images under exact autoequivalences -/

/-- The image `Φ(P)` of a property under an exact autoequivalence: `X ∈ Φ(P)` iff
`Φ⁻¹ X ∈ P`. -/
def image (Φ : TriEquiv C) (P : ObjectProperty C) : ObjectProperty C :=
  fun X => P (Φ.e.inverse.obj X)

section Image

variable (Φ : TriEquiv C)

instance (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    (image Φ P).IsClosedUnderIsomorphisms where
  of_iso e h := P.prop_of_iso (Φ.e.inverse.mapIso e) h

theorem image_obj_iff (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (X : C) :
    image Φ P (Φ.e.functor.obj X) ↔ P X :=
  P.prop_iff_of_iso (Φ.e.unitIso.app X).symm

@[simp] theorem image_id (P : ObjectProperty C) : image TriEquiv.id P = P := rfl

theorem image_comp (Φ Ψ : TriEquiv C) (P : ObjectProperty C) :
    image (Φ.comp Ψ) P = image Ψ (image Φ P) := rfl

theorem image_inf (P Q : ObjectProperty C) : image Φ (P ⊓ Q) = image Φ P ⊓ image Φ Q := rfl

theorem image_sup (P Q : ObjectProperty C) : image Φ (P ⊔ Q) = image Φ P ⊔ image Φ Q := rfl

theorem image_mono {P Q : ObjectProperty C} (h : P ≤ Q) : image Φ P ≤ image Φ Q :=
  fun _ hX => h _ hX

/-- Naturally isomorphic autoequivalences have the same images. -/
theorem image_congr {Φ Ψ : TriEquiv C} (h : Nonempty (Φ.e.functor ≅ Ψ.e.functor))
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] : image Φ P = image Ψ P := by
  ext X
  exact P.prop_iff_of_iso ((TriEquiv.inverseIsoOfFunctorIso h.some).app X)

theorem image_symm_image (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    image Φ.symm (image Φ P) = P := by
  ext X
  exact P.prop_iff_of_iso (Φ.e.unitIso.app X).symm

theorem image_isZero : image Φ (IsZero (C := C)) = IsZero := by
  ext X
  refine ⟨fun h => ?_, fun h => Φ.e.inverse.map_isZero h⟩
  exact (Φ.e.functor.map_isZero h).of_iso (Φ.e.counitIso.app X).symm

theorem image_nonzero : image Φ (nonzero (C := C)) = nonzero := by
  ext X
  exact not_congr (iff_of_eq (congrFun (image_isZero Φ) X))

theorem image_isoClass (X : C) : image Φ (isoClass X) = isoClass (Φ.e.functor.obj X) := by
  ext Y
  exact ⟨fun ⟨e⟩ => ⟨(Φ.e.counitIso.app Y).symm ≪≫ Φ.e.functor.mapIso e⟩,
    fun ⟨e⟩ => ⟨Φ.e.inverse.mapIso e ≪≫ (Φ.e.unitIso.app X).symm⟩⟩

/-- A triangulated functor maps an extension of `Q` by `P` to an extension of `Q'` by `P'`. -/
theorem extensionProduct_map (F : C ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
    {P Q P' Q' : ObjectProperty C} (hP : ∀ X, P X → P' (F.obj X))
    (hQ : ∀ X, Q X → Q' (F.obj X)) {X : C} (hX : ObjectProperty.extensionProduct P Q X) :
    ObjectProperty.extensionProduct P' Q' (F.obj X) := by
  obtain ⟨Y, Z, f, g, h, hT, hY, hZ⟩ := hX
  exact ⟨F.obj Y, F.obj Z, F.map f, F.map g, F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app Y,
    F.map_distinguished _ hT, hP Y hY, hQ Z hZ⟩

/-- The shift maps an extension of `Q` by `P` to an extension of `Q'` by `P'`. -/
theorem extensionProduct_shift (a : ℤ) {P Q P' Q' : ObjectProperty C}
    (hP : ∀ X, P X → P' (X⟦a⟧)) (hQ : ∀ X, Q X → Q' (X⟦a⟧)) {X : C}
    (hX : ObjectProperty.extensionProduct P Q X) :
    ObjectProperty.extensionProduct P' Q' (X⟦a⟧) := by
  obtain ⟨Y, Z, f, g, h, hT, hY, hZ⟩ := hX
  exact ⟨_, _, _, _, _, Triangle.shift_distinguished _ hT a, hP Y hY, hQ Z hZ⟩

theorem image_extensionProduct (P Q : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [Q.IsClosedUnderIsomorphisms] :
    image Φ (ObjectProperty.extensionProduct P Q) =
      ObjectProperty.extensionProduct (image Φ P) (image Φ Q) := by
  ext X
  constructor
  · intro hX
    have h := extensionProduct_map Φ.e.functor (P' := image Φ P) (Q' := image Φ Q)
      (fun Y hY => (image_obj_iff Φ P Y).2 hY) (fun Z hZ => (image_obj_iff Φ Q Z).2 hZ) hX
    exact ObjectProperty.prop_of_iso _ (Φ.e.counitIso.app X) h
  · intro hX
    exact extensionProduct_map Φ.e.inverse (fun Y hY => hY) (fun Z hZ => hZ) hX

theorem image_shift (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (a : ℤ) :
    image Φ (P.shift a) = (image Φ P).shift a := by
  ext X
  exact P.prop_iff_of_iso ((Φ.e.inverse.commShiftIso a).app X).symm

theorem image_rightOrthogonal (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    image Φ P.rightOrthogonal = (image Φ P).rightOrthogonal := by
  ext X
  constructor
  · intro hX Y f hY
    apply Φ.e.inverse.map_injective
    rw [Functor.map_zero]
    exact hX _ hY
  · intro hX Y f hY
    have h := hX (Φ.e.functor.map f ≫ Φ.e.counitIso.hom.app X) ((image_obj_iff Φ P Y).2 hY)
    apply Φ.e.functor.map_injective
    rw [Functor.map_zero, ← cancel_mono (Φ.e.counitIso.hom.app X), h, zero_comp]

theorem image_lowerTilt (A T : ObjectProperty C) [A.IsClosedUnderIsomorphisms]
    [T.IsClosedUnderIsomorphisms] :
    image Φ (lowerTilt A T) = lowerTilt (image Φ A) (image Φ T) := by
  rw [lowerTilt, image_extensionProduct, image_inf, image_rightOrthogonal, image_shift]
  rfl

theorem image_extensionProductIter (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (n : ℕ) : image Φ (P.extensionProductIter n) = (image Φ P).extensionProductIter n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ObjectProperty.extensionProductIter_succ, ObjectProperty.extensionProductIter_succ,
      image_extensionProduct, ih]

theorem image_filtration (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    image Φ (filtration P) = filtration (image Φ P) := by
  ext X
  change (∃ n, _) ↔ ∃ n, _
  refine exists_congr fun n => ?_
  have h := congrFun (image_extensionProductIter Φ (P ⊔ IsZero) n) X
  rw [image_sup, image_isZero] at h
  exact iff_of_eq h

theorem isSimpleIn_image_iff (H : ObjectProperty C) [H.IsClosedUnderIsomorphisms] (X : C) :
    IsSimpleIn (image Φ H) (Φ.e.functor.obj X) ↔ IsSimpleIn H X := by
  have hz : IsZero (Φ.e.functor.obj X) ↔ IsZero X :=
    ⟨fun h => (Φ.e.inverse.map_isZero h).of_iso (Φ.e.unitIso.app X),
      fun h => Φ.e.functor.map_isZero h⟩
  have he := image_obj_iff Φ (ObjectProperty.extensionProduct (H ⊓ nonzero) (H ⊓ nonzero)) X
  rw [image_extensionProduct, image_inf, image_nonzero] at he
  unfold IsSimpleIn
  rw [image_obj_iff, hz, he]

end Image

/-! ### Simple objects of a lower tilt, and the zero tilt -/

omit [HasZeroObject C] [Pretriangulated C] in
theorem isZero_shift_iff {X : C} (a : ℤ) : IsZero (X⟦a⟧) ↔ IsZero X :=
  ⟨fun h => ((shiftFunctor C (-a)).map_isZero h).of_iso
      ((shiftFunctorCompIsoId C a (-a) (add_neg_cancel a)).app X).symm,
    fun h => (shiftFunctor C a).map_isZero h⟩

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
theorem rightOrthogonal_of_isZero {P : ObjectProperty C} {X : C} (h : IsZero X) :
    P.rightOrthogonal X :=
  fun _ _ _ => h.eq_of_tgt _ _

/-- An object of `A ∩ T^⊥` lies in the lower tilt. -/
theorem lowerTilt_of_left {A T : ObjectProperty C} (hT0 : ∀ X, IsZero X → T X) {X : C}
    (hX : (A ⊓ T.rightOrthogonal) X) : lowerTilt A T X :=
  ⟨X, 0, 𝟙 X, 0, 0, contractible_distinguished X, hX,
    hT0 _ ((isZero_shift_iff 1).2 (isZero_zero C))⟩

/-- An object of `T[-1]` lies in the lower tilt. -/
theorem lowerTilt_of_right {A T : ObjectProperty C} (hA0 : ∀ X, IsZero X → A X) {X : C}
    (hX : T (X⟦(1 : ℤ)⟧)) : lowerTilt A T X :=
  ⟨0, X, 0, 𝟙 X, 0, contractible_distinguished₁ X,
    ⟨hA0 _ (isZero_zero C), rightOrthogonal_of_isZero (isZero_zero C)⟩, hX⟩

/-- **A simple object of a lower tilt lies on one side of it**: in `A ∩ T^⊥`, or isomorphic to a
nonzero `Z` with `Z[1] ∈ T`. -/
theorem IsSimpleIn.lowerTilt_cases {A T : ObjectProperty C} [A.IsClosedUnderIsomorphisms]
    (hA0 : ∀ X, IsZero X → A X) (hT0 : ∀ X, IsZero X → T X) {X : C}
    (hX : IsSimpleIn (lowerTilt A T) X) :
    (A ⊓ T.rightOrthogonal) X ∨ ∃ Z, T (Z⟦(1 : ℤ)⟧) ∧ ¬IsZero Z ∧ Nonempty (X ≅ Z) := by
  obtain ⟨⟨F, Z, f, g, h, hT, hF, hZ⟩, hX0, hXs⟩ := hX
  by_cases hF0 : IsZero F
  · have : IsIso g := (Triangle.isZero₁_iff_isIso₂ _ hT).1 hF0
    refine Or.inr ⟨Z, hZ, fun hZ0 => hX0 (hZ0.of_iso (asIso g)), ⟨asIso g⟩⟩
  by_cases hZ0 : IsZero Z
  · have : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).1 hZ0
    exact Or.inl (ObjectProperty.prop_of_iso _ (asIso f) hF)
  exact absurd ⟨F, Z, f, g, h, hT, ⟨lowerTilt_of_left hT0 hF, hF0⟩,
    ⟨lowerTilt_of_right hA0 hZ, hZ0⟩⟩ hXs

/-! ### Torsion classes of a heart -/

section Heart

variable (t : TStructure C)

/-- Zero objects lie in the heart. -/
theorem heart_of_isZero {X : C} (hX : IsZero X) : t.heart X := by
  obtain ⟨X', Y, hX', hY, f, g, h, hT⟩ := t.exists_triangle_zero_one (0 : C)
  have : IsIso h := (Triangle.isZero₁_iff_isIso₂ _ (rot_of_distTriang _ hT)).1 (isZero_zero C)
  have hYle : t.le 0 Y := (t.le 0).prop_of_iso (asIso h).symm
    (t.le_monotone (show (-1 : ℤ) ≤ 0 by norm_num) _ (t.le_shift 0 1 (-1) (by norm_num) X' hX'))
  have hY0 : IsZero Y := by
    rw [IsZero.iff_id_eq_zero]
    exact t.zero' _ hYle hY
  have hX'0 : IsZero X' := (isZero_shift_iff 1).1 (hY0.of_iso (asIso h).symm)
  exact ⟨(t.le 0).prop_of_iso (hX'0.iso hX) hX',
    (t.ge 0).prop_of_iso (hY0.iso hX) (t.ge_one_le _ hY)⟩

/-- The zero objects form a torsion class of the heart. -/
theorem isTorsionClass_isZero : IsTorsionClass t.heart (IsZero (C := C)) where
  le _ h := heart_of_isZero t h
  isClosedUnderIsomorphisms := inferInstance
  prop_of_isZero _ h := h
  ext _ _ _ _ _ _ hT h₁ h₃ := Triangle.isZero₂_of_isZero₁₃ _ hT h₁ h₃
  quot X₁ X₂ X₃ f g h hT h₁ h₂ h₃ := by
    have : IsIso h := (Triangle.isZero₁_iff_isIso₂ _ (rot_of_distTriang _ hT)).1 h₂
    have : t.IsLE X₁ 0 := ⟨h₁.1⟩
    have : t.IsGE X₃ 0 := ⟨h₃.2⟩
    have : t.IsLE (X₁⟦(1 : ℤ)⟧) (-1) := t.isLE_shift X₁ 0 1 (-1) (by norm_num)
    have h0 : inv h = 0 := t.zero (inv h) (-1) 0 (by norm_num)
    rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id h, h0, comp_zero]

/-- The lower tilt at the zero class is the heart itself. -/
theorem lowerTilt_isZero : lowerTilt t.heart (IsZero (C := C)) = t.heart := by
  ext X
  constructor
  · rintro ⟨F, Z, f, g, h, hT, ⟨hF, -⟩, hZ⟩
    have : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).1 ((isZero_shift_iff 1).1 hZ)
    exact t.heart.prop_of_iso (asIso f) hF
  · intro hX
    exact lowerTilt_of_left (fun _ h => h) ⟨hX, fun _ _ h => h.eq_of_src _ _⟩

/-- **A torsion class is recovered from its lower tilt**: `A ∩ (lower tilt of A at T)[1] = T`. -/
theorem inf_shift_lowerTilt {T : ObjectProperty C} (hT : IsTorsionClass t.heart T) :
    t.heart ⊓ (lowerTilt t.heart T).shift (-1 : ℤ) = T := by
  have := hT.isClosedUnderIsomorphisms
  ext X
  constructor
  · rintro ⟨hX, F, Z, f, g, h, hTr, ⟨hF, -⟩, hZ⟩
    have : t.IsLE F 0 := ⟨hF.1⟩
    have : t.IsGE X 0 := ⟨hX.2⟩
    have : t.IsGE (X⟦(-1 : ℤ)⟧) 1 := t.isGE_shift X 0 (-1) 1 (by norm_num)
    have hf : f = 0 := t.zero f 0 1 (by norm_num)
    have : t.IsGE (Z⟦(1 : ℤ)⟧) 0 := ⟨(hT.le _ hZ).2⟩
    have : t.IsGE Z 1 := t.isGE_of_shift Z 1 1 0 (by norm_num)
    have hZ2 : t.IsGE (Z⟦(-1 : ℤ)⟧) 2 := t.isGE_shift Z 1 (-1) 2 (by norm_num)
    obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hTr) (𝟙 F)
      (by change 𝟙 F ≫ f = 0; rw [hf, comp_zero])
    have hu0 : u = 0 := t.zero_of_isLE_of_isGE u 0 2 (by norm_num) ‹_› hZ2
    have hF0 : IsZero F := by rw [IsZero.iff_id_eq_zero, hu, hu0]; exact zero_comp
    have : IsIso g := (Triangle.isZero₁_iff_isIso₂ _ hTr).1 hF0
    exact T.prop_of_iso ((shiftFunctor C (1 : ℤ)).mapIso (asIso g).symm ≪≫
      (shiftFunctorCompIsoId C (-1 : ℤ) 1 (by norm_num)).app X) hZ
  · intro hX
    refine ⟨hT.le _ hX, lowerTilt_of_right (fun _ h => heart_of_isZero t h) ?_⟩
    exact T.prop_of_iso ((shiftFunctorCompIsoId C (-1 : ℤ) 1 (by norm_num)).app X).symm hX

end Heart

/-! ### Rigidity of filtrations by objects with independent classes -/

section Rigidity

variable {Λ : Type*} [AddCommGroup Λ] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (S : ι → C) (cl : C → Λ) (cl_iso : ∀ {X Y : C}, (X ≅ Y) → cl X = cl Y)
  (cl_triangle : ∀ {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : X₃ ⟶ X₁⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C → cl X₂ = cl X₁ + cl X₃)
  (cl_zero : ∀ X, IsZero X → cl X = 0)

include cl_iso cl_triangle cl_zero in
/-- A filtration by the `S i` has a multiplicity vector, which detects zero objects and the
`S j` themselves. -/
theorem exists_multiplicity {X : C}
    (hX : filtration (ObjectProperty.ofObj S).isoClosure X) :
    ∃ m : ι → ℕ, cl X = ∑ k, (m k : ℤ) • cl (S k) ∧ (m = 0 → IsZero X) ∧
      ∀ j, m = Pi.single j 1 → Nonempty (X ≅ S j) := by
  obtain ⟨n, hX⟩ := hX
  have base : ∀ Y, ((ObjectProperty.ofObj S).isoClosure ⊔ IsZero) Y → ∃ m : ι → ℕ,
      cl Y = ∑ k, (m k : ℤ) • cl (S k) ∧ (m = 0 → IsZero Y) ∧
        ∀ j, m = Pi.single j 1 → Nonempty (Y ≅ S j) := by
    rintro Y (⟨_, ⟨k⟩, ⟨e⟩⟩ | hY)
    · refine ⟨Pi.single k 1, ?_, fun h => absurd (congr_fun h k) (by simp), fun j hj => ?_⟩
      · rw [cl_iso e]
        simp [Pi.single_apply]
      · have : k = j := by
          by_contra hkj
          have := congr_fun hj k
          simp [hkj] at this
        subst this
        exact ⟨e⟩
    · refine ⟨0, by simp [cl_zero Y hY], fun _ => hY, fun j hj => ?_⟩
      have := congr_fun hj j
      simp at this
  induction n generalizing X with
  | zero => exact base X hX
  | succ n ih =>
    rw [ObjectProperty.extensionProductIter_succ] at hX
    obtain ⟨Y, Z, f, g, h, hT, hY, hZ⟩ := hX
    obtain ⟨mY, hclY, hY0, hYs⟩ := base Y hY
    obtain ⟨mZ, hclZ, hZ0, hZs⟩ := ih hZ
    refine ⟨mY + mZ, ?_, fun hm => ?_, fun j hj => ?_⟩
    · rw [cl_triangle f g h hT, hclY, hclZ, ← Finset.sum_add_distrib]
      simp [add_smul]
    · have hmY : mY = 0 := funext fun k => by have := congr_fun hm k; simp at this ⊢; omega
      have hmZ : mZ = 0 := funext fun k => by have := congr_fun hm k; simp at this ⊢; omega
      exact Triangle.isZero₂_of_isZero₁₃ _ hT (hY0 hmY) (hZ0 hmZ)
    · have hk : ∀ k, k ≠ j → mY k = 0 ∧ mZ k = 0 := fun k hk => by
        have := congr_fun hj k
        simp [hk] at this
        omega
      have hjj := congr_fun hj j
      simp only [Pi.add_apply, Pi.single_eq_same] at hjj
      rcases Nat.eq_zero_or_pos (mY j) with hYj | hYj
      · have hmY : mY = 0 := funext fun k => by
          by_cases hkj : k = j
          · subst hkj; simpa using hYj
          · simpa using (hk k hkj).1
        have hmZ : mZ = Pi.single j 1 := funext fun k => by
          by_cases hkj : k = j
          · subst hkj; simp; omega
          · simp [hkj, (hk k hkj).2]
        have : IsIso g := (Triangle.isZero₁_iff_isIso₂ _ hT).1 (hY0 hmY)
        obtain ⟨e⟩ := hZs j hmZ
        exact ⟨asIso g ≪≫ e⟩
      · have hmZ : mZ = 0 := funext fun k => by
          by_cases hkj : k = j
          · subst hkj; simp; omega
          · simpa using (hk k hkj).2
        have hmY : mY = Pi.single j 1 := funext fun k => by
          by_cases hkj : k = j
          · subst hkj; simp; omega
          · simp [hkj, (hk k hkj).1]
        have : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hZ0 hmZ)
        obtain ⟨e⟩ := hYs j hmY
        exact ⟨(asIso f).symm ≪≫ e⟩

include cl_iso cl_triangle cl_zero in
/-- **Rigidity**: if the classes of the `S i` are linearly independent, an object with a
filtration by the `S i` whose class is `cl (S j)` is isomorphic to `S j`. -/
theorem nonempty_iso_of_cl_eq (hS : LinearIndependent ℤ fun i => cl (S i)) {X : C}
    (hX : filtration (ObjectProperty.ofObj S).isoClosure X) {j : ι} (h : cl X = cl (S j)) :
    Nonempty (X ≅ S j) := by
  obtain ⟨m, hcl, -, hs⟩ := exists_multiplicity S cl cl_iso cl_triangle cl_zero hX
  refine hs j (funext fun k => ?_)
  have h0 := Fintype.linearIndependent_iff.1 hS
    (fun k => (m k : ℤ) - (Pi.single j (1 : ℤ) : ι → ℤ) k) (by
    simp only [sub_smul, Finset.sum_sub_distrib, ← hcl, h]
    simp [Pi.single_apply])
  have := h0 k
  rw [sub_eq_zero] at this
  by_cases hkj : k = j
  · subst hkj; simp at this ⊢; omega
  · simp [hkj] at this ⊢; omega

end Rigidity

/-! ### Windows -/

/-- The factors of the window `[A[-n], A]`: objects of some `A[-j]`, `0 ≤ j ≤ n`. -/
def windowFactor (A : ObjectProperty C) (n : ℕ) : ObjectProperty C :=
  fun X => ∃ j ≤ n, A (X⟦(j : ℤ)⟧)

instance (A : ObjectProperty C) [A.IsClosedUnderIsomorphisms] (n : ℕ) :
    (windowFactor A n).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨j, hj, h⟩ => ⟨j, hj, A.prop_of_iso ((shiftFunctor C (j : ℤ)).mapIso e) h⟩

/-- The window `[A[-n], A]`: objects with a finite filtration whose factors lie in `A[-j]` for
some `0 ≤ j ≤ n`. For the heart of a bounded t-structure these are the objects with cohomology
in degrees `0, …, n`. -/
def window (A : ObjectProperty C) (n : ℕ) : ObjectProperty C :=
  filtration (windowFactor A n)

theorem le_window_zero (A : ObjectProperty C) [A.IsClosedUnderIsomorphisms] :
    A ≤ window A 0 :=
  fun X hX => le_filtration _ X ⟨0, le_rfl, A.prop_of_iso ((shiftFunctorZero C ℤ).app X).symm hX⟩

/-- The shift of a filtration is a filtration of the shifts. -/
theorem filtration_shift {P Q : ObjectProperty C} (a : ℤ) (h : ∀ X, P X → Q (X⟦a⟧)) {X : C}
    (hX : filtration P X) : filtration Q (X⟦a⟧) := by
  obtain ⟨n, hX⟩ := hX
  have h' : ∀ Y, (P ⊔ IsZero) Y → (Q ⊔ IsZero) (Y⟦a⟧) :=
    fun Y hY => hY.imp (h Y) (fun hY => (isZero_shift_iff a).2 hY)
  refine ⟨n, ?_⟩
  induction n generalizing X with
  | zero => exact h' X hX
  | succ n ih =>
    rw [ObjectProperty.extensionProductIter_succ] at hX ⊢
    exact extensionProduct_shift a h' (fun Y hY => ih hY) hX

theorem image_window (Φ : TriEquiv C) (A : ObjectProperty C) [A.IsClosedUnderIsomorphisms]
    (n : ℕ) : image Φ (window A n) = window (image Φ A) n := by
  rw [window, window, image_filtration]
  congr 1
  ext X
  exact exists_congr fun j => and_congr_right fun _ =>
    A.prop_iff_of_iso ((Φ.e.inverse.commShiftIso (j : ℤ)).app X).symm

/-- **Windows compose**: a window of width `m` over the window `[A[-1], A]` lies in the window
`[A[-(m+1)], A]`. -/
theorem window_window_le [IsTriangulated C] (A : ObjectProperty C) [A.IsClosedUnderIsomorphisms]
    (m : ℕ) : window (window A 1) m ≤ window A (m + 1) := by
  refine filtration_le_filtration fun X ⟨j, hj, hX⟩ => ?_
  have h := filtration_shift (Q := fun X => ∃ l ≤ m + 1, A (X⟦(l : ℤ)⟧)) (-(j : ℤ))
    (fun Z ⟨l, hl, hZ⟩ => ⟨l + j, by omega, A.prop_of_iso
      ((shiftFunctorAdd' C (-(j : ℤ)) ((l + j : ℕ) : ℤ) (l : ℤ) (by push_cast; ring)).app Z) hZ⟩)
    hX
  exact ObjectProperty.prop_of_iso _ ((shiftFunctorCompIsoId C (j : ℤ) (-(j : ℤ))
    (add_neg_cancel _)).app X) h

theorem lowerTilt_le_window_one (A T : ObjectProperty C) [A.IsClosedUnderIsomorphisms]
    (hT : T ≤ A) : lowerTilt A T ≤ window A 1 := by
  rintro X ⟨F, Z, f, g, h, hTr, ⟨hF, -⟩, hZ⟩
  refine ⟨1, ?_⟩
  rw [ObjectProperty.extensionProductIter_succ]
  exact ⟨F, Z, f, g, h, hTr, Or.inl ⟨0, by norm_num, A.prop_of_iso
    ((shiftFunctorZero C ℤ).app F).symm hF⟩, Or.inl ⟨1, le_rfl, hT _ hZ⟩⟩

end WeylGallery

/-! ### Words of autoequivalences -/

namespace WeakStabilityCondition.StabilityCondition.GroupAction.TriEquiv

variable {B : Type*} (T : B → TriEquiv C)

theorem ofWord_append_functor_obj (ω ω' : List B) (X : C) :
    (ofWord T (ω ++ ω')).e.functor.obj X =
      (ofWord T ω).e.functor.obj ((ofWord T ω').e.functor.obj X) := by
  induction ω with
  | nil => rfl
  | cons i ω ih => exact congrArg (T i).e.functor.obj ih

theorem ofWord_append_inverse_obj (ω ω' : List B) (X : C) :
    (ofWord T (ω ++ ω')).e.inverse.obj X =
      (ofWord T ω').e.inverse.obj ((ofWord T ω).e.inverse.obj X) := by
  induction ω generalizing X with
  | nil => rfl
  | cons i ω ih => exact ih ((T i).e.inverse.obj X)

theorem ofSignedWord_map_true (ω : List B) :
    ofSignedWord T (ω.map fun i => (i, true)) = ofWord T ω := by
  induction ω with
  | nil => rfl
  | cons i ω ih => rw [List.map_cons, ofSignedWord, ih]; rfl

end WeakStabilityCondition.StabilityCondition.GroupAction.TriEquiv

/-! ### The hypotheses -/

open WeylGallery BilinearForm

variable (C) in
/-- **Hypotheses for Weyl-indexed galleries of tilts.** A t-structure `t` with heart `A`; a
configuration of type `M` of spherical objects `S_i` with twists `T_i`, under the conjugation
formula; a class map along which `T_i` acts by the reflection in `cl(S_i)`, with a cone of
positive classes; and three statements about hearts and their tilts: the simple tilt, tilt
composition, and `C` Serre in `A`. See the module docstring for which fields have no geometric
instance. -/
structure WeylGalleryHypotheses {B : Type*} (M : CoxeterMatrix B) (Λ : Type*)
    [AddCommGroup Λ] where
  /-- The t-structure; its heart is the starting heart `A`. -/
  t : TStructure C
  /-- Twists as a conjugation-equivariant map (Seidel–Thomas, Lemma 2.11). -/
  twists : TwistConjugation C
  /-- The spherical objects `S_i` and their twists `T_i`. -/
  conf : twists.Configuration M
  /-- The class map, to `K₀` or the numerical lattice. -/
  cl : C → Λ
  cl_iso : ∀ {X Y : C}, (X ≅ Y) → cl X = cl Y
  /-- Additivity on distinguished triangles. -/
  cl_triangle : ∀ {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : X₃ ⟶ X₁⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C → cl X₂ = cl X₁ + cl X₃
  /-- The pairing on classes, in the Mukai sign: minus the Euler form. -/
  form : LinearMap.BilinForm ℤ Λ
  form_symm : ∀ x y, form x y = form y x
  form_self : ∀ i, form (cl (conf.obj i)) (cl (conf.obj i)) = -2
  /-- The twist `T_i` acts on classes by the reflection in `cl(S_i)`. -/
  cl_twist : ∀ i X, cl ((conf.T i).e.functor.obj X) = reflect form (cl (conf.obj i)) (cl X)
  /-- **The sign of the class**: a cone of positive classes. -/
  cone : AddSubsemigroup Λ
  cl_mem_cone : ∀ X, t.heart X → ¬IsZero X → cl X ∈ cone
  neg_not_mem_cone : ∀ v ∈ cone, -v ∉ cone
  /-- The `S_i` are simple in `A`. -/
  isSimpleIn_obj : ∀ i, IsSimpleIn t.heart (conf.obj i)
  /-- **The simple tilt**: `T_i A` is the lower tilt of `A` at `Filt(S_i)`. For the
  finite-length hearts of Kleinian singularities this is in the proof of Bridgeland, *Stability
  conditions and Kleinian singularities*, Int. Math. Res. Not. IMRN 2009, Lemma 3.5, and for the
  `2`-Calabi–Yau categories of preprojective algebras in the proof of Ikeda, arXiv:1402.1392,
  Lemma 4.11. -/
  image_heart_eq_lowerTilt : ∀ i,
    image (conf.T i) t.heart = lowerTilt t.heart (filtration (isoClass (conf.obj i)))
  /-- **Tilt composition**: tilting the lower tilt of `A` at `T` at a simple object `X` of
  `T^⊥ ∩ A` is the lower tilt of `A` at `Filt(T ∪ {X})`, a torsion class. -/
  lowerTilt_lowerTilt_eq : ∀ T : ObjectProperty C, IsTorsionClass t.heart T →
    ∀ X, IsSimpleIn (lowerTilt t.heart T) X → (t.heart ⊓ T.rightOrthogonal) X →
      IsTorsionClass t.heart (filtration (T ⊔ isoClass X)) ∧
        lowerTilt (lowerTilt t.heart T) (filtration (isoClass X)) =
          lowerTilt t.heart (filtration (T ⊔ isoClass X))
  /-- The thick subcategory generated by the `S_i`, or any class containing them and stable
  under the twists. -/
  hull : ObjectProperty C
  hull_obj : ∀ i, hull (conf.obj i)
  hull_twist : ∀ i X, hull X → hull ((conf.T i).e.functor.obj X)
  /-- **`C` Serre in `A`**: the objects of `A` in the hull have a filtration by the `S_i`. -/
  heart_inf_hull_le : t.heart ⊓ hull ≤ filtration (ObjectProperty.ofObj conf.obj).isoClosure

namespace WeylGalleryHypotheses

variable {B : Type*} {M : CoxeterMatrix B} {Λ : Type*} [AddCommGroup Λ]
  (H : WeylGalleryHypotheses C M Λ)

/-- The simple roots `α_i = cl(S_i)`. -/
def root (i : B) : Λ := H.cl (H.conf.obj i)

/-- `F_ω = T_{i₁} ∘ ⋯ ∘ T_{i_k}`. -/
def F (ω : List B) : TriEquiv C := TriEquiv.ofWord H.conf.T ω

/-- The heart `F_ω A`. -/
def heartOf (ω : List B) : ObjectProperty C := image (H.F ω) H.t.heart

/-- `T_ω = A ∩ F_ω A[1]`. -/
def torsionOf (ω : List B) : ObjectProperty C := H.t.heart ⊓ (H.heartOf ω).shift (-1 : ℤ)

instance (ω : List B) : (H.heartOf ω).IsClosedUnderIsomorphisms := by
  unfold heartOf; infer_instance

theorem cl_of_isZero {X : C} (hX : IsZero X) : H.cl X = 0 := by
  have h := H.cl_triangle _ _ _ (contractible_distinguished (0 : C))
  have h0 : H.cl (0 : C) = 0 := by simpa using h
  rw [H.cl_iso (hX.iso (isZero_zero C)), h0]

theorem cl_shift_one (X : C) : H.cl (X⟦(1 : ℤ)⟧) = -H.cl X := by
  have h := H.cl_triangle _ _ _ (contractible_distinguished₂ X)
  rw [H.cl_of_isZero (isZero_zero C)] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem root_mem_cone (i : B) : H.root i ∈ H.cone :=
  H.cl_mem_cone _ (H.isSimpleIn_obj i).1 (H.isSimpleIn_obj i).2.1

theorem positiveCone_le_cone : positiveCone H.root ≤ H.cone :=
  AddSubsemigroup.closure_le.2 (Set.range_subset_iff.2 H.root_mem_cone)

theorem form_root_self (i : B) : H.form (H.root i) (H.root i) = -2 := H.form_self i

/-- `F_ω` acts on classes by `ω`. -/
theorem cl_F (ω : List B) (X : C) :
    H.cl ((H.F ω).e.functor.obj X) = reflectWord H.form H.root ω (H.cl X) := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    rw [reflectWord_cons_apply, ← ih]
    exact H.cl_twist i _

theorem F_nil : H.F [] = TriEquiv.id := rfl

theorem heartOf_nil : H.heartOf [] = H.t.heart := rfl

theorem heartOf_append (ω ω' : List B) :
    H.heartOf (ω ++ ω') = image (H.F ω) (H.heartOf ω') := by
  ext X
  exact iff_of_eq (congrArg H.t.heart (TriEquiv.ofWord_append_inverse_obj _ _ _ X))

theorem F_append_obj (ω ω' : List B) (X : C) :
    (H.F (ω ++ ω')).e.functor.obj X = (H.F ω).e.functor.obj ((H.F ω').e.functor.obj X) :=
  TriEquiv.ofWord_append_functor_obj _ _ _ _

theorem hull_F (ω : List B) {X : C} (hX : H.hull X) : H.hull ((H.F ω).e.functor.obj X) := by
  induction ω with
  | nil => exact hX
  | cons i ω ih => exact H.hull_twist i _ ih

/-- `F_ω S_i` is simple in `F_ω A`. -/
theorem isSimpleIn_heartOf (ω : List B) (i : B) :
    IsSimpleIn (H.heartOf ω) ((H.F ω).e.functor.obj (H.conf.obj i)) :=
  (isSimpleIn_image_iff _ _ _).2 (H.isSimpleIn_obj i)

/-- **The sign of the class**: a simple object of the lower tilt of `A` at `T` with positive
class lies in `A ∩ T^⊥`. -/
theorem mem_of_cl_mem_cone {T : ObjectProperty C} (hT : IsTorsionClass H.t.heart T) {X : C}
    (hX : IsSimpleIn (lowerTilt H.t.heart T) X) (hcl : H.cl X ∈ H.cone) :
    (H.t.heart ⊓ T.rightOrthogonal) X := by
  rcases hX.lowerTilt_cases (fun _ h => heart_of_isZero H.t h) hT.prop_of_isZero with h | h
  · exact h
  obtain ⟨Z, hZ, hZ0, ⟨e⟩⟩ := h
  have h1 : H.cl (Z⟦(1 : ℤ)⟧) ∈ H.cone :=
    H.cl_mem_cone _ (hT.le _ hZ) fun h => hZ0 ((isZero_shift_iff 1).1 h)
  rw [H.cl_shift_one, ← H.cl_iso e] at h1
  exact absurd h1 (H.neg_not_mem_cone _ hcl)

/-- **One step of the gallery.** If `F_ω A` is the lower tilt of `A` at a torsion class `T` and
`ω(α_i)` is a positive root, then `F_ω S_i` lies in `A ∩ T^⊥`, and `F_{ω i} A` is the lower tilt
of `A` at the torsion class `Filt(T ∪ {F_ω S_i})`. -/
theorem gallery_step {ω : List B} {T : ObjectProperty C} (hT : IsTorsionClass H.t.heart T)
    (hω : H.heartOf ω = lowerTilt H.t.heart T) {i : B}
    (hpos : reflectWord H.form H.root ω (H.root i) ∈ positiveCone H.root) :
    (H.t.heart ⊓ T.rightOrthogonal) ((H.F ω).e.functor.obj (H.conf.obj i)) ∧
      IsTorsionClass H.t.heart
        (filtration (T ⊔ isoClass ((H.F ω).e.functor.obj (H.conf.obj i)))) ∧
      H.heartOf (ω ++ [i]) =
        lowerTilt H.t.heart (filtration (T ⊔ isoClass ((H.F ω).e.functor.obj (H.conf.obj i)))) := by
  have := hT.isClosedUnderIsomorphisms
  have hs : IsSimpleIn (lowerTilt H.t.heart T) ((H.F ω).e.functor.obj (H.conf.obj i)) := by
    rw [← hω]; exact H.isSimpleIn_heartOf ω i
  have hcl : H.cl ((H.F ω).e.functor.obj (H.conf.obj i)) ∈ H.cone := by
    rw [H.cl_F]; exact H.positiveCone_le_cone hpos
  have hmem := H.mem_of_cl_mem_cone hT hs hcl
  obtain ⟨hT', heq⟩ := H.lowerTilt_lowerTilt_eq T hT _ hs hmem
  refine ⟨hmem, hT', ?_⟩
  rw [H.heartOf_append, ← heq, ← hω, heartOf,
    show image (H.F [i]) H.t.heart = image (H.conf.T i) H.t.heart from rfl,
    H.image_heart_eq_lowerTilt, image_lowerTilt, image_filtration, image_isoClass]
  rfl

/-- **The gallery theorem**: for a root-positive word `ω`, `T_ω = A ∩ F_ω A[1]` is a torsion
class of `A` and `F_ω A = ⟨T_ω^⊥ ∩ A, T_ω[-1]⟩`. -/
theorem isTorsionClass_torsionOf_and_heartOf_eq {ω : List B}
    (hω : IsRootPositive H.form H.root ω) :
    IsTorsionClass H.t.heart (H.torsionOf ω) ∧
      H.heartOf ω = lowerTilt H.t.heart (H.torsionOf ω) := by
  induction ω using List.reverseRecOn with
  | nil =>
    have h : H.torsionOf [] = IsZero := by
      have h0 := inf_shift_lowerTilt H.t (isTorsionClass_isZero H.t)
      rw [lowerTilt_isZero] at h0
      rw [torsionOf, heartOf_nil, h0]
    rw [h, heartOf_nil, lowerTilt_isZero]
    exact ⟨isTorsionClass_isZero H.t, rfl⟩
  | append_singleton ω i ih =>
    obtain ⟨hω', hpos⟩ := (isRootPositive_append_singleton _ _).1 hω
    obtain ⟨hT, heq⟩ := ih hω'
    obtain ⟨-, hT', heq'⟩ := H.gallery_step hT heq hpos
    have h : H.torsionOf (ω ++ [i]) =
        filtration (H.torsionOf ω ⊔ isoClass ((H.F ω).e.functor.obj (H.conf.obj i))) := by
      rw [torsionOf, heq']
      exact inf_shift_lowerTilt H.t hT'
    rw [h]
    exact ⟨hT', heq'⟩

theorem isTorsionClass_torsionOf {ω : List B} (hω : IsRootPositive H.form H.root ω) :
    IsTorsionClass H.t.heart (H.torsionOf ω) :=
  (H.isTorsionClass_torsionOf_and_heartOf_eq hω).1

/-- `F_ω A = ⟨T_ω^⊥ ∩ A, T_ω[-1]⟩`. -/
theorem heartOf_eq_lowerTilt {ω : List B} (hω : IsRootPositive H.form H.root ω) :
    H.heartOf ω = lowerTilt H.t.heart (H.torsionOf ω) :=
  (H.isTorsionClass_torsionOf_and_heartOf_eq hω).2

/-- If `ω i` is root-positive, `F_ω S_i` is simple in `F_ω A`, of class `ω(α_i) > 0`, and lies
in `A ∩ T_ω^⊥`. -/
theorem F_obj_mem {ω : List B} {i : B} (hω : IsRootPositive H.form H.root (ω ++ [i])) :
    IsSimpleIn (H.heartOf ω) ((H.F ω).e.functor.obj (H.conf.obj i)) ∧
      H.cl ((H.F ω).e.functor.obj (H.conf.obj i)) = reflectWord H.form H.root ω (H.root i) ∧
      (H.t.heart ⊓ (H.torsionOf ω).rightOrthogonal)
        ((H.F ω).e.functor.obj (H.conf.obj i)) := by
  obtain ⟨hω', hpos⟩ := (isRootPositive_append_singleton _ _).1 hω
  obtain ⟨hT, heq⟩ := H.isTorsionClass_torsionOf_and_heartOf_eq hω'
  exact ⟨H.isSimpleIn_heartOf ω i, H.cl_F ω _, (H.gallery_step hT heq hpos).1⟩

/-- `T_{ω i} = Filt(T_ω ∪ {F_ω S_i})`. -/
theorem torsionOf_append_singleton {ω : List B} {i : B}
    (hω : IsRootPositive H.form H.root (ω ++ [i])) :
    H.torsionOf (ω ++ [i]) =
      filtration (H.torsionOf ω ⊔ isoClass ((H.F ω).e.functor.obj (H.conf.obj i))) := by
  obtain ⟨hω', hpos⟩ := (isRootPositive_append_singleton _ _).1 hω
  obtain ⟨hT, heq⟩ := H.isTorsionClass_torsionOf_and_heartOf_eq hω'
  obtain ⟨-, hT', heq'⟩ := H.gallery_step hT heq hpos
  rw [torsionOf, heq']
  exact inf_shift_lowerTilt H.t hT'

/-! ### The longest element -/

theorem cl_zero' (X : C) (hX : IsZero X) : H.cl X = 0 := H.cl_of_isZero hX

/-- `T_i S_i ≅ S_i[-1]`, from the simple tilt and the sign of the class. -/
theorem twist_obj_self [Fintype B] [DecidableEq B] (hα : LinearIndependent ℤ H.root) (i : B) :
    Nonempty ((H.conf.T i).e.functor.obj (H.conf.obj i) ≅ (H.conf.obj i)⟦(-1 : ℤ)⟧) := by
  have hs : IsSimpleIn (lowerTilt H.t.heart (filtration (isoClass (H.conf.obj i))))
      ((H.conf.T i).e.functor.obj (H.conf.obj i)) := by
    rw [← H.image_heart_eq_lowerTilt]
    exact (isSimpleIn_image_iff _ _ _).2 (H.isSimpleIn_obj i)
  have hcl : H.cl ((H.conf.T i).e.functor.obj (H.conf.obj i)) = -H.root i := by
    rw [H.cl_twist, ← root, reflect_self _ _ (H.form_root_self i)]
  rcases hs.lowerTilt_cases (fun _ h => heart_of_isZero H.t h) (fun _ h => filtration_of_isZero _ h)
    with h | ⟨Z, hZ, -, ⟨e⟩⟩
  · exfalso
    have := H.cl_mem_cone _ h.1 hs.2.1
    rw [hcl] at this
    exact H.neg_not_mem_cone _ (H.root_mem_cone i) this
  · have hZ' : filtration (ObjectProperty.ofObj H.conf.obj).isoClosure (Z⟦(1 : ℤ)⟧) :=
      filtration_mono (fun Y ⟨e'⟩ => ⟨_, ⟨i⟩, ⟨e'⟩⟩) _ hZ
    have hclZ : H.cl (Z⟦(1 : ℤ)⟧) = H.cl (H.conf.obj i) := by
      rw [H.cl_shift_one, ← H.cl_iso e, hcl, neg_neg, root]
    obtain ⟨e'⟩ := nonempty_iso_of_cl_eq H.conf.obj H.cl H.cl_iso H.cl_triangle
      (fun _ h => H.cl_of_isZero h) hα hZ' hclZ
    exact ⟨e ≪≫ ((shiftFunctorCompIsoId C (1 : ℤ) (-1) (by norm_num)).app Z).symm ≪≫
      (shiftFunctor C (-1 : ℤ)).mapIso e'⟩

/-- **The last letter of a word.** If `u i` is root-positive and `u(α_i) = α_j`, then
`F_{u i} S_i ≅ S_j[-1]`. -/
theorem F_obj_iso_shift [Fintype B] [DecidableEq B] (hα : LinearIndependent ℤ H.root)
    {u : List B} {i j : B}
    (hω : IsRootPositive H.form H.root (u ++ [i]))
    (hu : reflectWord H.form H.root u (H.root i) = H.root j) :
    Nonempty ((H.F (u ++ [i])).e.functor.obj (H.conf.obj i) ≅ (H.conf.obj j)⟦(-1 : ℤ)⟧) := by
  obtain ⟨-, hcl, hmem⟩ := H.F_obj_mem hω
  have hX : filtration (ObjectProperty.ofObj H.conf.obj).isoClosure
      ((H.F u).e.functor.obj (H.conf.obj i)) :=
    H.heart_inf_hull_le _ ⟨hmem.1, H.hull_F u (H.hull_obj i)⟩
  obtain ⟨e⟩ := nonempty_iso_of_cl_eq H.conf.obj H.cl H.cl_iso H.cl_triangle
    (fun _ h => H.cl_of_isZero h) hα hX (hcl.trans hu)
  obtain ⟨e₁⟩ := H.twist_obj_self hα i
  rw [F_append_obj]
  exact ⟨(H.F u).e.functor.mapIso e₁ ≪≫
    ((H.F u).e.functor.commShiftIso (-1 : ℤ)).app (H.conf.obj i) ≪≫
    (shiftFunctor C (-1 : ℤ)).mapIso e⟩

/-- `u(α_i) = α_j` is `(u i)(α_i) = -α_j`. -/
theorem reflectWord_append_singleton_root (u : List B) (i : B) :
    reflectWord H.form H.root (u ++ [i]) (H.root i) =
      -reflectWord H.form H.root u (H.root i) := by
  rw [reflectWord_append_apply, reflectWord_cons_apply, reflectWord_nil, one_apply_eq_self,
    reflect_self _ _ (H.form_root_self i), map_neg]

/-- **Path independence**: words with the same image in the Artin group give the same heart. -/
theorem heartOf_eq_of_eq {ω ω' : List B}
    (h : CoxeterMatrix.ArtinGroup.ofSignedWord M (ω.map fun i => (i, true)) =
      CoxeterMatrix.ArtinGroup.ofSignedWord M (ω'.map fun i => (i, true))) :
    H.heartOf ω = H.heartOf ω' := by
  have := (TwistConjugation.nonempty_iso_of_eq H.conf h).1
  rw [TriEquiv.ofSignedWord_map_true, TriEquiv.ofSignedWord_map_true] at this
  exact image_congr this _

/-- **`F_{w₀} S_i ≅ S_{π i}[-1]`.** Let `ω₀` be a word and, for each `i`, `u i` a word such that
`u i ++ [i]` is root-positive, has the image of `ω₀` in the Artin group, and
`(u i)(α_i) = α_{π i}`; for a reduced word `ω₀` of the longest element `w₀` these are the
reduced words of `w₀` ending in `i`, and `π` is the diagram automorphism with
`w₀(α_i) = -α_{π i}`. Then `F_{ω₀} S_i ≅ S_{π i}[-1]` for every `i`. -/
theorem longest_obj_iso_shift [Fintype B] [DecidableEq B] (hα : LinearIndependent ℤ H.root)
    (ω₀ : List B) (π : B → B)
    (u : B → List B) (hpos : ∀ i, IsRootPositive H.form H.root (u i ++ [i]))
    (hart : ∀ i, CoxeterMatrix.ArtinGroup.ofSignedWord M ((u i ++ [i]).map fun k => (k, true)) =
      CoxeterMatrix.ArtinGroup.ofSignedWord M (ω₀.map fun k => (k, true)))
    (hu : ∀ i, reflectWord H.form H.root (u i) (H.root i) = H.root (π i)) (i : B) :
    Nonempty ((H.F ω₀).e.functor.obj (H.conf.obj i) ≅ (H.conf.obj (π i))⟦(-1 : ℤ)⟧) := by
  obtain ⟨e⟩ := H.F_obj_iso_shift hα (hpos i) (hu i)
  have h := (TwistConjugation.nonempty_iso_of_eq H.conf (hart i)).1
  rw [TriEquiv.ofSignedWord_map_true, TriEquiv.ofSignedWord_map_true] at h
  exact ⟨(h.some.app _).symm ≪≫ e⟩

/-! ### The Garside bound, the left edge, and twists along the new simple objects -/

/-- `F_ω A` lies in the window `[A[-1], A]` for a root-positive word. -/
theorem heartOf_le_window_one {ω : List B} (hω : IsRootPositive H.form H.root ω) :
    H.heartOf ω ≤ window H.t.heart 1 := by
  rw [H.heartOf_eq_lowerTilt hω]
  exact lowerTilt_le_window_one _ _ (H.isTorsionClass_torsionOf hω).le

/-- **The Garside bound.** If a word is the concatenation of `m` root-positive words, then
`F A` lies in the window `[A[-m], A]`. For `F = Δ^k x₁ ⋯ x_l`, with `Δ` the positive lift of
`w₀` and the `x_j` positive lifts of Weyl group elements, this is `A[-(k+l)] ≤ F A ≤ A`. -/
theorem heartOf_flatten_le_window [IsTriangulated C] (blocks : List (List B))
    (h : ∀ ω ∈ blocks, IsRootPositive H.form H.root ω) :
    H.heartOf blocks.flatten ≤ window H.t.heart blocks.length := by
  induction blocks with
  | nil => exact le_window_zero _
  | cons ω blocks ih =>
    rw [List.flatten_cons, H.heartOf_append, List.length_cons]
    refine (image_mono _ (ih fun ω' hω' => h ω' (List.mem_cons_of_mem _ hω'))).trans ?_
    rw [image_window]
    refine (filtration_mono fun X ⟨j, hj, hX⟩ => ⟨j, hj, ?_⟩).trans
      (window_window_le H.t.heart blocks.length)
    exact H.heartOf_le_window_one (h ω List.mem_cons_self) _ hX

/-- **The left edge, as the dual theorem**: `A` is the lower tilt of `F_ω⁻¹ A` at
`F_ω⁻¹ T_ω`. -/
theorem heart_eq_lowerTilt_image_symm {ω : List B} (hω : IsRootPositive H.form H.root ω) :
    H.t.heart = lowerTilt (image (H.F ω).symm H.t.heart)
      (image (H.F ω).symm (H.torsionOf ω)) := by
  have := (H.isTorsionClass_torsionOf hω).isClosedUnderIsomorphisms
  have h := congrArg (image (H.F ω).symm) (H.heartOf_eq_lowerTilt hω)
  rwa [heartOf, image_symm_image, image_lowerTilt] at h

/-- **Each step is the twist along the new simple object**: `τ(F_ω S_i) = [F_{ω i}] [F_ω]⁻¹`,
by the conjugation formula. -/
theorem twist_F_obj (ω : List B) (i : B) :
    H.twists.twist ((H.F ω).e.functor.obj (H.conf.obj i)) =
      AutQuot.mk (H.F (ω ++ [i])) * (AutQuot.mk (H.F ω))⁻¹ := by
  rw [H.twists.twist_conj _ _ (H.conf.isSpherical_obj i), ← H.conf.mk_T, F, F,
    AutQuot.mk_ofWord, AutQuot.mk_ofWord, List.map_append, List.prod_append, List.map_singleton,
    List.prod_singleton, Function.comp_apply]

/-- `F_{ω i} A = T_{F_ω S_i}(F_ω A)`: the image of `F_ω A` under any autoequivalence in the class
of the twist along `F_ω S_i` is `F_{ω i} A`. -/
theorem image_heartOf_of_twist (ω : List B) (i : B) {Φ : TriEquiv C}
    (hΦ : AutQuot.mk Φ = H.twists.twist ((H.F ω).e.functor.obj (H.conf.obj i))) :
    image Φ (H.heartOf ω) = H.heartOf (ω ++ [i]) := by
  rw [H.twist_F_obj, eq_mul_inv_iff_mul_eq] at hΦ
  have h : Nonempty (((H.F ω).comp Φ).e.functor ≅ (H.F (ω ++ [i])).e.functor) :=
    _root_.Quotient.exact hΦ
  rw [heartOf, ← image_comp]
  exact image_congr h _

end WeylGalleryHypotheses

end CategoryTheory.Triangulated
