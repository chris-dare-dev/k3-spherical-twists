/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Abelian.SerreClass.ExtensionClosure
import K3Twists.CategoryTheory.Triangulated.ExtComparison

/-!
# Window dévissage into a heart

Let `ι : H ⥤ D` be the inclusion of an abelian category into a pretriangulated category with the
properties of the heart of a t-structure that are used here (`AbelianHeartHypotheses`):

* the essential image of `ι` is closed under extensions;
* a short exact sequence `0 → A₁ → A₂ → A₃ → 0` of `H` extends to a distinguished triangle
  `ι A₁ → ι A₂ → ι A₃ → (ι A₁)⟦1⟧`;
* conversely, a distinguished triangle `ι A₁ → ι A₂ → ι A₃ → (ι A₁)⟦1⟧` comes from a short exact
  sequence.

These hold for the heart of every t-structure (Beilinson–Bernstein–Deligne, *Faisceaux pervers*,
1.2.5–1.2.6 and 1.3.6: the heart is an admissible abelian subcategory); Mathlib does not yet prove
that hearts are abelian, so here they are fields. `DerivedCategory/AbelianHeart.lean` builds an
instance for the standard heart `A ⥤ D(A)`.

## The abelian corollary

If every object of a family `𝒬` of objects of `D` is isomorphic to `ι A` for a simple object
`A` of `H`, then the objects `A` with `ι A` in the extension closure of `𝒬` form a **Serre class**
in `H` (`AbelianHeartHypotheses.isSerreClass_extensionClosure`): they are the objects with a
finite filtration whose subquotients are among those simple objects, and that class is closed
under subobjects, quotients and extensions.

Applied to a triangulated functor `F : C ⥤ D` with window data on a family `𝒮` whose images are
simple in `H`, with `a ≤ 0 < 1 ≤ b`:

* the essential image of `F` on the extension closure `𝒮̄` is a Serre subcategory of `H`
  (`AbelianHeartHypotheses.isSerreClass_image`);
* the first map of a distinguished triangle of `𝒮̄` is sent to a monomorphism of `H`
  (`AbelianHeartHypotheses.mono_of_distinguished`), and every subobject of `F X`, `X ∈ 𝒮̄`, is
  the image of the first map of such a triangle
  (`AbelianHeartHypotheses.exists_distinguished_of_mono`): the admissible subobjects of `X` in
  the exact category `𝒮̄` correspond to the subobjects of `F X` in `H`.

## What the corollary does not say

The correspondence is with subobjects in the **target** heart. It is not a statement about the
subobjects of `X` in a heart of the source. For `F = RΓ : D^b(ℙ¹) → D^b(vect)` and `𝒮 = {𝒪}`,
`F_n` is bijective on `Hom(𝒪, 𝒪⟦n⟧) = H^n(ℙ¹, 𝒪)` for every `n` and `F 𝒪 = k` is simple, so `F`
is fully faithful on `𝒮̄ = {𝒪^m}` and the admissible subobjects of `𝒪^m` are the subspaces of
`k^m`; but in the heart of coherent sheaves `𝒪` has the subobjects `𝒪(-d)`, `d ≥ 1`, which are not
in `𝒮̄`.

## Main definitions

* `CategoryTheory.Triangulated.AbelianHeartHypotheses`: the heart-type fields.

## Main results

* `AbelianHeartHypotheses.shortExact_of_iso`: a distinguished triangle with vertices in the image
  of `ι` is a short exact sequence of `H`.
* `AbelianHeartHypotheses.isSerreClass_extensionClosure`,
  `AbelianHeartHypotheses.isSerreClass_image`: the Serre property.
* `AbelianHeartHypotheses.mono_of_distinguished`,
  `AbelianHeartHypotheses.exists_distinguished_of_mono`: admissible subobjects and subobjects.

## Tags

window dévissage, heart, Serre class, admissible subobject
-/

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Limits Pretriangulated ZeroObject

namespace CategoryTheory.Triangulated

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {H : Type u₃} [Category.{v₃} H] [Abelian H]

/-- **Heart-type fields** for a functor `ι : H ⥤ D` from an abelian category: the properties of
the inclusion of the heart of a t-structure used by the abelian corollary of window dévissage
(Beilinson–Bernstein–Deligne, *Faisceaux pervers*, 1.2.5–1.2.6, 1.3.6). -/
structure AbelianHeartHypotheses (ι : H ⥤ D) [ι.Full] [ι.Faithful] [ι.Additive] : Prop where
  /-- The essential image is closed under extensions. -/
  ext_mem_essImage (T : Triangle D) : T ∈ distTriang D → ι.essImage T.obj₁ → ι.essImage T.obj₃ →
    ι.essImage T.obj₂
  /-- A short exact sequence extends to a distinguished triangle. -/
  distinguished_of_shortExact (S : ShortComplex H) : S.ShortExact →
    ∃ δ : ι.obj S.X₃ ⟶ (ι.obj S.X₁)⟦(1 : ℤ)⟧, Triangle.mk (ι.map S.f) (ι.map S.g) δ ∈ distTriang D
  /-- A distinguished triangle with vertices in the image comes from a short exact sequence. -/
  shortExact_of_distinguished (S : ShortComplex H) (δ : ι.obj S.X₃ ⟶ (ι.obj S.X₁)⟦(1 : ℤ)⟧) :
    Triangle.mk (ι.map S.f) (ι.map S.g) δ ∈ distTriang D → S.ShortExact

namespace AbelianHeartHypotheses

variable {ι : H ⥤ D} [ι.Full] [ι.Faithful] [ι.Additive] (h : AbelianHeartHypotheses ι)

omit [Preadditive D] [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [ι.Full] [ι.Additive] in
private theorem isZero_of_isZero_obj {A : H} (hA : IsZero (ι.obj A)) : IsZero A := by
  rw [IsZero.iff_id_eq_zero]
  exact ι.map_injective (hA.eq_of_src _ _)

include h

/-- The extension closure of a family of objects of the image stays in the image. -/
theorem extensionClosure_le_essImage {Q : ObjectProperty D} (hQ : Q ≤ ι.essImage) :
    Q.extensionClosure ≤ ι.essImage := by
  intro Y hY
  induction hY with
  | of_prop hY => exact hQ _ hY
  | of_isZero hY =>
    exact ι.essImage.prop_of_iso ((ι.map_isZero (isZero_zero H)).iso hY) (ι.obj_mem_essImage 0)
  | ext T hT _ _ h₁ h₃ => exact h.ext_mem_essImage T hT h₁ h₃

/-- A distinguished triangle with vertices isomorphic to `ι A₁`, `ι A₂`, `ι A₃` is a short exact
sequence `0 → A₁ → A₂ → A₃ → 0` of `H`. -/
theorem shortExact_of_iso {T : Triangle D} (hT : T ∈ distTriang D) {A₁ A₂ A₃ : H}
    (e₁ : ι.obj A₁ ≅ T.obj₁) (e₂ : ι.obj A₂ ≅ T.obj₂) (e₃ : ι.obj A₃ ≅ T.obj₃) :
    (ShortComplex.mk (ι.preimage (e₁.hom ≫ T.mor₁ ≫ e₂.inv))
      (ι.preimage (e₂.hom ≫ T.mor₂ ≫ e₃.inv))
      (ι.map_injective (by simp [comp_distTriang_mor_zero₁₂_assoc _ hT]))).ShortExact := by
  refine h.shortExact_of_distinguished _ (e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧') ?_
  refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_)
  · simp
  · simp
  · simp [← Functor.map_comp]

/-- **The abelian corollary, Serre form.** If every object of `Q` is isomorphic to `ι A` for a
simple object `A` of `H`, the objects `A` with `ι A` in the extension closure of `Q` form a Serre
class of `H`. -/
theorem isSerreClass_extensionClosure {Q : ObjectProperty D}
    (hQ : ∀ Y, Q Y → ∃ A : H, Simple A ∧ Nonempty (ι.obj A ≅ Y)) :
    ObjectProperty.IsSerreClass (fun A : H ↦ Q.extensionClosure (ι.obj A)) := by
  let R : ObjectProperty H := fun A ↦ ∃ Y, Q Y ∧ Nonempty (ι.obj A ≅ Y)
  have hR : ∀ A, R A → Simple A := by
    rintro A ⟨Y, hY, ⟨e⟩⟩
    obtain ⟨A', hA', ⟨e'⟩⟩ := hQ Y hY
    exact Simple.of_iso (ι.preimageIso (e ≪≫ e'.symm))
  have hQι : Q ≤ ι.essImage := fun Y hY ↦ by
    obtain ⟨A, -, ⟨e⟩⟩ := hQ Y hY
    exact ⟨A, ⟨e⟩⟩
  have key : (fun A : H ↦ Q.extensionClosure (ι.obj A)) = R.abelianExtensionClosure := by
    funext A
    apply propext
    constructor
    · intro hA
      have gen : ∀ Y, Q.extensionClosure Y → ∀ A, Nonempty (ι.obj A ≅ Y) →
          R.abelianExtensionClosure A := by
        intro Y hY
        induction hY with
        | of_prop hY => rintro A ⟨e⟩; exact .of_prop ⟨_, hY, ⟨e⟩⟩
        | of_isZero hY => rintro A ⟨e⟩; exact .of_isZero (isZero_of_isZero_obj (hY.of_iso e))
        | ext T hT h₁ h₃ ih₁ ih₃ =>
          rintro A ⟨e₂⟩
          obtain ⟨A₁, ⟨e₁⟩⟩ := h.extensionClosure_le_essImage hQι _ h₁
          obtain ⟨A₃, ⟨e₃⟩⟩ := h.extensionClosure_le_essImage hQι _ h₃
          exact .ext _ (h.shortExact_of_iso hT e₁ e₂ e₃) (ih₁ A₁ ⟨e₁⟩) (ih₃ A₃ ⟨e₃⟩)
      exact gen _ hA A ⟨Iso.refl _⟩
    · intro hA
      induction hA with
      | of_prop hA =>
        obtain ⟨Y, hY, ⟨e⟩⟩ := hA
        exact Q.extensionClosure.prop_of_iso e.symm (.of_prop hY)
      | of_isZero hA => exact .of_isZero (ι.map_isZero hA)
      | ext S hS _ _ h₁ h₃ =>
        obtain ⟨δ, hδ⟩ := h.distinguished_of_shortExact S hS
        exact .ext _ hδ h₁ h₃
  rw [key]
  exact ObjectProperty.isSerreClass_abelianExtensionClosure hR

section Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {F : C ⥤ D} [F.CommShift ℤ] [F.IsTriangulated] {P : ObjectProperty C} {a b : ℤ}

/-- **The abelian corollary.** If the window condition holds on `P` with `a ≤ 2` and `1 ≤ b`, and
every `F S`, `S ∈ P`, is isomorphic to `ι A` for a simple object `A` of `H`, then the objects of
`H` isomorphic to `F X` for some `X` in the extension closure of `P` form a Serre class. -/
theorem isSerreClass_image (ha : a ≤ 2) (hb : 1 ≤ b)
    (hW : ∀ ⦃S T : C⦄, P S → P T → F.IsExtWindow a b S T)
    (hP : ∀ S, P S → ∃ A : H, Simple A ∧ Nonempty (ι.obj A ≅ F.obj S)) :
    ObjectProperty.IsSerreClass
      (fun A : H ↦ ∃ X, P.extensionClosure X ∧ Nonempty (F.obj X ≅ ι.obj A)) := by
  have key : (fun A : H ↦ ∃ X, P.extensionClosure X ∧ Nonempty (F.obj X ≅ ι.obj A)) =
      fun A : H ↦ (P.map F).extensionClosure (ι.obj A) := by
    funext A
    rw [← F.map_extensionClosure_eq ha hb hW]
    rfl
  rw [key]
  refine h.isSerreClass_extensionClosure fun Y hY ↦ ?_
  obtain ⟨S, hS, ⟨e⟩⟩ := hY
  obtain ⟨A, hA, ⟨e'⟩⟩ := hP S hS
  exact ⟨A, hA, ⟨e' ≪≫ e⟩⟩

/-- **Admissible subobjects map to subobjects.** If `T₁ → T₂ → T₃ → T₁⟦1⟧` is distinguished with
`T₁`, `T₃` in the extension closure of `P`, and every `F S`, `S ∈ P`, is isomorphic to the image
of a simple object, then `F` of the first map is a monomorphism of `H`. -/
theorem mono_of_distinguished
    (hP : ∀ S, P S → ∃ A : H, Simple A ∧ Nonempty (ι.obj A ≅ F.obj S))
    {T : Triangle C} (hT : T ∈ distTriang C) (h₃ : P.extensionClosure T.obj₃) {A₁ A₂ : H}
    (e₁ : ι.obj A₁ ≅ F.obj T.obj₁) (e₂ : ι.obj A₂ ≅ F.obj T.obj₂) :
    Mono (ι.preimage (e₁.hom ≫ F.map T.mor₁ ≫ e₂.inv)) := by
  have hQι : P.map F ≤ ι.essImage := by
    rintro Y ⟨S, hS, ⟨e⟩⟩
    obtain ⟨A, -, ⟨e'⟩⟩ := hP S hS
    exact ⟨A, ⟨e' ≪≫ e⟩⟩
  obtain ⟨A₃, ⟨e₃⟩⟩ :=
    h.extensionClosure_le_essImage hQι _ (F.map_extensionClosure_le P _ ⟨_, h₃, ⟨Iso.refl _⟩⟩)
  exact (h.shortExact_of_iso (F.map_distinguished T hT) e₁ e₂ e₃).mono_f

/-- **Subobjects come from admissible subobjects.** With the window condition on `P` for
`a ≤ 0` and `1 ≤ b`, and every `F S`, `S ∈ P`, isomorphic to the image of a simple object: every
subobject `A ⊆ B` of `ι B ≅ F X`, `X` in the extension closure of `P`, is `F` of the first map of a
distinguished triangle `X₁ → X → X₃ → X₁⟦1⟧` with `X₁`, `X₃` in the extension closure. -/
theorem exists_distinguished_of_mono (ha : a ≤ 0) (hb : 1 ≤ b)
    (hW : ∀ ⦃S T : C⦄, P S → P T → F.IsExtWindow a b S T)
    (hP : ∀ S, P S → ∃ A : H, Simple A ∧ Nonempty (ι.obj A ≅ F.obj S))
    {X : C} (hX : P.extensionClosure X) {B : H} (e : ι.obj B ≅ F.obj X) {A : H} (i : A ⟶ B)
    [Mono i] :
    ∃ (X₁ X₃ : C) (f : X₁ ⟶ X) (g : X ⟶ X₃) (δ : X₃ ⟶ X₁⟦(1 : ℤ)⟧),
      Triangle.mk f g δ ∈ distTriang C ∧ P.extensionClosure X₁ ∧ P.extensionClosure X₃ ∧
        ∃ e₁ : ι.obj A ≅ F.obj X₁, e₁.hom ≫ F.map f = ι.map i ≫ e.hom := by
  have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    .mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)) inferInstance
      inferInstance
  have hSerre := h.isSerreClass_image (by lia) hb hW hP
  have hB : ∃ X', P.extensionClosure X' ∧ Nonempty (F.obj X' ≅ ι.obj B) := ⟨X, hX, ⟨e.symm⟩⟩
  obtain ⟨X₁, hX₁, ⟨e₁⟩⟩ := hSerre.prop_of_mono i hB
  obtain ⟨X₃, hX₃, ⟨e₃⟩⟩ := hSerre.prop_of_epi (cokernel.π i) hB
  obtain ⟨δ, hδ⟩ := h.distinguished_of_shortExact _ hS
  obtain ⟨u, hu⟩ := (F.isExtWindow_of_extensionClosure hW hX₃ hX₁).surjective 1 (by lia) hb
    (e₃.hom ≫ δ ≫ e₁.inv⟦(1 : ℤ)⟧')
  replace hu : F.map u ≫ (F.commShiftIso (1 : ℤ)).hom.app X₁ =
      e₃.hom ≫ δ ≫ e₁.inv⟦(1 : ℤ)⟧' := hu
  obtain ⟨X₂, f, g, hT⟩ := distinguished_cocone_triangle₂ u
  have hFT := F.map_distinguished _ hT
  have comm : (F.mapTriangle.obj (Triangle.mk f g u)).mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' = e₃.hom ≫ δ := by
    dsimp
    rw [hu]
    simp [← Functor.map_comp]
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism₂ _ _ hFT hδ e₁.hom e₃.hom comm
  let φ : F.mapTriangle.obj (Triangle.mk f g u) ⟶ Triangle.mk (ι.map i) (ι.map (cokernel.π i)) δ :=
    { hom₁ := e₁.hom, hom₂ := c, hom₃ := e₃.hom, comm₁ := hc₁, comm₂ := hc₂, comm₃ := comm }
  have : IsIso φ.hom₂ := isIso₂_of_isIso₁₃ φ hFT hδ (by dsimp [φ]; infer_instance)
    (by dsimp [φ]; infer_instance)
  have hX₂ : P.extensionClosure X₂ := .ext _ hT hX₁ hX₃
  let ψ := F.fullyFaithfulOfIsExtWindow ha (by lia) hW
  let θ : X₂ ≅ X := P.extensionClosure.ι.mapIso
    (ψ.preimageIso (X := ⟨X₂, hX₂⟩) (Y := ⟨X, hX⟩) (asIso φ.hom₂ ≪≫ e))
  have hθ : F.map θ.hom = c ≫ e.hom :=
    ψ.map_preimage (X := ⟨X₂, hX₂⟩) (Y := ⟨X, hX⟩) (φ.hom₂ ≫ e.hom)
  have hT' : Triangle.mk (f ≫ θ.hom) (θ.inv ≫ g) u ∈ distTriang C :=
    isomorphic_distinguished _ hT _
      (Triangle.isoMk _ _ (Iso.refl _) θ.symm (Iso.refl _) (by simp) (by simp) (by simp))
  refine ⟨X₁, X₃, f ≫ θ.hom, θ.inv ≫ g, u, hT', hX₁, hX₃, e₁.symm, ?_⟩
  have hc₁' : F.map f ≫ c = e₁.hom ≫ ι.map i := hc₁
  simp [hθ, reassoc_of% hc₁']

end Functor

end AbelianHeartHypotheses

end CategoryTheory.Triangulated
