/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# The heart of a t-structure is abelian

Let `t` be a t-structure on a triangulated category `C` and `H` a heart of `t`
(`TStructure.Heart`: a preadditive category with a fully faithful additive functor to `C` whose
essential image is `t.heart`). Then `H` is an abelian category, and its short exact sequences are
the distinguished triangles of `C` with vertices in the heart (Beilinson–Bernstein–Deligne,
*Faisceaux pervers*, Théorème 1.3.6).

The proof checks the two conditions of Mathlib's criterion `Triangulated.AbelianSubcategory.abelian`
(BBD, §1.2): negative Hom spaces between heart objects vanish, and every morphism of the heart is
admissible, because the cone of a morphism of the heart lies in degrees `[-1, 0]` and its
truncation triangle has vertices `K⟦1⟧` and `Q` with `K`, `Q` in the heart.

## Main results

* `TStructure.ιHeart_hom_shift_eq_zero`: `Hom(X, Y⟦n⟧) = 0` for `X`, `Y` in the heart and `n < 0`.
* `TStructure.admissibleMorphism_ιHeart`: every morphism of the heart is admissible.
* `TStructure.hasFiniteProducts_heart`: a heart has finite products (finite biproducts of `C`
  lie in the heart).
* `TStructure.heartAbelian`: the abelian structure on a heart; `heartFullSubcategoryAbelian` is
  the case of the full subcategory `t.heart.FullSubcategory`.
* `TStructure.shortExact_of_distTriang`, `TStructure.exists_distTriang_of_shortExact`: short
  exact sequences of the heart are exactly the distinguished triangles of `C` on heart objects.

Mathlib records the first statement as a TODO in `Mathlib/CategoryTheory/Triangulated/TStructure/
Heart.lean`; this file is written so that it can move there.

## Tags

t-structure, heart, abelian category, triangulated category
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v' u' v u

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)

/-- The zero object lies in the heart. -/
theorem heart_zero : t.heart (0 : C) :=
  (t.mem_heart_iff _).2 ⟨t.isLE_of_isZero (isZero_zero C) 0, t.isGE_of_isZero (isZero_zero C) 0⟩

/-- The heart is closed under binary biproducts. -/
theorem heart_biprod {X Y : C} (hX : t.heart X) (hY : t.heart Y) : t.heart (X ⊞ Y) := by
  rw [t.mem_heart_iff] at hX hY ⊢
  exact ⟨t.isLE₂ _ (binaryBiproductTriangle_distinguished X Y) 0 hX.1 hY.1,
    t.isGE₂ _ (binaryBiproductTriangle_distinguished X Y) 0 hX.2 hY.2⟩

variable {H : Type u'} [Category.{v'} H] [Preadditive H] [t.Heart H]

/-- **Negative Hom vanishing on the heart.** For `X`, `Y` in the heart and `n < 0`, every map
`X ⟶ Y⟦n⟧` is zero: `Y⟦n⟧` is `≥ -n > 0`. -/
theorem ιHeart_hom_shift_eq_zero ⦃X Y : H⦄ ⦃n : ℤ⦄
    (f : t.ιHeart.obj X ⟶ (t.ιHeart.obj Y)⟦n⟧) (hn : n < 0) : f = 0 := by
  have : t.IsGE ((t.ιHeart.obj Y)⟦n⟧) (-n) := t.isGE_shift _ 0 n (-n)
  exact t.zero f 0 (-n) (by lia)

/-- **Admissibility.** Complete `f : X₁ ⟶ X₂` of the heart to a distinguished triangle
`X₁ → X₂ → X₃ → X₁⟦1⟧`. Then `X₃` lies in degrees `[-1, 0]`, and its truncation triangle
`τ_{<0} X₃ → X₃ → τ_{≥0} X₃` has the form `K⟦1⟧ → X₃ → Q` with `K` and `Q` in the heart. -/
theorem admissibleMorphism_ιHeart :
    AbelianSubcategory.admissibleMorphism (t.ιHeart (H := H)) = ⊤ := by
  ext X₁ X₂ f₁
  simp only [MorphismProperty.top_apply, iff_true]
  intro X₃ f₂ f₃ hT
  have hX₃_le : t.IsLE X₃ 0 := by
    apply t.isLE₂ _ (rot_of_distTriang _ hT) 0
    · change t.IsLE (t.ιHeart.obj X₂) 0
      infer_instance
    · change t.IsLE ((t.ιHeart.obj X₁)⟦(1 : ℤ)⟧) 0
      have := t.isLE_shift (t.ιHeart.obj X₁) 0 1 (-1)
      exact t.isLE_of_le _ (-1) 0
  have hX₃_ge : t.IsGE X₃ (-1) := by
    apply t.isGE₂ _ (rot_of_distTriang _ hT) (-1)
    · change t.IsGE (t.ιHeart.obj X₂) (-1)
      exact t.isGE_of_ge _ (-1) 0
    · change t.IsGE ((t.ιHeart.obj X₁)⟦(1 : ℤ)⟧) (-1)
      exact t.isGE_shift _ 0 1 (-1)
  have hQ_le : t.IsLE ((t.truncGE 0).obj X₃) 0 := by
    apply t.isLE₂ _ (rot_of_distTriang _ (t.triangleLTGE_distinguished 0 X₃)) 0
    · exact hX₃_le
    · change t.IsLE (((t.truncLT 0).obj X₃)⟦(1 : ℤ)⟧) 0
      have : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
      have := t.isLE_shift ((t.truncLT 0).obj X₃) (-1) 1 (-2)
      exact t.isLE_of_le _ (-2) 0
  have hQ : t.heart ((t.truncGE 0).obj X₃) :=
    (t.mem_heart_iff _).mpr ⟨hQ_le, inferInstance⟩
  have hK_ge : t.IsGE ((t.truncLT 0).obj X₃) (-1) := by
    apply t.isGE₂ _ (inv_rot_of_distTriang _ (t.triangleLTGE_distinguished 0 X₃)) (-1)
    · change t.IsGE (((t.truncGE 0).obj X₃)⟦(-1 : ℤ)⟧) (-1)
      have : t.IsGE (((t.truncGE 0).obj X₃)⟦(-1 : ℤ)⟧) 1 := t.isGE_shift _ 0 (-1) 1
      exact t.isGE_of_ge _ (-1) 1
    · exact hX₃_ge
  have : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
  have hK : t.heart (((t.truncLT 0).obj X₃)⟦(-1 : ℤ)⟧) :=
    (t.mem_heart_iff _).mpr ⟨t.isLE_shift _ (-1) (-1) 0, t.isGE_shift _ (-1) (-1) 0⟩
  rw [← t.essImage_ιHeart H] at hQ hK
  obtain ⟨Q, ⟨eQ⟩⟩ := hQ
  obtain ⟨K, ⟨eK⟩⟩ := hK
  let e₁ : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ≅ (t.truncLT 0).obj X₃ :=
    (shiftFunctor C (1 : ℤ)).mapIso eK ≪≫
      (shiftEquiv C (1 : ℤ)).counitIso.app ((t.truncLT 0).obj X₃)
  let α : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ⟶ X₃ := e₁.hom ≫ (t.truncLTι 0).app X₃
  let β : X₃ ⟶ t.ιHeart.obj Q := (t.truncGEπ 0).app X₃ ≫ eQ.inv
  let γ : t.ιHeart.obj Q ⟶ (t.ιHeart.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ :=
    eQ.hom ≫ (t.truncGEδLT 0).app X₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.inv
  have hT₀ : Triangle.mk ((t.truncLTι 0).app X₃) ((t.truncGEπ 0).app X₃)
      ((t.truncGEδLT 0).app X₃) ∈ distTriang C :=
    t.triangleLTGE_distinguished 0 X₃
  exact ⟨K, Q, α, β, γ, isomorphic_distinguished _ hT₀ _
    (Triangle.isoMk _ _ e₁ (Iso.refl _) eQ (by simp [α]) (by simp [β]) (by simp [γ]))⟩

include t in
variable (H) in
/-- A heart has a zero object: the object over `0 : C`. -/
theorem exists_isZero_heart : ∃ Z : H, IsZero Z := by
  have h := t.heart_zero
  rw [← t.essImage_ιHeart H] at h
  obtain ⟨Z, ⟨e⟩⟩ := h
  refine ⟨Z, (IsZero.iff_id_eq_zero Z).2 (t.ιHeart.map_injective ?_)⟩
  rw [Functor.map_id, Functor.map_zero]
  exact ((isZero_zero C).of_iso e).eq_of_src _ _

include t in
variable (H) in
/-- A heart has binary biproducts: the biproduct in `C` of two heart objects lies in the heart,
and the biproduct maps lift through the fully faithful inclusion. -/
theorem hasBinaryBiproducts_heart : HasBinaryBiproducts H where
  has_binary_biproduct X Y := by
    have h := t.heart_biprod (t.ιHeart_obj_mem X) (t.ιHeart_obj_mem Y)
    rw [← t.essImage_ιHeart H] at h
    obtain ⟨B, ⟨e⟩⟩ := h
    let b : BinaryBicone X Y :=
      { pt := B
        fst := t.ιHeart.preimage (e.hom ≫ biprod.fst)
        snd := t.ιHeart.preimage (e.hom ≫ biprod.snd)
        inl := t.ιHeart.preimage (biprod.inl ≫ e.inv)
        inr := t.ιHeart.preimage (biprod.inr ≫ e.inv)
        inl_fst := t.ιHeart.map_injective (by simp)
        inl_snd := t.ιHeart.map_injective (by simp)
        inr_fst := t.ιHeart.map_injective (by simp)
        inr_snd := t.ιHeart.map_injective (by simp) }
    refine hasBinaryBiproduct_of_total b (t.ιHeart.map_injective ?_)
    simp only [b, Functor.map_add, Functor.map_comp, Functor.map_preimage, Functor.map_id]
    calc _ = e.hom ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ e.inv := by
          simp only [Preadditive.add_comp, Preadditive.comp_add, assoc]
      _ = 𝟙 _ := by rw [biprod.total, id_comp, e.hom_inv_id]

include t in
variable (H) in
/-- A heart has finite products. -/
theorem hasFiniteProducts_heart : HasFiniteProducts H := by
  obtain ⟨Z, hZ⟩ := t.exists_isZero_heart H
  have : HasZeroObject H := ⟨Z, hZ⟩
  have := t.hasBinaryBiproducts_heart H
  exact hasFiniteProducts_of_has_binary_and_terminal

variable (H) in
/-- **The heart of a t-structure is abelian** (Beilinson–Bernstein–Deligne, *Faisceaux pervers*,
Théorème 1.3.6), through Mathlib's criterion `Triangulated.AbelianSubcategory.abelian`. -/
@[instance_reducible]
def heartAbelian [IsTriangulated C] : Abelian H :=
  have := t.hasFiniteProducts_heart H
  AbelianSubcategory.abelian t.ιHeart (t.ιHeart_hom_shift_eq_zero) (t.admissibleMorphism_ιHeart)

/-- The abelian structure on the full subcategory `t.heart.FullSubcategory`. -/
@[instance_reducible]
def heartFullSubcategoryAbelian [IsTriangulated C] : Abelian t.heart.FullSubcategory :=
  letI := t.hasHeartFullSubcategory
  t.heartAbelian t.heart.FullSubcategory

/-- **Distinguished triangles on the heart are short exact.** If
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` is a distinguished triangle of `C` with `X₁`, `X₂`, `X₃` in the heart,
then `0 → X₁ → X₂ → X₃ → 0` is short exact in the heart. -/
theorem shortExact_of_distTriang [IsTriangulated C] {X₁ X₂ X₃ : H} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} {δ : t.ιHeart.obj X₃ ⟶ (t.ιHeart.obj X₁)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (t.ιHeart.map f) (t.ιHeart.map g) δ ∈ distTriang C) :
    (ShortComplex.mk f g (t.ιHeart.map_injective (by
      simpa using comp_distTriang_mor_zero₁₂ _ hT))).ShortExact := by
  letI := t.heartAbelian H
  have := t.hasFiniteProducts_heart H
  have hKer := AbelianSubcategory.isLimitKernelForkOfDistTriang
    (t.ιHeart_hom_shift_eq_zero (H := H)) f g δ hT
  have hCok := AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
    (t.ιHeart_hom_shift_eq_zero (H := H)) f g δ hT
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hKer)
    (Fork.IsLimit.mono hKer) (Cofork.IsColimit.epi hCok)

/-- **Short exact sequences of the heart are distinguished triangles.** A short exact sequence
`0 → X₁ → X₂ → X₃ → 0` of the heart extends to a distinguished triangle
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` of `C`. -/
theorem exists_distTriang_of_shortExact [IsTriangulated C] {S : ShortComplex H}
    (hS : S.ShortExact) :
    ∃ δ : t.ιHeart.obj S.X₃ ⟶ (t.ιHeart.obj S.X₁)⟦(1 : ℤ)⟧,
      Triangle.mk (t.ιHeart.map S.f) (t.ιHeart.map S.g) δ ∈ distTriang C := by
  letI := t.heartAbelian H
  have := t.hasFiniteProducts_heart H
  have := hS.epi_g
  obtain ⟨K, i, δ, hT⟩ := AbelianSubcategory.exists_distinguished_triangle_of_epi
    (t.ιHeart_hom_shift_eq_zero (H := H)) (t.admissibleMorphism_ιHeart (H := H)) S.g
  have hK := AbelianSubcategory.isLimitKernelForkOfDistTriang
    (t.ιHeart_hom_shift_eq_zero (H := H)) i S.g δ hT
  let e : S.X₁ ≅ K := IsLimit.conePointUniqueUpToIso hS.fIsKernel hK
  have he : e.hom ≫ i = S.f := IsLimit.conePointUniqueUpToIso_hom_comp hS.fIsKernel hK
    WalkingParallelPair.zero
  refine ⟨δ ≫ (t.ιHeart.map e.inv)⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _ ?_⟩
  refine Triangle.isoMk _ _ (t.ιHeart.mapIso e) (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_
  · simp [← Functor.map_comp, he]
  · simp [← Functor.map_comp]

end CategoryTheory.Triangulated.TStructure
