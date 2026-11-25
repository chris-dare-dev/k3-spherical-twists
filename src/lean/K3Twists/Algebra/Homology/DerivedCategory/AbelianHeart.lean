/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.ExtComparison.Heart
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# The standard heart of a derived category

For an abelian category `C`, the functor `singleFunctor C 0 : C ⥤ D(C)` (complexes concentrated in
degree zero) satisfies the heart-type fields `AbelianHeartHypotheses`
(`DerivedCategory.abelianHeartHypotheses_singleFunctor`):

* its essential image, the heart of the canonical t-structure, is closed under extensions
  (Mathlib's `TStructure.isLE₂`, `TStructure.isGE₂` and
  `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`);
* a short exact sequence gives a distinguished triangle (Mathlib's
  `ShortComplex.ShortExact.singleTriangle_distinguished`);
* a distinguished triangle of complexes concentrated in degree zero is a short exact sequence: the
  long exact homology sequence in degrees `-1`, `0`, `1`, where the outer terms vanish.

This is the instance of the heart-type fields from real objects; the abelian corollary of window
dévissage applies to every triangulated functor into `D(C)` whose window data are checked on
objects with simple images in `C`.

## Main results

* `DerivedCategory.shortExact_of_distinguished_singleFunctor`
* `DerivedCategory.abelianHeartHypotheses_singleFunctor`

## Tags

derived category, heart, t-structure, short exact sequence
-/

universe w v u

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A distinguished triangle `A₁ → A₂ → A₃ → A₁⟦1⟧` of complexes concentrated in degree zero comes
from a short exact sequence. -/
theorem shortExact_of_distinguished_singleFunctor (S : ShortComplex C)
    (δ : (singleFunctor C 0).obj S.X₃ ⟶ ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((singleFunctor C 0).map S.f) ((singleFunctor C 0).map S.g) δ ∈
      distTriang _) :
    S.ShortExact := by
  let E := singleFunctorCompHomologyFunctorIso C 0
  have nat : ∀ {X Y : C} (f : X ⟶ Y),
      f = E.inv.app X ≫ (homologyFunctor C 0).map ((singleFunctor C 0).map f) ≫ E.hom.app Y := by
    intro X Y f
    have := E.hom.naturality f
    dsimp at this
    rw [this, Iso.inv_hom_id_app_assoc]
  have hexact := HomologySequence.exact₂ _ hT 0
  have hmono : Mono ((homologyFunctor C 0).map ((singleFunctor C 0).map S.f)) :=
    (HomologySequence.mono_homologyMap_mor₁_iff _ hT (-1) 0).2
      ((isZero_of_isGE ((singleFunctor C 0).obj S.X₃) 0 (-1) (by norm_num)).eq_of_src _ _)
  have hepi : Epi ((homologyFunctor C 0).map ((singleFunctor C 0).map S.g)) :=
    (HomologySequence.epi_homologyMap_mor₂_iff _ hT 0 1).2
      ((isZero_of_isLE ((singleFunctor C 0).obj S.X₁) 0 1 (by norm_num)).eq_of_tgt _ _)
  refine .mk' (ShortComplex.exact_of_iso ?_ hexact) ?_ ?_
  · exact ShortComplex.isoMk (E.app S.X₁) (E.app S.X₂) (E.app S.X₃)
      (by simpa using (E.hom.naturality S.f).symm) (by simpa using (E.hom.naturality S.g).symm)
  · rw [nat S.f]
    infer_instance
  · rw [nat S.g]
    infer_instance

variable (C) in
/-- **The heart-type fields for the standard heart** `C ⥤ D(C)`. -/
theorem abelianHeartHypotheses_singleFunctor :
    Triangulated.AbelianHeartHypotheses (singleFunctor C 0) where
  ext_mem_essImage T hT h₁ h₃ := by
    obtain ⟨A₁, ⟨e₁⟩⟩ := h₁
    obtain ⟨A₃, ⟨e₃⟩⟩ := h₃
    have hle₁ : TStructure.t.IsLE T.obj₁ 0 := TStructure.t.isLE_of_iso e₁ 0
    have hle₃ : TStructure.t.IsLE T.obj₃ 0 := TStructure.t.isLE_of_iso e₃ 0
    have hge₁ : TStructure.t.IsGE T.obj₁ 0 := TStructure.t.isGE_of_iso e₁ 0
    have hge₃ : TStructure.t.IsGE T.obj₃ 0 := TStructure.t.isGE_of_iso e₃ 0
    have : TStructure.t.IsLE T.obj₂ 0 := TStructure.t.isLE₂ T hT 0 hle₁ hle₃
    have : TStructure.t.IsGE T.obj₂ 0 := TStructure.t.isGE₂ T hT 0 hge₁ hge₃
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₂ 0
    exact ⟨Y, ⟨e.symm⟩⟩
  distinguished_of_shortExact S hS := ⟨hS.singleδ, hS.singleTriangle_distinguished⟩
  shortExact_of_distinguished S δ hT := shortExact_of_distinguished_singleFunctor S δ hT

end DerivedCategory
