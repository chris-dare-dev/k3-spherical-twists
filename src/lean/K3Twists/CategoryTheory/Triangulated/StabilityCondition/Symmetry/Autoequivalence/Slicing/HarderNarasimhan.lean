/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Slicing.Quotient
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Uniqueness

/-!
# HN filtrations along an exact autoequivalence

The step "apply `V` to the resulting objects and arrows" of the tower algorithm in the draft
*Harder–Narasimhan towers of spherical twist words on a Picard-rank-one K3 surface*: an exact
autoequivalence `Φ` carries `P_σ(φ)` to `P_{Φσ}(φ)`, so it carries an HN filtration of `E` for a
slicing `s` to an HN filtration of `Φ E` for the transported slicing `Φ s`, with the same phases
and with factors `Φ` of the old factors (`TriEquiv.mapHN`, built on `HNFiltration.mapF`).

By uniqueness of HN filtrations (`HNFiltration.exists_iso_of_nonzero`) these are all of them:
every HN filtration of `Φ E` for `Φ s` whose factors are nonzero has the length and the phases of
the given one, and factors isomorphic to the images of its factors
(`TriEquiv.exists_iso_of_hnFiltration`). This is the sentence "By HN uniqueness these are exactly
the triangles required for `E_{j+1}`" in the proof of the tower theorem.

## Main definitions

* `TriEquiv.mapHN`: the HN filtration of `Φ E` for `Φ s` obtained by applying `Φ`.

## Main results

* `TriEquiv.isZero_functor_obj_iff`: `Φ` preserves and reflects zero objects.
* `TriEquiv.act_symm_act`: `Φ (Φ⁻¹ s) = s` for slicings; in the draft, `V (V⁻¹ η) = η`.
* `TriEquiv.exists_iso_of_hnFiltration`: every HN filtration of `Φ E` for `Φ s` with nonzero
  factors is the image of one of `E` for `s`, up to isomorphism of factors.

## Tags

stability condition, slicing, autoequivalence, Harder–Narasimhan filtration
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section mapF

variable {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {P : ℝ → ObjectProperty C} {P' : ℝ → ObjectProperty D} {E : C}
  (Fil : HNFiltration C P E) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
  (hP : ∀ φ X, P φ X → P' φ (F.obj X))

@[simp]
theorem HNFiltration.mapF_n : (Fil.mapF F hP).n = Fil.n := rfl

@[simp]
theorem HNFiltration.mapF_φ (i : Fin (Fil.mapF F hP).n) : (Fil.mapF F hP).φ i = Fil.φ i := rfl

@[simp]
theorem HNFiltration.mapF_factor (i : Fin (Fil.mapF F hP).n) :
    (Fil.mapF F hP).factor i = F.obj (Fil.factor i) := rfl

end mapF

namespace WeakStabilityCondition.StabilityCondition.GroupAction.TriEquiv

/-- Semistable objects of `s` go to semistable objects of `Φ s` of the same phase. -/
theorem act_P_functor_obj (Φ : TriEquiv C) (s : Slicing C) {φ : ℝ} {X : C} (h : s.P φ X) :
    (Φ.act s).P φ (Φ.e.functor.obj X) :=
  show s.P φ (Φ.e.inverse.obj (Φ.e.functor.obj X)) from (s.P φ).prop_of_iso (Φ.e.unitIso.app X) h

/-- The HN filtration of `Φ E` for `Φ s` obtained by applying `Φ` to an HN filtration of `E`
for `s`: same length, same phases, factors `Φ` of the old factors. -/
def mapHN (Φ : TriEquiv C) {s : Slicing C} {E : C} (F : HNFiltration C s.P E) :
    HNFiltration C (Φ.act s).P (Φ.e.functor.obj E) :=
  F.mapF Φ.e.functor (fun _ _ h => Φ.act_P_functor_obj s h)

@[simp]
theorem mapHN_n (Φ : TriEquiv C) {s : Slicing C} {E : C} (F : HNFiltration C s.P E) :
    (Φ.mapHN F).n = F.n := rfl

@[simp]
theorem mapHN_φ (Φ : TriEquiv C) {s : Slicing C} {E : C} (F : HNFiltration C s.P E)
    (i : Fin (Φ.mapHN F).n) : (Φ.mapHN F).φ i = F.φ i := rfl

@[simp]
theorem mapHN_factor (Φ : TriEquiv C) {s : Slicing C} {E : C} (F : HNFiltration C s.P E)
    (i : Fin (Φ.mapHN F).n) : (Φ.mapHN F).factor i = Φ.e.functor.obj (F.factor i) := rfl

/-- An exact autoequivalence preserves and reflects zero objects. -/
theorem isZero_functor_obj_iff (Φ : TriEquiv C) (X : C) :
    IsZero (Φ.e.functor.obj X) ↔ IsZero X :=
  ⟨fun h => (Φ.e.inverse.map_isZero h).of_iso (Φ.e.unitIso.app X),
    fun h => Φ.e.functor.map_isZero h⟩

/-- `Φ (Φ⁻¹ s) = s`: in the draft, `V (V⁻¹ η) = η`. -/
theorem act_symm_act (Φ : TriEquiv C) (s : Slicing C) : Φ.act (Φ.symm.act s) = s := by
  rw [← act_comp, act_congr (Ψ := TriEquiv.id) Φ.e.counitIso s, act_id]

/-- **HN filtrations along an exact autoequivalence.** Let `F` be an HN filtration of `E` for
`s` and `G` an HN filtration of `Φ E` for `Φ s`, both with nonzero factors. Then `G` has the
length and the phases of `F`, and its factors are the images under `Φ` of those of `F`, up to
isomorphism. -/
theorem exists_iso_of_hnFiltration (Φ : TriEquiv C) (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (G : HNFiltration C (Φ.act s).P (Φ.e.functor.obj E))
    (hF : ∀ i, ¬IsZero (F.factor i)) (hG : ∀ j, ¬IsZero (G.factor j)) :
    ∃ h : F.n = G.n, ∀ i : Fin F.n, F.φ i = G.φ (Fin.cast h i) ∧
      Nonempty (Φ.e.functor.obj (F.factor i) ≅ G.factor (Fin.cast h i)) := by
  obtain ⟨h, hi⟩ := (Φ.mapHN F).exists_iso_of_nonzero (Φ.act s) G
    (fun i => by
      rw [mapHN_factor, isZero_functor_obj_iff]
      exact hF i) hG
  exact ⟨h, fun i => hi i⟩

end WeakStabilityCondition.StabilityCondition.GroupAction.TriEquiv

end CategoryTheory.Triangulated
