/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.ObjectProperty.Coreflection
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Evaluation
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.FiltrationOperations

/-!
# Truncations of a slicing are coreflections

In a distinguished triangle `X → D → Y → X⟦1⟧` with `X` in a class `P`, the map `X → D` is a
coreflection of `D` into `P` (`ObjectProperty.IsCoreflection`) as soon as no object of `P` maps
nontrivially to `Y` or to `Y⟦-1⟧` (`Pretriangulated.isCoreflection_of_distTriang`). For a
slicing this gives:

* `Slicing.isCoreflection_geProp_of_top`: in the lemma "Evaluation of one phase", the top
  quotient `M → D` (with `M` of phases at least `t` and the cone of phases below `t`) is the
  coreflection of `D` into the objects of phases at least `t`, so it is the radical of `D` for
  that class; `Slicing.isoOfTop` is the uniqueness of `M` over `D` that this gives;
* `Slicing.exists_isCoreflection_gtProp`, `Slicing.isLeftAdjoint_ι_gtProp`: every object has a
  coreflection into the objects of phases above `t`, the first term of its HN filtration cut at
  `t`; the inclusion of that class is a left adjoint.

## Tags

slicing, stability condition, truncation, coreflection, evaluation
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- In a distinguished triangle `X → D → Y → X⟦1⟧` with `X` in `P`, the map `X → D` is a
coreflection of `D` into `P` when every object of `P` has only zero maps to `Y` and to
`Y⟦-1⟧`. -/
theorem Pretriangulated.isCoreflection_of_distTriang {P : ObjectProperty C} {X D Y : C}
    {f : X ⟶ D} {g : D ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (hX : P X) (hY : ∀ ⦃S : C⦄, P S → ∀ u : S ⟶ Y, u = 0)
    (hY' : ∀ ⦃S : C⦄, P S → ∀ u : S ⟶ Y⟦(-1 : ℤ)⟧, u = 0) : P.IsCoreflection f := by
  refine ⟨hX, fun S hS => ⟨fun f₁ f₂ w => ?_, fun u => ?_⟩⟩
  · have hx : (f₁ - f₂) ≫ f = 0 := by
      simp only at w
      rw [Preadditive.sub_comp, w, sub_self]
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ (Triangle.mk f g h).invRotate
      (inv_rot_of_distTriang _ hT) (f₁ - f₂) hx
    have hy0 : y = 0 := hY' hS y
    rw [hy0, zero_comp] at hy
    exact sub_eq_zero.mp hy
  · obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₂ (Triangle.mk f g h) hT u (hY hS _)
    exact ⟨v, hv.symm⟩

namespace Triangulated.Slicing

/-- **The evaluation lemma as a coreflection.** Let `M → D → C → M⟦1⟧` be distinguished, `M` of
phases at least `t` and `C` of phases below `t`. Then `M → D` is the coreflection of `D` into the
objects of phases at least `t`: `M` is the radical of `D` for that class. -/
theorem isCoreflection_geProp_of_top (s : Slicing C) {t : ℝ} {M D C' : C} {ι : M ⟶ D}
    {q : D ⟶ C'} {δ : C' ⟶ M⟦(1 : ℤ)⟧} (hT : Triangle.mk ι q δ ∈ distTriang C)
    (hM : s.geProp C t M) (hC : s.ltProp C t C') : (s.geProp C t).IsCoreflection ι :=
  ⟨hM, fun _ hS => s.comp_bijective_of_top hT hC hS⟩

/-- The top quotient of the evaluation lemma is unique over `D`: for two such triangles
`M → D → C` and `K → D → D'`, the isomorphism `K ≅ M` of coreflections commutes with the maps
to `D`. -/
def isoOfTop (s : Slicing C) {t : ℝ} {M D C' K D' : C} {ι : M ⟶ D} {q : D ⟶ C'}
    {δ : C' ⟶ M⟦(1 : ℤ)⟧} (hT : Triangle.mk ι q δ ∈ distTriang C) {κ : K ⟶ D} {p : D ⟶ D'}
    {ε : D' ⟶ K⟦(1 : ℤ)⟧} (hT' : Triangle.mk κ p ε ∈ distTriang C) (hM : s.geProp C t M)
    (hC : s.ltProp C t C') (hK : s.geProp C t K) (hD' : s.ltProp C t D') : K ≅ M :=
  (s.isCoreflection_geProp_of_top hT' hK hD').isoOfIsCoreflection
    (s.isCoreflection_geProp_of_top hT hM hC)

@[reassoc (attr := simp)]
theorem isoOfTop_hom_comp (s : Slicing C) {t : ℝ} {M D C' K D' : C} {ι : M ⟶ D} {q : D ⟶ C'}
    {δ : C' ⟶ M⟦(1 : ℤ)⟧} (hT : Triangle.mk ι q δ ∈ distTriang C) {κ : K ⟶ D} {p : D ⟶ D'}
    {ε : D' ⟶ K⟦(1 : ℤ)⟧} (hT' : Triangle.mk κ p ε ∈ distTriang C) (hM : s.geProp C t M)
    (hC : s.ltProp C t C') (hK : s.geProp C t K) (hD' : s.ltProp C t D') :
    (s.isoOfTop hT hT' hM hC hK hD').hom ≫ ι = κ :=
  ObjectProperty.IsCoreflection.isoOfIsCoreflection_hom_comp _ _

/-- Phases at most `t` stay at most `t` after a negative shift. -/
theorem leProp_shift_neg_one (s : Slicing C) {t : ℝ} {Y : C} (hY : s.leProp C t Y) :
    s.leProp C t (Y⟦(-1 : ℤ)⟧) :=
  s.leProp_mono C (show t + ((-1 : ℤ) : ℝ) ≤ t by push_cast; linarith) _
    (s.leProp_shift C t Y (-1) hY)

/-- **The truncation at a cutoff.** In a distinguished triangle `X → D → Y → X⟦1⟧` with `X` of
phases above `t` and `Y` of phases at most `t`, the map `X → D` is the coreflection of `D` into
the objects of phases above `t`. -/
theorem isCoreflection_gtProp_of_triangle (s : Slicing C) {t : ℝ} {X D Y : C} {f : X ⟶ D}
    {g : D ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (hX : s.gtProp C t X) (hY : s.leProp C t Y) : (s.gtProp C t).IsCoreflection f :=
  isCoreflection_of_distTriang hT hX (fun _ hS u => s.hom_eq_zero_of_gtProp_leProp hS hY u)
    (fun _ hS u => s.hom_eq_zero_of_gtProp_leProp hS (s.leProp_shift_neg_one hY) u)

/-- Every object has a coreflection into the objects of phases above `t`: the first term of its
HN filtration cut at `t`. -/
theorem exists_isCoreflection_gtProp [IsTriangulated C] (s : Slicing C) (t : ℝ) (D : C) :
    ∃ (X : C) (f : X ⟶ D), (s.gtProp C t).IsCoreflection f := by
  obtain ⟨F⟩ := s.hn_exists D
  obtain ⟨X, Y, GX, GY, f, g, h, hT, hGX, hGY, -, -⟩ := F.exists_split_at_cutoff C t
  have hX : s.gtProp C t X := by
    by_cases hn : 0 < GX.n
    · exact s.gtProp_of_hn C GX t hGX hn
    · exact Or.inl (GX.isZero_of_length_zero (by omega))
  have hY : s.leProp C t Y := by
    by_cases hn : 0 < GY.n
    · exact s.leProp_of_hn C GY t hGY hn
    · exact Or.inl (GY.isZero_of_length_zero (by omega))
  exact ⟨X, f, s.isCoreflection_gtProp_of_triangle hT hX hY⟩

/-- The objects of phases above `t` form a coreflective subcategory: its inclusion is a left
adjoint, whose right adjoint is the truncation. -/
theorem isLeftAdjoint_ι_gtProp [IsTriangulated C] (s : Slicing C) (t : ℝ) :
    (s.gtProp C t).ι.IsLeftAdjoint :=
  ObjectProperty.isLeftAdjoint_ι_iff.2 (s.exists_isCoreflection_gtProp t)

end Triangulated.Slicing

end CategoryTheory
