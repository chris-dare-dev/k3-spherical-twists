/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Coreflection
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.IntrinsicPhases
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Orthogonality and extension closure of the phase cuts of a slicing

For a slicing `s` on a triangulated category and a real number `t`, the four phase cuts come in
two orthogonal pairs, `(P(≥ t), P(< t))` and `(P(> t), P(≤ t))`, and every object splits along
either pair (Bridgeland, arXiv:math/0212237, §3). This file proves the consequences of the split
that the cut criterion for cones uses:

* `Slicing.exists_split_geProp_ltProp`: every object `E` sits in a distinguished triangle
  `E_{≥t} → E → E_{<t} → E_{≥t}⟦1⟧` with `E_{≥t}` of phases at least `t` and `E_{<t}` of phases
  below `t`. It is the split at the cutoff (`HNFiltration.exists_split_at_cutoff`, which gives
  the `(> t', ≤ t')` split) moved to a cutoff `t' < t` below which no phase of a chosen HN
  filtration lies in `[t', t)`. `Slicing.exists_split_gtProp_leProp` restates the existing split
  without its interval hypothesis;
* `Slicing.exists_isCoreflection_geProp`: the first map of that triangle is the coreflection of
  `E` into the objects of phases at least `t`; the inclusion of that class is a left adjoint;
* `Slicing.geProp_iff_hom_eq_zero`, `Slicing.ltProp_iff_hom_eq_zero` and their `(> t, ≤ t)`
  analogues: each class of a pair is the orthogonal of the other;
* `Slicing.geProp_ext₂` and its three analogues, and the instances
  `ObjectProperty.IsTriangulatedClosed₂` for all four classes: the classes are closed under
  extensions;
* `Slicing.semistable_of_geProp_of_leProp`: an object with phases at least `t` and at most `t`
  is semistable of phase `t`.

## Tags

slicing, stability condition, truncation, orthogonal, extension closure
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.Triangulated.Slicing

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Shifts and phase bounds -/

/-- Phases at least `t` stay at least `t` after a positive shift. -/
theorem geProp_shift_one (s : Slicing C) {t : ℝ} {X : C} (hX : s.geProp C t X) :
    s.geProp C t (X⟦(1 : ℤ)⟧) :=
  s.geProp_anti C (show t ≤ t + ((1 : ℤ) : ℝ) by push_cast; linarith) _
    (s.geProp_shift C t X 1 hX)

/-- Every map from an object with phases at least `t` to one with phases below `t`, shifted by
`-1`, vanishes. -/
theorem hom_eq_zero_of_geProp_ltProp_shift (s : Slicing C) {t : ℝ} {X Y : C}
    (hX : s.geProp C t X) (hY : s.ltProp C t Y) (f : X ⟶ Y⟦(-1 : ℤ)⟧) : f = 0 :=
  s.hom_eq_zero_of_geProp_ltProp hX (s.ltProp_shift_neg_one hY) f

/-- Every map from an object with phases above `t` to one with phases at most `t`, shifted by
`-1`, vanishes. -/
theorem hom_eq_zero_of_gtProp_leProp_shift (s : Slicing C) {t : ℝ} {X Y : C}
    (hX : s.gtProp C t X) (hY : s.leProp C t Y) (f : X ⟶ Y⟦(-1 : ℤ)⟧) : f = 0 :=
  s.hom_eq_zero_of_gtProp_leProp hX (s.leProp_shift_neg_one hY) f

/-! ### The two splits -/

/-- **The `(> t, ≤ t)` split.** Every object `E` sits in a distinguished triangle
`X → E → Y → X⟦1⟧` with `X` of phases above `t` and `Y` of phases at most `t`. -/
theorem exists_split_gtProp_leProp [IsTriangulated C] (s : Slicing C) (t : ℝ) (E : C) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧ s.gtProp C t X ∧ s.leProp C t Y := by
  obtain ⟨F⟩ := s.hn_exists E
  obtain ⟨X, Y, GX, GY, f, g, h, hT, hGX, hGY, -, -⟩ := F.exists_split_at_cutoff C t
  refine ⟨X, Y, f, g, h, hT, ?_, ?_⟩
  · by_cases hn : 0 < GX.n
    · exact s.gtProp_of_hn C GX t hGX hn
    · exact Or.inl (GX.isZero_of_length_zero (by omega))
  · by_cases hn : 0 < GY.n
    · exact s.leProp_of_hn C GY t hGY hn
    · exact Or.inl (GY.isZero_of_length_zero (by omega))

/-- Below a real number `t`, the finitely many phases of an HN filtration leave a gap: some
`t' < t` bounds every phase below `t`. -/
private theorem exists_gap_below {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (t : ℝ) :
    ∃ t' < t, ∀ i, F.φ i < t → F.φ i ≤ t' := by
  classical
  let S : Finset ℝ := insert (t - 1) ((Finset.univ.image F.φ).filter (· < t))
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  refine ⟨S.max' hS, ?_, fun i hi => S.le_max' _ ?_⟩
  · rw [Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · linarith
    · exact (Finset.mem_filter.mp hy).2
  · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _
      (Finset.mem_univ _), hi⟩)

/-- **The `(≥ t, < t)` split.** Every object `E` sits in a distinguished triangle
`X → E → Y → X⟦1⟧` with `X` of phases at least `t` and `Y` of phases below `t`. -/
theorem exists_split_geProp_ltProp [IsTriangulated C] (s : Slicing C) (t : ℝ) (E : C) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧ s.geProp C t X ∧ s.ltProp C t Y := by
  obtain ⟨F⟩ := s.hn_exists E
  obtain ⟨t', ht', hgap⟩ := exists_gap_below F t
  obtain ⟨X, Y, GX, GY, f, g, h, hT, hGX, hGY, -, hGXorig⟩ := F.exists_split_at_cutoff C t'
  refine ⟨X, Y, f, g, h, hT, ?_, ?_⟩
  · by_cases hn : 0 < GX.n
    · refine s.geProp_of_hn C GX t (fun j => ?_) hn
      obtain ⟨i, hi⟩ := hGXorig j
      by_contra hlt
      have := hgap i (by rw [← hi]; exact lt_of_not_ge hlt)
      linarith [hGX j]
    · exact Or.inl (GX.isZero_of_length_zero (by omega))
  · by_cases hn : 0 < GY.n
    · exact s.ltProp_of_hn C GY t (fun j => (hGY j).trans_lt ht') hn
    · exact Or.inl (GY.isZero_of_length_zero (by omega))

/-- Every object has a coreflection into the objects of phases at least `t`: the first map of
its `(≥ t, < t)` split. -/
theorem exists_isCoreflection_geProp [IsTriangulated C] (s : Slicing C) (t : ℝ) (D : C) :
    ∃ (X : C) (f : X ⟶ D), (s.geProp C t).IsCoreflection f := by
  obtain ⟨X, Y, f, g, h, hT, hX, hY⟩ := s.exists_split_geProp_ltProp t D
  exact ⟨X, f, s.isCoreflection_geProp_of_top hT hX hY⟩

/-- The objects of phases at least `t` form a coreflective subcategory. -/
theorem isLeftAdjoint_ι_geProp [IsTriangulated C] (s : Slicing C) (t : ℝ) :
    (s.geProp C t).ι.IsLeftAdjoint :=
  ObjectProperty.isLeftAdjoint_ι_iff.2 (s.exists_isCoreflection_geProp t)

/-! ### Orthogonality -/

/-- In a distinguished triangle `X → D → Y → X⟦1⟧` whose second map vanishes, `Y` is zero as
soon as every map `X⟦1⟧ → Y` vanishes. -/
private theorem isZero₃_of_mor₂_eq_zero {X D Y : C} {f : X ⟶ D} {g : D ⟶ Y}
    {h : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C) (hg : g = 0)
    (hY : ∀ y : X⟦(1 : ℤ)⟧ ⟶ Y, y = 0) : IsZero Y := by
  rw [IsZero.iff_id_eq_zero]
  obtain ⟨y, hy⟩ := Triangle.yoneda_exact₃ _ hT (𝟙 Y) (show g ≫ 𝟙 Y = 0 by rw [hg, zero_comp])
  have hy0 : y = 0 := hY y
  rw [hy0, comp_zero] at hy
  exact hy

/-- In a distinguished triangle `X → D → Y → X⟦1⟧` whose first map vanishes, `X` is zero as
soon as every map `X → Y⟦-1⟧` vanishes. -/
private theorem isZero₁_of_mor₁_eq_zero {X D Y : C} {f : X ⟶ D} {g : D ⟶ Y}
    {h : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C) (hf : f = 0)
    (hX : ∀ y : X ⟶ Y⟦(-1 : ℤ)⟧, y = 0) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT) (𝟙 X)
    (show 𝟙 X ≫ f = 0 by rw [hf, comp_zero])
  have hy0 : y = 0 := hX y
  rw [hy0, zero_comp] at hy
  exact hy

/-- An object that maps trivially to the second term of a split lies in the first class. -/
private theorem prop_of_split_of_hom_eq_zero {A B : ObjectProperty C}
    [A.IsClosedUnderIsomorphisms] {X X₁ X₂ : C} {f : X₁ ⟶ X} {g : X ⟶ X₂}
    {h : X₂ ⟶ X₁⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C) (h₁ : A X₁) (h₂ : B X₂)
    (hvan : ∀ y : X₁⟦(1 : ℤ)⟧ ⟶ X₂, y = 0) (hX : ∀ ⦃Y : C⦄, B Y → ∀ f : X ⟶ Y, f = 0) :
    A X := by
  have hZ : IsZero X₂ := isZero₃_of_mor₂_eq_zero hT (hX h₂ g) hvan
  have : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hZ
  exact A.prop_of_iso (asIso f) h₁

/-- An object that receives only zero maps from the first term of a split lies in the second
class. -/
private theorem prop_of_split_of_hom_eq_zero' {A B : ObjectProperty C}
    [B.IsClosedUnderIsomorphisms] {Y Y₁ Y₂ : C} {f : Y₁ ⟶ Y} {g : Y ⟶ Y₂}
    {h : Y₂ ⟶ Y₁⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C) (h₁ : A Y₁) (h₂ : B Y₂)
    (hvan : ∀ y : Y₁ ⟶ Y₂⟦(-1 : ℤ)⟧, y = 0) (hY : ∀ ⦃X : C⦄, A X → ∀ f : X ⟶ Y, f = 0) :
    B Y := by
  have hZ : IsZero Y₁ := isZero₁_of_mor₁_eq_zero hT (hY h₁ f) hvan
  have : IsIso g := (Triangle.isZero₁_iff_isIso₂ _ hT).mp hZ
  exact B.prop_of_iso (asIso g).symm h₂

/-- **Orthogonality, `≥ t` side.** An object has phases at least `t` exactly when it maps
trivially to every object of phases below `t`. -/
theorem geProp_iff_hom_eq_zero [IsTriangulated C] (s : Slicing C) {t : ℝ} {X : C} :
    s.geProp C t X ↔ ∀ ⦃Y : C⦄, s.ltProp C t Y → ∀ f : X ⟶ Y, f = 0 := by
  refine ⟨fun hX _ hY f => s.hom_eq_zero_of_geProp_ltProp hX hY f, fun hX => ?_⟩
  obtain ⟨X₁, X₂, f, g, h, hT, h₁, h₂⟩ := s.exists_split_geProp_ltProp t X
  exact prop_of_split_of_hom_eq_zero (B := s.ltProp C t) hT h₁ h₂
    (fun y => s.hom_eq_zero_of_geProp_ltProp (s.geProp_shift_one h₁) h₂ y) hX

/-- **Orthogonality, `< t` side.** An object has phases below `t` exactly when it receives only
zero maps from objects of phases at least `t`. -/
theorem ltProp_iff_hom_eq_zero [IsTriangulated C] (s : Slicing C) {t : ℝ} {Y : C} :
    s.ltProp C t Y ↔ ∀ ⦃X : C⦄, s.geProp C t X → ∀ f : X ⟶ Y, f = 0 := by
  refine ⟨fun hY _ hX f => s.hom_eq_zero_of_geProp_ltProp hX hY f, fun hY => ?_⟩
  obtain ⟨Y₁, Y₂, f, g, h, hT, h₁, h₂⟩ := s.exists_split_geProp_ltProp t Y
  exact prop_of_split_of_hom_eq_zero' (A := s.geProp C t) hT h₁ h₂
    (fun y => s.hom_eq_zero_of_geProp_ltProp_shift h₁ h₂ y) hY

/-- **Orthogonality, `> t` side.** An object has phases above `t` exactly when it maps trivially
to every object of phases at most `t`. -/
theorem gtProp_iff_hom_eq_zero [IsTriangulated C] (s : Slicing C) {t : ℝ} {X : C} :
    s.gtProp C t X ↔ ∀ ⦃Y : C⦄, s.leProp C t Y → ∀ f : X ⟶ Y, f = 0 := by
  refine ⟨fun hX _ hY f => s.hom_eq_zero_of_gtProp_leProp hX hY f, fun hX => ?_⟩
  obtain ⟨X₁, X₂, f, g, h, hT, h₁, h₂⟩ := s.exists_split_gtProp_leProp t X
  exact prop_of_split_of_hom_eq_zero (B := s.leProp C t) hT h₁ h₂
    (fun y => s.hom_eq_zero_of_gtProp_leProp (s.gtProp_shift_one h₁) h₂ y) hX

/-- **Orthogonality, `≤ t` side.** An object has phases at most `t` exactly when it receives
only zero maps from objects of phases above `t`. -/
theorem leProp_iff_hom_eq_zero [IsTriangulated C] (s : Slicing C) {t : ℝ} {Y : C} :
    s.leProp C t Y ↔ ∀ ⦃X : C⦄, s.gtProp C t X → ∀ f : X ⟶ Y, f = 0 := by
  refine ⟨fun hY _ hX f => s.hom_eq_zero_of_gtProp_leProp hX hY f, fun hY => ?_⟩
  obtain ⟨Y₁, Y₂, f, g, h, hT, h₁, h₂⟩ := s.exists_split_gtProp_leProp t Y
  exact prop_of_split_of_hom_eq_zero' (A := s.gtProp C t) hT h₁ h₂
    (fun y => s.hom_eq_zero_of_gtProp_leProp_shift h₁ h₂ y) hY

/-! ### Extension closure -/

/-- A left orthogonal is closed under extensions. -/
private theorem ext₂_of_left_orth {A B : ObjectProperty C}
    (hA : ∀ X, A X ↔ ∀ ⦃Y : C⦄, B Y → ∀ f : X ⟶ Y, f = 0) {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} {h : X₃ ⟶ X₁⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C) (h₁ : A X₁)
    (h₃ : A X₃) : A X₂ := by
  refine (hA X₂).2 fun Y hY x => ?_
  obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ _ hT x ((hA X₁).1 h₁ hY _)
  rw [hy, (hA X₃).1 h₃ hY y, comp_zero]

/-- A right orthogonal is closed under extensions. -/
private theorem ext₂_of_right_orth {A B : ObjectProperty C}
    (hB : ∀ Y, B Y ↔ ∀ ⦃X : C⦄, A X → ∀ f : X ⟶ Y, f = 0) {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} {h : X₃ ⟶ X₁⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C) (h₁ : B X₁)
    (h₃ : B X₃) : B X₂ := by
  refine (hB X₂).2 fun X hX x => ?_
  obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ _ hT x ((hB X₃).1 h₃ hX _)
  rw [hy, (hB X₁).1 h₁ hX y, zero_comp]

/-- **Extension closure of `P(≥ t)`.** In a distinguished triangle `X₁ → X₂ → X₃ → X₁⟦1⟧` with
the outer terms of phases at least `t`, so is the middle term. -/
theorem geProp_ext₂ [IsTriangulated C] (s : Slicing C) {t : ℝ} {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} {h : X₃ ⟶ X₁⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (h₁ : s.geProp C t X₁) (h₃ : s.geProp C t X₃) : s.geProp C t X₂ :=
  ext₂_of_left_orth (B := s.ltProp C t) (fun _ => s.geProp_iff_hom_eq_zero) hT h₁ h₃

/-- **Extension closure of `P(< t)`.** -/
theorem ltProp_ext₂ [IsTriangulated C] (s : Slicing C) {t : ℝ} {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} {h : X₃ ⟶ X₁⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (h₁ : s.ltProp C t X₁) (h₃ : s.ltProp C t X₃) : s.ltProp C t X₂ :=
  ext₂_of_right_orth (A := s.geProp C t) (fun _ => s.ltProp_iff_hom_eq_zero) hT h₁ h₃

/-- **Extension closure of `P(> t)`.** -/
theorem gtProp_ext₂ [IsTriangulated C] (s : Slicing C) {t : ℝ} {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} {h : X₃ ⟶ X₁⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (h₁ : s.gtProp C t X₁) (h₃ : s.gtProp C t X₃) : s.gtProp C t X₂ :=
  ext₂_of_left_orth (B := s.leProp C t) (fun _ => s.gtProp_iff_hom_eq_zero) hT h₁ h₃

/-- **Extension closure of `P(≤ t)`.** -/
theorem leProp_ext₂ [IsTriangulated C] (s : Slicing C) {t : ℝ} {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} {h : X₃ ⟶ X₁⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (h₁ : s.leProp C t X₁) (h₃ : s.leProp C t X₃) : s.leProp C t X₂ :=
  ext₂_of_right_orth (A := s.gtProp C t) (fun _ => s.leProp_iff_hom_eq_zero) hT h₁ h₃

instance [IsTriangulated C] (s : Slicing C) (t : ℝ) : (s.geProp C t).IsTriangulatedClosed₂ :=
  .mk' fun _ hT h₁ h₃ => s.geProp_ext₂ (by exact hT) h₁ h₃

instance [IsTriangulated C] (s : Slicing C) (t : ℝ) : (s.ltProp C t).IsTriangulatedClosed₂ :=
  .mk' fun _ hT h₁ h₃ => s.ltProp_ext₂ (by exact hT) h₁ h₃

instance [IsTriangulated C] (s : Slicing C) (t : ℝ) : (s.gtProp C t).IsTriangulatedClosed₂ :=
  .mk' fun _ hT h₁ h₃ => s.gtProp_ext₂ (by exact hT) h₁ h₃

instance [IsTriangulated C] (s : Slicing C) (t : ℝ) : (s.leProp C t).IsTriangulatedClosed₂ :=
  .mk' fun _ hT h₁ h₃ => s.leProp_ext₂ (by exact hT) h₁ h₃

/-! ### Semistable objects as an intersection of cuts -/

/-- **One phase.** An object whose phases are at least `t` and at most `t` is semistable of
phase `t`. -/
theorem semistable_of_geProp_of_leProp (s : Slicing C) {t : ℝ} {X : C} (hge : s.geProp C t X)
    (hle : s.leProp C t X) : s.P t X := by
  by_cases hX : IsZero X
  · exact s.zero_mem_of_isZero C t X hX
  obtain ⟨F, hn, hfirst, hlast⟩ := s.exists_hn_nonzero_boundaries C hX
  have hplus : F.phiPlus C hn ≤ t := by
    rcases hle with hZ | ⟨G, hG, hGle⟩
    · exact absurd hZ hX
    · exact (F.phiPlus_le_of_firstFactor_nonzero C s G hn hG hfirst).trans hGle
  have hminus : t ≤ F.phiMinus C hn := by
    rcases hge with hZ | ⟨G, hG, hGge⟩
    · exact absurd hZ hX
    · exact hGge.trans (G.phiMinus_le_of_lastFactor_nonzero C s F hG hn hlast)
  have hn1 : F.n = 1 := by
    by_contra h
    have hlt : F.φ ⟨F.n - 1, by omega⟩ < F.φ ⟨0, hn⟩ := F.hφ (Fin.mk_lt_mk.mpr (by omega))
    change F.phiMinus C hn < F.phiPlus C hn at hlt
    linarith
  have hφ : F.φ ⟨0, by omega⟩ = t := by
    have h₁ : F.phiPlus C hn = F.φ ⟨0, hn⟩ := rfl
    have h₂ : F.phiMinus C hn = F.φ ⟨0, hn⟩ := by
      change F.φ ⟨F.n - 1, _⟩ = _
      congr 1
      exact Fin.ext (by simp [hn1])
    linarith
  have := F.semistable_of_length_one C s.closedUnderIso hn1
  rwa [hφ] at this

end CategoryTheory.Triangulated.Slicing
