/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.WeylTilt
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.ExtensionClosure
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Heart
import Mathlib.CategoryTheory.Simple

/-!
# Weyl galleries at the heart `P((0, 1])` of a stability condition

The Weyl-gallery theorems (`CategoryTheory.Triangulated.WeylGalleryHypotheses`, in
`StabilityCondition/WeylTilt.lean`) state tilts as properties of objects, with their own notions
of simple object (`WeylGallery.IsSimpleIn`) and torsion class (`WeylGallery.IsTorsionClass`).
Hearts of slicings are abelian categories in the library (`Slicing.HeartCat`,
`StabilityCondition/Weak/Foundation/Slicing/Heart.lean`). This file connects the two at
`A = P((a, a+1])`, without changing either:

* **Simple objects** (`TStructure.isSimpleIn_heart_iff`, `Slicing.isSimpleIn_heartProp_iff`): an
  object of the heart of a t-structure is simple in the abelian heart exactly when it is
  `IsSimpleIn` the heart. Distinguished triangles on heart objects are the short exact sequences,
  so a nonzero subobject with nonzero cokernel is an extension of two nonzero heart objects.
* **Phase cuts are torsion classes** (`Slicing.isTorsionClass_heartProp_inf_gtProp`): for
  `θ ≤ a + 1`, the objects of `P((θ, a+1])` form an `IsTorsionClass` of `P((a, a+1])`.
* **Their lower tilts are the rotated hearts** (`Slicing.lowerTilt_heartProp`): for
  `a ≤ θ ≤ a + 1`, the lower tilt `⟨T^⊥ ∩ A, T[-1]⟩` of `A = P((a, a+1])` at `T = P((θ, a+1])` is
  `P((θ-1, θ])`. Here `T^⊥ ∩ A = P((a, θ])` by the torsion pair of the heart
  (`Slicing.exists_shortExact_heartAbove`), and an object of `P((θ-1, θ])` is cut at phase `a`.
* **The sign of the class from the central charge**
  (`PreStabilityCondition.WithClassMap.chargeCone`): the classes with `Im Z > 0`, or `Im Z = 0` and
  `Re Z < 0`, form a cone with no pair `x, -x` that contains the class of every nonzero object of
  `P((0, 1])` (`charge_mem_of_heartProp`).

**The instance at `P((0, 1])`** (`WeylGalleryHypotheses.ofWithClassMap`): for a prestability
condition `σ` with class map `v`, the t-structure of the slicing at `0`, the class map `v` and the
charge cone fill the fields `t`, `cl`, `cl_iso`, `cl_triangle`, `cone`, `cl_mem_cone` and
`neg_not_mem_cone` of `WeylGalleryHypotheses`, and simple objects of the abelian category
`P((0, 1])` fill `isSimpleIn_obj`. The remaining fields are the configuration of twists with its
action on classes, the simple tilt, tilt composition and `C` Serre in `A`, as in
`StabilityCondition/WeylTilt.lean`: they need the twist functors of a `2`-Calabi–Yau category,
and the library has none. In this instance a gallery heart whose torsion class is a phase cut
is the heart of the rotated slicing (`WeylGalleryHypotheses.heartOf_eq_heartProp`):
`F_ω P((0, 1]) = P((θ-1, θ])` when `T_ω = P((θ, 1])`.

## References

* D. Happel, I. Reiten and S. O. Smalø, *Tilting in abelian categories and quasitilted algebras*,
  Mem. Amer. Math. Soc. 575 (1996), §I.2.
* T. Bridgeland, *Stability conditions on triangulated categories*, arXiv:math/0212237, §3 and
  Lemma 5.3 (tilting `P((0, 1])` at a phase cut rotates the slicing).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated.WeylGallery
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-! ### Simple objects of a heart -/

namespace TStructure

variable (t : TStructure C) {H : Type*} [Category H] [Preadditive H] [t.Heart H]

omit [IsTriangulated C] in
/-- A heart object whose image is zero is zero. -/
theorem isZero_of_isZero_ιHeart {X : H} (h : IsZero (t.ιHeart.obj X)) : IsZero X := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact t.ιHeart.map_injective (by rw [Functor.map_id, Functor.map_zero, h])

/-- **`IsSimpleIn` is simplicity in the abelian heart.** An object of the heart `H` of a
t-structure is a simple object of the abelian category `H` exactly when its image is
`IsSimpleIn` the heart. -/
theorem isSimpleIn_heart_iff (X : H) : IsSimpleIn t.heart (t.ιHeart.obj X) ↔ Simple X := by
  let _ := t.heartAbelian H
  constructor
  · rintro ⟨-, hX0, hXs⟩
    refine ⟨fun {Y} f _ => ⟨fun hf h0 => ?_, fun hf0 => ?_⟩⟩
    · apply hX0
      have hY : IsZero Y := by
        rw [IsZero.iff_id_eq_zero, ← cancel_mono f, h0, comp_zero, comp_zero]
      exact t.ιHeart.map_isZero (hY.of_iso (asIso f).symm)
    · let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hS : S.ShortExact := ShortComplex.ShortExact.mk'
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)) inferInstance
        inferInstance
      obtain ⟨δ, hT⟩ := t.exists_distTriang_of_shortExact hS
      by_cases hY : IsZero (t.ιHeart.obj Y)
      · exact absurd ((t.isZero_of_isZero_ιHeart hY).eq_of_src f 0) hf0
      by_cases hQ : IsZero (t.ιHeart.obj (cokernel f))
      · exact hS.isIso_f_iff.mpr (t.isZero_of_isZero_ιHeart hQ)
      · exact absurd ⟨_, _, _, _, _, hT, ⟨t.ιHeart_obj_mem Y, hY⟩,
          ⟨t.ιHeart_obj_mem (cokernel f), hQ⟩⟩ hXs
  · intro hX
    refine ⟨t.ιHeart_obj_mem X, fun h => Simple.not_isZero X (t.isZero_of_isZero_ιHeart h), ?_⟩
    rintro ⟨A, B, a, b, c, hT, ⟨hA, hA0⟩, ⟨hB, hB0⟩⟩
    rw [← t.essImage_ιHeart H] at hA hB
    obtain ⟨A', ⟨eA⟩⟩ := hA
    obtain ⟨B', ⟨eB⟩⟩ := hB
    let f' : A' ⟶ X := t.ιHeart.preimage (eA.hom ≫ a)
    let g' : X ⟶ B' := t.ιHeart.preimage (b ≫ eB.inv)
    have hT' : Triangle.mk (t.ιHeart.map f') (t.ιHeart.map g')
        (eB.hom ≫ c ≫ (shiftFunctor C (1 : ℤ)).map eA.inv) ∈ distTriang C := by
      refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ eA (Iso.refl _) eB ?_ ?_ ?_)
      · simp [f']
      · simp [g']
      · simp only [Triangle.mk_mor₃, Triangle.mk_obj₁, Category.assoc, ← Functor.map_comp,
          Iso.inv_hom_id, Functor.map_id, Category.comp_id]
    have hS := t.shortExact_of_distTriang hT'
    have := hS.mono_f
    have hf' : f' ≠ 0 := by
      intro h0
      have hA' : IsZero A' := by
        rw [IsZero.iff_id_eq_zero, ← cancel_mono f', h0, comp_zero, comp_zero]
      exact hA0 ((t.ιHeart.map_isZero hA').of_iso eA.symm)
    have hiso : IsIso f' := (Simple.mono_isIso_iff_nonzero f').mpr hf'
    exact hB0 ((t.ιHeart.map_isZero (hS.isIso_f_iff.mp hiso)).of_iso eB.symm)

end TStructure

/-! ### Phase cuts of the heart of a slicing -/

namespace Slicing

variable (s : Slicing C)

/-- **Simple objects of `P((a, a+1])`**: `IsSimpleIn` the heart is simplicity in the abelian
category `P((a, a+1])`. -/
theorem isSimpleIn_heartProp_iff (a : ℝ) (X : s.HeartCat C a) :
    IsSimpleIn (s.heartProp C a) X.obj ↔ Simple X := by
  have := (s.toTStructure C a).isSimpleIn_heart_iff X
  rw [Slicing.toTStructure_heart] at this
  exact this

/-- `P((a, a+1])` is closed under extensions. -/
theorem heartProp_ext {a : ℝ} (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : s.heartProp C a T.obj₁) (h₃ : s.heartProp C a T.obj₃) : s.heartProp C a T.obj₂ :=
  ⟨(s.gtProp C a).ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1,
    (s.leProp C (a + 1)).ext_of_isTriangulatedClosed₂ T hT h₁.2 h₃.2⟩

omit [IsTriangulated C] in
theorem gtProp_of_shift_one {t : ℝ} {X : C} (h : s.gtProp C t (X⟦(1 : ℤ)⟧)) :
    s.gtProp C (t - 1) X := by
  have := s.gtProp_shift C t _ (-1) h
  rw [show t + ((-1 : ℤ) : ℝ) = t - 1 by push_cast; ring] at this
  exact (s.gtProp C (t - 1)).prop_of_iso
    ((shiftFunctorCompIsoId C (1 : ℤ) (-1) (by norm_num)).app X) this

omit [IsTriangulated C] in
theorem leProp_of_shift_one {t : ℝ} {X : C} (h : s.leProp C t (X⟦(1 : ℤ)⟧)) :
    s.leProp C (t - 1) X := by
  have := s.leProp_shift C t _ (-1) h
  rw [show t + ((-1 : ℤ) : ℝ) = t - 1 by push_cast; ring] at this
  exact (s.leProp C (t - 1)).prop_of_iso
    ((shiftFunctorCompIsoId C (1 : ℤ) (-1) (by norm_num)).app X) this

omit [IsTriangulated C] in
theorem gtProp_shift_one' {t : ℝ} {X : C} (h : s.gtProp C t X) :
    s.gtProp C (t + 1) (X⟦(1 : ℤ)⟧) := by
  have := s.gtProp_shift C t X 1 h
  rwa [Int.cast_one] at this

omit [IsTriangulated C] in
theorem leProp_shift_neg_one' {t : ℝ} {X : C} (h : s.leProp C t X) :
    s.leProp C (t - 1) (X⟦(-1 : ℤ)⟧) := by
  have := s.leProp_shift C t X (-1) h
  rwa [show t + ((-1 : ℤ) : ℝ) = t - 1 by push_cast; ring] at this

/-- **The phase cut `P((θ, a+1])` is a torsion class of `P((a, a+1])`**, for `θ ≤ a + 1`: it is
closed under extensions, and under quotients because a quotient in the heart is an extension of
`X₁[1] ∈ P(> a+1)` by an object of `P(> θ)`. -/
theorem isTorsionClass_heartProp_inf_gtProp {a θ : ℝ} (h₂ : θ ≤ a + 1) :
    IsTorsionClass (s.heartProp C a) (s.heartProp C a ⊓ s.gtProp C θ) where
  le := inf_le_left
  isClosedUnderIsomorphisms := inferInstance
  prop_of_isZero X hX := ⟨s.heartProp_of_isZero C hX a, s.gtProp_of_isZero C hX θ⟩
  ext X₁ X₂ X₃ f g h hT h₁ h₃ :=
    ⟨s.heartProp_ext _ hT h₁.1 h₃.1,
      (s.gtProp C θ).ext_of_isTriangulatedClosed₂ _ hT h₁.2 h₃.2⟩
  quot X₁ X₂ X₃ f g h hT h₁ h₂' h₃ := by
    refine ⟨h₃, (s.gtProp C θ).ext_of_isTriangulatedClosed₂ _ (rot_of_distTriang _ hT) h₂'.2 ?_⟩
    exact s.gtProp_anti C h₂ _ (s.gtProp_shift_one' h₁.1)

/-- **The lower tilt of `P((a, a+1])` at `P((θ, a+1])` is `P((θ-1, θ])`**, for
`a ≤ θ ≤ a + 1`. -/
theorem lowerTilt_heartProp {a θ : ℝ} (h₁ : a ≤ θ) (h₂ : θ ≤ a + 1) :
    lowerTilt (s.heartProp C a) (s.heartProp C a ⊓ s.gtProp C θ) = s.heartProp C (θ - 1) := by
  ext X
  constructor
  · rintro ⟨F, Z, f, g, h, hT, ⟨hFA, hForth⟩, hZ⟩
    -- `A ∩ T^⊥ = P((a, θ])`, by the torsion pair of the heart
    have hFle : s.leProp C θ F := by
      obtain ⟨X₁, X₃, i, p, w, hSES, hX₁, hX₃⟩ := s.exists_shortExact_heartAbove C h₁ h₂ ⟨F, hFA⟩
      have hi : i = 0 := ObjectProperty.hom_ext _ (hForth i.hom ⟨X₁.property, hX₁⟩)
      have : Mono i := hSES.mono_f
      have hX₁0 : IsZero X₁ := by
        rw [IsZero.iff_id_eq_zero, ← cancel_mono i, hi, comp_zero, comp_zero]
      have : IsIso p := hSES.isIso_g_iff.mpr hX₁0
      exact (s.leProp C θ).prop_of_iso ((s.heartProp C a).ι.mapIso (asIso p)).symm hX₃
    have hF : s.heartProp C (θ - 1) F :=
      ⟨s.gtProp_anti C (by linarith) _ hFA.1, by rwa [sub_add_cancel]⟩
    have hZ' : s.heartProp C (θ - 1) Z := by
      refine ⟨s.gtProp_of_shift_one hZ.2, ?_⟩
      rw [sub_add_cancel]
      have := s.leProp_of_shift_one hZ.1.2
      rw [add_sub_cancel_right] at this
      exact s.leProp_mono C h₁ _ this
    exact s.heartProp_ext (Triangle.mk f g h) hT hF hZ'
  · intro hX
    obtain ⟨X₁, X₃, hX₁, hX₃, f, g, h, hT⟩ := s.exists_distTriang_gtProp_leProp C a X
    -- `X₁ ∈ P((a, θ])`: an extension of `X ∈ P(≤ θ)` by `X₃[-1] ∈ P(≤ a - 1)`
    have hX₁le : s.leProp C θ X₁ :=
      (s.leProp C θ).ext_of_isTriangulatedClosed₂ _ (inv_rot_of_distTriang _ hT)
        (s.leProp_mono C (by linarith) _ (s.leProp_shift_neg_one' hX₃))
        (by have := hX.2; rwa [sub_add_cancel] at this)
    -- `X₃ ∈ P((θ - 1, a])`: an extension of `X₁[1] ∈ P(> a + 1)` by `X ∈ P(> θ - 1)`
    have hX₃gt : s.gtProp C (θ - 1) X₃ :=
      (s.gtProp C (θ - 1)).ext_of_isTriangulatedClosed₂ _ (rot_of_distTriang _ hT) hX.1
        (s.gtProp_anti C (by linarith) _ (s.gtProp_shift_one' hX₁))
    refine ⟨X₁, X₃, f, g, h, hT, ⟨⟨hX₁, s.leProp_mono C h₂ _ hX₁le⟩, fun Y u hY =>
      Slicing.hom_eq_zero_of_gtProp_leProp s hY.2 hX₁le u⟩, ?_⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact s.gtProp_anti C (by linarith) _ (s.gtProp_shift_one' hX₃gt)
    · exact s.leProp_shift C a X₃ 1 hX₃ |>.elim (fun h => Or.inl h) fun h => by
        rw [Int.cast_one] at *
        exact Or.inr h
    · have := s.gtProp_shift_one' hX₃gt
      rwa [sub_add_cancel] at this

end Slicing

/-! ### The charge cone -/

namespace PreStabilityCondition.WithClassMap

variable {Λ : Type*} [AddCommGroup Λ] {v : K₀ C →+ Λ}

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] in
/-- **The cone of a central charge**: the classes with `Im Z > 0`, or `Im Z = 0` and
`Re Z < 0`. -/
def chargeCone (Z : Λ →+ ℂ) : AddSubsemigroup Λ where
  carrier := {x | 0 < (Z x).im ∨ ((Z x).im = 0 ∧ (Z x).re < 0)}
  add_mem' {x y} hx hy := by
    show 0 < (Z (x + y)).im ∨ ((Z (x + y)).im = 0 ∧ (Z (x + y)).re < 0)
    rw [map_add, Complex.add_im, Complex.add_re]
    rcases hx with hx | ⟨hx, hx'⟩ <;> rcases hy with hy | ⟨hy, hy'⟩
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] in
/-- **The charge cone contains no pair `x, -x`.** -/
theorem neg_notMem_chargeCone (Z : Λ →+ ℂ) {x : Λ} (hx : x ∈ chargeCone Z) :
    -x ∉ chargeCone Z := by
  intro hx'
  change 0 < (Z (-x)).im ∨ ((Z (-x)).im = 0 ∧ (Z (-x)).re < 0) at hx'
  change 0 < (Z x).im ∨ ((Z x).im = 0 ∧ (Z x).re < 0) at hx
  rw [map_neg, Complex.neg_im, Complex.neg_re] at hx'
  rcases hx with hx | ⟨hx, hx''⟩ <;> rcases hx' with hx' | ⟨hx', hx'''⟩ <;> linarith

omit [IsTriangulated C] in
/-- **The class of every nonzero object of `P((0, 1])` lies in the charge cone.** -/
theorem classOf_mem_chargeCone (σ : WithClassMap C v) {E : C} (hE : σ.slicing.heartProp C 0 E)
    (hZ : ¬IsZero E) : classOf C v E ∈ chargeCone σ.Z :=
  σ.charge_mem_of_heartProp hE hZ

end PreStabilityCondition.WithClassMap

/-! ### The instance at `P((0, 1])` -/

open PreStabilityCondition BilinearForm
open WeakStabilityCondition.StabilityCondition.GroupAction

namespace WeylGalleryHypotheses

variable {Λ : Type*} [AddCommGroup Λ] {v : K₀ C →+ Λ} {B : Type*} {M : CoxeterMatrix B}

/-- **The Weyl-gallery hypotheses at the heart `P((0, 1])` of a prestability condition.** The
t-structure is that of the slicing at `0`, the class map is `v`, and the cone of positive classes
is the charge cone of the central charge. The spherical objects `S_i` are simple objects of the
abelian category `P((0, 1])`. The remaining inputs are the twists with their action on classes,
the simple tilt, tilt composition and `C` Serre in `A`, stated on `P((0, 1])`. -/
def ofWithClassMap (σ : WithClassMap C v) (twists : TwistConjugation C)
    (conf : twists.Configuration M) (form : LinearMap.BilinForm ℤ Λ)
    (form_symm : ∀ x y, form x y = form y x)
    (form_self : ∀ i, form (classOf C v (conf.obj i)) (classOf C v (conf.obj i)) = -2)
    (cl_twist : ∀ i X, classOf C v ((conf.T i).e.functor.obj X) =
      reflect form (classOf C v (conf.obj i)) (classOf C v X))
    (isSimple : ∀ i, ∃ h : σ.slicing.heartProp C 0 (conf.obj i),
      Simple (⟨conf.obj i, h⟩ : σ.slicing.HeartCat C 0))
    (image_heart_eq_lowerTilt : ∀ i, image (conf.T i) (σ.slicing.heartProp C 0) =
      lowerTilt (σ.slicing.heartProp C 0) (filtration (isoClass (conf.obj i))))
    (lowerTilt_lowerTilt_eq : ∀ T : ObjectProperty C,
      IsTorsionClass (σ.slicing.heartProp C 0) T →
      ∀ X, IsSimpleIn (lowerTilt (σ.slicing.heartProp C 0) T) X →
        (σ.slicing.heartProp C 0 ⊓ T.rightOrthogonal) X →
        IsTorsionClass (σ.slicing.heartProp C 0) (filtration (T ⊔ isoClass X)) ∧
          lowerTilt (lowerTilt (σ.slicing.heartProp C 0) T) (filtration (isoClass X)) =
            lowerTilt (σ.slicing.heartProp C 0) (filtration (T ⊔ isoClass X)))
    (hull : ObjectProperty C) (hull_obj : ∀ i, hull (conf.obj i))
    (hull_twist : ∀ i X, hull X → hull ((conf.T i).e.functor.obj X))
    (heart_inf_hull_le : σ.slicing.heartProp C 0 ⊓ hull ≤
      filtration (ObjectProperty.ofObj conf.obj).isoClosure) :
    WeylGalleryHypotheses C M Λ where
  t := σ.slicing.toTStructure C 0
  twists := twists
  conf := conf
  cl := classOf C v
  cl_iso := classOf_iso C v
  cl_triangle f g h hT := classOf_triangle C v (Triangle.mk f g h) hT
  form := form
  form_symm := form_symm
  form_self := form_self
  cl_twist := cl_twist
  cone := WithClassMap.chargeCone σ.Z
  cl_mem_cone X hX hX0 := σ.classOf_mem_chargeCone
    ((σ.slicing.toTStructure_mem_heart_iff C 0 X).mp hX) hX0
  neg_not_mem_cone _ hx := WithClassMap.neg_notMem_chargeCone σ.Z hx
  isSimpleIn_obj i := by
    obtain ⟨h, hs⟩ := isSimple i
    rw [Slicing.toTStructure_heart]
    exact (σ.slicing.isSimpleIn_heartProp_iff 0 ⟨_, h⟩).mpr hs
  image_heart_eq_lowerTilt i := by
    rw [Slicing.toTStructure_heart]
    exact image_heart_eq_lowerTilt i
  lowerTilt_lowerTilt_eq := by
    rw [Slicing.toTStructure_heart]
    exact lowerTilt_lowerTilt_eq
  hull := hull
  hull_obj := hull_obj
  hull_twist := hull_twist
  heart_inf_hull_le := by
    rw [Slicing.toTStructure_heart]
    exact heart_inf_hull_le

/-- **A gallery heart whose torsion class is a phase cut is a rotated heart.** Let the heart of
`H` be `P((0, 1])` for a slicing `s` (for `ofWithClassMap` this is `Slicing.toTStructure_heart`).
If `ω` is root-positive and `T_ω = P((θ, 1])` with `0 ≤ θ ≤ 1`, then `F_ω A = P((θ - 1, θ])`. -/
theorem heartOf_eq_heartProp (H : WeylGalleryHypotheses C M Λ) (s : Slicing C)
    (hH : H.t.heart = s.heartProp C 0) {ω : List B} (hω : IsRootPositive H.form H.root ω)
    {θ : ℝ} (h₁ : 0 ≤ θ) (h₂ : θ ≤ 1) (hT : H.torsionOf ω = s.heartProp C 0 ⊓ s.gtProp C θ) :
    H.heartOf ω = s.heartProp C (θ - 1) := by
  rw [H.heartOf_eq_lowerTilt hω, hT, hH]
  exact s.lowerTilt_heartProp h₁ (by linarith)

end WeylGalleryHypotheses

end CategoryTheory.Triangulated
