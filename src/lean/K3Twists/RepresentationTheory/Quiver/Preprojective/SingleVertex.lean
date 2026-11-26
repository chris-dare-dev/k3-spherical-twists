/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Algebra.Homology.DerivedCategory.AbelianHeart
import K3Twists.RepresentationTheory.Quiver.Preprojective.WallModel
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The formal wall model of one sphere, from real objects

The quiver with one vertex and no arrows (`Quiver.Preprojective.pointQuiver`) is the half
`Ext`-quiver of a single spherical object `S`: its representations are vector spaces, and the
iterated extensions of `S` are `S ⊗ V` for finite-dimensional `V`. This file builds
`Quiver.Preprojective.RealizationHypotheses` for it from real objects:

* source and target: the derived category `D(Vect_k)` of finite-dimensional vector spaces
  (`FGModuleCat k`), with its standard heart
  (`DerivedCategory.abelianHeartHypotheses_singleFunctor`);
* the realization functor: the identity, which satisfies the window condition in every degree;
* the vertex simple: the line `k`, simple in `FGModuleCat k` (`SingleVertex.simple_line`);
* every finite-dimensional space is an iterated extension of `k` in `D(Vect_k)`
  (`SingleVertex.mem_extensionClosure`), by induction on the dimension;
* the model of a space `X` is `X` as a representation of the double of the one-vertex quiver
  (`DoubledRep.ofVect`), and its subobjects in `FGModuleCat k` are its subspaces
  (`SingleVertex.subobjectIso`, through `ModuleCat.subobjectModule` and the fully faithful
  inclusion into `ModuleCat k`), with the dimension as multiplicity.

By the realization constructor this gives `FormalWallHypotheses` for `FGModuleCat k`
(`SingleVertex.formalWallHypotheses`). This is the case of the spherical evaluation: one vertex,
no loops. For a quiver with arrows or loops the source of the realization is the derived category
of nilpotent modules over the preprojective algebra (the Ginzburg dg algebra in the Dynkin case,
Davison, arXiv:2106.07692), which Mathlib cannot build yet: it has no abelian category of quiver
representations with its derived category, and no dg categories. That source, not a
2-Calabi–Yau structure, is the missing input for an instance with arrows.
-/

noncomputable section

universe w u

open CategoryTheory Limits Module

namespace Quiver.Preprojective

/-- The quiver with one vertex and no arrows, the half `Ext`-quiver of one sphere. -/
def pointQuiver : PUnit.{1} → PUnit.{1} → Type :=
  fun _ _ ↦ PEmpty

instance (i j : PUnit.{1}) : Fintype (pointQuiver i j) :=
  inferInstanceAs (Fintype PEmpty)

instance (i j : PUnit.{1}) : IsEmpty (pointQuiver i j) :=
  inferInstanceAs (IsEmpty PEmpty)

variable (k : Type u) [Field k]

namespace DoubledRep

/-- A vector space as a representation of the double of the quiver with one vertex and no
arrows. -/
def ofVect (X : Type u) [AddCommGroup X] [Module k X] :
    DoubledRep k pointQuiver (fun _ ↦ X) where
  A a := isEmptyElim a
  B a := isEmptyElim a

variable {k} {X : Type u} [AddCommGroup X] [Module k X]

lemma ofVect_isPreprojective : (ofVect k X).IsPreprojective := fun _ ↦ by
  simp [relation]

lemma ofVect_isNilpotent : (ofVect k X).IsNilpotent := by
  refine ⟨1, fun w hw ↦ ?_⟩
  obtain ⟨a, w', rfl⟩ := List.exists_cons_of_length_pos hw
  rcases a with ⟨_, _, a⟩ | ⟨_, _, a⟩ <;> exact isEmptyElim a

/-- The subrepresentations of `ofVect k X` are the subspaces of `X`. -/
def ofVectSubrepsIso : (ofVect k X).subreps ≃o Submodule k X where
  toFun P := (P : PUnit.{1} → Submodule k X) PUnit.unit
  invFun p := ⟨fun _ ↦ p, fun _ _ a ↦ isEmptyElim a⟩
  left_inv _ := Subtype.ext (funext fun _ ↦ rfl)
  right_inv _ := rfl
  map_rel_iff' := ⟨fun h _ ↦ h, fun h ↦ h _⟩

lemma dimVec_ofVectSubrepsIso_symm (p : Submodule k X) :
    dimVec (ofVectSubrepsIso.symm p) = fun _ ↦ finrank k p :=
  rfl

end DoubledRep

namespace SingleVertex

/-- The model of a finite-dimensional space: the space itself, as a representation of the double
of the one-vertex quiver. -/
def model (X : FGModuleCat.{u} k) : WallRep k pointQuiver where
  V _ := X
  rep := DoubledRep.ofVect k X
  isPreprojective := DoubledRep.ofVect_isPreprojective
  isNilpotent := DoubledRep.ofVect_isNilpotent

/-- The inclusion of finite-dimensional spaces into all spaces. -/
abbrev incl : FGModuleCat.{u} k ⥤ ModuleCat.{u} k :=
  forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)

variable {k}

/-- Every subobject of a finite-dimensional space in `ModuleCat` is finite-dimensional. -/
lemma exists_of_mono_incl (X : FGModuleCat.{u} k) ⦃Y : ModuleCat.{u} k⦄
    (f : Y ⟶ (incl k).obj X) [Mono f] :
    ∃ (Z : FGModuleCat.{u} k) (g : Z ⟶ X) (_ : Mono g) (e : (incl k).obj Z ≅ Y),
      e.hom ≫ f = (incl k).map g := by
  have hinj : Function.Injective f := (ModuleCat.mono_iff_injective f).mp inferInstance
  have hX : Module.Finite k ((incl k).obj X) := (inferInstance : Module.Finite k X)
  have : Module.Finite k Y := Module.Finite.of_injective f.hom hinj
  let Z : FGModuleCat.{u} k := FGModuleCat.of k Y
  let g : Z ⟶ X := (incl k).preimage (X := Z) (Y := X) f
  have hg : (incl k).map g = f := (incl k).map_preimage (X := Z) (Y := X) f
  have : Mono g := (incl k).mono_of_mono_map (by rw [hg]; infer_instance)
  exact ⟨Z, g, this, Iso.refl _, by rw [hg]; rfl⟩

/-- **The subobjects of a finite-dimensional space are its subspaces.** -/
def subobjectIso (X : FGModuleCat.{u} k) : Subobject X ≃o Submodule k X :=
  ((incl k).subobjectOrderIso X (exists_of_mono_incl X)).trans
    (ModuleCat.subobjectModule ((incl k).obj X))

lemma finrank_subobjectIso (X : FGModuleCat.{u} k) (N : Subobject X) :
    finrank k (subobjectIso X N) = finrank k (N : FGModuleCat.{u} k) := by
  let N' := (incl k).subobjectOrderIso X (exists_of_mono_incl X) N
  have hinj : Function.Injective N'.arrow.hom :=
    (ModuleCat.mono_iff_injective N'.arrow).mp inferInstance
  change finrank k (LinearMap.range N'.arrow.hom) = _
  rw [LinearMap.finrank_range_of_inj hinj]
  exact ((incl k).underlyingMapSubobjectIso N).toLinearEquiv.finrank_eq

/-- **The line is simple.** -/
lemma simple_line : Simple (FGModuleCat.of k k) := by
  rw [simple_iff_subobject_isSimpleOrder]
  have : IsSimpleOrder (Submodule k k) := Ideal.isSimpleOrder
  exact (subobjectIso (FGModuleCat.of k k)).isSimpleOrder

/-- Dimension is additive on short exact sequences of finite-dimensional spaces. -/
lemma finrank_shortExact {S : ShortComplex (FGModuleCat.{u} k)} (hS : S.ShortExact) :
    finrank k S.X₂ = finrank k S.X₁ + finrank k S.X₃ := by
  have hS' := hS.map_of_exact (incl k)
  have hinj := hS'.moduleCat_injective_f
  have hsurj := hS'.moduleCat_surjective_g
  have hex := hS'.exact.moduleCat_range_eq_ker
  have : Module.Finite k (S.map (incl k)).X₂ := (inferInstance : Module.Finite k S.X₂)
  have h := LinearMap.finrank_range_add_finrank_ker (S.map (incl k)).g.hom
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, ← hex,
    LinearMap.finrank_range_of_inj hinj] at h
  change finrank k (S.map (incl k)).X₂ =
    finrank k (S.map (incl k)).X₁ + finrank k (S.map (incl k)).X₃
  omega

/-- A space of dimension zero is a zero object. -/
lemma isZero_of_finrank_eq_zero {X : FGModuleCat.{u} k} (h : finrank k X = 0) : IsZero X := by
  have : Subsingleton X := Module.finrank_zero_iff.mp h
  rw [IsZero.iff_id_eq_zero]
  exact FGModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)

variable [HasDerivedCategory.{w} (FGModuleCat.{u} k)]

/-- **Every finite-dimensional space is an iterated extension of the line** in `D(Vect_k)`: a
nonzero vector gives a short exact sequence `0 → k → X → X/k → 0`, hence a distinguished
triangle, and the quotient has smaller dimension. -/
theorem mem_extensionClosure (X : FGModuleCat.{u} k) :
    (ObjectProperty.extensionClosure fun Y ↦ ∃ _ : PUnit.{1},
      Y = (DerivedCategory.singleFunctor (FGModuleCat.{u} k) 0).obj (FGModuleCat.of k k))
      ((DerivedCategory.singleFunctor (FGModuleCat.{u} k) 0).obj X) := by
  suffices h : ∀ n (X : FGModuleCat.{u} k), finrank k X = n →
      (ObjectProperty.extensionClosure fun Y ↦ ∃ _ : PUnit.{1},
        Y = (DerivedCategory.singleFunctor (FGModuleCat.{u} k) 0).obj (FGModuleCat.of k k))
        ((DerivedCategory.singleFunctor (FGModuleCat.{u} k) 0).obj X) from h _ X rfl
  intro n
  induction n with
  | zero =>
    intro X hX
    exact .of_isZero ((DerivedCategory.singleFunctor _ 0).map_isZero (isZero_of_finrank_eq_zero hX))
  | succ n ih =>
    intro X hX
    have : Nontrivial X := (Module.finrank_pos_iff (R := k)).mp (by rw [hX]; omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : X)
    let f : FGModuleCat.of k k ⟶ X := FGModuleCat.ofHom (LinearMap.toSpanSingleton k X v)
    have hf : Function.Injective (LinearMap.toSpanSingleton k X v) :=
      smul_left_injective k hv
    have : Mono f := (incl k).mono_of_mono_map ((ModuleCat.mono_iff_injective _).mpr hf)
    have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
      .mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)) inferInstance
        inferInstance
    have hdim : finrank k X =
        finrank k (FGModuleCat.of k k) + finrank k (cokernel f : FGModuleCat.{u} k) :=
      finrank_shortExact hS
    have h₁ : finrank k (FGModuleCat.of k k) = 1 := Module.finrank_self k
    obtain ⟨δ, hδ⟩ := (DerivedCategory.abelianHeartHypotheses_singleFunctor
      (FGModuleCat.{u} k)).distinguished_of_shortExact _ hS
    exact .ext _ hδ (.of_prop ⟨PUnit.unit, rfl⟩) (ih (cokernel f) (by omega))

/-- **The realization hypotheses of one sphere, from real objects**: the identity of
`D(Vect_k)`, with the line as vertex simple and each space its own model. -/
def realizationHypotheses :
    RealizationHypotheses k pointQuiver (𝟭 (DerivedCategory (FGModuleCat.{u} k)))
      (DerivedCategory.singleFunctor (FGModuleCat.{u} k) 0)
      (DerivedCategory.singleFunctor (FGModuleCat.{u} k) 0) where
  heartC := DerivedCategory.abelianHeartHypotheses_singleFunctor _
  heartD := DerivedCategory.abelianHeartHypotheses_singleFunctor _
  S _ := FGModuleCat.of k k
  mem_extensionClosure := mem_extensionClosure
  window _ _ := Functor.isExtWindow_id 0 1 _ _
  G := 𝟭 _
  isoG := Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm
  simple_G_S _ := simple_line
  model X := model k X
  subobjectIso X := (subobjectIso X).trans DoubledRep.ofVectSubrepsIso.symm
  dim X _ := finrank k X
  dim_iso e := funext fun _ ↦ (FGModuleCat.isoToLinearEquiv e).finrank_eq
  dim_S _ := funext fun _ ↦ by simp
  dimVec_subobjectIso X N := by
    change DoubledRep.dimVec (DoubledRep.ofVectSubrepsIso.symm (subobjectIso X N)) = _
    rw [DoubledRep.dimVec_ofVectSubrepsIso_symm, finrank_subobjectIso]
  charge _ _ := Complex.I
  im_charge_pos _ _ := by simp
  seesaw _ _ := by simp [cross]

/-- **The formal wall model of one sphere**, obtained from the realization constructor: the
finite-dimensional spaces, with their subspaces as subobjects. -/
def formalWallHypotheses : FormalWallHypotheses (FGModuleCat.{u} k) k pointQuiver :=
  (realizationHypotheses (k := k)).toFormalWallHypotheses

end SingleVertex

end Quiver.Preprojective
