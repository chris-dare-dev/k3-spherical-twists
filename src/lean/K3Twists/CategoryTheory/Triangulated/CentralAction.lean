/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Budget
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.FiltrationOperations
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Center.Preadditive
import Mathlib.CategoryTheory.Retract
import Mathlib.RingTheory.Ideal.Operations

/-!
# Central annihilators along twist words

A central element `z` of a category (an endomorphism of the identity functor, Mathlib's
`CatCenter`) acts on every object by `z_X : X ⟶ X`, naturally in `X`. For a ring map
`φ : R →+* CatCenter C` the annihilator of `X` is the ideal `{r : φ(r)_X = 0}`.

The obstruction this file formalizes: a word in letters that commute with `z` keeps every object
it reaches killed by `z` when the seed is, and then `z` kills every Harder–Narasimhan factor and
every phase truncation of the result. An object on which `z` acts nontrivially is therefore never
an HN factor of such a word applied to the seed, nor a direct summand of one.

## Main results

* `Functor.CommutesWithCenter Φ z`: `Φ(z_X) = z_{Φ X}` for every `X` (`Φ` is `z`-linear); closed
  under composition, and inherited by the inverse of an equivalence
  (`Functor.CommutesWithCenter.inverse`), so by inverse twists.
* `CatCenter.annihilator φ X` and `CatCenter.annihilator_map_eq`: a faithful letter that commutes
  with every `φ r` preserves annihilators, `Ann(Φ X) = Ann(X)`; `annihilator_le_map` without
  faithfulness.
* `CatCenter.app_eq_zero_of_retract`: `z` kills every retract (direct summand) of an object it
  kills.
* In a pretriangulated category: `CatCenter.app_obj₁_eq_zero`, `app_obj₃_eq_zero`. If `z` kills
  the middle vertex of a distinguished triangle `X → E → Y → X⟦1⟧` with `Hom(X, Y⟦-1⟧) = 0`, it
  kills both ends. `HNFiltration.app_chain_eq_zero`, `HNFiltration.app_factor_eq_zero`: if
  `z_E = 0`, then `z` vanishes on every prefix and every factor of every HN filtration of `E` for a
  slicing. `Slicing.app_eq_zero_of_cut`: the same for both pieces of a truncation triangle at a
  phase cut `(≥ t, < t)`.
* `CatCenter.annihilator_mul_le`: `Ann(X) · Ann(Y) ⊆ Ann(E)` along a distinguished triangle.
  Without `z`-linearity this is all an evaluation triangle gives: `Ann(E) ∩ Ann(S)` squared kills
  `T_S E`. The extension `M` of two objects killed by `z` need not be killed by `z`; that is how the
  obstruction can separate `M` from its factors.
* `CentralAnnihilatorHypotheses`: a central element `z`, letters that commute with it, a seed
  killed by `z` and a target not killed by `z`. `CentralAnnihilatorHypotheses.not_retract_factor`:
  for every word, every slicing and every HN filtration of the word applied to the seed, the
  target is not a retract of (in particular not isomorphic to) any factor.

## The linearity criterion

For a spherical twist `T_S`, the criterion is: `z_S = 0` and `Ext^{-1}(S, S) = 0` imply that
`T_S` and `T_S⁻¹` are `z`-linear. It is not proved here and enters only as the field
`CentralAnnihilatorHypotheses.letter_commutes`. On objects, `T_S(z_E)` and `z_{T_S E}` both
complete the same morphism of evaluation triangles, and fill-ins of triangles are not unique, so
the criterion needs twist functors with functorial cones, that is, a Fourier–Mukai kernel or an
enhancement. For a sheaf `S` on a curve, the twist kernel is the cone of `S^∨ ⊠ S → 𝒪_Δ`
(Seidel–Thomas, arXiv:math/0001043, §2), and the difference of the two actions of `z` on it
factors through a map `(S^∨ ⊠ S)[1] → 𝒪_Δ`, an element of `Ext^{-1}(S, S)`. Mathlib has neither
twist functors nor kernels.

## The geometric instance (fields)

Let `X → Y` contract a configuration of curves with exceptional locus `Z` over `y ∈ Y`. The
complete local ring `Ô_{Y,y}` acts centrally on `D_Z(X)`, the complexes supported on `Z`. For
`x` on a component of multiplicity one of the fundamental cycle and on no other curve, there is
`f ∈ Ô_{Y,y}` killing `𝒪_x` and every fibre centre `S`, and acting nontrivially on the curve with
an embedded point `M_{d,x}`. With the linearity criterion for the fibre letters, the theorem
says that no word in fibre twists takes `𝒪_x` to an object with `M_{d,x}` among its HN factors.
The criterion says nothing at multiplicity at least two or at a node. Every field of this
instance lacks a geometric instance in the library: Mathlib has no derived category of coherent
sheaves on a surface, no `𝒪`-linear structure on one, and no twist functors.

The instance from objects Mathlib has (`CentralAnnihilatorHypotheses.ofLinear`) is the derived
category of `R`-modules with `z` multiplication by `t ∈ R`, letters any `R`-linear functors (the
shifts, for instance), a module `N` with `tN = 0` as the seed, and a module `M` with `tM ≠ 0`
as the target.
-/

namespace CategoryTheory

open Category Limits Pretriangulated

variable {C : Type*} [Category* C]

namespace Functor

/-- **`z`-linearity**: `Φ(z_X) = z_{Φ X}` for every object `X`. -/
def CommutesWithCenter (Φ : C ⥤ C) (z : CatCenter C) : Prop :=
  ∀ X, Φ.map (z.app X) = z.app (Φ.obj X)

namespace CommutesWithCenter

variable {z : CatCenter C}

lemma id : (𝟭 C).CommutesWithCenter z := fun _ ↦ rfl

lemma comp {Φ Ψ : C ⥤ C} (hΦ : Φ.CommutesWithCenter z) (hΨ : Ψ.CommutesWithCenter z) :
    (Φ ⋙ Ψ).CommutesWithCenter z := fun X ↦ by
  simp only [comp_map, comp_obj, hΦ X, hΨ (Φ.obj X)]

/-- The inverse of a `z`-linear autoequivalence is `z`-linear: inverse twists inherit
`z`-linearity from twists. -/
lemma inverse (e : C ≌ C) (h : e.functor.CommutesWithCenter z) :
    e.inverse.CommutesWithCenter z := fun X ↦ by
  apply e.functor.map_injective
  rw [e.fun_inv_map, h]
  exact (z.naturality_assoc _ _).trans (by simp)

end CommutesWithCenter

end Functor

namespace CatCenter

section ZeroMorphisms

variable [HasZeroMorphisms C] (z : CatCenter C)

/-- `z` kills every object isomorphic to one it kills. -/
lemma app_eq_zero_of_iso {X Y : C} (e : X ≅ Y) (hX : z.app X = 0) : z.app Y = 0 := by
  rw [← cancel_epi e.hom, z.naturality, hX, zero_comp, comp_zero]

/-- `z` kills every retract (direct summand) of an object it kills. -/
lemma app_eq_zero_of_retract {X Y : C} (h : Retract X Y) (hY : z.app Y = 0) : z.app X = 0 :=
  calc z.app X = h.i ≫ h.r ≫ z.app X := by rw [h.retract_assoc]
    _ = h.i ≫ z.app Y ≫ h.r := by rw [z.naturality]
    _ = 0 := by rw [hY, zero_comp, comp_zero]

variable {z} in
/-- A letter that commutes with `z` and preserves zero morphisms keeps objects killed by `z`. -/
lemma app_map_eq_zero {Φ : C ⥤ C} [Φ.PreservesZeroMorphisms] (h : Φ.CommutesWithCenter z)
    {X : C} (hX : z.app X = 0) : z.app (Φ.obj X) = 0 := by
  rw [← h X, hX, Φ.map_zero]

variable {z} in
/-- For a faithful letter that commutes with `z`, `z_{Φ X} = 0 ↔ z_X = 0`. -/
lemma app_map_eq_zero_iff {Φ : C ⥤ C} [Φ.PreservesZeroMorphisms] [Φ.Faithful]
    (h : Φ.CommutesWithCenter z) (X : C) : z.app (Φ.obj X) = 0 ↔ z.app X = 0 :=
  ⟨fun hX ↦ Φ.map_injective (by rw [h X, hX, Φ.map_zero]), app_map_eq_zero h⟩

end ZeroMorphisms

section Annihilator

variable [Preadditive C] {R : Type*} [CommRing R] (φ : R →+* CatCenter C)

/-- **The annihilator** of `X` for a central action `φ : R →+* CatCenter C`: the ideal of `r`
with `φ(r)_X = 0`. -/
def annihilator (X : C) : Ideal R where
  carrier := {r | (φ r).app X = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add, app_add] at ha hb ⊢
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' c r hr := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, mul_app] at hr ⊢
    rw [hr, comp_zero]

variable {φ} in
@[simp]
lemma mem_annihilator {X : C} {r : R} : r ∈ annihilator φ X ↔ (φ r).app X = 0 := Iff.rfl

/-- Isomorphic objects have the same annihilator. -/
lemma annihilator_congr {X Y : C} (e : X ≅ Y) : annihilator φ X = annihilator φ Y :=
  Ideal.ext fun _ ↦ ⟨app_eq_zero_of_iso _ e, app_eq_zero_of_iso _ e.symm⟩

/-- A letter commuting with the action can only enlarge the annihilator. -/
lemma annihilator_le_map {Φ : C ⥤ C} [Φ.PreservesZeroMorphisms]
    (h : ∀ r, Φ.CommutesWithCenter (φ r)) (X : C) :
    annihilator φ X ≤ annihilator φ (Φ.obj X) :=
  fun r hr ↦ app_map_eq_zero (h r) hr

/-- **Annihilators along letters**: a faithful letter commuting with the action preserves
annihilators, `Ann(Φ X) = Ann(X)`. -/
lemma annihilator_map_eq {Φ : C ⥤ C} [Φ.PreservesZeroMorphisms] [Φ.Faithful]
    (h : ∀ r, Φ.CommutesWithCenter (φ r)) (X : C) :
    annihilator φ (Φ.obj X) = annihilator φ X :=
  Ideal.ext fun r ↦ app_map_eq_zero_iff (h r) X

end Annihilator

/-! ### Triangles, HN filtrations and truncations -/

section Pretriangulated

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] (z : CatCenter C)

omit [HasZeroObject C] [Pretriangulated C] in
/-- If every map `X ⟶ Y⟦-1⟧` vanishes, so does every map `X⟦1⟧ ⟶ Y`. -/
lemma _root_.CategoryTheory.Pretriangulated.hom_shift_one_eq_zero {X Y : C}
    (h : ∀ f : X ⟶ Y⟦(-1 : ℤ)⟧, f = 0) (f : X⟦(1 : ℤ)⟧ ⟶ Y) : f = 0 := by
  have e := (shiftFunctorCompIsoId C (1 : ℤ) (-1) (by lia)).app X
  have h' : f⟦(-1 : ℤ)⟧' = 0 := by
    rw [← cancel_epi e.inv]
    simpa using h (e.inv ≫ f⟦(-1 : ℤ)⟧')
  exact (shiftFunctor C (-1 : ℤ)).map_injective (by rw [h', Functor.map_zero])

/-- **The first vertex.** If `z` kills `T.obj₂` and `Hom(T.obj₁, T.obj₃⟦-1⟧) = 0`, then `z` kills
`T.obj₁`. -/
lemma app_obj₁_eq_zero (T : Triangle C) (hT : T ∈ distTriang C) (h₂ : z.app T.obj₂ = 0)
    (hvan : ∀ f : T.obj₁ ⟶ T.obj₃⟦(-1 : ℤ)⟧, f = 0) : z.app T.obj₁ = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : T.obj₁ ⟶ T.obj₃⟦(-1 : ℤ)⟧, z.app T.obj₁ = g ≫ T.invRotate.mor₁ :=
    Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT) (z.app T.obj₁)
      (show z.app T.obj₁ ≫ T.mor₁ = 0 by rw [← z.naturality, h₂, comp_zero])
  rw [hg, hvan g]
  exact zero_comp

/-- **The third vertex.** If `z` kills `T.obj₂` and `Hom(T.obj₁, T.obj₃⟦-1⟧) = 0`, then `z` kills
`T.obj₃`. -/
lemma app_obj₃_eq_zero (T : Triangle C) (hT : T ∈ distTriang C) (h₂ : z.app T.obj₂ = 0)
    (hvan : ∀ f : T.obj₁ ⟶ T.obj₃⟦(-1 : ℤ)⟧, f = 0) : z.app T.obj₃ = 0 := by
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ hT (z.app T.obj₃)
    (by rw [z.naturality, h₂, zero_comp])
  rw [hg, hom_shift_one_eq_zero hvan g, comp_zero]

/-- **Products of annihilators along a triangle.** If `z` kills `T.obj₁` and `z'` kills `T.obj₃`,
then `z * z'` kills `T.obj₂`. -/
lemma app_obj₂_mul_eq_zero (z' : CatCenter C) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : z.app T.obj₁ = 0) (h₃ : z'.app T.obj₃ = 0) : (z * z').app T.obj₂ = 0 := by
  obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₂ _ hT (z'.app T.obj₂)
    (by rw [← z'.naturality, h₃, comp_zero])
  rw [mul_app', hu, assoc, z.naturality, h₁, zero_comp, comp_zero]

/-- `Ann(T.obj₁) · Ann(T.obj₃) ⊆ Ann(T.obj₂)`. -/
lemma annihilator_mul_le {R : Type*} [CommRing R] (φ : R →+* CatCenter C) (T : Triangle C)
    (hT : T ∈ distTriang C) :
    annihilator φ T.obj₁ * annihilator φ T.obj₃ ≤ annihilator φ T.obj₂ :=
  Ideal.mul_le.2 fun r hr s hs ↦ by
    rw [mem_annihilator, map_mul]
    exact app_obj₂_mul_eq_zero _ _ T hT hr hs

end Pretriangulated

end CatCenter

namespace Triangulated

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- **Central annihilators along an HN filtration, prefixes.** If `z_E = 0`, then `z` kills every
chain object of every HN filtration of `E` for a slicing. -/
theorem HNFiltration.app_chain_eq_zero (s : Slicing C) (z : CatCenter C) {E : C}
    (F : HNFiltration C s.P E) (hE : z.app E = 0) :
    ∀ (k : ℕ) (hk : k ≤ F.n), z.app (F.chain.obj' k (by lia)) = 0 := by
  -- the step condition `Hom(E_k, A_k⟦-1⟧) = 0` for each triangle `E_k → E_{k+1} → A_k`
  have hvan : ∀ i : Fin F.n,
      ∀ f : (F.triangle i).obj₁ ⟶ (F.triangle i).obj₃⟦(-1 : ℤ)⟧, f = 0 := by
    intro i f
    let e₁ := (F.triangle_obj₁ i).some
    have h := PostnikovTower.chain_hom_eq_zero F.toPostnikovTower
      ((F.triangle i).obj₃⟦(-1 : ℤ)⟧) i.val (by lia) (fun j hj g ↦
        s.hom_vanishing (F.φ j) (F.φ i + ((-1 : ℤ) : ℝ)) _ _
          (by have := F.hφ (show j < i from hj); push_cast; linarith)
          (F.semistable j) ((s.shift_int C (F.φ i) _ (-1)).1 (F.semistable i)) g)
      (e₁.inv ≫ f)
    rw [← cancel_epi e₁.inv, h, comp_zero]
  suffices h : ∀ (m k : ℕ) (hk : k ≤ F.n), F.n - k = m → z.app (F.chain.obj' k (by lia)) = 0 from
    fun k hk ↦ h _ k hk rfl
  intro m
  induction m with
  | zero =>
    intro k hk hm
    have hkn : k = F.n := by lia
    subst hkn
    exact z.app_eq_zero_of_iso F.top_iso.some.symm hE
  | succ m ih =>
    intro k hk hm
    have hkn : k < F.n := by lia
    let i : Fin F.n := ⟨k, hkn⟩
    have h₂ : z.app (F.triangle i).obj₂ = 0 :=
      z.app_eq_zero_of_iso (F.triangle_obj₂ i).some.symm (ih (k + 1) (by lia) (by lia))
    exact z.app_eq_zero_of_iso (F.triangle_obj₁ i).some
      (z.app_obj₁_eq_zero _ (F.triangle_dist i) h₂ (hvan i))

/-- **Central annihilators along an HN filtration, factors.** If `z_E = 0`, then `z` kills every
factor of every HN filtration of `E` for a slicing. -/
theorem HNFiltration.app_factor_eq_zero (s : Slicing C) (z : CatCenter C) {E : C}
    (F : HNFiltration C s.P E) (hE : z.app E = 0) (i : Fin F.n) :
    z.app (F.factor i) = 0 := by
  have h₂ : z.app (F.triangle i).obj₂ = 0 :=
    z.app_eq_zero_of_iso (F.triangle_obj₂ i).some.symm
      (F.app_chain_eq_zero s z hE (i.val + 1) (by lia))
  refine z.app_obj₃_eq_zero _ (F.triangle_dist i) h₂ fun f ↦ ?_
  let e₁ := (F.triangle_obj₁ i).some
  have h := PostnikovTower.chain_hom_eq_zero F.toPostnikovTower
    ((F.triangle i).obj₃⟦(-1 : ℤ)⟧) i.val (by lia) (fun j hj g ↦
      s.hom_vanishing (F.φ j) (F.φ i + ((-1 : ℤ) : ℝ)) _ _
        (by have := F.hφ (show j < i from hj); push_cast; linarith)
        (F.semistable j) ((s.shift_int C (F.φ i) _ (-1)).1 (F.semistable i)) g)
    (e₁.inv ≫ f)
  rw [← cancel_epi e₁.inv, h, comp_zero]

/-- **Central annihilators along a truncation.** For a distinguished triangle `X → E → Y → X⟦1⟧`
with `X` of phases at least `t` and `Y` of phases below `t`, if `z_E = 0` then `z_X = 0` and
`z_Y = 0`. -/
theorem Slicing.app_eq_zero_of_cut (s : Slicing C) (t : ℝ) (z : CatCenter C) (T : Triangle C)
    (hT : T ∈ distTriang C) (h₁ : s.geProp C t T.obj₁) (h₃ : s.ltProp C t T.obj₃)
    (h₂ : z.app T.obj₂ = 0) : z.app T.obj₁ = 0 ∧ z.app T.obj₃ = 0 := by
  have hvan : ∀ f : T.obj₁ ⟶ T.obj₃⟦(-1 : ℤ)⟧, f = 0 := fun f ↦
    s.zero_of_geProp_ltProp_at C t h₁
      (s.ltProp_mono C (by push_cast; linarith) _ (s.ltProp_shift C t _ (-1) h₃)) f
  exact ⟨z.app_obj₁_eq_zero T hT h₂ hvan, z.app_obj₃_eq_zero T hT h₂ hvan⟩

end Triangulated

/-! ### The annihilator obstruction -/

/-- **Inputs of the annihilator obstruction** for twist words: a central element `z`, letters
indexed by `ι` that commute with `z` (the linearity criterion, a field), a seed killed by `z` and a
target on which `z` acts nontrivially. Words act right to left: `word (i :: w)` applies `word w`
first, then the letter `i`. -/
structure CentralAnnihilatorHypotheses (C : Type*) [Category* C] [Preadditive C] (ι : Type*) where
  /-- The central element, for instance multiplication by `f ∈ Ô_{Y,y}`. -/
  z : CatCenter C
  /-- The letters, for instance the twists and inverse twists at the fibre centres. -/
  letter : ι → C ⥤ C
  letter_preservesZeroMorphisms : ∀ i, (letter i).PreservesZeroMorphisms
  /-- **The linearity criterion** (a field): each letter commutes with `z`. For a twist at a
  centre `S` it follows from `z_S = 0` and `Ext^{-1}(S, S) = 0` through the twist kernel
  (Seidel–Thomas, arXiv:math/0001043, §2); that argument needs functorial cones. -/
  letter_commutes : ∀ i, (letter i).CommutesWithCenter z
  /-- The seed, for instance a point `𝒪_x`. -/
  seed : C
  /-- `z` kills the seed. -/
  app_seed : z.app seed = 0
  /-- The target, for instance the curve with an embedded point `M_{d,x}`. -/
  target : C
  /-- `z` does not kill the target. -/
  app_target : z.app target ≠ 0

namespace CentralAnnihilatorHypotheses

variable [Preadditive C] {ι : Type*} (H : CentralAnnihilatorHypotheses C ι)

/-- The word `i₁ i₂ ⋯ iₙ`, applied right to left. -/
def word : List ι → C ⥤ C
  | [] => 𝟭 C
  | i :: w => word w ⋙ H.letter i

lemma word_commutes : ∀ w : List ι, (H.word w).CommutesWithCenter H.z
  | [] => Functor.CommutesWithCenter.id
  | i :: w => (word_commutes w).comp (H.letter_commutes i)

instance (w : List ι) : (H.word w).PreservesZeroMorphisms := by
  induction w with
  | nil => exact inferInstanceAs (𝟭 C).PreservesZeroMorphisms
  | cons i w ih =>
    have := H.letter_preservesZeroMorphisms i
    exact inferInstanceAs (H.word w ⋙ H.letter i).PreservesZeroMorphisms

/-- Every word keeps the seed killed by `z`. -/
lemma app_word_seed (w : List ι) : H.z.app ((H.word w).obj H.seed) = 0 :=
  CatCenter.app_map_eq_zero (H.word_commutes w) H.app_seed

/-- The target is not a retract of an object killed by `z`. -/
lemma not_retract_of_app_eq_zero {X : C} (hX : H.z.app X = 0) : IsEmpty (Retract H.target X) :=
  ⟨fun h ↦ H.app_target (H.z.app_eq_zero_of_retract h hX)⟩

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- **The annihilator obstruction.** For every word `w`, every slicing and every HN filtration of
`w(seed)`, the target is not a retract (direct summand) of any factor; in particular it is not
isomorphic to one. -/
theorem not_retract_factor (w : List ι) (s : Triangulated.Slicing C)
    (F : Triangulated.HNFiltration C s.P ((H.word w).obj H.seed)) (i : Fin F.n) :
    IsEmpty (Retract H.target (F.factor i)) :=
  H.not_retract_of_app_eq_zero (F.app_factor_eq_zero s H.z (H.app_word_seed w) i)

/-- The target is not isomorphic to any HN factor of a word applied to the seed. -/
theorem not_iso_factor (w : List ι) (s : Triangulated.Slicing C)
    (F : Triangulated.HNFiltration C s.P ((H.word w).obj H.seed)) (i : Fin F.n) :
    IsEmpty (H.target ≅ F.factor i) :=
  ⟨fun e ↦ (H.not_retract_factor w s F i).false
    { i := e.hom, r := e.inv, retract := e.hom_inv_id }⟩

/-! ### The instance from modules -/

end CentralAnnihilatorHypotheses

namespace CentralAnnihilatorHypotheses

open DerivedCategory

variable {R : Type*} [CommRing R] [HasDerivedCategory (ModuleCat R)]

/-- On `D(R-Mod)`, multiplication by `t ∈ R` commutes with every `R`-linear functor. -/
lemma commutesWithCenter_of_linear (t : R) (Φ : DerivedCategory (ModuleCat R) ⥤
    DerivedCategory (ModuleCat R)) [Φ.Linear R] :
    Φ.CommutesWithCenter (Linear.toCatCenter R _ t) := fun X ↦ by
  simp [Functor.map_smul]

/-- Multiplication by `t` on a module placed in degree zero vanishes iff `t` kills the module. -/
lemma toCatCenter_app_singleFunctor_eq_zero_iff (t : R) (N : ModuleCat R) :
    (Linear.toCatCenter R _ t).app ((singleFunctor (ModuleCat R) 0).obj N) = 0 ↔
      ∀ n : N, t • n = 0 := by
  have key : (Linear.toCatCenter R _ t).app ((singleFunctor (ModuleCat R) 0).obj N) =
      (singleFunctor (ModuleCat R) 0).map (t • 𝟙 N) := by
    simp [Functor.map_smul]
  rw [key]
  constructor
  · intro h n
    have h' : t • 𝟙 N = 0 :=
      (singleFunctor (ModuleCat R) 0).map_injective (by rw [h, Functor.map_zero])
    simpa using congrArg (fun f ↦ f.hom n) h'
  · intro h
    have h' : t • 𝟙 N = 0 := by
      ext n
      simpa using h n
    rw [h', Functor.map_zero]

/-- **The instance from modules.** On the derived category of `R`-modules, with `z` the
multiplication by `t`, any family of `R`-linear letters, a seed module `N` with `tN = 0` and a
target module `M` with `tM ≠ 0`, both in degree zero. -/
noncomputable def ofLinear {ι : Type*} (t : R)
    (letter : ι → DerivedCategory (ModuleCat R) ⥤ DerivedCategory (ModuleCat R))
    [∀ i, (letter i).Additive] [∀ i, (letter i).Linear R] (N M : ModuleCat R)
    (hN : ∀ n : N, t • n = 0) (hM : ∃ m : M, t • m ≠ 0) :
    CentralAnnihilatorHypotheses (DerivedCategory (ModuleCat R)) ι where
  z := Linear.toCatCenter R _ t
  letter := letter
  letter_preservesZeroMorphisms _ := inferInstance
  letter_commutes i := commutesWithCenter_of_linear t (letter i)
  seed := (singleFunctor (ModuleCat R) 0).obj N
  app_seed := (toCatCenter_app_singleFunctor_eq_zero_iff t N).2 hN
  target := (singleFunctor (ModuleCat R) 0).obj M
  app_target h := by
    obtain ⟨m, hm⟩ := hM
    exact hm ((toCatCenter_app_singleFunctor_eq_zero_iff t M).1 h m)

end CentralAnnihilatorHypotheses

end CategoryTheory
