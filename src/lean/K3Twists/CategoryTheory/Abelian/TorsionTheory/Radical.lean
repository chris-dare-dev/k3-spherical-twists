/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Abelian.TorsionTheory.Saturation
import K3Twists.CategoryTheory.ObjectProperty.Coreflection
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.TorsionTheory.Basic
import Mathlib.CategoryTheory.ObjectProperty.Subobject

/-!
# The radical as a coreflection

Let `P` be a class of objects of an abelian category `C`. A coreflection `ε : D ⟶ R` of `R` into
`P` (`ObjectProperty.IsCoreflection`, a representing object of `Hom(-, R)` on `P`) is the
inclusion of the radical `t(R)` as soon as `P` has one closure property:

* `IsCoreflection.mono_of_subobjects`, `IsCoreflection.mono_of_quotients`: the counit `ε` is a
  monomorphism if `P` is closed under subobjects, and also if `P` is closed under quotients;
* `IsCoreflection.isGreatest`: a monic coreflection is the largest subobject of `R` in `P`;
  conversely the largest subobject in `P` is a coreflection when `P` is closed under quotients
  (`isCoreflection_of_isGreatest`).

No exactness and no Serre property enters. A representing object need not exist, even for a
class closed under subobjects: `{0} ∪ {lines}` in vector spaces and `k²` (the model in
`K3TwistsTest/CoreflectionModel.lean`). Two sufficient conditions for existence, neither of
which implies the other:

* `exists_isGreatest_subobject`, `isLeftAdjoint_ι_of_isNoetherianObject`: `P` contains zero and
  is closed under quotients and extensions, and `R` is Noetherian (ACC on subobjects); the
  radical is that of the interval class of `P` on `Subobject R`;
* `isGreatest_sSup`, `isLeftAdjoint_ι_of_coproducts`: `C` is well-powered with coproducts and `P`
  is closed under quotients and coproducts (Mathlib's `ObjectProperty.prop_subobjectSSup`).

Further:

* `isLUB_imageSubobject_of_generator`: if every object of `P` is a quotient of a finite sum of
  copies of `G` in `P`, the radical is the supremum of the images of the maps `G ⟶ R`,
  `t(R) = im(G ⊗ Hom(G, R) → R)`;
* `rightOrthogonal_of_isGreatest_bot`, `mk₀_comp_injective_of_rightOrthogonal`: an object `K₀`
  with `t(K₀) = 0` receives no nonzero map from `P`, so `Ext¹(-, K₀)` is left exact on short
  exact sequences that begin in `P`;
* `exists_leftOrthogonal_subobject_of_potential`, `torsionTheory_of_potential`: a torsion pair
  `(⊥F, F)` from a test class and an `ℕ`-valued potential that drops on kernels, in place of a
  chain condition.

## Scope

The existence theorems are conditional: the first needs Noetherian objects, and nothing here
shows that a given heart of a stability condition is Noetherian. The representing object of
`Ext¹(-, K₀)` on `P` is not constructed here; only the left exactness is proved.

## References

* S. E. Dickson, *A torsion theory for Abelian categories*, Trans. Amer. Math. Soc. 121 (1966).
* B. Stenström, *Rings of Quotients*, Springer (1975), Chapter VI.

## Tags

torsion theory, radical, coreflection, representing object, Noetherian object, torsion pair
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] {P : ObjectProperty C}

namespace IsCoreflection

/-- With `P` closed under subobjects a coreflection is a monomorphism: its kernel lies in `P` and
has zero composite with `ε`. -/
theorem mono_of_subobjects [P.IsClosedUnderSubobjects] {D R : C} {ε : D ⟶ R}
    (h : P.IsCoreflection ε) : Mono ε := by
  apply Abelian.mono_of_kernel_ι_eq_zero
  exact h.hom_ext (P.prop_of_mono (kernel.ι ε) h.prop) (by simp)

/-- With `P` closed under quotients a coreflection is a monomorphism: its image lies in `P`, and
the factorization of the image through `ε` splits `D ↠ im ε`. -/
theorem mono_of_quotients [P.IsClosedUnderQuotients] {D R : C} {ε : D ⟶ R}
    (h : P.IsCoreflection ε) : Mono ε := by
  have hI : P (image ε) := P.prop_of_epi (factorThruImage ε) h.prop
  have hid : factorThruImage ε ≫ h.lift hI (image.ι ε) = 𝟙 D :=
    h.hom_ext h.prop (by simp)
  have : Mono (factorThruImage ε ≫ h.lift hI (image.ι ε)) := by rw [hid]; infer_instance
  have : Mono (factorThruImage ε) := mono_of_mono _ (h.lift hI (image.ι ε))
  rw [← image.fac ε]
  infer_instance

omit [Abelian C] in
/-- A monic coreflection is the largest subobject of `R` in `P`. -/
theorem isGreatest [P.IsClosedUnderIsomorphisms] {D R : C} {ε : D ⟶ R} [Mono ε]
    (h : P.IsCoreflection ε) : IsGreatest {A : Subobject R | P (A : C)} (Subobject.mk ε) :=
  ⟨P.prop_of_iso (Subobject.underlyingIso ε).symm h.prop,
    fun A hA => Subobject.le_mk_of_comm (h.lift hA A.arrow) (h.lift_comp hA _)⟩

end IsCoreflection

/-- The largest subobject in a quotient-closed class is a coreflection. -/
theorem isCoreflection_of_isGreatest [P.IsClosedUnderQuotients] {R : C} {t : Subobject R}
    (ht : IsGreatest {A : Subobject R | P (A : C)} t) : P.IsCoreflection t.arrow := by
  refine ⟨ht.1, fun A hA => ⟨fun g g' w => (cancel_mono t.arrow).1 w, fun f => ?_⟩⟩
  have hle : imageSubobject f ≤ t := ht.2 (P.prop_of_epi (factorThruImageSubobject f) hA)
  refine ⟨factorThruImageSubobject f ≫ Subobject.ofLE _ _ hle, ?_⟩
  simp only [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]

/-- For a class closed under quotients, a subobject is a coreflection exactly when it is the
largest subobject in the class. -/
theorem isCoreflection_arrow_iff [P.IsClosedUnderQuotients] {R : C} (t : Subobject R) :
    P.IsCoreflection t.arrow ↔ IsGreatest {A : Subobject R | P (A : C)} t := by
  refine ⟨fun h => ?_, isCoreflection_of_isGreatest⟩
  simpa using h.isGreatest

/-! ### Existence on Noetherian objects -/

section Noetherian

variable [P.ContainsZero] [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]

/-- `A ⊔ B` lies in `P` when `A` and `B` do, as a quotient of `A ⊕ B`: the candidates of the
interval class are closed under `⊔`. -/
theorem prop_sup {R : C} {A B : Subobject R} (hA : P (A : C)) (hB : P (B : C)) :
    P ((A ⊔ B : Subobject R) : C) :=
  (subQ_bot_iff _).1 ((P.intervalClass R).supClosed_cands ⊥ ⊤
    ⟨bot_le, le_top, (subQ_bot_iff A).2 hA⟩ ⟨bot_le, le_top, (subQ_bot_iff B).2 hB⟩).2.2

/-- **Existence of the radical on a Noetherian object.** If `P` contains zero and is closed under
quotients and extensions, a Noetherian object `R` has a largest subobject in `P`. Closure under
subobjects is neither needed nor sufficient. -/
theorem exists_isGreatest_subobject (R : C) [IsNoetherianObject R] :
    ∃ t : Subobject R, IsGreatest {A : Subobject R | P (A : C)} t :=
  ⟨_, isGreatest_intervalClass_rad R⟩

/-- On a Noetherian object the radical of the interval class is a coreflection. -/
theorem isCoreflection_intervalClass_rad (R : C) [IsNoetherianObject R] :
    P.IsCoreflection (P.intervalClass R).rad.arrow :=
  isCoreflection_of_isGreatest (isGreatest_intervalClass_rad R)

/-- On a Noetherian object the partial right adjoint of `P.ι` is defined. -/
theorem rightAdjointObjIsDefined_of_isNoetherianObject (R : C) [IsNoetherianObject R] :
    P.ι.rightAdjointObjIsDefined R :=
  (isCoreflection_intervalClass_rad R).rightAdjointObjIsDefined

/-- **Coreflectivity.** In an abelian category whose objects are Noetherian, a class containing
zero and closed under quotients and extensions is coreflective, with counit the radical. -/
theorem isLeftAdjoint_ι_of_isNoetherianObject [∀ R : C, IsNoetherianObject R] :
    P.ι.IsLeftAdjoint :=
  isLeftAdjoint_ι_iff.2 fun R => ⟨_, _, isCoreflection_intervalClass_rad R⟩

end Noetherian

/-! ### Existence from coproducts -/

section Coproducts

variable [WellPowered.{v} C] [HasCoproducts.{v} C] [P.IsClosedUnderQuotients]
  [∀ J : Type v, P.IsClosedUnderColimitsOfShape (Discrete J)]

/-- **Existence from coproducts.** In a well-powered abelian category with coproducts, if `P` is
closed under quotients and coproducts, the supremum of the subobjects of `R` in `P` is the
largest one. No chain condition and no extension closure is used. -/
theorem isGreatest_sSup (R : C) :
    IsGreatest {A : Subobject R | P (A : C)}
      (Subobject.sSup.{v} {A : Subobject R | P (A : C)}) :=
  ⟨ObjectProperty.prop_subobjectSSup.{v} P _ fun _ hA => hA,
    fun _ hA => Subobject.le_sSup.{v} _ _ hA⟩

/-- In a well-powered abelian category with coproducts, a class closed under quotients and
coproducts is coreflective. -/
theorem isLeftAdjoint_ι_of_coproducts : P.ι.IsLeftAdjoint :=
  isLeftAdjoint_ι_iff.2 fun R => ⟨_, _, isCoreflection_of_isGreatest (isGreatest_sSup R)⟩

end Coproducts

/-! ### The radical from a generator -/

/-- **The radical from a generator.** Let `P` be closed under quotients, `G` in `P`, and every
object of `P` a quotient of a finite sum `G ⊕ ⋯ ⊕ G`. Then the largest subobject `t` of `R` in
`P` is the supremum of the images of the morphisms `G ⟶ R`, that is
`t(R) = im(G ⊗ Hom(G, R) → R)`. Projectivity of `G` is not used. -/
theorem isLUB_imageSubobject_of_generator [P.IsClosedUnderQuotients] {G R : C} (hG : P G)
    (hgen : ∀ ⦃X : C⦄, P X → ∃ (n : ℕ) (π : (∐ fun _ : Fin n => G) ⟶ X), Epi π)
    {t : Subobject R} (ht : IsGreatest {A : Subobject R | P (A : C)} t) :
    IsLUB (Set.range fun f : G ⟶ R => imageSubobject f) t := by
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨f, rfl⟩
    exact ht.2 (P.prop_of_epi (factorThruImageSubobject f) hG)
  · obtain ⟨n, π, hπ⟩ := hgen ht.1
    have hf : ∀ j, u.Factors (Sigma.ι (fun _ : Fin n => G) j ≫ π ≫ t.arrow) := fun j =>
      Subobject.factors_of_le _ (hu ⟨_, rfl⟩)
        ((Subobject.factors_iff _ _).2 ⟨_, imageSubobject_arrow_comp _⟩)
    let g : (∐ fun _ : Fin n => G) ⟶ (u : C) := Sigma.desc fun j => u.factorThru _ (hf j)
    have hg : g ≫ u.arrow = π ≫ t.arrow :=
      Sigma.hom_ext _ _ fun j => by simp [g]
    have hk : kernel.ι π ≫ g = 0 := by
      rw [← cancel_mono u.arrow, Category.assoc, hg, ← Category.assoc, kernel.condition,
        zero_comp, zero_comp]
    refine Subobject.le_of_comm (Abelian.epiDesc π g hk) ?_
    rw [← cancel_epi π, ← Category.assoc, Abelian.comp_epiDesc, hg]

/-! ### Torsion-free objects and `Ext¹` -/

/-- An object `K` whose only subobject in a quotient-closed class `P` is `0` (`t(K) = 0`)
receives no nonzero morphism from an object of `P`. -/
theorem rightOrthogonal_of_isGreatest_bot [P.IsClosedUnderQuotients] {K : C}
    (hK : IsGreatest {B : Subobject K | P (B : C)} ⊥) : P.rightOrthogonal K := by
  refine (rightOrthogonal_iff _ _).2 fun A f hA => ?_
  have hle : imageSubobject f ≤ ⊥ := hK.2 (P.prop_of_epi (factorThruImageSubobject f) hA)
  rw [← imageSubobject_arrow_comp f, ← Subobject.ofLE_arrow hle, Subobject.bot_arrow]
  simp

/-- **`Ext¹(-, K₀)` is left exact on `P`.** Let `0 → X₁ → X₂ → X₃ → 0` be short exact with `X₁`
in `P`, and let `K₀` receive no nonzero morphism from `P` (for instance `t(K₀) = 0`). Then
pulling back along `X₂ → X₃` is injective on `Ext¹(X₃, K₀)`: the connecting map starts at
`Hom(X₁, K₀) = 0`. -/
theorem mk₀_comp_injective_of_rightOrthogonal [HasExt.{w} C] {S : ShortComplex C}
    (hS : S.ShortExact) (hX₁ : P S.X₁) {K₀ : C} (hK : P.rightOrthogonal K₀) :
    Function.Injective fun x : Abelian.Ext.{w} S.X₃ K₀ 1 =>
      (Abelian.Ext.mk₀ S.g).comp x (zero_add 1) := by
  have key : ∀ x : Abelian.Ext.{w} S.X₃ K₀ 1,
      (Abelian.Ext.mk₀ S.g).comp x (zero_add 1) = 0 → x = 0 := by
    intro x hx
    obtain ⟨x₁, hx₁⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS K₀ x hx (n₀ := 0) rfl
    have h₀ : x₁ = 0 := by
      rw [← Abelian.Ext.mk₀_homEquiv₀_apply x₁,
        (rightOrthogonal_iff _ _).1 hK (Abelian.Ext.homEquiv₀ x₁) hX₁, Abelian.Ext.mk₀_zero]
    rw [← hx₁, h₀, Abelian.Ext.comp_zero]
  intro x y hxy
  have h := key (x - y) (by
    simp only at hxy
    rw [sub_eq_add_neg, Abelian.Ext.comp_add, Abelian.Ext.comp_neg, hxy, add_neg_cancel])
  exact sub_eq_zero.1 h

/-! ### A torsion pair from a potential -/

section Potential

variable (F 𝒬 : ObjectProperty C) [F.ContainsZero] [F.IsClosedUnderIsomorphisms]
  [F.IsClosedUnderExtensions] (L : C → ℕ)

/-- **Torsion decomposition from a potential.** Let `F` contain zero and be closed under
extensions, and let `𝒬` be a test class: an object with no nonzero morphism to `𝒬` has no
nonzero morphism to `F`. Suppose that every nonzero `f : Y ⟶ q` with `q` in `𝒬` has image in
`F`, and that the potential `L : C → ℕ` drops strictly from `Y` to `ker f`. Then every `Y` has a
subobject `K ↪ Y` with no nonzero morphism to `F` and `Y / K` in `F`: iterate kernels of nonzero
maps to `𝒬`, which stops after at most `L Y` steps; `Y / K` is an iterated extension of the
images. The potential replaces a chain condition. -/
theorem exists_leftOrthogonal_subobject_of_potential
    (htest : ∀ Y : C, (∀ ⦃q : C⦄, 𝒬 q → ∀ f : Y ⟶ q, f = 0) → F.leftOrthogonal Y)
    (hstep : ∀ ⦃Y q : C⦄ (f : Y ⟶ q), 𝒬 q → f ≠ 0 → F (image f) ∧ L (kernel f) < L Y)
    (Y : C) : ∃ (K : C) (i : K ⟶ Y), Mono i ∧ F.leftOrthogonal K ∧ F (cokernel i) := by
  suffices h : ∀ n, ∀ Y : C, L Y = n →
      ∃ (K : C) (i : K ⟶ Y), Mono i ∧ F.leftOrthogonal K ∧ F (cokernel i) from h _ Y rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hY
  by_cases h0 : ∀ ⦃q : C⦄, 𝒬 q → ∀ f : Y ⟶ q, f = 0
  · exact ⟨Y, 𝟙 Y, inferInstance, htest Y h0, F.prop_of_isZero (isZero_cokernel_of_epi _)⟩
  · push Not at h0
    obtain ⟨q, hq, f, hf⟩ := h0
    obtain ⟨hFim, hL⟩ := hstep f hq hf
    obtain ⟨K, i, hi, hK, hcok⟩ := ih (L (kernel f)) (hY ▸ hL) (kernel f) rfl
    refine ⟨K, i ≫ kernel.ι f, inferInstance, hK, ?_⟩
    have h₁ : F.SubQ (Subobject.mk (i ≫ kernel.ι f)) (Subobject.mk (kernel.ι f)) :=
      (subQ_mk_iff i rfl).2 hcok
    have h₂ : F.SubQ (Subobject.mk (kernel.ι f)) (Subobject.mk (𝟙 Y)) :=
      (subQ_mk_iff (kernel.ι f) (Category.comp_id _)).2
        (F.prop_of_iso (Abelian.coimageIsoImage' f).symm hFim)
    exact (subQ_mk_iff (i ≫ kernel.ι f) (Category.comp_id _)).1 (subQ_trans h₁.le h₂.le h₁ h₂)

/-- **A torsion pair from a potential.** Under the hypotheses of
`exists_leftOrthogonal_subobject_of_potential`, the objects with no nonzero morphism to `F` and
the class `F` form a torsion pair `(⊥F, F)`; in particular `F` is a torsion-free class. -/
theorem torsionTheory_of_potential
    (htest : ∀ Y : C, (∀ ⦃q : C⦄, 𝒬 q → ∀ f : Y ⟶ q, f = 0) → F.leftOrthogonal Y)
    (hstep : ∀ ⦃Y q : C⦄ (f : Y ⟶ q), 𝒬 q → f ≠ 0 → F (image f) ∧ L (kernel f) < L Y) :
    Abelian.TorsionTheory F.leftOrthogonal F where
  leftOrthogonal_eq := rfl
  rightOrthogonal_eq := by
    ext Y
    refine ⟨fun hY => ?_, fun hY => (rightOrthogonal_iff _ _).2 fun X f hX =>
      (leftOrthogonal_iff _ _).1 hX f hY⟩
    obtain ⟨K, i, -, hK, hcok⟩ :=
      exists_leftOrthogonal_subobject_of_potential F 𝒬 L htest hstep Y
    have hi : i = 0 := (rightOrthogonal_iff _ _).1 hY i hK
    exact F.prop_of_iso (cokernelIsoOfEq hi ≪≫ cokernelZeroIsoTarget) hcok

end Potential

end CategoryTheory.ObjectProperty
