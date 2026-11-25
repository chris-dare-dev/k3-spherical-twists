/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.ObjectProperty.Coreflection
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.TorsionTheory.Basic

/-!
# Serre classes and torsion pairs from short exact sequences

Two constructions in an abelian category `A`:

* `ObjectProperty.isSerreClass_of_additive_nonneg`: if `w : A → M` takes values in an ordered
  additive group, is additive on short exact sequences (`w X₂ = w X₁ + w X₃`) and is
  nonnegative, then its kernel `{X | w X = 0}` is a Serre class. A short exact sequence with
  middle term in the kernel has both ends in it, because `w X₁` and `w X₃` are nonnegative with
  zero sum; conversely the kernel is closed under extensions. This is how the imaginary part of
  a central charge cuts out the phase-one objects of a heart.
* `Abelian.TorsionTheory.of_shortExact`: two classes closed under isomorphisms with no nonzero
  map from the first to the second, such that every object sits in a short exact sequence
  `0 → T' → X → F' → 0` with `T'` in the first and `F'` in the second, form a torsion pair in
  Mathlib's sense (Dickson, Trans. Amer. Math. Soc. 121 (1966)).
* `ObjectProperty.isCoreflection_of_shortExact`: in a torsion sequence `0 → T' → X → F' → 0`, with
  no nonzero map from the class to `F'`, the map `T' → X` is a coreflection of `X` into the class:
  `T'` is the torsion radical of `X`, with no chain condition on `X`.

## Tags

Serre class, torsion pair, additive function, short exact sequence
-/

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace ObjectProperty

variable {M : Type*} [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M]

/-- A function additive on short exact sequences vanishes on zero objects. -/
theorem eq_zero_of_additive_of_isZero (w : A → M)
    (hadd : ∀ S : ShortComplex A, S.ShortExact → w S.X₂ = w S.X₁ + w S.X₃) {Z : A}
    (hZ : IsZero Z) : w Z = 0 := by
  let S : ShortComplex A := ShortComplex.mk (𝟙 Z) (0 : Z ⟶ Z) (by simp)
  have hS : S.ShortExact :=
    { exact := S.exact_of_isZero_X₂ hZ
      mono_f := by dsimp [S]; infer_instance
      epi_g := ⟨fun _ _ _ => hZ.eq_of_src _ _⟩ }
  have h := hadd S hS
  simp only [S] at h
  exact left_eq_add.mp h

/-- **The kernel of a nonnegative additive function is a Serre class.** If `w` is additive on
short exact sequences and `0 ≤ w`, then `{X | w X = 0}` contains zero and is closed under
subobjects, quotients and extensions. -/
theorem isSerreClass_of_additive_nonneg (w : A → M)
    (hadd : ∀ S : ShortComplex A, S.ShortExact → w S.X₂ = w S.X₁ + w S.X₃)
    (hnonneg : ∀ X, 0 ≤ w X) : IsSerreClass (fun X : A => w X = 0) where
  exists_zero := ⟨0, isZero_zero A, eq_zero_of_additive_of_isZero w hadd (isZero_zero A)⟩
  prop_of_mono {X Y} f _ hY := by
    have h := hadd (ShortComplex.mk f (cokernel.π f) (cokernel.condition f))
      (ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _
        (cokernelIsCokernel f)) inferInstance inferInstance)
    simp only at h
    exact ((add_eq_zero_iff_of_nonneg (hnonneg _) (hnonneg _)).1 (h ▸ hY)).1
  prop_of_epi {X Y} f _ hX := by
    have h := hadd (ShortComplex.mk (kernel.ι f) f (kernel.condition f))
      (ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _
        (kernelIsKernel f)) inferInstance inferInstance)
    simp only at h
    exact ((add_eq_zero_iff_of_nonneg (hnonneg _) (hnonneg _)).1 (h ▸ hX)).2
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    rw [hadd S hS, h₁, h₃, add_zero]

/-- **A torsion sequence is a coreflection.** If `0 → X₁ → X₂ → X₃ → 0` is short exact, `X₁` lies
in `T`, and no object of `T` maps nontrivially to `X₃`, then `X₁ → X₂` is a coreflection of `X₂`
into `T`. -/
theorem isCoreflection_of_shortExact {T : ObjectProperty A} {S : ShortComplex A}
    (hS : S.ShortExact) (h₁ : T S.X₁) (h₃ : ∀ ⦃Y : A⦄ (f : Y ⟶ S.X₃), T Y → f = 0) :
    T.IsCoreflection S.f := by
  have := hS.mono_f
  refine ⟨h₁, fun Y hY => ⟨fun g g' w => (cancel_mono S.f).1 w, fun g => ?_⟩⟩
  have hg : g ≫ S.g = 0 := h₃ _ hY
  exact ⟨hS.fIsKernel.lift (KernelFork.ofι g hg), Fork.IsLimit.lift_ι hS.fIsKernel⟩

end ObjectProperty

namespace Abelian.TorsionTheory

/-- **A torsion pair from torsion sequences.** Let `T` and `F` be closed under isomorphisms,
with no nonzero map from an object of `T` to an object of `F`, and let every object `X` sit in a
short exact sequence `0 → T' → X → F' → 0` with `T'` in `T` and `F'` in `F`. Then `(T, F)` is a
torsion pair. -/
theorem of_shortExact {T F : ObjectProperty A} [T.IsClosedUnderIsomorphisms]
    [F.IsClosedUnderIsomorphisms] (hTF : ∀ ⦃X Y : A⦄ (f : X ⟶ Y), T X → F Y → f = 0)
    (hseq : ∀ X : A, ∃ (X₁ X₃ : A) (i : X₁ ⟶ X) (p : X ⟶ X₃) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧ T X₁ ∧ F X₃) :
    TorsionTheory T F where
  leftOrthogonal_eq := by
    ext X
    refine ⟨fun hX => ?_, fun hX Y f hY => hTF f hX hY⟩
    obtain ⟨X₁, X₃, i, p, w, hS, h₁, h₃⟩ := hseq X
    have hp : p = 0 := hX p h₃
    have hZ : IsZero X₃ := by
      have := hS.epi_g
      rw [IsZero.iff_id_eq_zero]
      exact (cancel_epi p).1 (by simp [hp])
    have : IsIso i := hS.isIso_f_iff.2 hZ
    exact T.prop_of_iso (asIso i) h₁
  rightOrthogonal_eq := by
    ext Y
    refine ⟨fun hY => ?_, fun hY X f hX => hTF f hX hY⟩
    obtain ⟨X₁, X₃, i, p, w, hS, h₁, h₃⟩ := hseq Y
    have hi : i = 0 := hY i h₁
    have hZ : IsZero X₁ := by
      have := hS.mono_f
      rw [IsZero.iff_id_eq_zero]
      exact (cancel_mono i).1 (by simp [hi])
    have : IsIso p := hS.isIso_g_iff.2 hZ
    exact F.prop_of_iso (asIso p).symm h₃

end Abelian.TorsionTheory

end CategoryTheory
