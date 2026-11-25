/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Abelian.TorsionTheory.Radical
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Coreflections: a counterexample and the torsion radical of modules

* **Closure under subobjects does not give a representing object.** In vector spaces over a
  field `k`, the class `{0} ∪ {lines}` of spaces of dimension at most one is closed under
  subobjects, and `k²` has no coreflection into it: the coreflection would be onto, since every
  vector of `k²` spans a line, and of dimension at most one.
* **The torsion radical.** Over a commutative ring `R`, the torsion modules (every element killed
  by a non-zero-divisor) contain zero and are closed under quotients and extensions. A Noetherian
  module `M` is a Noetherian object of `ModuleCat R`, so the existence theorem applies, and the
  radical of `M` is its torsion submodule; for `R = ℤ`, the torsion subgroup of a finitely
  generated abelian group.

Built by `lake test`.
-/

namespace CoreflectionModel

open CategoryTheory CategoryTheory.Limits

/-! ### `{0} ∪ {lines}` has no coreflection -/

/-- The vector spaces of dimension at most one. -/
def lines (k : Type) [Field k] : ObjectProperty (ModuleCat.{0} k) :=
  fun M => FiniteDimensional k M ∧ Module.finrank k M ≤ 1

theorem lines_closed (k : Type) [Field k] : (lines k).IsClosedUnderSubobjects where
  prop_of_mono {X Y} f hf hY := by
    have hinj : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).mp hf
    have := hY.1
    have : FiniteDimensional k X := FiniteDimensional.of_injective f.hom hinj
    exact ⟨this, (LinearMap.finrank_le_finrank_of_injective hinj).trans hY.2⟩

theorem lines_no_coreflection (k : Type) [Field k] :
    ¬ ∃ (D : ModuleCat.{0} k) (ε : D ⟶ ModuleCat.of k (Fin 2 → k)),
      (lines k).IsCoreflection ε := by
  rintro ⟨D, ε, ⟨⟨hD₁, hD₂⟩, hbij⟩⟩
  have hA : lines k (ModuleCat.of k k) :=
    ⟨inferInstanceAs (FiniteDimensional k k), by simp⟩
  have hsurj : Function.Surjective ε.hom := by
    intro v
    obtain ⟨g, hg⟩ := (hbij hA).2 (ModuleCat.ofHom (LinearMap.toSpanSingleton k _ v))
    refine ⟨g.hom 1, ?_⟩
    have := congrArg (fun h => h.hom (1 : k)) hg
    simpa using this
  have h₁ := LinearMap.finrank_range_le ε.hom
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h₁
  have h₂ : Module.finrank k (Fin 2 → k) = 2 := by rw [Module.finrank_pi]; simp
  have h₃ : Module.finrank k (Fin 2 → k) ≤ Module.finrank k D := h₁
  omega

/-! ### The torsion radical -/

variable {R : Type} [CommRing R]

variable (R) in
/-- The torsion modules: every element is killed by a non-zero-divisor. -/
def torsion : ObjectProperty (ModuleCat.{0} R) :=
  fun M => Module.IsTorsion R M

instance : (torsion R).IsClosedUnderQuotients where
  prop_of_epi {X Y} f hf hX := by
    intro y
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective f).mp hf y
    obtain ⟨a, ha⟩ := @hX x
    refine ⟨a, ?_⟩
    rw [Submonoid.smul_def] at ha ⊢
    rw [← map_smul, ha, map_zero]

instance : (torsion R).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    intro x
    obtain ⟨b, hb⟩ := @h₃ (S.g.hom x)
    rw [Submonoid.smul_def, ← map_smul] at hb
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS.exact _ hb
    obtain ⟨a, ha⟩ := @h₁ y
    rw [Submonoid.smul_def] at ha
    refine ⟨a * b, ?_⟩
    rw [Submonoid.smul_def, Submonoid.coe_mul, mul_smul, ← hy, ← map_smul, ha, map_zero]

instance : (torsion R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    fun _ => ⟨1, Subsingleton.elim _ _⟩⟩

/-- A Noetherian module is a Noetherian object of `ModuleCat R`. -/
theorem isNoetherianObject_of (M : Type) [AddCommGroup M] [Module R M] [IsNoetherian R M] :
    IsNoetherianObject (ModuleCat.of R M) := by
  let e := ModuleCat.subobjectModule (ModuleCat.of R M)
  have h : WellFounded fun A B : Subobject (ModuleCat.of R M) => B < A :=
    (InvImage.wf (fun A => e A) (wellFounded_gt (α := Submodule R M))).mono
      fun _ _ h => e.lt_iff_lt.mpr h
  exact ⟨h⟩

/-- **The torsion radical.** For a Noetherian module `M`, the radical of the class of torsion
modules on the subobjects of `M` is the torsion submodule. -/
theorem subobjectModule_rad (M : Type) [AddCommGroup M] [Module R M] [IsNoetherian R M] :
    haveI := isNoetherianObject_of (R := R) M
    ModuleCat.subobjectModule (ModuleCat.of R M)
        ((torsion R).intervalClass (ModuleCat.of R M)).rad =
      Submodule.torsion R M := by
  have := isNoetherianObject_of (R := R) M
  let e := ModuleCat.subobjectModule (ModuleCat.of R M)
  have hT : IsGreatest {A : Subobject (ModuleCat.of R M) | torsion R (A : ModuleCat R)}
      (e.symm (Submodule.torsion R M)) := by
    have : Mono (ModuleCat.ofHom (Submodule.torsion R M).subtype) :=
      (ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype _)
    refine ⟨?_, fun A hA => e.le_symm_apply.mpr ?_⟩
    · change torsion R ((Subobject.mk (ModuleCat.ofHom (Submodule.torsion R M).subtype) : _))
      exact (torsion R).prop_of_iso
        (Subobject.underlyingIso (ModuleCat.ofHom (Submodule.torsion R M).subtype)).symm
        (Submodule.torsion_isTorsion (R := R) (M := M))
    · change LinearMap.range A.arrow.hom ≤ Submodule.torsion R M
      rintro _ ⟨x, rfl⟩
      obtain ⟨a, ha⟩ := @hA x
      rw [Submonoid.smul_def] at ha
      exact (Submodule.mem_torsion_iff _).mpr ⟨a, by
        rw [Submonoid.smul_def, ← map_smul, ha, map_zero]⟩
  rw [(ObjectProperty.isGreatest_intervalClass_rad (P := torsion R) (ModuleCat.of R M)).unique hT]
  exact e.apply_symm_apply _

end CoreflectionModel
