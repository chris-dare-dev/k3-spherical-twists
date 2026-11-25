/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Subobjects of nonsplit extensions of simple objects

In an abelian category, an object glued from simple objects by nonsplit extensions can have very
few subobjects. This file proves the two cases a wall with two simple objects needs.

* `ShortComplex.ShortExact.subobject_eq_of_nonsplit`: if `0 → X₁ → X₂ → X₃ → 0` is short exact
  and does not split, and `X₁`, `X₃` are simple, then the subobjects of `X₂` are `⊥`, the image
  of `X₁` and `⊤`.
* `subobject_eq_of_nonsplit_of_nonsplit`: let `0 → A → P → B → 0` and `0 → P → M → A' → 0` be
  short exact with `A`, `B`, `A'` simple, and let `0 → A → M → U → 0` be short exact with
  `0 → B → U → A' → 0` short exact, compatible with the projections to `A'`. If `P` and `U` are
  nonsplit, then the subobjects of `M` form the single chain `⊥ < A < P < ⊤`.

No finiteness of length, no linear structure and no `Ext` groups are used: the argument works
with morphisms only. Nonsplit means that the projection has no section.
-/

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C] [Abelian C]

namespace ShortComplex

/-- **A nonsplit extension of simple objects has three subobjects.** If `0 → X₁ → X₂ → X₃ → 0` is
short exact, `X₁` and `X₃` are simple and `X₂ → X₃` has no section, every subobject of `X₂` is
`⊥`, the image of `X₁`, or `⊤`. -/
theorem ShortExact.subobject_eq_of_nonsplit {S : ShortComplex C} (hS : S.ShortExact)
    [Mono S.f] [Simple S.X₁] [Simple S.X₃] (hns : ∀ σ : S.X₃ ⟶ S.X₂, σ ≫ S.g ≠ 𝟙 S.X₃)
    (T : Subobject S.X₂) : T = ⊥ ∨ T = Subobject.mk S.f ∨ T = ⊤ := by
  have := hS.epi_g
  by_cases h : T.arrow ≫ S.g = 0
  · -- `T` lies in the image of `X₁`, which is simple
    have htf : hS.exact.lift T.arrow h ≫ S.f = T.arrow := hS.exact.lift_f _ _
    haveI : Mono (hS.exact.lift T.arrow h) := mono_of_mono_fac htf
    by_cases ht0 : hS.exact.lift T.arrow h = 0
    · left
      rw [← Subobject.mk_arrow T, Subobject.mk_eq_bot_iff_zero, ← htf, ht0, zero_comp]
    · right; left
      haveI := isIso_of_mono_of_ne_zero ht0
      rw [← Subobject.mk_arrow T]
      exact Subobject.mk_eq_mk_of_comm _ _ (asIso (hS.exact.lift T.arrow h)) htf
  · -- `T` maps onto the simple quotient `X₃`
    right; right
    haveI : Epi (T.arrow ≫ S.g) := epi_of_ne_zero_to_simple h
    have hk : (kernel.ι (T.arrow ≫ S.g) ≫ T.arrow) ≫ S.g = 0 := by simp
    have huf : hS.exact.lift _ hk ≫ S.f = kernel.ι (T.arrow ≫ S.g) ≫ T.arrow :=
      hS.exact.lift_f _ _
    haveI : Mono (hS.exact.lift _ hk) := mono_of_mono_fac huf
    by_cases hu0 : hS.exact.lift _ hk = 0
    · -- the kernel of `T → X₃` is zero, so `T → X₃` is an isomorphism and `X₂ → X₃` splits
      exfalso
      have hι : kernel.ι (T.arrow ≫ S.g) = 0 :=
        zero_of_comp_mono T.arrow (by rw [← huf, hu0, zero_comp])
      haveI : Mono (T.arrow ≫ S.g) := Preadditive.mono_of_kernel_zero hι
      haveI : IsIso (T.arrow ≫ S.g) := isIso_of_mono_of_epi _
      exact hns (inv (T.arrow ≫ S.g) ≫ T.arrow) (by simp)
    · -- the kernel of `T → X₃` is `X₁`, so `X₁ ⊆ T` and `T = X₂`
      haveI := isIso_of_mono_of_ne_zero hu0
      have hc : S.f ≫ cokernel.π T.arrow = 0 := by
        rw [← cancel_epi (hS.exact.lift _ hk), ← Category.assoc, huf]
        simp
      have hgc : S.g ≫ hS.exact.desc _ hc = cokernel.π T.arrow := hS.exact.g_desc _ _
      have hd : hS.exact.desc _ hc = 0 := by
        rw [← cancel_epi (T.arrow ≫ S.g), Category.assoc, hgc]
        simp
      haveI : Epi T.arrow := Preadditive.epi_of_cokernel_zero (by rw [← hgc, hd, comp_zero])
      haveI : IsIso T.arrow := isIso_of_mono_of_epi _
      exact Subobject.eq_top_of_isIso_arrow T

end ShortComplex

/-- **A length-three object glued from two nonsplit extensions is uniserial.** Let
`0 → A → P → B → 0` and `0 → P → M → A' → 0` be short exact, with `A`, `B`, `A'` simple. Let
`0 → A → M → U → 0` be short exact (the composite `A → P → M` and its cokernel `U = M/A`) and
`0 → B → U → A' → 0` short exact, with `M → U → A'` the projection of `M`. If `P → B` and
`U → A'` have no section, the subobjects of `M` are exactly `⊥`, `A`, `P` and `⊤`. -/
theorem subobject_eq_of_nonsplit_of_nonsplit {A B A' P M U : C} [Simple A] [Simple B]
    [Simple A'] {j : A ⟶ P} {q : P ⟶ B} {i : P ⟶ M} {p : M ⟶ A'} {k : B ⟶ U} {l : U ⟶ A'}
    {π : M ⟶ U} [Mono j] [Mono i] (wjq : j ≫ q = 0) (wip : i ≫ p = 0) (wkl : k ≫ l = 0)
    (wπ : (j ≫ i) ≫ π = 0) (hP : (ShortComplex.mk j q wjq).ShortExact)
    (hM : (ShortComplex.mk i p wip).ShortExact) (hU : (ShortComplex.mk k l wkl).ShortExact)
    (hπ : (ShortComplex.mk (j ≫ i) π wπ).ShortExact) (hπl : π ≫ l = p)
    (hPns : ∀ σ : B ⟶ P, σ ≫ q ≠ 𝟙 B) (hUns : ∀ σ : A' ⟶ U, σ ≫ l ≠ 𝟙 A')
    (T : Subobject M) :
    T = ⊥ ∨ T = Subobject.mk (j ≫ i) ∨ T = Subobject.mk i ∨ T = ⊤ := by
  have := hU.mono_f
  have := hπ.epi_g
  by_cases h : T.arrow ≫ p = 0
  · -- `T` lies in `P`, whose subobjects are `⊥`, `A` and `P`
    have hti : hM.exact.lift T.arrow h ≫ i = T.arrow := hM.exact.lift_f _ _
    haveI : Mono (hM.exact.lift T.arrow h) := mono_of_mono_fac hti
    rcases hP.subobject_eq_of_nonsplit hPns (Subobject.mk (hM.exact.lift T.arrow h)) with
      h0 | h1 | h2
    · left
      rw [Subobject.mk_eq_bot_iff_zero] at h0
      rw [← Subobject.mk_arrow T, Subobject.mk_eq_bot_iff_zero, ← hti, h0, zero_comp]
    · right; left
      rw [← Subobject.mk_arrow T]
      refine Subobject.mk_eq_mk_of_comm _ _ (Subobject.isoOfMkEqMk _ _ h1) ?_
      rw [Subobject.isoOfMkEqMk_hom, ← Category.assoc, Subobject.ofMkLEMk_comp, hti]
    · right; right; left
      have h3 : IsIso ((Subobject.underlyingIso (hM.exact.lift T.arrow h)).hom ≫
          hM.exact.lift T.arrow h) := by
        rw [Subobject.underlyingIso_hom_comp_eq_mk]
        exact (Subobject.isIso_arrow_iff_eq_top _).mpr h2
      haveI := IsIso.of_isIso_comp_left (Subobject.underlyingIso (hM.exact.lift T.arrow h)).hom
        (hM.exact.lift T.arrow h)
      rw [← Subobject.mk_arrow T]
      exact Subobject.mk_eq_mk_of_comm _ _ (asIso (hM.exact.lift T.arrow h)) hti
  · -- `T` maps onto `A'`
    have hw : (T.arrow ≫ π) ≫ l ≠ 0 := by rwa [Category.assoc, hπl]
    -- `M → U` has no section: a section would put a copy of `B` in `M` off `P`
    have hπns : ∀ σ : U ⟶ M, σ ≫ π ≠ 𝟙 U := by
      intro σ hσ
      have h1 : (k ≫ σ) ≫ p = 0 := by
        rw [← hπl, Category.assoc, ← Category.assoc σ, hσ, Category.id_comp, wkl]
      obtain ⟨t, ht⟩ : ∃ t : B ⟶ P, t ≫ i = k ≫ σ := ⟨_, hM.exact.lift_f (k ≫ σ) h1⟩
      by_cases htq : t ≫ q = 0
      · -- the copy of `B` lies in `A`, which `M → U` kills
        obtain ⟨e, he⟩ : ∃ e : B ⟶ A, e ≫ j = t := ⟨_, hP.exact.lift_f t htq⟩
        have hk0 : k = 0 := by
          calc k = (k ≫ σ) ≫ π := by rw [Category.assoc, hσ, Category.comp_id]
            _ = e ≫ ((j ≫ i) ≫ π) := by rw [← ht, ← he]; simp only [Category.assoc]
            _ = 0 := by rw [wπ, comp_zero]
        exact id_ne_zero B (zero_of_comp_mono k (by rw [Category.id_comp, hk0]))
      · -- the copy of `B` maps isomorphically onto `B`, so `P → B` splits
        haveI := isIso_of_hom_simple htq
        exact hPns (inv (t ≫ q) ≫ t) (by simp)
    -- the image of `T` in `U` is not inside `B`, so it is all of `U`
    haveI : Epi (T.arrow ≫ π) := by
      rcases hU.subobject_eq_of_nonsplit hUns (Subobject.mk (image.ι (T.arrow ≫ π))) with
        h0 | h1 | h2
      · exfalso; apply hw
        rw [Subobject.mk_eq_bot_iff_zero] at h0
        rw [← image.fac (T.arrow ≫ π), h0]; simp
      · exfalso; apply hw
        have h4 : image.ι (T.arrow ≫ π) = Subobject.ofMkLEMk _ k h1.le ≫ k :=
          (Subobject.ofMkLEMk_comp h1.le).symm
        rw [← image.fac (T.arrow ≫ π), h4]
        simp only [Category.assoc, wkl, comp_zero]
      · have h3 : IsIso ((Subobject.underlyingIso (image.ι (T.arrow ≫ π))).hom ≫
            image.ι (T.arrow ≫ π)) := by
          rw [Subobject.underlyingIso_hom_comp_eq_mk]
          exact (Subobject.isIso_arrow_iff_eq_top _).mpr h2
        haveI := IsIso.of_isIso_comp_left
          (Subobject.underlyingIso (image.ι (T.arrow ≫ π))).hom (image.ι (T.arrow ≫ π))
        rw [← image.fac (T.arrow ≫ π)]
        exact epi_comp _ _
    -- the kernel of `T → U` lies in `A`
    have hk : (kernel.ι (T.arrow ≫ π) ≫ T.arrow) ≫ π = 0 := by simp
    have huf : hπ.exact.lift _ hk ≫ (j ≫ i) = kernel.ι (T.arrow ≫ π) ≫ T.arrow :=
      hπ.exact.lift_f _ _
    haveI : Mono (hπ.exact.lift _ hk) := mono_of_mono_fac huf
    by_cases hu0 : hπ.exact.lift _ hk = 0
    · -- the kernel is zero: `T ≅ U` and `M → U` splits
      exfalso
      have hι : kernel.ι (T.arrow ≫ π) = 0 :=
        zero_of_comp_mono T.arrow (by rw [← huf, hu0, zero_comp])
      haveI : Mono (T.arrow ≫ π) := Preadditive.mono_of_kernel_zero hι
      haveI : IsIso (T.arrow ≫ π) := isIso_of_mono_of_epi _
      exact hπns (inv (T.arrow ≫ π) ≫ T.arrow) (by simp)
    · -- the kernel is `A`: then `A ⊆ T` and `T → U` is onto, so `T = M`
      right; right; right
      haveI := isIso_of_mono_of_ne_zero hu0
      have hc : (j ≫ i) ≫ cokernel.π T.arrow = 0 := by
        rw [← cancel_epi (hπ.exact.lift _ hk), ← Category.assoc, huf]
        simp
      have hgc : π ≫ hπ.exact.desc _ hc = cokernel.π T.arrow := hπ.exact.g_desc _ _
      have hd : hπ.exact.desc _ hc = 0 := by
        rw [← cancel_epi (T.arrow ≫ π), Category.assoc, hgc]
        simp
      haveI : Epi T.arrow := Preadditive.epi_of_cokernel_zero (by rw [← hgc, hd, comp_zero])
      haveI : IsIso T.arrow := isIso_of_mono_of_epi _
      exact Subobject.eq_top_of_isIso_arrow T

end CategoryTheory
