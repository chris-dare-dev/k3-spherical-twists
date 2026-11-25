/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Order.IntervalClass
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# Saturation and the radical on the subobjects of an object

Let `P` be a class of objects of an abelian category `C` and `R : C`. For subobjects `a ≤ b` of
`R`, `P.SubQ a b` says that the subquotient `b / a`, the cokernel of `a ⟶ b`, lies in `P`. If `P`
contains zero and is closed under quotients and extensions (a torsion class in the sense of
Dickson, for instance), this is an interval class on `Subobject R` (`P.intervalClass R`):

* `subQ_refl`: `a / a = 0`;
* `subQ_trans`: `0 → b/a → c/a → c/b → 0` is short exact (by pseudo-elements), so extension
  closure gives `trans`;
* `subQ_push`: `s/a ↠ (a' ⊔ s)/a'`, so quotient closure gives `push`;
* `subQ_sub`: `b/a ↪ c/a`, so closure under subobjects makes the class hereditary.

The order theory of `IntervalClass` then applies: on a Noetherian object (ACC on subobjects) the
radical `(P.intervalClass R).rad` is the largest subobject of `R` in `P`
(`isGreatest_intervalClass_rad`), the saturation of `a` is the largest `b ≥ a` with `b / a` in
`P`, and for a class that is also closed under subobjects the radical of a subobject `A` is
`A ⊓ t(R)` (`isGreatest_inf_intervalClass_rad`).

That `sat a` is the preimage in `R` of the radical of `R / a` would need the order isomorphism
between the subobjects of `R / a` and the subobjects of `R` above `a`, which is not used here.

## References

* S. E. Dickson, *A torsion theory for Abelian categories*, Trans. Amer. Math. Soc. 121 (1966).
* B. Stenström, *Rings of Quotients*, Springer (1975), Chapter VI.

## Tags

torsion class, radical, saturation, subquotient, interval class
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Subobject

open CategoryTheory.Abelian.Pseudoelement in
attribute [local instance] CategoryTheory.Abelian.Pseudoelement.objectToSort
  CategoryTheory.Abelian.Pseudoelement.homToFun in
/-- For subobjects `a ≤ b ≤ c`, the induced map `b / a ⟶ c / a` is a monomorphism. -/
theorem mono_cokernel_desc_ofLE {R : C} {a b c : Subobject R} (hab : a ≤ b) (hbc : b ≤ c) :
    Mono (cokernel.desc (ofLE a b hab) (ofLE b c hbc ≫ cokernel.π (ofLE a c (hab.trans hbc)))
      (by simp)) := by
  apply mono_of_zero_of_map_zero
  intro x hx
  obtain ⟨y, rfl⟩ := pseudo_surjective_of_epi (cokernel.π (ofLE a b hab)) x
  rw [← Abelian.Pseudoelement.comp_apply, cokernel.π_desc, Abelian.Pseudoelement.comp_apply] at hx
  obtain ⟨z, hz⟩ := pseudo_exact_of_exact (ShortComplex.exact_cokernel (ofLE a c (hab.trans hbc)))
    _ hx
  have hz' : (ofLE a b hab) z = y := by
    apply pseudo_injective_of_mono (ofLE b c hbc)
    rw [← Abelian.Pseudoelement.comp_apply, ofLE_comp_ofLE]
    exact hz
  rw [← hz', ← Abelian.Pseudoelement.comp_apply, cokernel.condition,
    Abelian.Pseudoelement.zero_apply]

end Subobject

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- `P.SubQ a b`: `a ≤ b`, and the subquotient `b / a`, the cokernel of `a ⟶ b`, lies in `P`. -/
def SubQ {R : C} (a b : Subobject R) : Prop :=
  ∃ h : a ≤ b, P (cokernel (Subobject.ofLE a b h))

variable {P}

theorem SubQ.le {R : C} {a b : Subobject R} (h : P.SubQ a b) : a ≤ b :=
  h.1

theorem subQ_iff_of_le {R : C} {a b : Subobject R} (h : a ≤ b) :
    P.SubQ a b ↔ P (cokernel (Subobject.ofLE a b h)) :=
  ⟨fun ⟨_, hP⟩ => hP, fun hP => ⟨h, hP⟩⟩

/-- The subquotient of two subobjects given by monomorphisms `f : A ⟶ R` and `g : B ⟶ R` with
`u ≫ g = f` is the cokernel of `u`. -/
theorem subQ_mk_iff [P.IsClosedUnderIsomorphisms] {R A B : C} {f : A ⟶ R} {g : B ⟶ R} [Mono f]
    [Mono g] (u : A ⟶ B) (hu : u ≫ g = f) :
    P.SubQ (Subobject.mk f) (Subobject.mk g) ↔ P (cokernel u) := by
  have e : cokernel (Subobject.ofLE _ _ (Subobject.mk_le_mk_of_comm u hu)) ≅ cokernel u := by
    rw [Subobject.ofLE_mk_le_mk_of_comm u hu]
    exact cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _
  rw [subQ_iff_of_le (Subobject.mk_le_mk_of_comm u hu)]
  exact ⟨fun h => P.prop_of_iso e h, fun h => P.prop_of_iso e.symm h⟩

/-- `b / ⊥` is `b`. -/
theorem subQ_bot_iff [P.IsClosedUnderIsomorphisms] {R : C} (b : Subobject R) :
    P.SubQ ⊥ b ↔ P (b : C) := by
  have h0 : Subobject.ofLE ⊥ b bot_le = 0 :=
    (IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero).eq_of_src _ _
  have e : cokernel (Subobject.ofLE ⊥ b bot_le) ≅ (b : C) :=
    cokernelIsoOfEq h0 ≪≫ cokernelZeroIsoTarget
  exact ⟨fun ⟨_, h⟩ => P.prop_of_iso e h, fun h => ⟨bot_le, P.prop_of_iso e.symm h⟩⟩

/-- `a / a = 0`. -/
theorem subQ_refl [P.ContainsZero] [P.IsClosedUnderIsomorphisms] {R : C} (a : Subobject R) :
    P.SubQ a a := by
  refine ⟨le_rfl, P.prop_of_isZero ?_⟩
  have : Epi (Subobject.ofLE a a le_rfl) := by rw [Subobject.ofLE_refl]; infer_instance
  exact isZero_cokernel_of_epi _

/-- Quotient closure gives `c / a ↠ c / b` for `a ≤ b ≤ c`. -/
theorem subQ_quot [P.IsClosedUnderQuotients] {R : C} {a b c : Subobject R} (hab : a ≤ b)
    (hbc : b ≤ c) (h : P.SubQ a c) : P.SubQ b c := by
  obtain ⟨hac, hP⟩ := h
  refine ⟨hbc, ?_⟩
  let d : cokernel (Subobject.ofLE a c hac) ⟶ cokernel (Subobject.ofLE b c hbc) :=
    cokernel.desc _ (cokernel.π _) (by
      rw [← Subobject.ofLE_comp_ofLE a b c hab hbc, Category.assoc, cokernel.condition,
        Limits.comp_zero])
  have : Epi d := epi_of_epi_fac (cokernel.π_desc _ _ _)
  exact P.prop_of_epi d hP

/-- Quotient closure gives `push`: `s / a ↠ (a' ⊔ s) / a'` for `a ≤ a'` and `a ≤ s`. -/
theorem subQ_push [P.IsClosedUnderQuotients] {R : C} {a a' s : Subobject R}
    (h₁ : a ≤ a') (h₂ : a ≤ s) (h : P.SubQ a s) : P.SubQ a' (a' ⊔ s) := by
  obtain ⟨_, hP⟩ := h
  refine ⟨le_sup_left, ?_⟩
  let π := cokernel.π (Subobject.ofLE a' (a' ⊔ s) le_sup_left)
  have hcomm : Subobject.ofLE a s h₂ ≫ Subobject.ofLE s (a' ⊔ s) le_sup_right =
      Subobject.ofLE a a' h₁ ≫ Subobject.ofLE a' (a' ⊔ s) le_sup_left := by simp
  let d : cokernel (Subobject.ofLE a s h₂) ⟶
      cokernel (Subobject.ofLE a' (a' ⊔ s) le_sup_left) :=
    cokernel.desc _ (Subobject.ofLE s (a' ⊔ s) le_sup_right ≫ π) (by
      rw [← Category.assoc, hcomm, Category.assoc, cokernel.condition, Limits.comp_zero])
  let e := (Subobject.supMonoFactorisation a' s).e
  have hfac : e ≫ (Subobject.supIsoImage a' s).hom = factorThruImage _ :=
    IsImage.e_isoExt_hom (Subobject.supIsImage a' s) (Image.isImage _)
  have he : Epi e := by
    have : e = factorThruImage _ ≫ (Subobject.supIsoImage a' s).inv := by
      rw [Iso.eq_comp_inv]; exact hfac
    rw [this]; infer_instance
  have hepi : Epi (Subobject.ofLE s (a' ⊔ s) le_sup_right ≫ π) := by
    constructor
    intro Z u v huv
    have : π ≫ u = π ≫ v := by
      rw [← cancel_epi e]
      ext
      · simp [e, π]
      · simpa [e] using huv
    exact (cancel_epi π).1 this
  have : Epi d := epi_of_epi_fac (cokernel.π_desc _ _ _)
  exact P.prop_of_epi d hP

/-- Subobject closure gives heredity: `b / a ↪ c / a` for `a ≤ b ≤ c`. -/
theorem subQ_sub [P.IsClosedUnderSubobjects] {R : C} {a b c : Subobject R} (hab : a ≤ b)
    (hbc : b ≤ c) (h : P.SubQ a c) : P.SubQ a b := by
  obtain ⟨_, hP⟩ := h
  have := Subobject.mono_cokernel_desc_ofLE hab hbc
  exact ⟨hab, P.prop_of_mono (cokernel.desc (Subobject.ofLE a b hab)
    (Subobject.ofLE b c hbc ≫ cokernel.π (Subobject.ofLE a c (hab.trans hbc))) _) hP⟩

open CategoryTheory.Abelian.Pseudoelement in
attribute [local instance] CategoryTheory.Abelian.Pseudoelement.objectToSort
  CategoryTheory.Abelian.Pseudoelement.homToFun in
/-- Extension closure gives `trans`: `0 → b/a → c/a → c/b → 0` is short exact. -/
theorem subQ_trans [P.IsClosedUnderExtensions] {R : C} {a b c : Subobject R} (hab : a ≤ b)
    (hbc : b ≤ c) (h₁ : P.SubQ a b) (h₂ : P.SubQ b c) : P.SubQ a c := by
  obtain ⟨_, h₁⟩ := h₁
  obtain ⟨_, h₂⟩ := h₂
  refine ⟨hab.trans hbc, ?_⟩
  let m := cokernel.desc (Subobject.ofLE a b hab)
    (Subobject.ofLE b c hbc ≫ cokernel.π (Subobject.ofLE a c (hab.trans hbc))) (by simp)
  let n := cokernel.desc (Subobject.ofLE a c (hab.trans hbc))
    (cokernel.π (Subobject.ofLE b c hbc))
    (by rw [← Subobject.ofLE_comp_ofLE a b c hab hbc, Category.assoc, cokernel.condition,
      Limits.comp_zero])
  have hmn : m ≫ n = 0 := by
    apply (cancel_epi (cokernel.π (Subobject.ofLE a b hab))).1
    simp [m, n]
  have hm : Mono m := Subobject.mono_cokernel_desc_ofLE hab hbc
  have hn : Epi n := epi_of_epi_fac (cokernel.π_desc _ _ _)
  have hex : (ShortComplex.mk m n hmn).Exact := by
    apply exact_of_pseudo_exact
    intro x hx
    obtain ⟨y, rfl⟩ :=
      pseudo_surjective_of_epi (cokernel.π (Subobject.ofLE a c (hab.trans hbc))) x
    change n _ = 0 at hx
    rw [← Abelian.Pseudoelement.comp_apply, cokernel.π_desc] at hx
    obtain ⟨z, hz⟩ :=
      pseudo_exact_of_exact (ShortComplex.exact_cokernel (Subobject.ofLE b c hbc)) _ hx
    refine ⟨(cokernel.π (Subobject.ofLE a b hab)) z, ?_⟩
    change m _ = _
    rw [← Abelian.Pseudoelement.comp_apply, cokernel.π_desc, Abelian.Pseudoelement.comp_apply]
    change _ = y at hz
    rw [hz]
  exact P.prop_X₂_of_shortExact (ShortComplex.ShortExact.mk' hex hm hn) h₁ h₂

variable (P)

/-- The interval class of a class `P` containing zero and closed under quotients and extensions
on the subobjects of `R`: `Q a b` says that `b / a` lies in `P`. -/
noncomputable def intervalClass [P.ContainsZero] [P.IsClosedUnderQuotients]
    [P.IsClosedUnderExtensions] (R : C) : IntervalClass (Subobject R) where
  Q := P.SubQ
  refl := subQ_refl
  trans := subQ_trans
  push := subQ_push

@[simp]
theorem intervalClass_Q [P.ContainsZero] [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    (R : C) (a b : Subobject R) : (P.intervalClass R).Q a b ↔ P.SubQ a b :=
  Iff.rfl

variable {P}

/-- A class closed under subobjects gives a hereditary interval class. -/
theorem intervalClass_hereditary [P.ContainsZero] [P.IsClosedUnderQuotients]
    [P.IsClosedUnderExtensions] [P.IsClosedUnderSubobjects] (R : C) :
    (P.intervalClass R).Hereditary :=
  fun _ _ _ hab hbc h => subQ_sub hab hbc h

/-- **The radical.** On a Noetherian object `R`, the radical of the interval class is the
largest subobject of `R` in `P`. -/
theorem isGreatest_intervalClass_rad [P.ContainsZero] [P.IsClosedUnderQuotients]
    [P.IsClosedUnderExtensions] (R : C) [IsNoetherianObject R] :
    IsGreatest {A : Subobject R | P (A : C)} (P.intervalClass R).rad := by
  have h := (P.intervalClass R).isGreatest_rad
  exact ⟨(subQ_bot_iff _).1 h.1, fun A hA => h.2 ((subQ_bot_iff A).2 hA)⟩

/-- **The restriction formula** `t(A) = A ⊓ t(R)` on a Noetherian object, for a class closed
under subobjects, quotients and extensions: `A ⊓ t(R)` is the largest subobject of `R` below `A`
that lies in `P`. This is not the splitting law for the image of `t(R)` in an extension. -/
theorem isGreatest_inf_intervalClass_rad [P.ContainsZero] [P.IsClosedUnderQuotients]
    [P.IsClosedUnderExtensions] [P.IsClosedUnderSubobjects] (R : C) [IsNoetherianObject R]
    (A : Subobject R) :
    IsGreatest {B : Subobject R | B ≤ A ∧ P (B : C)} (A ⊓ (P.intervalClass R).rad) := by
  have h := (P.intervalClass R).isGreatest_inf_rad (intervalClass_hereditary R) A
  exact ⟨⟨h.1.2.1, (subQ_bot_iff _).1 h.1.2.2⟩,
    fun B ⟨hBA, hB⟩ => h.2 ⟨bot_le, hBA, (subQ_bot_iff B).2 hB⟩⟩

/-- **The saturation.** On a Noetherian object, the saturation of `a` is the largest `b ≥ a` such
that `b / a` lies in `P`. -/
theorem isGreatest_intervalClass_sat [P.ContainsZero] [P.IsClosedUnderQuotients]
    [P.IsClosedUnderExtensions] {R : C} [IsNoetherianObject R] (a : Subobject R) :
    IsGreatest {b : Subobject R | P.SubQ a b} ((P.intervalClass R).sat a) :=
  ⟨(P.intervalClass R).Q_sat a, fun _ hb => (P.intervalClass R).le_sat_of_Q hb.le hb⟩

end ObjectProperty

end CategoryTheory
