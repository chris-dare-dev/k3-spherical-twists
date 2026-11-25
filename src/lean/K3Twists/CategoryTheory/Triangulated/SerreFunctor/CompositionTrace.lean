/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.SerreFunctor.TwoCalabiYau
import K3Twists.LinearAlgebra.PoincareDuality
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# The composition–trace pairing, the degree-two lemma and orthogonality

Let `D` be a Serre functor on a `k`-linear category with a shift. The Serre pairing
`Hom(A, B) × Hom(B, S A) → k` is composition followed by the Serre trace
(`SerreFunctorData.pairing_eq_trace_comp`). At an object `X` with `S X ≅ X⟦2⟧` this gives the
**composition–trace pairing**

`Hom(X, Y⟦1⟧) × Hom(Y, X⟦1⟧) → Hom(X, X⟦2⟧) ≅ Hom(X, S X) → k`, `(u, w) ↦ tr(u · w)`,

which separates both arguments (`SerreFunctorData.compTrace_separating_left`, `_right`). Only the
pointwise isomorphism `S X ≅ X⟦2⟧` at the objects in question is used, not a natural one.

## The degree-two lemma

`Functor.injective_map_shiftedHom_two`: let `F : C ⥤ D` be `k`-linear and commute with shifts,
and let `S X ≅ X⟦2⟧` in `D` at `X = F S`. If `dim Hom(S, S⟦2⟧) ≤ 1`, `F_1` is nonzero somewhere on
`Hom(S, U⟦1⟧)` and onto `Hom(F U, (F S)⟦1⟧)`, then `F_2` is injective on `Hom(S, S⟦2⟧)`. The
proof is the linear-algebra degree-two lemma (`LinearMap.injective_of_pairing_of_finrank_le_one`)
with the Yoneda products of source and target, which `F` intertwines with no sign
(`ShiftedHom.map_comp`), and the composition–trace pairing of the target, which separates its
left argument. An arbitrary nondegenerate pairing on the target would not do: the lemma needs the
pairing to factor through the Yoneda product into `Hom(F S, (F S)⟦2⟧)`. For `TwoCYHypotheses`
the isomorphism `S ≅ ⟦2⟧` is a field (`TwoCYHypotheses.injective_map_shiftedHom_two`).

## The orthogonality lemma

`SerreFunctorData.finrank_ext_one_eq_neg_euler`: let `P`, `Q` be objects of a Hom-finite
category with linear shifts and `S P ≅ P⟦2⟧`, with no negative extensions between them in either
order (as for objects of a heart) and `Hom(P, Q) = 0 = Hom(Q, P)` (as for nonisomorphic simple
objects of one abelian slice, by Schur's lemma). Then `Hom(P, Q⟦i⟧) = 0` for `i ≠ 1`, and
`dim Hom(P, Q⟦1⟧) = -χ(P, Q)` for the Euler form `χ(P, Q) = ∑ (-1)^i dim Hom(P, Q⟦i⟧)`
(`Triangulated.euler`). With Mukai's sign `χ(P, Q) = -⟨v(P), v(Q)⟩`, this is
`dim Ext¹(P, Q) = ⟨v(P), v(Q)⟩`; two such objects of one class `v` are orthogonal in every
degree exactly when `v² = 0` (`SerreFunctorData.ext_eq_zero_iff`). The hypotheses are the heart
and Schur facts named; nothing about the slice beyond them is used.

## Main results

* `SerreFunctorData.pairing_eq_trace_comp`, `SerreFunctorData.compTrace_separating_left`
* `Functor.injective_map_shiftedHom_two`, `TwoCYHypotheses.injective_map_shiftedHom_two`
* `SerreFunctorData.finrank_hom_shift_eq`, `SerreFunctorData.finrank_ext_one_eq_neg_euler`,
  `SerreFunctorData.ext_eq_zero_iff`

## Tags

Serre functor, trace, Yoneda product, Calabi–Yau, orthogonality, isotropic family
-/

noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory Limits Module

namespace CategoryTheory

namespace SerreFunctor.SerreFunctorData

variable {k : Type w} [Field k] {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C]
  (D : SerreFunctorData k C)

/-- **The Serre pairing is composition followed by the Serre trace.** -/
theorem pairing_eq_trace_comp {A B : C} (f : A ⟶ B) (g : B ⟶ D.S.obj A) :
    D.pairing A B f g = D.trace A (f ≫ g) := by
  have h := D.naturality_right f ((D.eta A B).symm g)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [trace_apply, pairing_apply, ← h, LinearEquiv.symm_apply_apply]
  simp [Linear.rightComp]

section Shift

variable [HasShift C ℤ] {X Y : C} (e : D.S.obj X ≅ X⟦(2 : ℤ)⟧)

/-- **The composition–trace pairing** `Hom(X, Y⟦1⟧) × Hom(Y, X⟦1⟧) → k`, `(u, w) ↦ tr(u · w)`, at
an object with `S X ≅ X⟦2⟧`. -/
def compTrace (u : ShiftedHom X Y (1 : ℤ)) (w : ShiftedHom Y X (1 : ℤ)) : k :=
  D.trace X (u.comp w (by norm_num : (1 : ℤ) + 1 = 2) ≫ e.inv)

theorem compTrace_eq_pairing (u : ShiftedHom X Y (1 : ℤ)) (w : ShiftedHom Y X (1 : ℤ)) :
    D.compTrace e u w = D.pairing X (Y⟦(1 : ℤ)⟧) u
      (w⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C 1 1 2 (by norm_num)).inv.app X ≫ e.inv) := by
  rw [pairing_eq_trace_comp]
  simp [compTrace, ShiftedHom.comp]

/-- The composition–trace pairing separates its left argument. -/
theorem compTrace_separating_left (u : ShiftedHom X Y (1 : ℤ))
    (hu : ∀ w, D.compTrace e u w = 0) : u = 0 := by
  refine D.pairing_separating_left X (Y⟦(1 : ℤ)⟧) u fun g ↦ ?_
  obtain ⟨w, hw⟩ := (shiftFunctor C (1 : ℤ)).map_surjective
    (g ≫ e.hom ≫ (shiftFunctorAdd' C 1 1 2 (by norm_num)).hom.app X)
  have hg : g = w⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C 1 1 2 (by norm_num)).inv.app X ≫ e.inv := by
    rw [hw]
    simp
  rw [hg, ← compTrace_eq_pairing]
  exact hu w

/-- The composition–trace pairing separates its right argument. -/
theorem compTrace_separating_right (w : ShiftedHom Y X (1 : ℤ))
    (hw : ∀ u, D.compTrace e u w = 0) : w = 0 := by
  have h := D.pairing_separating_right X (Y⟦(1 : ℤ)⟧)
    (w⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C 1 1 2 (by norm_num)).inv.app X ≫ e.inv)
    fun u ↦ by rw [← compTrace_eq_pairing]; exact hw u
  apply (shiftFunctor C (1 : ℤ)).map_injective
  simpa using h

include e in
/-- If every Yoneda product `u · w` vanishes, `u = 0`. -/
theorem eq_zero_of_comp_eq_zero (u : ShiftedHom X Y (1 : ℤ))
    (hu : ∀ w : ShiftedHom Y X (1 : ℤ), u.comp w (by norm_num : (1 : ℤ) + 1 = 2) = 0) :
    u = 0 :=
  D.compTrace_separating_left e u fun w ↦ by simp [compTrace, hu w]

end Shift

end SerreFunctor.SerreFunctorData

/-! ### The degree-two lemma -/

namespace Functor

variable {k : Type w} [Field k] {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
  [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ] [F.Additive] [F.Linear k]

/-- `F_n` as a `k`-linear map. -/
@[simps]
def shiftedHomMapLinearMap (X Y : C) (n : ℤ) :
    ShiftedHom X Y n →ₗ[k] ShiftedHom (F.obj X) (F.obj Y) n where
  toFun f := f.map F
  map_add' f g := ShiftedHom.map_add f g F
  map_smul' c f := ShiftedHom.map_smul c f F

/-- **The degree-two lemma.** Let `S (F S) ≅ (F S)⟦2⟧` for a Serre functor of the target. If
`dim Hom(S, S⟦2⟧) ≤ 1`, `F_1` is nonzero somewhere on `Hom(S, U⟦1⟧)` and `F_1` maps
`Hom(U, S⟦1⟧)` onto `Hom(F U, (F S)⟦1⟧)`, then `F_2` is injective on `Hom(S, S⟦2⟧)`. -/
theorem injective_map_shiftedHom_two (DS : SerreFunctor.SerreFunctorData k D) {S U : C}
    (e : DS.S.obj (F.obj S) ≅ (F.obj S)⟦(2 : ℤ)⟧) [FiniteDimensional k (S ⟶ S⟦(2 : ℤ)⟧)]
    (hdim : finrank k (S ⟶ S⟦(2 : ℤ)⟧) ≤ 1)
    (hu : ∃ u : ShiftedHom S U (1 : ℤ), u.map F ≠ 0)
    (hsurj : Function.Surjective (fun w : ShiftedHom U S (1 : ℤ) ↦ w.map F)) :
    Function.Injective (fun f : ShiftedHom S S (2 : ℤ) ↦ f.map F) :=
  LinearMap.injective_of_pairing_of_finrank_le_one
    (fun (u : ShiftedHom S U (1 : ℤ)) (w : ShiftedHom U S (1 : ℤ)) ↦
      u.comp w (by norm_num : (1 : ℤ) + 1 = 2))
    (fun (u : ShiftedHom (F.obj S) (F.obj U) (1 : ℤ)) (w : ShiftedHom (F.obj U) (F.obj S) (1 : ℤ)) ↦
      u.comp w (by norm_num : (1 : ℤ) + 1 = 2))
    (fun u ↦ u.map F) (fun w ↦ w.map F) (F.shiftedHomMapLinearMap S S 2)
    (fun u w ↦ ShiftedHom.map_comp u w _ F) hdim hu hsurj
    (fun u' hu' ↦ DS.eq_zero_of_comp_eq_zero e u' hu')

end Functor

/-- **The degree-two lemma on a 2-Calabi–Yau target.** With `TwoCYHypotheses` on the target, the
isomorphism `S ≅ ⟦2⟧` comes from the Serre functor field. -/
theorem Triangulated.TwoCYHypotheses.injective_map_shiftedHom_two {k : Type w} [Field k]
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] [Preadditive C]
    [Linear k C] [HasShift C ℤ] [HasZeroObject D]
    [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [Linear k D] {Λ : Type*} [AddCommGroup Λ] {q : LinearMap.BilinForm ℤ Λ}
    {v : Triangulated.K₀ D →+ Λ} (h : Triangulated.TwoCYHypotheses k D q v)
    (F : C ⥤ D) [F.CommShift ℤ] [F.Additive] [F.Linear k] {S U : C}
    [FiniteDimensional k (S ⟶ S⟦(2 : ℤ)⟧)] (hdim : finrank k (S ⟶ S⟦(2 : ℤ)⟧) ≤ 1)
    (hu : ∃ u : ShiftedHom S U (1 : ℤ), u.map F ≠ 0)
    (hsurj : Function.Surjective (fun w : ShiftedHom U S (1 : ℤ) ↦ w.map F)) :
    Function.Injective (fun f : ShiftedHom S S (2 : ℤ) ↦ f.map F) := by
  obtain ⟨DS, ⟨i⟩⟩ := h.serre
  exact F.injective_map_shiftedHom_two DS (i.app _) hdim hu hsurj

/-! ### The orthogonality lemma -/

namespace Triangulated

variable (k : Type w) [Field k] {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C]
  [HasShift C ℤ]

/-- The **Euler form** `χ(P, Q) = ∑ᵢ (-1)^i dim Hom(P, Q⟦i⟧)`, a finite sum (`finsum`: zero if
infinitely many terms are nonzero). -/
def euler (P Q : C) : ℤ :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (finrank k (P ⟶ Q⟦i⟧) : ℤ)

end Triangulated

namespace SerreFunctor.SerreFunctorData

variable {k : Type w} [Field k] {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear k]
  [HomFinite k C] (D : SerreFunctorData k C)

omit [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear k] in
private theorem finrank_eq_zero_of_forall {X Y : C} (h : ∀ f : X ⟶ Y, f = 0) :
    finrank k (X ⟶ Y) = 0 :=
  Module.finrank_zero_iff.2 ⟨fun f g ↦ (h f).trans (h g).symm⟩

/-- `Hom(X, Y) ≃ Hom(X⟦n⟧, Y⟦n⟧)`, as a `k`-linear equivalence. -/
private def shiftLinearEquiv (n : ℤ) (X Y : C) : (X ⟶ Y) ≃ₗ[k] (X⟦n⟧ ⟶ Y⟦n⟧) :=
  LinearEquiv.ofBijective ((shiftFunctor C n).mapLinearMap k)
    ⟨(shiftFunctor C n).map_injective, (shiftFunctor C n).map_surjective⟩

/-- **Serre duality in shifted degrees**: if `S P ≅ P⟦2⟧`, then
`dim Hom(P, Q⟦i⟧) = dim Hom(Q, P⟦2 - i⟧)`. -/
theorem finrank_hom_shift_eq {P : C} (eP : D.S.obj P ≅ P⟦(2 : ℤ)⟧) (Q : C) (i : ℤ) :
    finrank k (P ⟶ Q⟦i⟧) = finrank k (Q ⟶ P⟦2 - i⟧) := by
  rw [D.finrank_hom_eq P (Q⟦i⟧)]
  refine ((Linear.homCongr k (Iso.refl _)
    (eP ≪≫ (shiftFunctorAdd' C (2 - i) i 2 (by lia)).app P)).trans
      (shiftLinearEquiv i Q (P⟦2 - i⟧)).symm).finrank_eq

variable {D} {P Q : C} (eP : D.S.obj P ≅ P⟦(2 : ℤ)⟧)
  (hPQ : ∀ i : ℤ, i < 0 → ∀ f : P ⟶ Q⟦i⟧, f = 0) (hQP : ∀ i : ℤ, i < 0 → ∀ f : Q ⟶ P⟦i⟧, f = 0)
  (h₀ : ∀ f : P ⟶ Q, f = 0) (h₀' : ∀ f : Q ⟶ P, f = 0)

include eP hPQ hQP h₀ h₀'

/-- **Orthogonality in degrees other than one.** -/
theorem finrank_hom_shift_eq_zero (i : ℤ) (hi : i ≠ 1) : finrank k (P ⟶ Q⟦i⟧) = 0 := by
  rcases lt_trichotomy i 0 with hneg | rfl | hpos
  · exact finrank_eq_zero_of_forall (hPQ i hneg)
  · rw [(Linear.homCongr k (Iso.refl P) ((shiftFunctorZero C ℤ).app Q)).finrank_eq]
    exact finrank_eq_zero_of_forall h₀
  · rw [D.finrank_hom_shift_eq eP Q i]
    rcases eq_or_lt_of_le (show 2 ≤ i by lia) with rfl | hlt
    · rw [show (2 : ℤ) - 2 = 0 by norm_num,
        (Linear.homCongr k (Iso.refl Q) ((shiftFunctorZero C ℤ).app P)).finrank_eq]
      exact finrank_eq_zero_of_forall h₀'
    · exact finrank_eq_zero_of_forall (hQP (2 - i) (by lia))

/-- **The orthogonality lemma**: `dim Ext¹(P, Q) = -χ(P, Q)`. -/
theorem finrank_ext_one_eq_neg_euler :
    (finrank k (P ⟶ Q⟦(1 : ℤ)⟧) : ℤ) = -Triangulated.euler k P Q := by
  rw [Triangulated.euler, finsum_eq_single _ (1 : ℤ) fun i hi ↦ by
    rw [finrank_hom_shift_eq_zero eP hPQ hQP h₀ h₀' i hi]; simp]
  simp [Int.negOnePow_one]

/-- **Orthogonality**: with `χ(P, Q) = -c` (Mukai's sign: `c = ⟨v(P), v(Q)⟩`), `P` and `Q` are
orthogonal in every degree exactly when `c = 0`; in particular two such objects of one class `v`
are orthogonal exactly when `v² = 0`. -/
theorem ext_eq_zero_iff {c : ℤ} (hχ : Triangulated.euler k P Q = -c) :
    (∀ i : ℤ, ∀ f : P ⟶ Q⟦i⟧, f = 0) ↔ c = 0 := by
  have h1 := finrank_ext_one_eq_neg_euler eP hPQ hQP h₀ h₀'
  rw [hχ, neg_neg] at h1
  constructor
  · intro h
    rw [← h1, finrank_eq_zero_of_forall (h 1), Nat.cast_zero]
  · intro hc i f
    have hfin : finrank k (P ⟶ Q⟦i⟧) = 0 := by
      rcases eq_or_ne i 1 with rfl | hi
      · exact_mod_cast h1.trans hc
      · exact finrank_hom_shift_eq_zero eP hPQ hQP h₀ h₀' i hi
    exact (Module.finrank_zero_iff.1 hfin).elim f 0

end SerreFunctor.SerreFunctorData

end CategoryTheory
