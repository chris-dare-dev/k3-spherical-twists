/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.SerreFunctor.TwoCalabiYau

/-!
# The Mukai budget: consistency models and two refuted formulations

A theorem proved from hypotheses that cannot hold together says nothing. This file shows that
`MukaiBudget` and `TwoCYHypotheses` can hold, and keeps two formulations of the budget that fail
as regression tests:

* **An integer-valued budget needs `e ≥ 0`.** With values in `ℤ`, Mukai's lemma on `0 → 0 → 0`
  only gives `e(0) ≤ 0`. The constant `-1` satisfies every other field, and the budget inequality
  fails on the empty tower of `0` (`constNeg`, `int_budget_fails`). `MukaiBudget` takes values in
  `ℕ` for this reason.
* **Riemann–Roch `e = 2 + v²` is not a field on all objects.** Mukai's lemma forces `e(0) = 0`,
  while an additive class map has `v(0) = 0` (`not_forall_riemannRoch`). `TwoCYHypotheses` states
  Riemann–Roch for objects with `End = k` and no negative self-extensions only.

The models are relative: `zeroBudget` lives on any pretriangulated category, and `twoCYOfIsZero` on
any `k`-linear pretriangulated category whose objects are all zero. Neither says anything about a
K3 surface; the real-object check of the budget is in the quiver model,
`Quiver.Kronecker.DoubledRep.sum_selfExtDim_le_of_hnFiltration`.

Built by `lake test`.
-/

noncomputable section

namespace CategoryTheory.Triangulated.BudgetModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe w v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Consistency of `MukaiBudget` -/

/-- `MukaiBudget` is inhabited on every pretriangulated category, by `e := 0`. -/
def zeroBudget : MukaiBudget C where
  e := fun _ => 0
  e_iso := fun _ => rfl
  mukai := fun _ _ _ => le_refl _

example (s : Slicing C) {E : C} (F : HNFiltration C s.P E) :
    ∑ i, (zeroBudget (C := C)).e (F.factor i) ≤ (zeroBudget (C := C)).e E :=
  zeroBudget.slicing_sum_le s F

/-! ### Refuted: an integer-valued budget without `e ≥ 0` -/

/-- The integer-valued variant of `MukaiBudget`, with the same fields and no nonnegativity. -/
structure MukaiBudgetInt (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] where
  /-- The budget. -/
  e : C → ℤ
  /-- Invariance under isomorphism. -/
  e_iso : ∀ {X Y : C}, (X ≅ Y) → e X = e Y
  /-- Mukai's lemma. -/
  mukai : ∀ T ∈ distTriang C, (∀ f : T.obj₁ ⟶ T.obj₃, f = 0) → e T.obj₁ + e T.obj₃ ≤ e T.obj₂

/-- The constant `-1` satisfies every field of the integer-valued variant. -/
def constNeg : MukaiBudgetInt C where
  e := fun _ => -1
  e_iso := fun _ => rfl
  mukai := fun _ _ _ => by norm_num

theorem constNeg_e_zero_neg : (constNeg (C := C)).e 0 < 0 := by
  simp [constNeg]

/-- The tower of `0` with no factors. -/
def emptyTower : PostnikovTower C (0 : C) where
  n := 0
  chain := ComposableArrows.mk₀ (0 : C)
  triangle := Fin.elim0
  triangle_dist := fun i => i.elim0
  triangle_obj₁ := fun i => i.elim0
  triangle_obj₂ := fun i => i.elim0
  base_isZero := isZero_zero C
  top_iso := ⟨Iso.refl _⟩

/-- **The integer-valued budget fails on the empty tower of `0`**: the empty sum `0` is not at
most `e(0) = -1`. -/
theorem int_budget_fails :
    ¬ (∑ i, (constNeg (C := C)).e ((emptyTower (C := C)).factor i) ≤ (constNeg (C := C)).e 0) := by
  change ¬ ((∑ _i : Fin 0, (-1 : ℤ)) ≤ -1)
  simp

/-- With values in `ℕ` the budget holds on the same tower. -/
example (b : MukaiBudget C) : ∑ i, b.e ((emptyTower (C := C)).factor i) ≤ b.e 0 :=
  b.tower_sum_le _ fun i => i.elim0

/-! ### Refuted: Riemann–Roch on all objects -/

/-- **Riemann–Roch `e = 2 + q(v, v)` cannot hold on all objects**, for any Mukai budget, any class
map `v` additive on distinguished triangles and any bilinear form `q`: at the zero object,
`e(0) = 0` by Mukai's lemma and `v(0) = 0` by additivity. -/
theorem not_forall_riemannRoch (b : MukaiBudget C) {Λ : Type*} [AddCommGroup Λ]
    (q : LinearMap.BilinForm ℤ Λ) (v : K₀ C →+ Λ) :
    ¬ ∀ X : C, (b.e X : ℤ) = 2 + q (classOf C v X) (classOf C v X) := by
  intro h
  have h0 := h 0
  rw [b.e_zero, classOf_isZero C v (isZero_zero C)] at h0
  simp at h0

/-! ### Consistency of `TwoCYHypotheses`, relative to a category of zero objects -/

section TwoCY

variable (k : Type w) [Field k] [Linear k C]

/-- **`TwoCYHypotheses` holds on a `k`-linear pretriangulated category whose objects are all
zero**: every Hom-space is zero, the shift by two is a Serre functor, `e = 0`, and no object has
`End = k`. -/
theorem twoCYOfIsZero (hC : ∀ X : C, IsZero X) {Λ : Type*} [AddCommGroup Λ]
    (q : LinearMap.BilinForm ℤ Λ) (v : K₀ C →+ Λ) : TwoCYHypotheses k C q v := by
  have hsub : ∀ A B : C, Subsingleton (A ⟶ B) := fun A B => ⟨fun f g => (hC A).eq_of_src f g⟩
  have hdual : ∀ A B : C, Subsingleton (Module.Dual k (A ⟶ B)) := fun A B =>
    ⟨fun φ ψ => LinearMap.ext fun f => by rw [Subsingleton.elim f 0, map_zero, map_zero]⟩
  have hfin : ∀ X : C, Module.finrank k (X ⟶ X⟦(1 : ℤ)⟧) = 0 := fun X =>
    Module.finrank_zero_of_subsingleton
  refine
    { homFinite := ⟨fun A B => Module.Finite.of_finite⟩
      serre := ⟨{ S := shiftFunctor C (2 : ℤ)
                  eta := fun A B => LinearEquiv.ofSubsingleton _ _
                  naturality_left := fun _ _ => Subsingleton.elim _ _
                  naturality_right := fun _ _ => Subsingleton.elim _ _ }, ⟨Iso.refl _⟩⟩
      mukai := fun T _ _ => by simp only [selfExtDim, hfin]; rfl
      even := fun X => by simp only [selfExtDim, hfin]; exact ⟨0, rfl⟩
      riemannRoch := fun X hEnd _ => ?_ }
  rw [Module.finrank_zero_of_subsingleton] at hEnd
  exact absurd hEnd zero_ne_one

end TwoCY

end CategoryTheory.Triangulated.BudgetModel
