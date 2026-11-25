/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Uniqueness
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The Mukai budget lemma

Let `e(E) = dim Ext¹(E, E)` on a 2-Calabi–Yau triangulated category, `D^b(X)` of a K3 surface
`X` for instance. Mukai's lemma (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.5) says that for a
distinguished triangle `A → D → B → A⟦1⟧` with `Hom(A, B) = 0`,

  `e(A) + e(B) ≤ e(D)`.

This file takes Mukai's lemma as the defining property of an abstract budget `e` and proves the
**Mukai budget lemma**: `e` is superadditive along every Postnikov tower whose triangles have no
maps from sub to quotient. The step condition follows from pairwise orthogonality of the factors,
so the budget holds along every HN filtration of every phase predicate with Hom vanishing from
higher to lower phase, at every slicing in particular:

  `∑ e(M_i) ≤ e(E)`.

No wall, path, word, autoequivalence, Picard rank or Riemann–Roch formula is used. HN prefixes are
instances of the tower form; so are the truncation towers of a t-structure, which this library
does not formalize.

## Main definitions

* `CategoryTheory.Triangulated.MukaiBudget`: an `ℕ`-valued function on objects, invariant under
  isomorphism and superadditive on Hom-orthogonal distinguished triangles (Mukai's lemma).
* `CategoryTheory.Triangulated.selfExtDim`: `dim_k Hom(X, X⟦1⟧)` on a `k`-linear category.
* `CategoryTheory.Triangulated.MukaiBudget.ofSelfExtDim`: the budget `e = selfExtDim k`, whose
  invariance under isomorphism is a theorem (`selfExtDim_congr`), from Mukai's lemma for it.

## Main results

* `MukaiBudget.e_zero`: Mukai's lemma on `0 → 0 → 0` forces `e(0) = 0`.
* `MukaiBudget.tower_sum_le`: **the budget along a Hom-orthogonal Postnikov tower**.
* `PostnikovTower.triangle_hom_eq_zero`: pairwise orthogonality of the factors gives the step
  condition.
* `MukaiBudget.hn_sum_le`, `MukaiBudget.slicing_sum_le`: **the budget along HN filtrations**.
* `MukaiBudget.card_nonrigid_le`: at most `⌊e(E)/2⌋` factors have `e ≠ 0`, using only that no
  factor has `e = 1`; evenness of `e` is one sufficient source (`card_nonrigid_le_of_even`).
* `MukaiBudget.e_factor_eq_zero_or_two`, `MukaiBudget.eq_of_e_factor_ne_zero`: if `e(E) = 2`, every
  factor has `e ∈ {0, 2}` and at most one has `e = 2`.
* `MukaiBudget.rigid_factors`: a rigid object has only rigid HN factors.
* `MukaiBudget.sum_e_eq_of_nonzero`: the sum `∑ e(M_i)`, hence the defect `e(E) - ∑ e(M_i)`, does
  not depend on the HN filtration with nonzero factors (HN uniqueness).

## Implementation notes

* `e` is `ℕ`-valued, and that is part of the interface, not a convenience: nonnegativity does not
  follow from the other two fields. For an integer-valued `e`, Mukai's lemma on `0 → 0 → 0` only
  gives `e(0) ≤ 0`, and the constant `-1` satisfies every field while the budget fails on the empty
  tower of `0` (`K3TwistsTest/BudgetModel.lean`).
* Invariance under isomorphism is a field because a Postnikov tower is tied to its chain only up
  to isomorphism. For `e = dim Hom(E, E⟦1⟧)` it holds in every `k`-linear category; no linearity of
  the shift functor is used (`selfExtDim_congr`).
* Mukai's lemma is a field. It is not a consequence of `k`-linearity: in the bounded derived
  category of vector spaces, the sum of `k → 0 → k⟦1⟧ → k⟦1⟧` and `k⟦-1⟧ → k⟦-1⟧ → 0 → k`
  is a distinguished triangle `A → D → B → A⟦1⟧` with `Hom(A, B) = 0`, `dim Hom(A, A⟦1⟧) = 1` and
  `dim Hom(D, D⟦1⟧) = dim Hom(B, B⟦1⟧) = 0`. Its proof needs Serre duality in dimension two.
* Evenness of `e` is not a field here: the counting results ask only that no factor has `e = 1`.
  On a 2-Calabi–Yau category every value is even (`TwoCYHypotheses.even` in
  `CategoryTheory/Triangulated/SerreFunctor/TwoCalabiYau.lean`).

## References

* A. Bayer, T. Bridgeland, *Derived automorphism groups of K3 surfaces of Picard rank 1*,
  arXiv:1310.8266, Lemma 2.5.
* S. Mukai, *On the moduli space of bundles on K3 surfaces I*, in *Vector bundles on algebraic
  varieties*, Tata Inst. Fund. Res. Stud. Math. 11 (1987).

## Tags

Mukai's lemma, Postnikov tower, Harder–Narasimhan filtration, slicing, self-extensions
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe w v u

namespace CategoryTheory.Triangulated

/-- **A Mukai budget.** A function `e` on objects with values in `ℕ`, invariant under
isomorphism, with `e(A) + e(B) ≤ e(D)` for every distinguished triangle `A → D → B → A⟦1⟧` with
`Hom(A, B) = 0`.

The model is `e(E) = dim Ext¹(E, E)` on a 2-Calabi–Yau category, where the inequality is Mukai's
lemma (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.5, after Mukai, *On the moduli space of bundles
on K3 surfaces I*, 1987). The values are natural numbers on purpose: nonnegativity is an
independent axiom, which an integer-valued version would have to state. -/
structure MukaiBudget (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] where
  /-- The budget of an object, `dim Ext¹(E, E)` in the geometric case. -/
  e : C → ℕ
  /-- Isomorphic objects have the same budget. -/
  e_iso : ∀ {X Y : C}, (X ≅ Y) → e X = e Y
  /-- **Mukai's lemma**: for a distinguished triangle `A → D → B → A⟦1⟧` with `Hom(A, B) = 0`,
  `e(A) + e(B) ≤ e(D)` (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.5). On a 2-Calabi–Yau category
  the second vanishing used in its proof, `Hom(B, A⟦2⟧) = 0`, is Serre dual to the first. -/
  mukai : ∀ T ∈ distTriang C, (∀ f : T.obj₁ ⟶ T.obj₃, f = 0) →
    e T.obj₁ + e T.obj₃ ≤ e T.obj₂

/-! ### The budget of a `k`-linear category -/

section SelfExt

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  (k : Type w) [Field k] [Linear k C]

/-- `dim_k Hom(X, X⟦1⟧)`, the dimension of `Ext¹(X, X)`. It is `0` when the space is
infinite-dimensional, so it is meant for Hom-finite categories. -/
abbrev selfExtDim (X : C) : ℕ :=
  Module.finrank k (X ⟶ X⟦(1 : ℤ)⟧)

/-- **Invariance under isomorphism needs only a `k`-linear category.** An isomorphism `X ≅ Y`
gives `Hom(X, X⟦n⟧) ≃ Hom(Y, Y⟦n⟧)` by composing with it and with its image under the shift
functor; no linearity of the shift functor is used. -/
theorem finrank_shiftHom_congr (n : ℤ) {X Y : C} (i : X ≅ Y) :
    Module.finrank k (X ⟶ X⟦n⟧) = Module.finrank k (Y ⟶ Y⟦n⟧) :=
  (Linear.homCongr k i ((shiftFunctor C n).mapIso i)).finrank_eq

theorem selfExtDim_congr {X Y : C} (i : X ≅ Y) : selfExtDim k X = selfExtDim k Y :=
  finrank_shiftHom_congr k 1 i

end SelfExt

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section Linear

variable (k : Type w) [Field k] [Linear k C]

/-- **The budget `e = dim Hom(E, E⟦1⟧)`.** On a `k`-linear category it is invariant under
isomorphism (`selfExtDim_congr`); Mukai's lemma for it is the one input. -/
def MukaiBudget.ofSelfExtDim
    (mukai : ∀ T ∈ distTriang C, (∀ f : T.obj₁ ⟶ T.obj₃, f = 0) →
      selfExtDim k T.obj₁ + selfExtDim k T.obj₃ ≤ selfExtDim k T.obj₂) :
    MukaiBudget C where
  e := selfExtDim k
  e_iso := selfExtDim_congr k
  mukai := mukai

@[simp]
theorem MukaiBudget.ofSelfExtDim_e
    (mukai : ∀ T ∈ distTriang C, (∀ f : T.obj₁ ⟶ T.obj₃, f = 0) →
      selfExtDim k T.obj₁ + selfExtDim k T.obj₃ ≤ selfExtDim k T.obj₂) (X : C) :
    (MukaiBudget.ofSelfExtDim k mukai).e X = selfExtDim k X :=
  rfl

end Linear

/-! ### Orthogonality along a tower -/

namespace PostnikovTower

/-- If `Hom(M_j, X) = 0` for the factors `M_0, …, M_{k-1}`, then `Hom(A_k, X) = 0` for the chain
object `A_k` they filter. -/
theorem chain_hom_eq_zero {E : C} (P : PostnikovTower C E) (X : C) :
    ∀ (k : ℕ) (hk : k ≤ P.n), (∀ j : Fin P.n, j.val < k → ∀ f : P.factor j ⟶ X, f = 0) →
      ∀ f : P.chain.obj' k (by lia) ⟶ X, f = 0 := by
  intro k
  induction k with
  | zero =>
    intro _ _ f
    exact P.base_isZero.eq_of_src f 0
  | succ k ih =>
    intro hk hX f
    let T := P.triangle ⟨k, by lia⟩
    let e₁ : T.obj₁ ≅ P.chain.obj' k (by lia) := (P.triangle_obj₁ ⟨k, by lia⟩).some
    let e₂ : T.obj₂ ≅ P.chain.obj' (k + 1) (by lia) := (P.triangle_obj₂ ⟨k, by lia⟩).some
    have hIH := ih (by lia) (fun j hj => hX j (by lia))
    have hf' : T.mor₁ ≫ (e₂.hom ≫ f) = 0 := by
      have : T.mor₁ ≫ e₂.hom ≫ f = e₁.hom ≫ (e₁.inv ≫ T.mor₁ ≫ e₂.hom ≫ f) := by simp
      rw [this, hIH (e₁.inv ≫ T.mor₁ ≫ e₂.hom ≫ f), comp_zero]
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T (P.triangle_dist _) _ hf'
    have hg0 : g = 0 := hX ⟨k, by lia⟩ (by simp) g
    have : e₂.hom ≫ f = 0 := by rw [hg, hg0, comp_zero]
    calc f = e₂.inv ≫ e₂.hom ≫ f := by simp
      _ = 0 := by rw [this, comp_zero]

/-- **Pairwise orthogonality of the factors gives the step condition.** If `Hom(M_j, M_i) = 0`
for `j < i`, every triangle `A_i → A_{i+1} → M_i` of the tower has `Hom(A_i, M_i) = 0`. -/
theorem triangle_hom_eq_zero {E : C} (P : PostnikovTower C E)
    (hfac : ∀ i j : Fin P.n, j < i → ∀ f : P.factor j ⟶ P.factor i, f = 0) (i : Fin P.n)
    (f : (P.triangle i).obj₁ ⟶ (P.triangle i).obj₃) : f = 0 := by
  let e₁ := (P.triangle_obj₁ i).some
  have h := chain_hom_eq_zero P (P.factor i) i.val (by lia)
    (fun j hj => hfac i j (Fin.mk_lt_mk.mpr hj)) (e₁.inv ≫ f)
  calc f = e₁.hom ≫ e₁.inv ≫ f := by simp
    _ = 0 := by erw [h]; exact comp_zero

end PostnikovTower

namespace MukaiBudget

variable (b : MukaiBudget C)

/-! ### The zero object -/

/-- Mukai's lemma on the contractible triangle `0 → 0 → 0` forces `e(0) = 0`. -/
theorem e_zero : b.e (0 : C) = 0 := by
  have h := b.mukai _ (contractible_distinguished (0 : C))
    (fun f => (isZero_zero C).eq_of_tgt f 0)
  change b.e 0 + b.e 0 ≤ b.e 0 at h
  lia

theorem e_of_isZero {X : C} (hX : IsZero X) : b.e X = 0 :=
  (b.e_iso hX.isoZero).trans b.e_zero

/-! ### The budget along towers and HN filtrations -/

/-- **The Mukai budget lemma, tower form.** If every triangle `A_k → A_{k+1} → M_k` of a Postnikov
tower of `E` has `Hom(A_k, M_k) = 0`, then `∑ e(M_k) ≤ e(E)`. The induction runs over the chain
prefixes: `∑_{i<k} e(M_i) ≤ e(A_k)`. -/
theorem tower_sum_le {E : C} (P : PostnikovTower C E)
    (horth : ∀ i, ∀ f : (P.triangle i).obj₁ ⟶ (P.triangle i).obj₃, f = 0) :
    ∑ i, b.e (P.factor i) ≤ b.e E := by
  have key : ∀ k (hk : k ≤ P.n),
      ∑ i : Fin k, b.e (P.factor ⟨i, by lia⟩) ≤ b.e (P.chain.obj' k (by lia)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [Fin.sum_univ_castSucc]
      have h1 := ih (by lia)
      have hT := b.mukai _ (P.triangle_dist ⟨k, by lia⟩) (horth _)
      rw [b.e_iso (P.triangle_obj₁ ⟨k, by lia⟩).some,
        b.e_iso (P.triangle_obj₂ ⟨k, by lia⟩).some] at hT
      exact (Nat.add_le_add_right h1 _).trans hT
  exact (key P.n le_rfl).trans (b.e_iso P.top_iso.some).le

/-- **The Mukai budget lemma for HN filtrations.** For any phase predicate with no maps from
higher to lower phase, every HN filtration of `E` has `∑ e(M_i) ≤ e(E)`. Only the Hom vanishing
and the strict decrease of the phases are used. -/
theorem hn_sum_le {P : ℝ → ObjectProperty C}
    (hvan : ∀ φ₁ φ₂ A B, φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ f : A ⟶ B, f = 0)
    {E : C} (F : HNFiltration C P E) :
    ∑ i, b.e (F.factor i) ≤ b.e E :=
  b.tower_sum_le F.toPostnikovTower
    (PostnikovTower.triangle_hom_eq_zero _ fun i j hji =>
      hvan (F.φ j) (F.φ i) _ _ (F.hφ hji) (F.semistable j) (F.semistable i))

/-- **The Mukai budget lemma at a slicing.** For every slicing `s` and every HN filtration of `E`
for `s`, `∑ e(M_i) ≤ e(E)`. -/
theorem slicing_sum_le (s : Slicing C) {E : C} (F : HNFiltration C s.P E) :
    ∑ i, b.e (F.factor i) ≤ b.e E :=
  b.hn_sum_le s.hom_vanishing F

/-- One factor has at most the budget of the whole. -/
theorem e_factor_le {P : ℝ → ObjectProperty C}
    (hvan : ∀ φ₁ φ₂ A B, φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ f : A ⟶ B, f = 0)
    {E : C} (F : HNFiltration C P E) (i : Fin F.n) : b.e (F.factor i) ≤ b.e E :=
  (Finset.single_le_sum (f := fun j => b.e (F.factor j)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)).trans (b.hn_sum_le hvan F)

/-- **A rigid object has only rigid HN factors**, at every slicing. -/
theorem rigid_factors {P : ℝ → ObjectProperty C}
    (hvan : ∀ φ₁ φ₂ A B, φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ f : A ⟶ B, f = 0)
    {E : C} (hE : b.e E = 0) (F : HNFiltration C P E) (i : Fin F.n) : b.e (F.factor i) = 0 := by
  have := b.e_factor_le hvan F i
  lia

/-! ### Counting non-rigid factors -/

private theorem two_mul_card_filter_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, f i ≠ 1) :
    2 * (s.filter fun i => f i ≠ 0).card ≤ ∑ i ∈ s, f i := by
  calc 2 * (s.filter fun i => f i ≠ 0).card = ∑ _i ∈ s.filter (fun i => f i ≠ 0), 2 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ s.filter (fun i => f i ≠ 0), f i := Finset.sum_le_sum fun i hi => by
        have hi' := Finset.mem_filter.1 hi
        have := h i hi'.1
        lia
    _ ≤ ∑ i ∈ s, f i := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- **At most `⌊e(E)/2⌋` non-rigid factors**, using only that no factor has `e = 1`. -/
theorem card_nonrigid_le {P : ℝ → ObjectProperty C}
    (hvan : ∀ φ₁ φ₂ A B, φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ f : A ⟶ B, f = 0)
    {E : C} (F : HNFiltration C P E) (hne : ∀ i, b.e (F.factor i) ≠ 1) :
    (Finset.univ.filter fun i => b.e (F.factor i) ≠ 0).card ≤ b.e E / 2 := by
  have h1 := two_mul_card_filter_le_sum Finset.univ (fun i => b.e (F.factor i))
    (fun i _ => hne i)
  have h2 := b.hn_sum_le hvan F
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  lia

/-- The count of non-rigid factors when `e` takes only even values. -/
theorem card_nonrigid_le_of_even {P : ℝ → ObjectProperty C}
    (hvan : ∀ φ₁ φ₂ A B, φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ f : A ⟶ B, f = 0)
    (heven : ∀ X, Even (b.e X)) {E : C} (F : HNFiltration C P E) :
    (Finset.univ.filter fun i => b.e (F.factor i) ≠ 0).card ≤ b.e E / 2 :=
  b.card_nonrigid_le hvan F fun i h => by
    obtain ⟨r, hr⟩ := heven (F.factor i)
    lia

/-- **`e(E) = 2`: every factor has `e ∈ {0, 2}`**, if no factor has `e = 1`. -/
theorem e_factor_eq_zero_or_two {P : ℝ → ObjectProperty C}
    (hvan : ∀ φ₁ φ₂ A B, φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ f : A ⟶ B, f = 0)
    {E : C} (hE : b.e E = 2) (F : HNFiltration C P E) (hne : ∀ i, b.e (F.factor i) ≠ 1)
    (i : Fin F.n) : b.e (F.factor i) = 0 ∨ b.e (F.factor i) = 2 := by
  have := b.e_factor_le hvan F i
  have := hne i
  lia

/-- **`e(E) = 2`: at most one factor is non-rigid**, if no factor has `e = 1`. -/
theorem eq_of_e_factor_ne_zero {P : ℝ → ObjectProperty C}
    (hvan : ∀ φ₁ φ₂ A B, φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ f : A ⟶ B, f = 0)
    {E : C} (hE : b.e E = 2) (F : HNFiltration C P E) (hne : ∀ i, b.e (F.factor i) ≠ 1)
    {i j : Fin F.n} (hi : b.e (F.factor i) ≠ 0) (hj : b.e (F.factor j) ≠ 0) : i = j := by
  have hcard := b.card_nonrigid_le hvan F hne
  rw [hE] at hcard
  exact Finset.card_le_one.mp (by simpa using hcard) i (by simpa using hi) j (by simpa using hj)

/-! ### The defect does not depend on the filtration -/

/-- **The budget sum is a function of the slicing.** Two HN filtrations of `E` with nonzero factors
have the same `∑ e(M_i)`, by uniqueness of HN filtrations; so the defect `e(E) - ∑ e(M_i)` is a
function of the slicing and the object. It does depend on the slicing. -/
theorem sum_e_eq_of_nonzero (s : Slicing C) {E : C} (F G : HNFiltration C s.P E)
    (hF : ∀ i, ¬IsZero (F.factor i)) (hG : ∀ j, ¬IsZero (G.factor j)) :
    ∑ i, b.e (F.factor i) = ∑ j, b.e (G.factor j) := by
  obtain ⟨hn, hi⟩ := HNFiltration.exists_iso_of_nonzero s F G hF hG
  refine Fintype.sum_equiv (finCongr hn) _ _ (fun i => ?_)
  obtain ⟨e⟩ := (hi i).2
  exact b.e_iso e

end MukaiBudget

end CategoryTheory.Triangulated
