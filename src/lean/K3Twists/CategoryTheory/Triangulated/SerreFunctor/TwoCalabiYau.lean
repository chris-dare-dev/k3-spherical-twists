/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.GrothendieckGroup.Basic
import K3Twists.CategoryTheory.Triangulated.SerreFunctor.Objects
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Tower
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# The 2-Calabi–Yau inputs of the Mukai budget

`TwoCYHypotheses k C q v` lists what the Mukai budget uses about a Hom-finite `k`-linear
triangulated category `C` whose Serre functor is the shift by two, `D^b(X)` of a K3 surface `X`
for instance, with a class map `v : K₀(C) → Λ` to a lattice with a symmetric bilinear form `q` (the
Mukai vector and the Mukai pairing). The budget is `e(E) = dim Hom(E, E⟦1⟧) = dim Ext¹(E, E)`
(`selfExtDim`), a natural number, so its nonnegativity is explicit, and its invariance under
isomorphism is a theorem of `k`-linear categories (`selfExtDim_congr`). The fields:

* Hom-finiteness;
* a Serre functor naturally isomorphic to `⟦2⟧` (a natural isomorphism of functors, not one
  isomorphism per object);
* Mukai's lemma for `e` (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.5);
* evenness of `e`;
* Riemann–Roch `e(E) = 2 + q(v(E), v(E))` for simple objects only: `End(E) = k` and no negative
  self-extensions.

From them, `TwoCYHypotheses.toMukaiBudget` is a `MukaiBudget`, and the budget theorems apply with
no hypothesis on the factors (`TwoCYHypotheses.atMostOnce_e`, `TwoCYHypotheses.carriesOnce_e_iff`).

## Sign convention

The pairing is Mukai's: `χ(E, F) = -q(v(E), v(F))`, so spherical classes have square `-2`
(`TwoCYHypotheses.sq_classOf_eq_neg_two`), the class of a point has square `0`, and
`e = 2 + q(v, v)` on simple objects.

## Why Riemann–Roch is not a field on all objects

On a 2-Calabi–Yau category `χ(E, E) = Σ (-1)^i dim Hom(E, E⟦i⟧)` and Serre duality give
`χ(E, E) = 2 dim End(E) - e(E)` when `E` has no negative self-extensions, so `e = 2 + q(v, v)`
needs `dim End(E) = 1`. It fails at the zero object, where Mukai's lemma forces `e(0) = 0` while
`v(0) = 0` (`K3TwistsTest/BudgetModel.lean`), and on direct sums, whose endomorphisms are larger.

## Real objects

The library has no 2-Calabi–Yau triangulated category, so this structure has no instance built
from real objects yet. In the preprojective model of a wall (`RepresentationTheory/Quiver/
Kronecker/Budget.lean`) Mukai's inequality, evenness and Riemann–Roch for representations with
one-dimensional endomorphisms are theorems, for extensions of representations rather than for
triangles: the model is the heart of the wall, not a triangulated category.

## Main definitions

* `CategoryTheory.Triangulated.TwoCYHypotheses`: the inputs.
* `CategoryTheory.Triangulated.TwoCYHypotheses.toMukaiBudget`: the budget `e = dim Ext¹`.

## Main results

* `selfExtDim_eq_zero_of_isSphericalObject`: a `2`-spherical object is rigid.
* `TwoCYHypotheses.finrank_shift_two`: `dim Hom(E, E⟦2⟧) = dim End(E)`, by Serre duality.
* `TwoCYHypotheses.selfExtDim_eq_two_of_isotropic`, `TwoCYHypotheses.sq_classOf_eq_neg_two`:
  Riemann–Roch for a simple isotropic object and for a spherical object.
* `TwoCYHypotheses.atMostOnce_e`, `TwoCYHypotheses.carriesOnce_e_iff`: the budget theorems.

## References

* A. Bayer, T. Bridgeland, *Derived automorphism groups of K3 surfaces of Picard rank 1*,
  arXiv:1310.8266, §2.
* D. Huybrechts, *Fourier–Mukai transforms in algebraic geometry*, Oxford, 2006, Ch. 10 (the
  Mukai vector and pairing).

## Tags

Calabi–Yau category, Serre functor, Mukai's lemma, Riemann–Roch, Mukai vector
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w' w v u

namespace CategoryTheory.Triangulated

/-- **A `2`-spherical object is rigid**: `Hom(E, E⟦1⟧) = 0`. -/
theorem selfExtDim_eq_zero_of_isSphericalObject {k : Type w} [Field k] {C : Type u}
    [Category.{v} C] [Preadditive C] [Linear k C] [HasShift C ℤ]
    {D : SerreFunctor.SerreFunctorData k C} {E : C} (h : SerreFunctor.IsSphericalObject D 2 E) :
    selfExtDim k E = 0 :=
  h.finrank_hom_eq_zero 1 one_ne_zero (by norm_num)

/-- **The 2-Calabi–Yau inputs of the Mukai budget** on a `k`-linear pretriangulated category `C`,
with a class map `v : K₀(C) → Λ` and a bilinear form `q` on `Λ` (Mukai's sign: `χ = -q ∘ v`).
`C` stands for `D^b(X)` of a K3 surface, `v` for the Mukai vector and `q` for the Mukai
pairing. -/
structure TwoCYHypotheses (k : Type w) [Field k] (C : Type u) [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Linear k C] {Λ : Type w'} [AddCommGroup Λ] (q : LinearMap.BilinForm ℤ Λ) (v : K₀ C →+ Λ) :
    Prop where
  /-- Every Hom-space is finite-dimensional. -/
  homFinite : SerreFunctor.HomFinite k C
  /-- A Serre functor naturally isomorphic to the shift by two: Serre duality
  `Hom(A, B)^* ≅ Hom(B, A⟦2⟧)`, natural in both variables (Bondal–Kapranov; for a K3 surface,
  Huybrechts, *Fourier–Mukai transforms in algebraic geometry*, Ch. 3). -/
  serre : ∃ D : SerreFunctor.SerreFunctorData k C, Nonempty (D.S ≅ shiftFunctor C (2 : ℤ))
  /-- **Mukai's lemma**: for a distinguished triangle `A → D → B → A⟦1⟧` with `Hom(A, B) = 0`,
  `e(A) + e(B) ≤ e(D)` (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.5). -/
  mukai : ∀ T ∈ distTriang C, (∀ f : T.obj₁ ⟶ T.obj₃, f = 0) →
    selfExtDim k T.obj₁ + selfExtDim k T.obj₃ ≤ selfExtDim k T.obj₂
  /-- **`e` is even.** On `D^b(X)` of a K3 surface, Serre duality gives
  `dim Hom(E, E⟦i⟧) = dim Hom(E, E⟦2 - i⟧)`, so `e(E) ≡ χ(E, E) = -v(E)² (mod 2)`, and the Mukai
  lattice is even (Huybrechts, *Fourier–Mukai transforms in algebraic geometry*, Ch. 10). -/
  even : ∀ X : C, Even (selfExtDim k X)
  /-- **Riemann–Roch for simple objects**: if `End(E) = k` and `E` has no negative
  self-extensions, then `e(E) = 2 + q(v(E), v(E))`. With Serre duality `χ(E, E) = 2 - e(E)`, and
  `χ(E, E) = -q(v(E), v(E))` (Mukai; Huybrechts, *Fourier–Mukai transforms in algebraic geometry*,
  Ch. 10). Stated only for such objects: on all objects it fails at `0` and on direct sums. -/
  riemannRoch : ∀ X : C, Module.finrank k (X ⟶ X) = 1 →
    (∀ n : ℤ, n < 0 → ∀ f : X ⟶ X⟦n⟧, f = 0) →
    (selfExtDim k X : ℤ) = 2 + q (classOf C v X) (classOf C v X)

namespace TwoCYHypotheses

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Linear k C]
  {Λ : Type w'} [AddCommGroup Λ] {q : LinearMap.BilinForm ℤ Λ} {v : K₀ C →+ Λ}
  (h : TwoCYHypotheses k C q v)

/-- **The Mukai budget `e = dim Ext¹`** of a 2-Calabi–Yau category. -/
def toMukaiBudget : MukaiBudget C :=
  MukaiBudget.ofSelfExtDim k h.mukai

@[simp]
theorem toMukaiBudget_e (X : C) : h.toMukaiBudget.e X = selfExtDim k X :=
  rfl

theorem even_e (X : C) : Even (h.toMukaiBudget.e X) :=
  h.even X

include h in
/-- **Serre duality in degree two**: `dim Hom(E, E⟦2⟧) = dim End(E)`. For a simple object this is
the one-dimensional top self-extension that makes `χ(E, E) = 2 - e(E)`. -/
theorem finrank_shift_two (X : C) :
    Module.finrank k (X ⟶ X⟦(2 : ℤ)⟧) = Module.finrank k (X ⟶ X) := by
  haveI := h.homFinite
  obtain ⟨D, ⟨i⟩⟩ := h.serre
  rw [D.finrank_hom_eq X X]
  exact ((Linear.homCongr k (Iso.refl X) (i.app X)).finrank_eq).symm

include h in
/-- **Riemann–Roch for a simple isotropic object**: `e(E) = 2`, the self-extensions of a point. -/
theorem selfExtDim_eq_two_of_isotropic {X : C} (hEnd : Module.finrank k (X ⟶ X) = 1)
    (hneg : ∀ n : ℤ, n < 0 → ∀ f : X ⟶ X⟦n⟧, f = 0)
    (hiso : q (classOf C v X) (classOf C v X) = 0) : selfExtDim k X = 2 := by
  have := h.riemannRoch X hEnd hneg
  rw [hiso] at this
  lia

include h in
/-- **A `2`-spherical object has a class of square `-2`.** -/
theorem sq_classOf_eq_neg_two {D : SerreFunctor.SerreFunctorData k C} {X : C}
    (hX : SerreFunctor.IsSphericalObject D 2 X) :
    q (classOf C v X) (classOf C v X) = -2 := by
  have hrr := h.riemannRoch X hX.finrank_end
    (fun n hn f => hX.vanishing n (by lia) (by lia) f)
  rw [selfExtDim_eq_zero_of_isSphericalObject hX] at hrr
  lia

include h in
/-- **At most one factor with `e = 2`, the others rigid**, for every HN filtration of an object
with `e(E) = 2`, at every slicing: evenness rules out factors with `e = 1`. -/
theorem atMostOnce_e (s : Slicing C) {E : C} (hE : selfExtDim k E = 2)
    (F : HNFiltration C s.P E) :
    F.AtMostOnce (fun X => selfExtDim k X = 2) (fun X => selfExtDim k X = 0) :=
  h.toMukaiBudget.atMostOnce_e_of_even s.hom_vanishing h.even_e hE F

include h in
/-- **The tower property for `e`, as zero defect**: `E` with `e(E) = 2` has one HN factor with
`e = 2` and the others rigid exactly when the budget defect of an HN filtration with nonzero
factors vanishes. -/
theorem carriesOnce_e_iff (s : Slicing C) {E : C} (hE : selfExtDim k E = 2) :
    s.CarriesOnce (fun X => selfExtDim k X = 2) (fun X => selfExtDim k X = 0) E ↔
      ∃ F : HNFiltration C s.P E, (∀ i, ¬IsZero (F.factor i)) ∧
        ∑ i, selfExtDim k (F.factor i) = selfExtDim k E :=
  h.toMukaiBudget.carriesOnce_e_iff s hE fun _ X _ h1 => by
    obtain ⟨r, hr⟩ := h.even X
    change selfExtDim k X = 1 at h1
    lia

end TwoCYHypotheses

end CategoryTheory.Triangulated
