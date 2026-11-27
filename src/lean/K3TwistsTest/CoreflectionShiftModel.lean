/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.ObjectProperty.CoreflectionShift
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Coreflections into a shifted class: models

* **The zero class.** In a pretriangulated category, the zero morphism `0 ⟶ K⟦1⟧` represents
  `Hom(-, K⟦1⟧)` on the zero objects, so its adjoint `0⟦-1⟧ ⟶ K` is a coreflection of `K` into
  the shifted zero class; conversely the zero morphism `0⟦-1⟧ ⟶ K`, checked by hand, gives back
  a representing object. Both directions of `isCoreflection_shift_iff_homEquiv` are used, with
  the shift adjunction of Mathlib's `shiftEquiv'`, and `Hom(-, K⟦1⟧)` is representable on the
  zero objects.
* **Transport across an autoequivalence.** For the shift itself, `Φ = ⟦-1⟧`, the hypothesis of
  `isCoreflection_shift_of_equivalence` holds by definition.
* **A brick.** In `ModuleCat k` over a field `k`, the module `k` is a brick: its endomorphisms
  are scalars. `End(k)` has the basis `𝟙`, so `⨁_{j < 1} k ⟶ k` is a coreflection of `k` into
  `addClosure k`, and so is `⨁_j k ⟶ M` for any basis of `Hom(k, M)`.
* **The single-edge corollary** in a `k`-linear pretriangulated category: the radical
  `⨁_j S⟦-1⟧ ⟶ K` from a brick `S` and a basis of `Hom(S, K⟦1⟧)`.

Built by `lake test`.
-/

namespace CoreflectionShiftModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

/-! ### The zero class in a pretriangulated category -/

section ZeroClass

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

open ZeroObject

/-- The zero objects. -/
def zeroClass : ObjectProperty C := fun X => IsZero X

instance : (zeroClass (C := C)).IsClosedUnderIsomorphisms where
  of_iso e h := IsZero.of_iso h e.symm

variable (C) in
/-- The shift adjunction `⟦-1⟧ ⊣ ⟦1⟧` of Mathlib's `shiftEquiv'`. -/
abbrev adj : shiftFunctor C (-1 : ℤ) ⊣ shiftFunctor C (1 : ℤ) :=
  (shiftEquiv' C (-1 : ℤ) 1 (neg_add_cancel 1)).toAdjunction

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Composition is bijective on the morphisms out of a zero object. -/
theorem bijective_of_isZero {X Y R : C} (hX : IsZero X) (f : Y ⟶ R) :
    Function.Bijective fun g : X ⟶ Y => g ≫ f :=
  ⟨fun g g' _ => hX.eq_of_src g g', fun _ => ⟨0, hX.eq_of_src _ _⟩⟩

omit [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The zero morphism represents `Hom(-, K⟦1⟧)` on the zero objects. -/
theorem isCoreflection_zero (K : C) : zeroClass.IsCoreflection (0 : (0 : C) ⟶ K⟦(1 : ℤ)⟧) :=
  ⟨isZero_zero C, fun _ hX => bijective_of_isZero hX _⟩

/-- Its adjoint `0⟦-1⟧ ⟶ K` is a coreflection of `K` into the shifted zero class. -/
example (K : C) :
    (zeroClass.shift (1 : ℤ)).IsCoreflection (((adj C).homEquiv (0 : C) K).symm 0) :=
  (isCoreflection_shift_homEquiv_symm_iff _ (adj C) _).2 (isCoreflection_zero K)

omit [HasZeroObject C] [Pretriangulated C] in
/-- An object whose shift by `1` is zero is zero. -/
theorem isZero_of_isZero_shift {X : C} (hX : IsZero (X⟦(1 : ℤ)⟧)) : IsZero X :=
  ((shiftFunctor C (-1 : ℤ)).map_isZero hX).of_iso (shiftShiftNeg X (1 : ℤ)).symm

/-- Conversely, the zero morphism `0⟦-1⟧ ⟶ K` is a coreflection into the shifted zero class, by
hand, so its adjoint represents `Hom(-, K⟦1⟧)` on the zero objects. -/
example (K : C) : zeroClass.IsCoreflection ((adj C).homEquiv (0 : C) K 0) := by
  refine (isCoreflection_shift_iff_homEquiv _ (adj C) _).1 ⟨?_, fun X hX => ?_⟩
  · exact (shiftFunctor C (1 : ℤ)).map_isZero
      ((shiftFunctor C (-1 : ℤ)).map_isZero (isZero_zero C))
  · exact bijective_of_isZero (isZero_of_isZero_shift hX) _

/-- `Hom(-, K⟦1⟧)` is representable on the zero objects. -/
example (K : C) : (zeroClass.ι.op ⋙ yoneda.obj (K⟦(1 : ℤ)⟧)).IsRepresentable :=
  (exists_isCoreflection_shift_iff zeroClass (1 : ℤ) K).1
    ⟨_, _, (isCoreflection_shift_homEquiv_symm_iff _ (adj C) _).2 (isCoreflection_zero K)⟩

/-- Transport across the autoequivalence `⟦-1⟧`: a coreflection of `K⟦1⟧` into a class gives
one of `K` into the shifted class. -/
example (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] {D K : C}
    {ε' : D ⟶ K⟦(1 : ℤ)⟧} (h : P.IsCoreflection ε') :
    (P.shift (1 : ℤ)).IsCoreflection
      (((shiftEquiv' C (-1 : ℤ) 1 (neg_add_cancel 1)).toAdjunction.homEquiv D K).symm ε') :=
  isCoreflection_shift_of_equivalence P (shiftEquiv' C (-1 : ℤ) 1 (neg_add_cancel 1))
    (fun _ => Iff.rfl) h

end ZeroClass

/-! ### A brick in vector spaces -/

section Brick

variable (k : Type) [Field k]

/-- The module `k` over itself. -/
abbrev S : ModuleCat.{0} k := ModuleCat.of k k

/-- An endomorphism of `k` is multiplication by its value at `1`. -/
theorem hom_apply (f : S k ⟶ S k) (x : k) : f.hom x = f.hom 1 * x := by
  rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- `k` is a brick: its endomorphisms are scalars. -/
theorem brick (f : S k ⟶ S k) : ∃ c : k, f = c • 𝟙 (S k) :=
  ⟨f.hom 1, by ext; simp⟩

/-- `End(k) ≃ k`, `f ↦ f 1`. -/
def endEquiv : (S k ⟶ S k) ≃ₗ[k] k where
  toFun f := f.hom 1
  invFun c := c • 𝟙 (S k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by ext; simp
  right_inv c := by simp

/-- The basis `𝟙` of `End(k)`. -/
noncomputable def endBasis : Module.Basis (Fin 1) k (S k ⟶ S k) :=
  (Module.Basis.singleton (Fin 1) k).map (endEquiv k).symm

/-- `⨁_{j < 1} k ⟶ k`, with component `𝟙`, is a coreflection of `k` into `addClosure k`. -/
example : (addClosure (S k)).IsCoreflection (biproduct.desc fun j => endBasis k j) :=
  isCoreflection_biproductDesc_basis (brick k) (endBasis k)

/-- For any basis `e` of `Hom(k, M)`, `⨁_j k ⟶ M` with components `e_j` is a coreflection of `M`
into `addClosure k`. -/
example (M : ModuleCat.{0} k) {m : ℕ} (e : Module.Basis (Fin m) k (S k ⟶ M)) :
    (addClosure (S k)).IsCoreflection (biproduct.desc fun j => e j) :=
  isCoreflection_biproductDesc_basis (brick k) e

end Brick

/-! ### The single-edge corollary -/

section SingleEdge

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {k : Type*} [Field k] [Linear k C]

/-- In a `k`-linear pretriangulated category, a brick `S` and a basis of `Hom(S, K⟦1⟧)` give the
radical `⨁_j S⟦-1⟧ ⟶ K` of `K` for `(addClosure S)[-1]`. -/
example {S K : C} (hS : ∀ f : S ⟶ S, ∃ c : k, f = c • 𝟙 S) {m : ℕ}
    (e : Module.Basis (Fin m) k (S ⟶ K⟦(1 : ℤ)⟧)) :
    ((addClosure S).shift (1 : ℤ)).IsCoreflection
      (biproduct.desc (f := fun _ : Fin m => S⟦(-1 : ℤ)⟧) fun j =>
        ((adj C).homEquiv S K).symm (e j)) :=
  isCoreflection_desc_shift_addClosure (adj C) hS e

end SingleEdge

end CoreflectionShiftModel
