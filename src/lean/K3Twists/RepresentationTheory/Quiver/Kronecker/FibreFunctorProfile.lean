/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import K3Twists.CategoryTheory.MassProfile.FibreFunctor
import K3Twists.Combinatorics.Quiver.Kronecker.CartanMatrix
import K3Twists.RepresentationTheory.Quiver.Kronecker.Ext

/-!
# The fibre-functor profile of `RHom(A, -)` on Kronecker representations

The instance from real objects of `FibreFunctorProfile`. For representations `X`, `Y` of the
doubled Kronecker quiver with `g` arrows and the preprojective relations, the standard complex
`C⁰ → C¹ → C²` (`Ext.lean`) has `H⁰ = Hom(X, Y)` and `H¹ = Ext¹(X, Y)`; its cokernel
`Ext2 X Y = C² ⧸ im d₁₂` has dimension `dim Hom(Y, X)` (`finrank_Ext2`), the numerical form of the
`2`-Calabi–Yau duality of the preprojective algebra. With Crawley-Boevey's formula
`dim Ext¹(X, Y) = dim Hom(X, Y) + dim Hom(Y, X) - (x, y)` (Amer. J. Math. 122 (2000), Lemma 1),
the Euler characteristic of `RHom(A, E)` is `(a, e) = aᵀ C e`, `C = [[2, -g], [-g, 2]]` the Cartan
matrix, which is `-⟨a, e⟩` for the form `⟨x, y⟩ = -xᵀ C y` of Mukai's sign (`mukaiDimForm`).

So `homFibreFunctorProfile A` is a fibre-functor profile on the finite-dimensional
representations with the relations, with class map the dimension vector and `w = v(A)`, and
`FibreFunctorProfile.abs_le_mass` reads

  `dim Hom(A, E) + dim Ext¹(A, E) + dim Ext²(A, E) ≥ |(a, e)|`, with equal parity

(`abs_cartanForm_le`).
-/

open Module Matrix

namespace Quiver.Kronecker

open DoubledRep

variable {k ι V₀ V₁ W₀ W₁ : Type*} [Field k] [Fintype ι] [AddCommGroup V₀] [Module k V₀]
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup W₀] [Module k W₀] [AddCommGroup W₁]
  [Module k W₁]

namespace DoubledRep

/-- `Ext²` of the standard complex: the cokernel `C² ⧸ im d₁₂` of its last differential. -/
abbrev Ext2 (X : DoubledRep k ι V₀ V₁) (Y : DoubledRep k ι W₀ W₁) :=
  ((V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁)) ⧸ LinearMap.range (d₁₂ X Y)

variable [FiniteDimensional k V₀] [FiniteDimensional k V₁] [FiniteDimensional k W₀]
  [FiniteDimensional k W₁]

/-- **`2`-Calabi–Yau duality, numerically**: `dim Ext²(X, Y) = dim Hom(Y, X)`. -/
theorem finrank_Ext2 (X : DoubledRep k ι V₀ V₁) (Y : DoubledRep k ι W₀ W₁) :
    finrank k (Ext2 X Y) = finrank k (Hom Y X) := by
  have e₁ := Submodule.finrank_quotient_add_finrank (LinearMap.range (d₁₂ X Y))
  have e₂ : finrank k (LinearMap.range (d₀₁ Y X)) + finrank k (Hom Y X) =
      finrank k ((W₀ →ₗ[k] V₀) × (W₁ →ₗ[k] V₁)) := by
    rw [← ker_d₀₁]
    exact LinearMap.finrank_range_add_finrank_ker _
  rw [finrank_range_d₁₂] at e₁
  simp only [Module.finrank_prod, Module.finrank_linearMap] at e₁ e₂
  linarith [mul_comm (finrank k V₀) (finrank k W₀), mul_comm (finrank k V₁) (finrank k W₁)]

end DoubledRep

variable (k ι) in
/-- Finite-dimensional representations with the preprojective relations, on coordinate spaces
`k^{d₀}`, `k^{d₁}` for every dimension vector `d`. -/
def PreprojectiveRep : Type _ :=
  Σ d : ℕ × ℕ, {E : DoubledRep k ι (Fin d.1 → k) (Fin d.2 → k) // E.IsPreprojective}

variable (ι) in
/-- The form `⟨x, y⟩ = -xᵀ C y` of Mukai's sign on dimension vectors, `C` the Cartan matrix of
the Kronecker quiver with `|ι|` arrows. -/
noncomputable def mukaiDimForm : LinearMap.BilinForm ℤ (Fin 2 → ℤ) :=
  -Matrix.toBilin' (cartanMatrix (Fintype.card ι : ℤ))

lemma mukaiDimForm_apply (x y : Fin 2 → ℤ) :
    mukaiDimForm ι x y = -(2 * x 0 * y 0 + 2 * x 1 * y 1 -
      Fintype.card ι * (x 0 * y 1 + x 1 * y 0)) := by
  simp [mukaiDimForm, Matrix.toBilin'_apply', cartanMatrix, dotProduct, mulVec,
    Fin.sum_univ_two]
  ring

variable [FiniteDimensional k V₀] [FiniteDimensional k V₁]

/-- **The fibre-functor profile of `RHom(A, -)`**: graded dimensions `dim Hom(A, E)`,
`dim Ext¹(A, E)`, `dim Ext²(A, E)` in degrees `0, 1, 2`, class map the dimension vector and
`w = v(A)`. -/
noncomputable def homFibreFunctorProfile (A : DoubledRep k ι V₀ V₁) (hA : A.IsPreprojective) :
    FibreFunctorProfile (PreprojectiveRep k ι) (Fin 2 → ℤ) (mukaiDimForm ι) where
  dims E := Finsupp.single 0 (finrank k (Hom A E.2.1)) +
    Finsupp.single 1 (finrank k (Ext1 A E.2.1)) + Finsupp.single 2 (finrank k (Ext2 A E.2.1))
  cls E := ![E.1.1, E.1.2]
  w := ![finrank k V₀, finrank k V₁]
  poincareNegOne_dims E := by
    have h := finrank_Ext1 hA E.2.2
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    simp only [Finsupp.poincareNegOne_add, Finsupp.poincareNegOne_single, finrank_Ext2,
      mukaiDimForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one, neg_neg]
    simp only [Int.negOnePow_zero, Int.negOnePow_one, Units.val_one, Units.val_neg, one_mul,
      neg_mul, show Int.negOnePow 2 = 1 from Int.negOnePow_even 2 even_two]
    have h' := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h' ⊢
    linarith

/-- `dim Hom(A, E) + dim Ext¹(A, E) + dim Ext²(A, E) ≥ |(a, e)|`, `(a, e) = aᵀ C e` the
symmetric Euler form, with equal parity. -/
theorem abs_cartanForm_le (A : DoubledRep k ι V₀ V₁) (hA : A.IsPreprojective)
    (E : PreprojectiveRep k ι) :
    |mukaiDimForm ι ![finrank k V₀, finrank k V₁] ![E.1.1, E.1.2]| ≤
      finrank k (Hom A E.2.1) + finrank k (Ext1 A E.2.1) + finrank k (Ext2 A E.2.1) := by
  have := (homFibreFunctorProfile A hA).abs_le_mass E
  simpa [FibreFunctorProfile.mass, homFibreFunctorProfile] using this

end Quiver.Kronecker
