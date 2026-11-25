/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The Gram matrix of a family and the Tits identity

For a bilinear form `B` on a module over a commutative ring and a finite family `s : ι → M`, the
**Gram matrix** is `G i j = B(s i, s j)`. The **Tits identity** expresses the form on a combination
of the family through it:

```
B(Σ aᵢ sᵢ, Σ aᵢ sᵢ) = aᵀ G a.
```

With the K3 sign convention `χ(E, F) = -⟨v(E), v(F)⟩`, if the classes `vᵢ` of the simple objects
of a wall have `-⟨vᵢ, vⱼ⟩ = Aᵢⱼ`, then the class of an object of multiplicities `a` has square
`-aᵀ A a`: minus the Tits form of the quiver of the wall
(`apply_sum_smul_sum_smul_of_apply_eq_neg`). For two simples it is the binary case
`apply_smul_add_smul_self`.

No symmetry of `B` and no hypothesis on `ι` beyond finiteness is used.
-/

namespace BilinearForm

open Matrix

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : M →ₗ[R] M →ₗ[R] R)

/-- The Gram matrix `G i j = B(s i, s j)` of a family. -/
def gram (s : ι → M) : Matrix ι ι R :=
  Matrix.of fun i j => B (s i) (s j)

@[simp]
theorem gram_apply (s : ι → M) (i j : ι) : gram B s i j = B (s i) (s j) :=
  rfl

variable [Fintype ι]

/-- **The Tits identity.** `B(Σ aᵢ sᵢ, Σ aᵢ sᵢ) = aᵀ G a` for the Gram matrix `G` of `s`. -/
theorem apply_sum_smul_sum_smul (s : ι → M) (a : ι → R) :
    B (∑ i, a i • s i) (∑ i, a i • s i) = a ⬝ᵥ (gram B s *ᵥ a) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    dotProduct, mulVec, gram_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The Tits identity with the K3 sign.** If `B(s i, s j) = -A i j`, then
`B(Σ aᵢ sᵢ, Σ aᵢ sᵢ) = -aᵀ A a`. -/
theorem apply_sum_smul_sum_smul_of_apply_eq_neg (s : ι → M) (A : Matrix ι ι R)
    (hA : ∀ i j, B (s i) (s j) = -A i j) (a : ι → R) :
    B (∑ i, a i • s i) (∑ i, a i • s i) = -(a ⬝ᵥ (A *ᵥ a)) := by
  rw [apply_sum_smul_sum_smul]
  have : gram B s = -A := by
    ext i j
    simp [hA]
  rw [this, neg_mulVec, dotProduct_neg]

/-- **The Tits identity for two classes.**
`B(ax + by, ax + by) = a² B(x, x) + ab (B(x, y) + B(y, x)) + b² B(y, y)`. -/
theorem apply_smul_add_smul_self (x y : M) (a b : R) :
    B (a • x + b • y) (a • x + b • y) =
      a ^ 2 * B x x + a * b * (B x y + B y x) + b ^ 2 * B y y := by
  have h := apply_sum_smul_sum_smul B ![x, y] ![a, b]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h]
  simp only [dotProduct, mulVec, gram_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

end BilinearForm
