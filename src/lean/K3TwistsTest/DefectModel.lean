/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Dimension.ExactSequenceDefect
import K3Twists.RepresentationTheory.Quiver.Kronecker.FibreFunctorProfile

/-!
# The defect identity at the contraction of a rational curve, and fibre-functor profiles

At the wall contracting a smooth rational curve `C`, take `A = 𝒪_C`, `B = 𝒪_C(-1)[1]` and a framing
object `D` with `m = D · C` (up to sign). `RHom(D, -)` has dimensions `m + 1` in degree `0` on `A`
and `m` in degree `-1` on `B`. In the extension presenting the point sheaf the connecting map has
rank `m`, so `R = m t⁻¹` and `P_E = 1`; in the reverse extension it vanishes and
`P_E = (m + 1) + m t⁻¹`. Both have Euler characteristic `1`; their totals differ by `2R(1) = 2m`,
so over a family with Euler characteristic `2` (the projective line of extensions) the unsigned
jump is `-4m` while the signed one is `0`. Only the dimensions are inputs here; the identities
are the defect identity of `LinearAlgebra/Dimension/ExactSequenceDefect.lean`.
-/

open LaurentPolynomial Finsupp

namespace DefectModel

variable (m : ℕ)

/-- The degree-resolved dimensions at the curve wall: `RHom(D, A)`, `RHom(D, B)`, the point
extension and the reverse extension, and the rank of the connecting map for the point. -/
noncomputable def dimA : ℤ →₀ ℕ := single 0 (m + 1)
noncomputable def dimB : ℤ →₀ ℕ := single (-1) m
noncomputable def dimPoint : ℤ →₀ ℕ := single 0 1
noncomputable def dimReverse : ℤ →₀ ℕ := single 0 (m + 1) + single (-1) m
noncomputable def rankPoint : ℤ →₀ ℕ := single (-1) m

lemma point_degreewise (j : ℤ) :
    dimPoint j + rankPoint m (j - 1) + rankPoint m j = dimA m j + dimB m j := by
  simp only [dimPoint, rankPoint, dimA, dimB, single_apply]
  split_ifs <;> omega

lemma reverse_degreewise (j : ℤ) :
    dimReverse m j + (0 : ℤ →₀ ℕ) (j - 1) + (0 : ℤ →₀ ℕ) j = dimA m j + dimB m j := by
  simp [dimReverse, dimA, dimB]

/-- `P_E = P_A + P_B - (1 + t) m t⁻¹` for the point extension. -/
example : poincare dimPoint = poincare (dimA m) + poincare (dimB m) -
    (1 + T 1) * poincare (rankPoint m) :=
  poincare_eq_sub_mul (point_degreewise m)

/-- The connecting rank is forced: any `R` with the same dimensions is `m t⁻¹`. -/
example (r : ℤ →₀ ℕ) (h : ∀ j, dimPoint j + r (j - 1) + r j = dimA m j + dimB m j) :
    r = rankPoint m :=
  defect_unique h (point_degreewise m)

/-- Both extensions have Euler characteristic `1`. -/
example : dimPoint.poincareNegOne = 1 ∧ (dimReverse m).poincareNegOne = 1 := by
  constructor
  · simp [dimPoint]
  · simp [dimReverse, Int.negOnePow_neg]

/-- The totals differ by `2R(1) = 2m`; over a family with Euler characteristic `2` the unsigned
jump from the reverse side to the point side is `-4m`. -/
example : 2 * ((dimPoint.poincareOne : ℤ) - (dimReverse m).poincareOne) = -4 * m := by
  simp [dimPoint, dimReverse]
  ring

end DefectModel

namespace FibreFunctorModel

open Quiver.Kronecker DoubledRep Module

/-- The form of Mukai's sign on dimension vectors of the `2`-Kronecker quiver:
`⟨s₀, s₀⟩ = -2` for the simple at a vertex, `⟨s₀, s₁⟩ = 2`, `⟨δ, δ⟩ = 0` for `δ = (1, 1)`. -/
example : mukaiDimForm (Fin 2) ![1, 0] ![1, 0] = -2 ∧ mukaiDimForm (Fin 2) ![1, 0] ![0, 1] = 2 ∧
    mukaiDimForm (Fin 2) ![1, 1] ![1, 1] = 0 := by
  simp [mukaiDimForm_apply]

variable (k : Type*) [Field k]

/-- The simple representation at vertex zero, `k ⇉ 0`. -/
def simpleZero : DoubledRep k (Fin 2) (Fin 1 → k) (Fin 0 → k) := ⟨fun _ ↦ 0, fun _ ↦ 0⟩

lemma simpleZero_isPreprojective : (simpleZero k).IsPreprojective := by
  simp [IsPreprojective, simpleZero]

/-- The fibre-functor profile of `RHom(S₀, -)` bounds `|⟨v(S₀), v(E)⟩|` on every preprojective
representation; at `E = S₀` the bound is `2 ≤ dim Hom + dim Ext¹ + dim Ext²`. -/
example : 2 ≤ finrank k (Hom (simpleZero k) (simpleZero k)) +
    finrank k (Ext1 (simpleZero k) (simpleZero k)) +
      finrank k (Ext2 (simpleZero k) (simpleZero k)) := by
  have := abs_cartanForm_le (simpleZero k) (simpleZero_isPreprojective k)
    ⟨(1, 0), ⟨simpleZero k, simpleZero_isPreprojective k⟩⟩
  simp only [Module.finrank_fin_fun, mukaiDimForm_apply] at this
  norm_num at this
  exact_mod_cast this

end FibreFunctorModel
