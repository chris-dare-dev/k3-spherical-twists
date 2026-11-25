/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.Eichler
import Mathlib.Data.ZMod.Basic

/-!
# Tests for Eichler transvections

* The closed power formula `E(e, x, q)ⁿ = E(e, nx, n²q)` needs `2q = B(x, x)`: on the hyperbolic
  plane `MukaiLattice ℤ PUnit`, `E(pt, 0, 1)² = E(pt, 0, 2) ≠ E(pt, 0, 4)`.
* The descent of `x ↦ E_Q(e, x)` to `e^⊥/Re` needs `Q e = 0`, not only `B(e, e) = 0`: for
  `Q(a, b) = a² + ab` on `(ZMod 2)²` and `e = (1, 0)`, the polar form vanishes at `(e, e)` but
  `Q e = 1`, and `E_Q(e, e) ≠ E_Q(e, 0)`.

Built by `lake test`.
-/

namespace K3TwistsTest.Eichler

open BilinearForm Mukai

/-- **The power formula needs `2q = B(x, x)`.** -/
example :
    eichler (mukaiForm (0 : PUnit →ₗ[ℤ] PUnit →ₗ[ℤ] ℤ)) corankUnit 0 1 ^ 2 ≠
      eichler (mukaiForm (0 : PUnit →ₗ[ℤ] PUnit →ₗ[ℤ] ℤ)) corankUnit (((2 : ℕ) : ℤ) • 0)
        (((2 : ℕ) : ℤ) ^ 2 * 1) := by
  intro h
  have := LinearMap.congr_fun h ((1 : ℤ), PUnit.unit, (0 : ℤ))
  simp [sq, mul_apply_eq_comp, eichler_apply, corankUnit, pairing] at this

/-- The general power formula gives the right answer there: `E(pt, 0, 1)² = E(pt, 0, 2)`. -/
example :
    eichler (mukaiForm (0 : PUnit →ₗ[ℤ] PUnit →ₗ[ℤ] ℤ)) corankUnit 0 1 ^ 2 =
      eichler (mukaiForm (0 : PUnit →ₗ[ℤ] PUnit →ₗ[ℤ] ℤ)) corankUnit 0 2 := by
  rw [eichler_pow_eq _ (fun x y => pairing_comm _ (fun _ _ => rfl) x y)
    (by simp [corankUnit, pairing]) (by simp)]
  norm_num

/-- The bilinear form `B((a, b), (a', b')) = aa' + ab'` on `(ZMod 2)²`. -/
def B2 : LinearMap.BilinForm (ZMod 2) (ZMod 2 × ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) (fun v w => v.1 * w.1 + v.1 * w.2)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)

/-- `Q(a, b) = a² + ab`. -/
def Q2 : QuadraticForm (ZMod 2) (ZMod 2 × ZMod 2) := LinearMap.BilinMap.toQuadraticMap B2

/-- **Descent needs `Q e = 0`.** -/
example :
    Q2.polarBilin ((1 : ZMod 2), (0 : ZMod 2)) (1, 0) = 0 ∧
      Q2 ((1 : ZMod 2), (0 : ZMod 2)) = 1 ∧
      eichlerQ Q2 ((1 : ZMod 2), (0 : ZMod 2)) (0 + (1 : ZMod 2) • ((1 : ZMod 2), (0 : ZMod 2))) ≠
        eichlerQ Q2 ((1 : ZMod 2), (0 : ZMod 2)) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, Q2, B2,
      LinearMap.BilinMap.toQuadraticMap_apply]
    decide
  · simp [Q2, B2, LinearMap.BilinMap.toQuadraticMap_apply]
  · intro h
    have h1 := congrArg (fun f => (f ((0 : ZMod 2), (1 : ZMod 2))).1) h
    simp [eichlerQ, eichler_apply, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      Q2, B2, LinearMap.BilinMap.toQuadraticMap_apply] at h1

end K3TwistsTest.Eichler
