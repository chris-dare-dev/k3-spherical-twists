/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.BPS

/-!
# Models of the BPS interface

* **One spherical object** (`pointQuiver`): the quiver with one vertex and no arrows. Its Kac data
  are `A_{e} = 1` and `A_{ne} = 0` for `n ≥ 2` (`oneKac`), and the interface `oneBPS` takes the
  framed series to be the multiplier. So `KacData` and `BPSHypotheses` are consistent. The model
  gives `Ω_e = -1`, and `Ω_{2e} = 0` because the multiple of a rigid object is not a root.
* **The curve wall** (`curveWallBPS`, the instance from a quiver): `Ω = -1` at `(2, 1)`,
  `Ω = -2` at `(2, 2)`, `Ω = 0` at `(3, 1)`. The alternating words of the affine Kronecker quiver
  are root-positive, so the new simple objects along their galleries have `Ω = -1`. The curve wall
  is affine with `l = 1` (`curveWallKac_isAffine`), and the general value at an affine wall gives
  `Ω = -2` at `(2, 2)` again.
* **An affine wall with three vertices** (`triangleBPS`): the quiver `Ã₂`, with Kac polynomials
  `1`, `q + 2`, `0`. It meets `KacData.IsAffine` at `δ = (1, 1, 1)` (`triangleKac_isAffine`), and
  `Ω_{2δ} = -3`.

The checks of `Ω` go through the CY3 local model `Quiver.BPSHypotheses.localModel`, which both
models meet by definition. Built by `lake test`.
-/

namespace K3TwistsTest.BPSModel

open MvPowerSeries MvPowerSeries.FramedMultiplier CoxeterMatrix Quiver
open AlgebraicGeometry.K3.EllipticWithSection

/-! ### One spherical object -/

/-- The quiver with one vertex and no arrows. -/
def pointQuiver : Unit → Unit → ℕ := fun _ _ => 0

theorem rootForm_pointQuiver (v : Unit → ℤ) : rootForm pointQuiver v v = -2 * v () ^ 2 := by
  rw [rootForm_apply_self]
  simp [Matrix.mulVec, dotProduct, rootMatrix]
  ring

theorem isSignCoherent_pointQuiver : IsSignCoherent pointQuiver := fun v _ => by
  rcases le_total 0 (v ()) with h | h
  · exact Or.inl fun _ => h
  · exact Or.inr fun _ => h

/-- The Kac polynomials of the one-vertex quiver: `1` at `e` and `0` elsewhere. -/
noncomputable def oneKacFun (v : Unit → ℤ) : Polynomial ℤ := by
  classical
  exact if IsPositiveVector v ∧ rootForm pointQuiver v v = -2 then 1 else 0

/-- **The Kac data of one spherical object**, with `A = 1` on the real roots by descent. -/
noncomputable def oneKac : KacData pointQuiver :=
  KacData.ofSignCoherent pointQuiver (fun _ _ => rfl) isSignCoherent_pointQuiver oneKacFun
    (fun i => by
      simp only [oneKacFun, isPositiveVector_stdRoot, rootForm_stdRoot_self, and_self,
        ↓reduceIte])
    (fun v _ h => by
      unfold oneKacFun
      split_ifs with h1
      · exfalso
        linarith [h1.2]
      · rfl)
    (fun i v hv _ hw => by
      unfold oneKacFun
      rw [rootForm_stdReflect _ (fun _ _ => rfl)]
      simp only [hv, hw, true_and])

/-- **The consistency model of the BPS interface**: one spherical object, with the framed series
the multiplier and `Ω = -A(1)`. -/
noncomputable def oneBPS : BPSHypotheses pointQuiver where
  toKacData := oneKac
  bpsQ α := -(oneKac.kac (dimVec α)).eval 1
  framed w := Z w fun α => -(oneKac.kac (dimVec α)).eval 1
  framed_eq_kac _ := rfl
  framed_eq_bps _ := rfl
  Ω α := -(oneKac.kac (dimVec α)).eval 1
  localModel _ _ := rfl

/-- The spherical object has `Ω = -1`. -/
example : oneBPS.Ω (Finsupp.single () 1) = -1 :=
  oneBPS.omega_single ()

/-- Its double has `Ω = 0`: `2e` is not a root. -/
example : oneBPS.Ω (Finsupp.single () 2) = 0 := by
  refine oneBPS.omega_eq_zero ⟨Finsupp.single () 2, by simp⟩ ?_
  rw [rootForm_pointQuiver]
  simp

/-- The interface says exactly `Ω = -A(1)`. -/
example : ∃ H : BPSHypotheses pointQuiver, H.toKacData = oneKac ∧
    H.Ω = fun α => -(oneKac.kac (dimVec α)).eval 1 :=
  (BPSHypotheses.exists_iff pointQuiver oneKac _).2 fun _ => rfl

/-! ### The curve wall -/

/-- `(a, b)` as a positive class of the curve wall. -/
noncomputable def cls (a b : ℕ) (h : a ≠ 0) : Pos (Fin 2) :=
  ⟨Finsupp.single 0 a + Finsupp.single 1 b, fun h' => h (by
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h'
    simpa using this)⟩

/-- The real root `(2, 1)` has `Ω = -1`. -/
example : curveWallBPS.Ω (cls 2 1 (by norm_num)).1 = -1 :=
  curveWall_omega_real _ (by simp [cls])

/-- The imaginary root `(2, 2)` has `Ω = -2 = -χ(ℙ¹)`. -/
example : curveWallBPS.Ω (cls 2 2 (by norm_num)).1 = -2 :=
  curveWall_omega_null _ (by simp [cls])

/-- The class `(3, 1)`, that is `(0, 2C, 3)`, has `Ω = 0`. -/
example : curveWallBPS.Ω (cls 3 1 (by norm_num)).1 = 0 :=
  curveWall_omega_eq_zero _ (by simp [cls])

/-- The alternating words of the curve wall are root-positive. -/
theorem isRootPositive_curveWall_alternating :
    BilinearForm.IsRootPositive (rootForm curveWallExt) stdRoot [0, 1, 0, 1, 0, 1] := by
  have he : curveWallExt = fun i j : Fin 2 => if i = j then 0 else 2 :=
    funext fun i => funext fun j => curveWallExt_eq i j
  rw [he, isRootPositive_rootForm_iff]
  decide

/-- **Weyl descent along a gallery of the curve wall**: the new simple objects along the gallery
of `[0, 1, 0, 1, 0, 1]` have `Ω = -1`. -/
example {v : Fin 2 → ℤ} (hv : v ∈ stdPrefixRoots curveWallExt [0, 1, 0, 1, 0, 1]) :
    curveWallBPS.Ω (ofVec v) = -1 :=
  curveWallBPS.omega_eq_neg_one_of_isRootPositive isRootPositive_curveWall_alternating hv

/-- The affine value at the curve wall: `Ω_{(2, 2)} = -2`, from `A_{2δ} = q + 1`. -/
example : curveWallBPS.Ω (cls 2 2 (by norm_num)).1 = -2 :=
  curveWall_omega_null_of_isAffine _ (n := 2) (by norm_num) (by
    ext i
    fin_cases i <;> simp [cls])

/-! ### An affine wall with three vertices -/

/-- The `Ext`-quiver `Ã₂` of three spherical objects pairing to `1`, as at an affine wall of an
`A₂` configuration: one arrow between any two distinct vertices. -/
def triangleQuiver (i j : Fin 3) : ℕ := if i = j then 0 else 1

theorem triangleQuiver_symm (i j : Fin 3) : triangleQuiver i j = triangleQuiver j i := by
  simp only [triangleQuiver, eq_comm]

/-- The root form of `Ã₂` is `-((a - b)² + (a - c)² + (b - c)²)`. -/
theorem rootForm_triangleQuiver (v : Fin 3 → ℤ) :
    rootForm triangleQuiver v v = -((v 0 - v 1) ^ 2 + (v 0 - v 2) ^ 2 + (v 1 - v 2) ^ 2) := by
  rw [rootForm_apply_self]
  simp [Matrix.mulVec, dotProduct, rootMatrix, triangleQuiver, Fin.sum_univ_three]
  ring

theorem isSignCoherent_triangleQuiver : IsSignCoherent triangleQuiver := by
  refine isSignCoherent_of_posSemidef _ triangleQuiver_symm (fun v => ?_) (fun v hv => ?_)
  · rw [rootForm_triangleQuiver]
    nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 0 - v 2), sq_nonneg (v 1 - v 2)]
  · rw [rootForm_triangleQuiver] at hv
    have h1 : v 0 = v 1 := by
      nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 0 - v 2), sq_nonneg (v 1 - v 2)]
    have h2 : v 0 = v 2 := by
      nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 0 - v 2), sq_nonneg (v 1 - v 2)]
    by_cases h0 : v 0 = 0
    · left
      ext i
      fin_cases i <;> simp [h0, ← h1, ← h2]
    · right
      intro i
      fin_cases i <;> simp [h0, ← h1, ← h2]

/-- The Kac polynomials of `Ã₂`: `1` on the real roots, `q + 2` on the imaginary roots
`n(1, 1, 1)`, `n ≥ 1`, and `0` elsewhere. -/
noncomputable def triangleKacFun (v : Fin 3 → ℤ) : Polynomial ℤ := by
  classical
  exact if IsPositiveVector v ∧ rootForm triangleQuiver v v = -2 then 1
    else if IsPositiveVector v ∧ rootForm triangleQuiver v v = 0 then Polynomial.X + 2 else 0

/-- **The Kac data of `Ã₂`**, with `A = 1` on the real roots by descent. -/
noncomputable def triangleKac : KacData triangleQuiver :=
  KacData.ofSignCoherent triangleQuiver triangleQuiver_symm isSignCoherent_triangleQuiver
    triangleKacFun
    (fun i => by
      simp only [triangleKacFun, isPositiveVector_stdRoot, rootForm_stdRoot_self, and_self,
        ↓reduceIte])
    (fun v _ h => by
      unfold triangleKacFun
      split_ifs with h1 h2
      · exfalso
        linarith [h1.2]
      · exfalso
        linarith [h2.2]
      · rfl)
    (fun i v hv _ hw => by
      unfold triangleKacFun
      rw [rootForm_stdReflect _ triangleQuiver_symm]
      simp only [hv, hw, true_and])

/-- **`Ã₂` is affine**: connected, negative semidefinite, `δ = (1, 1, 1)` in the radical, and
`A_{nδ} = q + 2`, the value `q + l` at `l + 1 = 3` vertices. -/
theorem triangleKac_isAffine : triangleKac.IsAffine ![1, 1, 1] where
  isIndecomposable := by
    refine (Matrix.isIndecomposable_iff_reflTransGen _).2 fun i j => ?_
    by_cases h : i = j
    · rw [h]
    · exact Relation.ReflTransGen.single (by simp [rootMatrix, triangleQuiver, h])
  rootForm_self_nonpos v := by
    rw [rootForm_triangleQuiver]
    nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 0 - v 2), sq_nonneg (v 1 - v 2)]
  isPositiveVector := ⟨fun i => by fin_cases i <;> simp, fun h => by simpa using congrFun h 0⟩
  rootForm_eq_zero v := by
    simp [rootForm, Matrix.toBilin'_apply, rootMatrix, triangleQuiver, Fin.sum_univ_three]
    ring
  kac_smul n hn := by
    change triangleKacFun _ = _
    have hpos : IsPositiveVector ((n : ℤ) • ![(1 : ℤ), 1, 1]) :=
      ⟨fun i => by fin_cases i <;> simp, fun h => by
        have := congrFun h 0
        simp only [Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_one, Pi.zero_apply,
          Nat.cast_eq_zero] at this
        omega⟩
    have hform : rootForm triangleQuiver ((n : ℤ) • ![(1 : ℤ), 1, 1])
        ((n : ℤ) • ![(1 : ℤ), 1, 1]) = 0 := by
      rw [rootForm_triangleQuiver]
      simp
    simp only [triangleKacFun, hpos, true_and, hform]
    norm_num

/-- **The consistency model of an affine wall with three vertices**: the interface on `Ã₂`, with
the framed series the multiplier and `Ω = -A(1)`. -/
noncomputable def triangleBPS : BPSHypotheses triangleQuiver where
  toKacData := triangleKac
  bpsQ α := -(triangleKac.kac (dimVec α)).eval 1
  framed w := Z w fun α => -(triangleKac.kac (dimVec α)).eval 1
  framed_eq_kac _ := rfl
  framed_eq_bps _ := rfl
  Ω α := -(triangleKac.kac (dimVec α)).eval 1
  localModel _ _ := rfl

/-- The class `n(1, 1, 1)`. -/
noncomputable def nullCls (n : ℕ) (h : n ≠ 0) : Pos (Fin 3) :=
  ⟨Finsupp.single 0 n + Finsupp.single 1 n + Finsupp.single 2 n, fun h' => h (by
    have := congrArg (fun f : Fin 3 →₀ ℕ => f 0) h'
    simpa using this)⟩

theorem dimVec_nullCls (n : ℕ) (h : n ≠ 0) : dimVec (nullCls n h).1 = (n : ℤ) • ![1, 1, 1] := by
  ext i
  fin_cases i <;> simp [nullCls]

/-- `Ω_{2δ} = -3` at the affine wall `Ã₂`, minus the Euler characteristic of two smooth rational
curves meeting in a point. -/
example : triangleBPS.Ω (nullCls 2 (by norm_num)).1 = -3 := by
  rw [triangleBPS.omega_eq_neg_card_of_isAffine triangleKac_isAffine _ (n := 2) (by norm_num)
    (dimVec_nullCls 2 (by norm_num))]
  simp

end K3TwistsTest.BPSModel
