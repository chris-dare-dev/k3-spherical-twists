/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.FramedMultiplier
import K3Twists.Combinatorics.DT.BPS

/-!
# The BPS interface at the curve wall: an instance from a quiver

On the elliptic K3 surface `X` with a section `C` (`EllipticWithSection/Lattice.lean`), the curve
wall has the spherical simples `A = 𝒪_C` and `B = 𝒪_C(-1)[1]`, with `⟨v(A), v(B)⟩ = 2`. This file
builds the BPS interface `Quiver.BPSHypotheses` of the wall from its quiver:

* **The `Ext`-quiver is computed from the classes** (`curveWallExt`): `⟨v(A), v(B)⟩` arrows
  between the two vertices, the affine Kronecker quiver (`curveWallExt_eq`). Its root form is
  `-2(a - b)²` (`rootForm_curveWallExt`). It is positive semidefinite with isotropic vectors the
  multiples of `(1, 1)`, hence sign coherent (`isSignCoherent_curveWallExt`).
* **The Kac data are those of the Kronecker quiver** (`curveWallKac`). Kac (Invent. Math. 56,
  1980) gives `A = 1` on the real roots, `A = q + 1` on the imaginary roots `(n, n)`, `n ≥ 1`,
  which count the projective line of regular representations, and `A = 0` elsewhere
  (`kroneckerKac`). The fields of `Quiver.KacData` are proved from the Tits form: `A = 1` on
  the real roots by Weyl descent (`Quiver.KacData.ofSignCoherent`), and the reflection invariance
  because the values depend only on positivity and `q`.
* **The interface** (`curveWallBPS`): the nilpotent BPS invariants of the tripled quiver are the
  affine Kronecker indices `kroneckerBPS` of `FramedMultiplier.lean`, and they are minus the Kac
  polynomials at one (`kroneckerBPS_eq_neg_kac`).

**Which fields have no geometric instance.** Mozgovoy's formula localized to the nilpotent locus
(`framed_eq_kac`), the framed/unframed identity (`framed_eq_bps`) and the CY3 local model
(`localModel`) are met by taking the framed series to be the multiplier and the local invariants
to be those of the quiver, as the fields assert. The framed moduli of the tripled quiver, the
Behrend function and the moduli of objects on the threefold `X × 𝔸¹` are not in the library. The
CY3 local model has no published proof and no human review. The Kac data and the quiver are not
assumed: they are computed from the classes of the wall and the Tits form.

**Consequences**, each using the CY3 local model through `Quiver.BPSHypotheses.omega_eq`:

* `Ω = -1` on every real root `(a, b)`, `(a - b)² = 1` (`curveWall_omega_real`), by Weyl descent;
* `Ω_{(n, n)} = -2 = -χ(ℙ¹)` for `n ≥ 1`, the class of `n` points of `C`
  (`curveWall_omega_null`);
* `Ω = 0` at `(a, b)` with `|a - b| ≥ 2` (`curveWall_omega_eq_zero`). Since
  `a v(A) + b v(B) = (0, (a - b)C, a)` with `a, b ≥ 0`, these are the classes `(0, kC, n)` with
  `|k| ≥ 2` and `n ≥ max(0, k)`, and the local invariants vanish there.

**The curve wall is affine of type `Ã₁`** (`curveWallKac_isAffine`): the quiver is connected with
negative semidefinite root form, `δ = (1, 1)` spans the radical, and the Kronecker Kac polynomial
`q + 1` at `nδ` is the published value `q + l` at `l = 1`. So the general value at an affine wall,
`Quiver.BPSHypotheses.omega_eq_neg_card_of_isAffine`, gives `Ω_{(n, n)} = -2` again
(`curveWall_omega_null_of_isAffine`).
-/

open MvPowerSeries MvPowerSeries.FramedMultiplier CoxeterMatrix Quiver

namespace AlgebraicGeometry.K3.EllipticWithSection

open Mukai

/-! ### The `Ext`-quiver of the curve wall -/

/-- The two simples of the curve wall, `v(𝒪_C)` and `v(𝒪_C(-1)[1])`. -/
def wallSimple : Fin 2 → MukaiLattice ℤ NS :=
  ![wallA, wallB]

/-- **The `Ext`-quiver of the curve wall**, from the Mukai pairing of its simples. -/
def curveWallExt (i j : Fin 2) : ℕ :=
  if i = j then 0 else (pairing intersection (wallSimple i) (wallSimple j)).toNat

/-- It is the affine Kronecker quiver: two arrows between the two vertices. -/
theorem curveWallExt_eq (i j : Fin 2) : curveWallExt i j = if i = j then 0 else 2 := by
  fin_cases i <;> fin_cases j <;>
    simp [curveWallExt, wallSimple, pairing_wallA_wallB,
      pairing_comm intersection intersection_comm wallB wallA]

theorem curveWallExt_symm (i j : Fin 2) : curveWallExt i j = curveWallExt j i := by
  rw [curveWallExt_eq, curveWallExt_eq]
  simp only [eq_comm]

/-- The root form of the curve wall is `-2(a - b)²`. -/
theorem rootForm_curveWallExt (v : Fin 2 → ℤ) :
    rootForm curveWallExt v v = -2 * (v 0 - v 1) ^ 2 := by
  rw [rootForm_apply_self]
  simp [Matrix.mulVec, dotProduct, rootMatrix, curveWallExt_eq, Fin.sum_univ_two]
  ring

/-- **The root form of the curve wall is sign coherent**: positive semidefinite, with isotropic
vectors the multiples of `(1, 1)`. -/
theorem isSignCoherent_curveWallExt : IsSignCoherent curveWallExt := by
  refine isSignCoherent_of_posSemidef _ curveWallExt_symm (fun v => ?_) (fun v hv => ?_)
  · rw [rootForm_curveWallExt]
    nlinarith [sq_nonneg (v 0 - v 1)]
  · rw [rootForm_curveWallExt] at hv
    have h : v 0 = v 1 := by nlinarith [sq_nonneg (v 0 - v 1)]
    by_cases h0 : v 0 = 0
    · left
      ext i
      fin_cases i <;> simp [h0, ← h]
    · right
      intro i
      fin_cases i <;> simp [h0, ← h]

/-! ### The Kac data -/

/-- **The Kac polynomials of the Kronecker quiver** (Kac, Invent. Math. 56, 1980): `1` on the real
roots, `q + 1` on the imaginary roots `(n, n)`, `n ≥ 1`, and `0` at every other vector. -/
noncomputable def kroneckerKac (v : Fin 2 → ℤ) : Polynomial ℤ := by
  classical
  exact if IsPositiveVector v ∧ rootForm curveWallExt v v = -2 then 1
    else if IsPositiveVector v ∧ rootForm curveWallExt v v = 0 then Polynomial.X + 1 else 0

theorem kroneckerKac_stdRoot (i : Fin 2) : kroneckerKac (stdRoot i) = 1 := by
  simp only [kroneckerKac, isPositiveVector_stdRoot, rootForm_stdRoot_self, and_self,
    ↓reduceIte]

theorem kroneckerKac_eq_zero (v : Fin 2 → ℤ) (h : rootForm curveWallExt v v ≤ -4) :
    kroneckerKac v = 0 := by
  unfold kroneckerKac
  split_ifs with h1 h2
  · exfalso
    linarith [h1.2]
  · exfalso
    linarith [h2.2]
  · rfl

theorem kroneckerKac_stdReflect (i : Fin 2) (v : Fin 2 → ℤ) (hv : IsPositiveVector v)
    (hw : IsPositiveVector (stdReflect curveWallExt i v)) :
    kroneckerKac (stdReflect curveWallExt i v) = kroneckerKac v := by
  unfold kroneckerKac
  rw [rootForm_stdReflect _ curveWallExt_symm]
  simp only [hv, hw, true_and]

/-- **The Kac data of the curve wall**: the Kronecker Kac polynomials, with `A = 1` on the real
roots obtained by Weyl descent. -/
noncomputable def curveWallKac : KacData curveWallExt :=
  KacData.ofSignCoherent curveWallExt curveWallExt_symm isSignCoherent_curveWallExt kroneckerKac
    kroneckerKac_stdRoot (fun v _ h => kroneckerKac_eq_zero v h)
    (fun i v hv _ hw => kroneckerKac_stdReflect i v hv hw)

/-! ### The interface -/

/-- **The affine Kronecker indices are minus the Kac polynomials at one.** -/
theorem kroneckerBPS_eq_neg_kac (α : Pos (Fin 2)) :
    kroneckerBPS α.1 = -(kroneckerKac (dimVec α.1)).eval 1 := by
  have hpos := isPositiveVector_dimVec α
  have hform := rootForm_curveWallExt (dimVec α.1)
  simp only [dimVec_apply] at hform
  have hne : α.1 0 ≠ 0 ∨ α.1 1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    exact α.2 (Finsupp.ext fun i => by fin_cases i <;> simp [h.1, h.2])
  have h1 : (-2 * ((α.1 0 : ℤ) - α.1 1) ^ 2 = -2) ↔ ((α.1 0 : ℤ) - α.1 1) ^ 2 = 1 := by
    constructor <;> intro h <;> linarith
  have h0 : (-2 * ((α.1 0 : ℤ) - α.1 1) ^ 2 = 0) ↔ (α.1 0 = α.1 1 ∧ α.1 0 ≠ 0) := by
    constructor
    · intro h
      have hab : (α.1 0 : ℤ) = α.1 1 := by nlinarith [sq_nonneg ((α.1 0 : ℤ) - α.1 1)]
      have hab' : α.1 0 = α.1 1 := by exact_mod_cast hab
      refine ⟨hab', ?_⟩
      rcases hne with h' | h'
      · exact h'
      · rwa [hab']
    · rintro ⟨h, -⟩
      rw [h]
      ring
  simp only [kroneckerBPS, kroneckerIndex, kroneckerForm_two, kroneckerKac, hpos, true_and, hform,
    h1, h0]
  split_ifs <;> norm_num

/-- **The BPS interface of the curve wall**, built from its `Ext`-quiver and the Kac polynomials of
that quiver. The framed series is the multiplier, and the local invariants are the quiver's; see
the module docstring for the fields with no geometric instance. -/
noncomputable def curveWallBPS : BPSHypotheses curveWallExt where
  toKacData := curveWallKac
  bpsQ := kroneckerBPS
  framed w := Z w kroneckerBPS
  framed_eq_kac w := by
    unfold Z framedS
    congr 1
    exact S_congr fun α => by rw [kroneckerBPS_eq_neg_kac α]; rfl
  framed_eq_bps _ := rfl
  Ω := kroneckerBPS
  localModel _ _ := rfl

/-- The curve-wall multiplier of `FramedMultiplier.lean` is the multiplier of the interface. -/
theorem curveWallMultiplier_eq (D : NS) :
    curveWallMultiplier (R := ℤ) D = framedS (wallFraming D) curveWallBPS.Ω :=
  rfl

/-! ### Consequences -/

/-- **`Ω = -1` on every real root of the curve wall**, `(a - b)² = 1`, by Weyl descent. Uses the
CY3 local model `Quiver.BPSHypotheses.localModel`. -/
theorem curveWall_omega_real (α : Pos (Fin 2)) (h : ((α.1 0 : ℤ) - α.1 1) ^ 2 = 1) :
    curveWallBPS.Ω α.1 = -1 := by
  have hnorm : rootForm curveWallExt (dimVec α.1) (dimVec α.1) = -2 := by
    rw [rootForm_curveWallExt]
    simp only [dimVec_apply, h]
    norm_num
  obtain ⟨-, -, hreal⟩ := exists_eq_stdRoot_of_reflect_invariant curveWallExt curveWallExt_symm
    isSignCoherent_curveWallExt (fun _ => ()) (fun _ _ _ _ _ => rfl) _
    (isPositiveVector_dimVec α) hnorm
  exact curveWallBPS.omega_eq_neg_one_of_isRealRoot α hreal

/-- **`Ω_{(n, n)} = -2 = -χ(ℙ¹)`** for `n ≥ 1`: the imaginary roots of the curve wall, the class
of `n` points of `C`. Uses the CY3 local model `Quiver.BPSHypotheses.localModel`. -/
theorem curveWall_omega_null (α : Pos (Fin 2)) (h : α.1 0 = α.1 1) : curveWallBPS.Ω α.1 = -2 := by
  rw [curveWallBPS.omega_eq α]
  have hpos := isPositiveVector_dimVec α
  have hform : rootForm curveWallExt (dimVec α.1) (dimVec α.1) = 0 := by
    rw [rootForm_curveWallExt]
    simp [h]
  change -(kroneckerKac (dimVec α.1)).eval 1 = -2
  simp only [kroneckerKac, hpos, true_and, hform]
  norm_num

/-- **`Ω = 0` at the classes `(a, b)` with `|a - b| ≥ 2`**: in Mukai coordinates
`a v(A) + b v(B) = (0, (a - b)C, a)` with `a, b ≥ 0`, the classes `(0, kC, n)` with `|k| ≥ 2` and
`n ≥ max(0, k)`. Uses the CY3 local model `Quiver.BPSHypotheses.localModel`. -/
theorem curveWall_omega_eq_zero (α : Pos (Fin 2)) (h : 2 ≤ |(α.1 0 : ℤ) - α.1 1|) :
    curveWallBPS.Ω α.1 = 0 := by
  refine curveWallBPS.omega_eq_zero α ?_
  rw [rootForm_curveWallExt]
  simp only [dimVec_apply]
  have := sq_abs ((α.1 0 : ℤ) - α.1 1)
  nlinarith [abs_nonneg ((α.1 0 : ℤ) - α.1 1)]

/-- The class `a v(A) + b v(B)` is `(0, (a - b)C, a)`. -/
theorem wallClass_eq_curve (a b : ℤ) : wallClass a b = (0, (a - b) • curve, a) := by
  rw [wallClass_eq]
  ext <;> simp [curve]

/-! ### The curve wall is affine -/

/-- **The curve wall is affine of type `Ã₁`**: its `Ext`-quiver is connected with negative
semidefinite root form, `δ = (1, 1)` lies in the radical, and the Kronecker Kac polynomial at
`nδ`, `n ≥ 1`, is `q + 1`, the value `q + l` at an affine quiver with `l + 1 = 2` vertices. -/
theorem curveWallKac_isAffine : curveWallKac.IsAffine ![1, 1] where
  isIndecomposable := by
    refine (Matrix.isIndecomposable_iff_reflTransGen _).2 fun i j => ?_
    by_cases h : i = j
    · rw [h]
    · refine Relation.ReflTransGen.single ?_
      simp [rootMatrix, h, curveWallExt_eq]
  rootForm_self_nonpos v := by
    rw [rootForm_curveWallExt]
    nlinarith [sq_nonneg (v 0 - v 1)]
  isPositiveVector := ⟨fun i => by fin_cases i <;> simp, fun h => by simpa using congrFun h 0⟩
  rootForm_eq_zero v := by
    simp [rootForm, Matrix.toBilin'_apply, rootMatrix, curveWallExt_eq, Fin.sum_univ_two]
    ring
  kac_smul n hn := by
    change kroneckerKac _ = _
    have hpos : IsPositiveVector ((n : ℤ) • ![(1 : ℤ), 1]) :=
      ⟨fun i => by fin_cases i <;> simp, fun h => by
        have := congrFun h 0
        simp only [Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_one, Pi.zero_apply,
          Nat.cast_eq_zero] at this
        omega⟩
    have hform : rootForm curveWallExt ((n : ℤ) • ![(1 : ℤ), 1]) ((n : ℤ) • ![(1 : ℤ), 1]) = 0 := by
      rw [rootForm_curveWallExt]
      simp
    simp only [kroneckerKac, hpos, true_and, hform]
    norm_num

/-- **`Ω_{(n, n)} = -2`** from the general value `-(l + 1)` at the imaginary roots of an affine
wall (`Quiver.BPSHypotheses.omega_eq_neg_card_of_isAffine`), at `l = 1`. Uses the CY3 local model
`Quiver.BPSHypotheses.localModel`. -/
theorem curveWall_omega_null_of_isAffine (α : Pos (Fin 2)) {n : ℕ} (hn : 0 < n)
    (h : dimVec α.1 = (n : ℤ) • ![1, 1]) : curveWallBPS.Ω α.1 = -2 := by
  rw [curveWallBPS.omega_eq_neg_card_of_isAffine curveWallKac_isAffine α hn h]
  simp

end AlgebraicGeometry.K3.EllipticWithSection
