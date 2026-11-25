/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.CurveWall
import K3Twists.Combinatorics.DT.Quivers

/-!
# The framed multiplier at the curve wall

On the elliptic K3 surface `X` of `Lattice.lean`, the wall where the section `C` is contracted has
the spherical simples `A = 𝒪_C` and `B = 𝒪_C(-1)[1]` with `⟨v(A), v(B)⟩ = 2`
(`pairing_wallA_wallB`). Their `Ext`-quiver, oriented, is the affine Kronecker quiver, and its
Tits form is `q₂(a, b) = -v(aA + bB)²/2` (`selfPairing_wallClass_eq_kroneckerForm`). This file
builds the framed multiplier of that wall from the classes of the library and checks it against
the numbers already proved for the curve wall.

* **BPS indices from the Mukai lattice.** The affine Kronecker index of `(a, b)` is `-1` exactly
  when `v(aA + bB)` is spherical and `-2` exactly when it is isotropic and nonzero
  (`kroneckerIndex_eq_neg_one_iff`, `kroneckerIndex_eq_neg_two_iff`). On the named objects:
  `𝒪_C(j)` and `M_{d,x}` have index `-1`, `𝒪_x` for `x ∈ C` has index `-2`, and the thickenings
  `K_ε ⊗ 𝒪_X/(I_x I_C^{r+1})`, `r ≥ 1`, have index `0` (`kroneckerIndex_named`). The index `-2`
  at `(1, 1)` counts the projective line of regular representations of that dimension; on the
  surface these are the points of `C ≅ ℙ¹`, whose class is `v(A) + v(B)` (`wallA_add_wallB`).
* **All positive classes have phase one** at the stability condition of `CurveWall.lean`
  (`arg_charge_of_pos`), so the whole positive sector is one wall-crossing factor.
* **The framing by a line bundle.** `𝒪_X(D)` frames the wall by
  `p = (χ(𝒪_X(D), A), χ(𝒪_X(D), B)) = (1 - C·D, C·D)` (`wallFraming_eq`), and
  `p·(a, b) = χ(𝒪_X(D), aA + bB)` (`pair_wallFraming`). For `D = L^{-i}` and `m = i(L·C)`,
  `C·D = -m` and `p = (m + 1, -m)`.
* **The curve-wall multiplier** `curveWallMultiplier D`. Its exponents are `-(n + m + 1)` at
  `(n + 1, n)`, `m - n` at `(n, n + 1)` and `-2n` at `(n, n)` (`curveWall_exponent_R`,
  `curveWall_exponent_L`, `curveWall_exponent_diag`); its `xy` coefficient is `2 - m(m + 1)`
  (`coeff_curveWallMultiplier_one_one`); it does not see the root `(m, m + 1)`, the class
  `χ`-orthogonal to `𝒪_X(D)` (`curveWall_blind`); and framed by `𝒪_X` its coefficient at
  `(2, 2)` is `8` (`coeff_curveWallMultiplier_two_two`).
* **The point and the Jordan quiver.** A point `𝒪_x` off `C` has `v(𝒪_x)² = 0`, so Riemann–Roch
  gives `dim Ext¹(𝒪_x, 𝒪_x) = 2 dim End + v² = 2`: its `Ext`-quiver is the Jordan quiver with its
  dual loop. An object `E` frames it by `χ(E, 𝒪_x) = rk E` (`pointFraming_eq`): `1` for a line
  bundle and `2` for the rank-two extension `S` of `rankTwo_classes`. The geometric framed series
  of `S` is `Z_1(-y)²` and not `Z_1(y)²` for any line bundle (`pointMultiplier_rankTwo_ne`).

That the stable objects at the wall are the semistable representations of this quiver
(formality of the `Ext`-algebra, Davison, arXiv:2106.07692, Proposition 7.8), the values of the
Kac polynomials, and that framed counts at the wall are given by the multiplier (Mozgovoy,
arXiv:1107.6044) are cited, not formalized.
-/

open Complex MvPowerSeries MvPowerSeries.FramedMultiplier Quiver.Kronecker
open scoped Real

namespace AlgebraicGeometry.K3.EllipticWithSection

open Mukai

variable {R : Type*} [CommRing R]

/-! ### BPS indices from the Mukai lattice -/

/-- **The index `-1` marks the spherical wall classes.** -/
theorem kroneckerIndex_eq_neg_one_iff (a b : ℕ) :
    kroneckerIndex a b = -1 ↔ IsSpherical intersection (wallClass a b) := by
  rw [IsSpherical, selfPairing_wallClass_eq_kroneckerForm, kroneckerIndex]
  constructor
  · intro h
    by_cases h1 : kroneckerForm 2 a b = 1
    · rw [h1]; norm_num
    · exfalso
      simp only [h1, ↓reduceIte] at h
      split_ifs at h
      norm_num at h
  · intro h
    have h1 : kroneckerForm 2 a b = 1 := by linarith
    simp [h1]

/-- **The index `-2` marks the nonzero isotropic wall classes.** -/
theorem kroneckerIndex_eq_neg_two_iff (a b : ℕ) :
    kroneckerIndex a b = -2 ↔ IsIsotropic intersection (wallClass a b) ∧ (a ≠ 0 ∨ b ≠ 0) := by
  rw [IsIsotropic, selfPairing_wallClass, kroneckerIndex_eq]
  constructor
  · intro h
    by_cases h1 : a = b + 1 ∨ b = a + 1
    · simp only [h1, ↓reduceIte] at h
      norm_num at h
    · by_cases h2 : a = b ∧ a ≠ 0
      · obtain ⟨rfl, ha⟩ := h2
        exact ⟨by ring, Or.inl ha⟩
      · simp only [h1, h2, ↓reduceIte] at h
        norm_num at h
  · rintro ⟨h, hab⟩
    have hab' : (a : ℤ) = b := by nlinarith [sq_nonneg ((a : ℤ) - b)]
    have : a = b := by exact_mod_cast hab'
    subst this
    have h2 : a ≠ 0 := by omega
    simp [h2]

/-- **The indices of the named wall objects.** `𝒪_C(j)` (multiplicities `(j + 1, j)`) and the
curve with an embedded point `M_{d,x}` (multiplicities `(d + 2, d + 1)`) have index `-1`; a point
`𝒪_x` of `C` (multiplicities `(1, 1)`) has index `-2`; the thickening of `Lattice.lean` with
`r ≥ 1`, whose multiplicities differ by `r + 1 ≥ 2`, has index `0`. -/
theorem kroneckerIndex_named (j d r : ℕ) (ε : ℕ) (hr : 1 ≤ r) :
    (curveSheaf j = wallClass (j + 1 : ℕ) j ∧ kroneckerIndex (j + 1) j = -1) ∧
      (embeddedPoint d = wallClass (d + 2 : ℕ) (d + 1 : ℕ) ∧ kroneckerIndex (d + 2) (d + 1) = -1) ∧
      (point = wallClass 1 1 ∧ kroneckerIndex 1 1 = -2) ∧
      kroneckerIndex ((r + 1) * (r + 1 + ε) + 1) ((r + 1) * (r + 1 + ε) + 1 - (r + 1)) = 0 := by
  refine ⟨⟨by rw [curveSheaf_eq_wallClass]; push_cast; rfl, ?_⟩,
    ⟨by rw [embeddedPoint_eq_wallClass]; push_cast; ring_nf, ?_⟩, ⟨point_eq_wallClass, ?_⟩, ?_⟩
  · rw [kroneckerIndex_eq]; simp
  · rw [kroneckerIndex_eq]; simp
  · rw [kroneckerIndex_eq]; simp
  · rw [kroneckerIndex_eq]
    have hle : r + 1 ≤ (r + 1) * (r + 1 + ε) + 1 := by nlinarith
    have h1 : ¬((r + 1) * (r + 1 + ε) + 1 = (r + 1) * (r + 1 + ε) + 1 - (r + 1) + 1 ∨
        (r + 1) * (r + 1 + ε) + 1 - (r + 1) = (r + 1) * (r + 1 + ε) + 1 + 1) := by omega
    have h2 : ¬((r + 1) * (r + 1 + ε) + 1 = (r + 1) * (r + 1 + ε) + 1 - (r + 1) ∧
        (r + 1) * (r + 1 + ε) + 1 ≠ 0) := by omega
    simp only [h1, h2, ↓reduceIte]

/-- **Every positive class has phase one** at the curve-wall stability condition. -/
theorem arg_charge_of_pos {a b : ℕ} (hab : a ≠ 0 ∨ b ≠ 0) :
    arg (charge (wallClass a b)) = π :=
  arg_charge_wallClass (by omega)

/-! ### The framing by a line bundle -/

/-- The framing of the curve wall by `𝒪_X(D)`: `(χ(𝒪_X(D), A), χ(𝒪_X(D), B))`, where
`χ = -⟨v, v⟩`. -/
def wallFraming (D : NS) : Fin 2 → ℤ :=
  ![-pairing intersection (lineBundle D) wallA, -pairing intersection (lineBundle D) wallB]

/-- `χ(𝒪_X(D), A) = 1 - C·D` and `χ(𝒪_X(D), B) = C·D`. -/
theorem wallFraming_eq (D : NS) :
    wallFraming D = ![1 - intersection curve D, intersection curve D] := by
  have hA : pairing intersection (lineBundle D) wallA = intersection curve D - 1 := by
    rw [pairing_comm intersection intersection_comm, wallA, pairing_curveSheaf_lineBundle]
  have hB : pairing intersection (lineBundle D) wallB = -intersection curve D := by
    simp [wallB]
    ring
  ext i
  fin_cases i
  · show -pairing intersection (lineBundle D) wallA = 1 - intersection curve D
    rw [hA]
    ring
  · show -pairing intersection (lineBundle D) wallB = intersection curve D
    rw [hB]
    ring

/-- The framing pairing is the Euler pairing: `p·(a, b) = χ(𝒪_X(D), aA + bB)`. -/
theorem pair_wallFraming (D : NS) (a b : ℕ) :
    pair (wallFraming D) (mk2 a b) = -pairing intersection (lineBundle D) (wallClass a b) := by
  rw [pair_mk2, wallClass, pairing_add_right, pairing_smul_right, pairing_smul_right]
  simp only [wallFraming, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- For `C·D = -m` the framing is `(m + 1, -m)`. -/
theorem wallFraming_of_intersection {D : NS} {m : ℤ} (h : intersection curve D = -m) :
    wallFraming D = ![m + 1, -m] := by
  rw [wallFraming_eq, h]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    ring
  · simp

/-! ### The curve-wall multiplier -/

/-- **The framed multiplier of the curve wall**, framed by `𝒪_X(D)`:
`∏_{α > 0} (1 - x^α)^{χ(𝒪_X(D), α) Ω_α}` with the affine Kronecker indices `Ω`. -/
noncomputable def curveWallMultiplier (D : NS) : MvPowerSeries (Fin 2) R :=
  framedS (wallFraming D) kroneckerBPS

/-- The exponent of the curve-wall multiplier at `(a, b)`. -/
noncomputable def curveWallExponent (D : NS) (a b : ℕ) : ℤ :=
  pair (wallFraming D) (mk2 a b) * kroneckerBPS (mk2 a b)

/-- At the real root `(n + 1, n)` the exponent is `-(n + m + 1)`. -/
theorem curveWall_exponent_R {D : NS} {m : ℤ} (h : intersection curve D = -m) (n : ℕ) :
    curveWallExponent D (n + 1) n = -(n + m + 1) := by
  rw [curveWallExponent, wallFraming_of_intersection h, kronecker_exponent_R]
  ring

/-- At the real root `(n, n + 1)` the exponent is `m - n`. -/
theorem curveWall_exponent_L {D : NS} {m : ℤ} (h : intersection curve D = -m) (n : ℕ) :
    curveWallExponent D n (n + 1) = m - n := by
  rw [curveWallExponent, wallFraming_of_intersection h, kronecker_exponent_L]
  ring

/-- At the imaginary root `(n, n)` the exponent is `-2n`, whatever the framing. -/
theorem curveWall_exponent_diag (D : NS) {n : ℕ} (hn : n ≠ 0) :
    curveWallExponent D n n = -2 * n := by
  rw [curveWallExponent, wallFraming_eq, kronecker_exponent_diag _ _ hn]
  ring

/-- **The `xy` coefficient is `2 - m(m + 1)`** for `C·D = -m`. -/
theorem coeff_curveWallMultiplier_one_one {D : NS} {m : ℤ} (h : intersection curve D = -m) :
    coeff (mk2 1 1) (curveWallMultiplier (R := R) D) = ((2 - m * (m + 1) : ℤ) : R) := by
  rw [curveWallMultiplier, wallFraming_of_intersection h, coeff_kronecker_one_one]
  congr 1
  ring

/-- **The framing does not see the root `(m, m + 1)`.** For `C·D = -m`, the class
`mA + (m + 1)B` is `χ`-orthogonal to `𝒪_X(D)`, the framed pairing vanishes there, and the
curve-wall multiplier does not depend on the index at `(m, m + 1)`. -/
theorem curveWall_blind {D : NS} {m : ℕ} (h : intersection curve D = -m) :
    pairing intersection (lineBundle D) (wallClass m (m + 1 : ℕ)) = 0 ∧
      pair (wallFraming D) (mk2 m (m + 1)) = 0 ∧
      ∀ c : ℤ, framedS (R := R) (wallFraming D) (Function.update kroneckerBPS (mk2 m (m + 1)) c) =
        curveWallMultiplier D := by
  have hp : pair (wallFraming D) (mk2 m (m + 1)) = 0 := by
    rw [wallFraming_of_intersection h]
    exact pair_signed_blind m
  refine ⟨?_, hp, fun c => ?_⟩
  · have := pair_wallFraming D m (m + 1)
    rw [hp] at this
    linarith
  · classical
    exact framedS_update_of_pair_eq_zero _ _ hp c

/-- **The coefficient `8`.** Framed by `𝒪_X` (`C·𝒪_X = 0`, framing `(1, 0)`), the coefficient of
`x²y²` in the curve-wall multiplier is `8`. -/
theorem coeff_curveWallMultiplier_two_two :
    coeff (mk2 2 2) (curveWallMultiplier (R := ℤ) 0) = 8 := by
  rw [curveWallMultiplier, wallFraming_of_intersection (m := 0) (by simp)]
  simpa using coeff_kronecker_two_two

/-! ### The point and the Jordan quiver -/

/-- `2 dim End(𝒪_x) + v(𝒪_x)² = 2`: by Riemann–Roch `dim Ext¹(𝒪_x, 𝒪_x) = 2`, one loop of the
Jordan quiver and its dual. -/
theorem point_ext_one : 2 * 1 + selfPairing intersection point = 2 := by
  rw [show selfPairing intersection point = 0 from isIsotropic_point]
  norm_num

/-- The framing of a point `𝒪_x` by an object of class `v`: `χ(E, 𝒪_x) = -⟨v, v(𝒪_x)⟩`. -/
def pointFraming (v : MukaiLattice NS) : ℤ := -pairing intersection v point

/-- `χ(E, 𝒪_x) = rk E`. -/
theorem pointFraming_eq (v : MukaiLattice NS) : pointFraming v = v.1 := by
  obtain ⟨r, c, s⟩ := v
  simp [pointFraming]

/-- A line bundle frames a point by `1`, the rank-two extension `S` of `rankTwo_classes` by
`2`. -/
theorem pointFraming_lineBundle_rankTwo (D : NS) :
    pointFraming (lineBundle D) = 1 ∧
      pointFraming (lineBundle (-2, 2) + lineBundle (-1, 0)) = 2 := by
  constructor <;> simp [pointFraming_eq]

/-- The geometric framed series of a point framed by an object of class `v` of nonnegative rank:
the Jordan quiver with framing `rk E`. -/
noncomputable def pointMultiplier (v : MukaiLattice NS) : MvPowerSeries Unit R :=
  Z (fun _ => (pointFraming v).toNat) jordanBPS

/-- Its coefficient of `y` is `(-1)^{rk E} rk E` (with `rk E` read as `0` if it is negative). -/
theorem coeff_pointMultiplier (v : MukaiLattice NS) :
    coeff (Finsupp.single () 1) (pointMultiplier (R := R) v) =
      (-1) ^ v.1.toNat * (v.1.toNat : R) := by
  rw [pointMultiplier, coeff_atom_jordan, pointFraming_eq]

/-- **Framing by `S` is not the square of framing by a line bundle**: the series of the
rank-two extension `S` is `Z_1(-y)²`, not `Z_1(y)²`. -/
theorem pointMultiplier_rankTwo_ne (D : NS) :
    pointMultiplier (R := ℤ) (lineBundle (-2, 2) + lineBundle (-1, 0)) ≠
      pointMultiplier (lineBundle D) * pointMultiplier (lineBundle D) := by
  obtain ⟨h1, h2⟩ := pointFraming_lineBundle_rankTwo D
  simp only [pointMultiplier, h1, h2]
  exact jordan_Z_two_ne

/-- ... while it is `Z_1(-y)²` (`Z_add` in geometric variables). -/
theorem pointMultiplier_rankTwo_eq (D : NS) :
    pointMultiplier (R := R) (lineBundle (-2, 2) + lineBundle (-1, 0)) =
      rescale (eps 1) (pointMultiplier (lineBundle D)) *
        rescale (eps 1) (pointMultiplier (lineBundle D)) := by
  obtain ⟨h1, h2⟩ := pointFraming_lineBundle_rankTwo D
  simp only [pointMultiplier, h1, h2]
  exact jordan_Z_two_eq

end AlgebraicGeometry.K3.EllipticWithSection
