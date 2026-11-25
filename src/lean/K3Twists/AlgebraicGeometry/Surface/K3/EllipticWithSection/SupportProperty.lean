/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.CurveWall
import K3Twists.LinearAlgebra.Lattice.Mukai.Support

/-!
# The root test and the support property at the curve wall

The charge of the curve wall of the elliptic K3 surface with a section
(`EllipticWithSection/CurveWall.lean`), the charge of Tramel and Xia (arXiv:1702.06252) at
`H = C + 2F`, `β = -C/4`, `z = 2 - i`, is the normalized charge of
`LinearAlgebra/Lattice/Mukai/Support.lean`

```
Z(r, c, s) = 3r - s + β·c + i (H·c - r)                 (charge_eq_normalizedCharge)
```

with `x = 3` and `a = 1`, on the real model `ℝ × NS_ℝ × ℝ` of `MukaiLattice ℤ NS`. Here
`H² = 2`, `β² = -1/8` and

```
δ = 2x + β² - a²/H² = 6 - 1/8 - 1/2 = 43/8                (normalizedDelta_curveWall).
```

* **The root test** (`re_charge_pos`): `δ > 2`, and the intersection form is negative definite on
  `H^⊥ = ℝC'` with `C' = C` (`H·(w₁C + w₂F) = w₂`), so by the completed square every root of
  positive rank with `Im Z = 0` has `Re Z > 0`: the rank bound `r² ≤ 2/δ = 16/43` leaves no
  positive-rank candidate.
* **The support property** (`exists_supportProperty_charge`): on the kernel of `Z` a real class
  has `c₂ = r`, `s = 11r/4 + c₁/2` and square `-2(c₁ - r/4)² - 43r²/8`, negative definite; an
  integral class there of square at least `-2` is zero. So there is `D` with `‖v‖ ≤ D |Z(v)|` for
  every integral class of square at least `-2`.

These are lattice statements: that `Z` is the charge of a stability condition is the cited
theorem of Tramel and Xia.
-/

namespace AlgebraicGeometry.K3.EllipticWithSection

open Mukai Complex

/-- The intersection form on `NS ⊗ ℝ = ℝC ⊕ ℝF`: `(a, b)·(a', b') = -2aa' + ab' + a'b`. -/
noncomputable def intersectionReal : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => -2 * x.1 * y.1 + x.1 * y.2 + x.2 * y.1)
    (fun x y z => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun x y z => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

@[simp]
lemma intersectionReal_apply (x y : ℝ × ℝ) :
    intersectionReal x y = -2 * x.1 * y.1 + x.1 * y.2 + x.2 * y.1 :=
  rfl

lemma intersectionReal_comm (x y : ℝ × ℝ) : intersectionReal x y = intersectionReal y x := by
  simp only [intersectionReal_apply]
  ring

/-- The real model `NS → NS ⊗ ℝ`. -/
def toRealNS : NS →+ ℝ × ℝ := (Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)

@[simp]
lemma toRealNS_apply (x : NS) : toRealNS x = ((x.1 : ℝ), (x.2 : ℝ)) :=
  rfl

lemma intersectionReal_toRealNS (x y : NS) :
    intersectionReal (toRealNS x) (toRealNS y) = intersection x y := by
  simp [intersection_apply]

lemma finite_toRealNS_norm_le (R : ℝ) : {x : NS | ‖toRealNS x‖ ≤ R}.Finite := by
  refine ((finite_int_abs_le R).prod (finite_int_abs_le R)).subset fun x hx => ?_
  have h := norm_prod_le_iff.mp hx
  exact ⟨by simpa [Real.norm_eq_abs] using h.1, by simpa [Real.norm_eq_abs] using h.2⟩

/-- The class `β = -C/4` of the curve-wall charge in `NS ⊗ ℝ`. -/
noncomputable abbrev betaReal : ℝ × ℝ := (-1 / 4, 0)

/-- The polarization `H = C + 2F` in `NS ⊗ ℝ`. -/
abbrev polarizationReal : ℝ × ℝ := (1, 2)

/-- The normalized charge with `x = 3`, `β = -C/4`, `H = C + 2F`, `a = 1`. -/
noncomputable abbrev curveWallCharge : MukaiLattice ℝ (ℝ × ℝ) →ₗ[ℝ] ℂ :=
  normalizedCharge intersectionReal 3 betaReal polarizationReal 1

/-- **The curve-wall charge is a normalized charge**: `Z(v) = 3r - s + β·c + i (H·c - r)` on the
real model of `v`. -/
theorem charge_eq_normalizedCharge (v : MukaiLattice ℤ NS) :
    charge v = curveWallCharge (realModel toRealNS v) := by
  apply Complex.ext
  · rw [re_charge, re_normalizedCharge]
    obtain ⟨r, ⟨a, b⟩, s⟩ := v
    simp
    ring
  · rw [im_charge, im_normalizedCharge]
    obtain ⟨r, ⟨a, b⟩, s⟩ := v
    simp

/-- `δ = 43/8` for the curve-wall charge. -/
theorem normalizedDelta_curveWall :
    normalizedDelta intersectionReal 3 betaReal polarizationReal 1 = 43 / 8 := by
  norm_num [normalizedDelta]

/-- The intersection form is negative definite on `H^⊥`: `H·w = w₂`, and `w·w = -2w₁²` there. -/
lemma intersectionReal_neg_of_orthogonal (w : ℝ × ℝ) (hw : intersectionReal polarizationReal w = 0)
    (hw0 : w ≠ 0) : intersectionReal w w < 0 := by
  obtain ⟨w₁, w₂⟩ := w
  simp only [intersectionReal_apply] at hw ⊢
  have h2 : w₂ = 0 := by linarith
  have h1 : w₁ ≠ 0 := fun h1 => hw0 (by simp [h1, h2])
  subst h2
  have : 0 < w₁ ^ 2 := by positivity
  nlinarith

/-- **The root test at the curve wall.** Every root of positive rank with `Im Z = 0` has
`Re Z > 0`: `δ = 43/8 > 2`. -/
theorem re_charge_pos {v : MukaiLattice ℤ NS} (hv : IsSpherical intersection v) (hr : 0 < v.1)
    (him : (charge v).im = 0) : 0 < (charge v).re := by
  rw [charge_eq_normalizedCharge] at him ⊢
  have hv' : selfPairing intersectionReal (realModel toRealNS v) = -2 := by
    rw [selfPairing_realModel intersectionReal_toRealNS, hv]
    norm_num
  refine re_normalizedCharge_pos intersectionReal_comm (by norm_num) (by norm_num)
    (fun w hw => ?_) (by rw [normalizedDelta_curveWall]; norm_num) hv' ?_ ?_
  · by_cases hw0 : w = 0
    · simp [hw0]
    · exact (intersectionReal_neg_of_orthogonal w hw hw0).le
  · obtain ⟨r, c, s⟩ := v
    simpa using (show (1 : ℝ) ≤ r by exact_mod_cast hr)
  · rw [im_normalizedCharge] at him
    linarith

/-- On the kernel of the curve-wall charge a real class has `c₂ = r`, `s = 11r/4 + c₁/2`, and
square `-2(c₁ - r/4)² - 43r²/8`. -/
private lemma ker_curveWallCharge {v : MukaiLattice ℝ (ℝ × ℝ)} (hv : curveWallCharge v = 0) :
    v.2.1.2 = v.1 ∧ 4 * v.2.2 = 11 * v.1 + 2 * v.2.1.1 ∧
      selfPairing intersectionReal v = -2 * (v.2.1.1 - v.1 / 4) ^ 2 - 43 / 8 * v.1 ^ 2 := by
  have hre := congrArg Complex.re hv
  have him := congrArg Complex.im hv
  rw [re_normalizedCharge, Complex.zero_re] at hre
  rw [im_normalizedCharge, Complex.zero_im] at him
  obtain ⟨r, ⟨c₁, c₂⟩, s⟩ := v
  simp only [intersectionReal_apply] at hre him
  have h2 : c₂ = r := by linarith
  have hs : 4 * s = 11 * r + 2 * c₁ := by rw [h2] at hre; linarith
  refine ⟨h2, hs, ?_⟩
  simp only [selfPairing_mk, intersectionReal_apply]
  rw [h2]
  linear_combination (-r / 2) * hs

/-- **The support property at the curve wall.** There is `D` with `‖v‖ ≤ D |Z(v)|` for every
integral class `v` with `v² ≥ -2`, the norm being that of the real model. -/
theorem exists_supportProperty_charge :
    ∃ D, ∀ v : MukaiLattice ℤ NS, -2 ≤ selfPairing intersection v →
      ‖realModel toRealNS v‖ ≤ D * ‖charge v‖ := by
  have hker : ∀ v, curveWallCharge v = 0 → v ≠ 0 → mukaiForm intersectionReal v v < 0 := by
    intro v hv hv0
    obtain ⟨h2, hs, hsq⟩ := ker_curveWallCharge hv
    change selfPairing intersectionReal v < 0
    rw [hsq]
    obtain ⟨r, ⟨c₁, c₂⟩, s⟩ := v
    simp only at h2 hs ⊢
    by_cases hr : r = 0
    · have hc₁ : c₁ ≠ 0 := by
        intro hc₁
        apply hv0
        have : s = 0 := by rw [hr, hc₁] at hs; linarith
        simp [hr, hc₁, h2, this]
      rw [hr]
      have : 0 < c₁ ^ 2 := by positivity
      nlinarith
    · have : 0 < r ^ 2 := by positivity
      nlinarith [sq_nonneg (c₁ - r / 4)]
  have hroot : ∀ w ∈ Set.range (realModel toRealNS), w ≠ 0 →
      -2 ≤ mukaiForm intersectionReal w w → curveWallCharge w ≠ 0 := by
    rintro _ ⟨v, rfl⟩ hw0 hw2 hZ
    obtain ⟨h2, hs, hsq⟩ := ker_curveWallCharge hZ
    change -2 ≤ selfPairing intersectionReal _ at hw2
    rw [hsq] at hw2
    obtain ⟨r, ⟨c₁, c₂⟩, s⟩ := v
    simp only [realModel_apply, toRealNS_apply] at h2 hs hw2 hw0
    have h2' : c₂ = r := by exact_mod_cast h2
    have hs' : 4 * s = 11 * r + 2 * c₁ := by exact_mod_cast hs
    have hr : r = 0 := by
      by_contra hr
      have h1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by
        rw [← sq_abs, ← Int.cast_abs]
        exact one_le_pow₀ (by exact_mod_cast Int.one_le_abs hr)
      nlinarith [sq_nonneg ((c₁ : ℝ) - r / 4)]
    subst hr
    have hc : c₁ = 2 * s := by omega
    subst hc
    have hs0 : s = 0 := by
      have : ((s : ℝ)) ^ 2 * 8 ≤ 2 := by push_cast at hw2; nlinarith
      by_contra hs0
      have h1 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by
        rw [← sq_abs, ← Int.cast_abs]
        exact one_le_pow₀ (by exact_mod_cast Int.one_le_abs hs0)
      linarith
    apply hw0
    simp [hs0, h2']
  obtain ⟨D, hD⟩ := exists_supportProperty (mukaiForm intersectionReal) curveWallCharge hker
    (finite_range_realModel_norm_le finite_toRealNS_norm_le) hroot
  refine ⟨D, fun v hv => ?_⟩
  rw [charge_eq_normalizedCharge]
  refine hD _ ⟨⟨v, rfl⟩, ?_⟩
  change -2 ≤ selfPairing intersectionReal _
  rw [selfPairing_realModel intersectionReal_toRealNS]
  exact_mod_cast hv

end AlgebraicGeometry.K3.EllipticWithSection
