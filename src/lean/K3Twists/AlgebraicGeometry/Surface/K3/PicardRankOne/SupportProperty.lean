/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.Visibility

/-!
# The support property in Picard rank one

Let `X` be a K3 surface with `Pic X = ℤH`, `H² = 2d > 0`. Its Mukai lattice is the Mukai lattice
`MukaiLattice ℤ ℤ` of the rank-one lattice `(ℤ, 2dxy)`, with real model `MukaiLattice ℝ ℝ` along
`ℤ → ℝ`. At the point `p = (b, t)` of the projective model the central charge `Z_p` vanishes on
the kernel line of `κ_p = (1, b, dt)`, of square `-2d·height(p)`. If `d·height(p) > 1`, a nonzero
integral class `rκ_p` in the kernel has square `-2dr²·height(p) < -2`, so no class of square at
least `-2` has charge zero, and the support property of `Lattice/Mukai/Support.lean` holds:

* `exists_supportProperty_normalizedCharge`: for the normalized charge at `p`;
* `exists_supportProperty_modelCharge`: for the central charge `Z_p` itself, through the
  `GL₂⁺(ℝ)` comparison `modelCharge_eq_normalizedCharge`: there is `D` with
  `‖v‖ ≤ D |Z_p(v)|` for every integral class with `⟨v, v⟩ ≥ -2`.

In the coordinate `z = b + ia` of the upper half-plane, `height(p) = a²`, so the condition reads
`d (Im z)² > 1`. It is the condition of `rayClear_of_one_lt`: the punctures of roots lie at
heights `1/(dr²) ≤ 1/d`.

**Strata in Picard rank one are `A₁`** (`eq_or_eq_neg_of_modelCharge_eq_zero`): the kernel of
`Z_p` is the line of `κ_p`, so two roots whose charges vanish at `p` are equal or opposite, and
the kernel root system at a puncture is `{±δ}`.
-/

namespace AlgebraicGeometry.K3.PicardRankOne

open Mukai MukaiVector

/-- The real model `ℤ → ℝ` of the rank-one lattice. -/
abbrev intCast : ℤ →+ ℝ := Int.castAddHom ℝ

lemma rankOneForm_intCast (d x y : ℤ) :
    rankOneForm (d : ℝ) (intCast x) (intCast y) = rankOneForm d x y := by
  simp

lemma finite_intCast_norm_le (R : ℝ) : {x : ℤ | ‖intCast x‖ ≤ R}.Finite := by
  simpa [Real.norm_eq_abs] using finite_int_abs_le R

/-- On the kernel of the normalized charge at `p`, a real class `(r, c, s)` has `c = rb`, `s = drt`
and square `-2dr²·height(p)`. -/
private lemma ker_normalizedCharge {d : ℝ} (hd : d ≠ 0) {p : ℝ × ℝ} {v : MukaiLattice ℝ ℝ}
    (hv : normalizedCharge (rankOneForm d) (d * p.2) 0 1 (2 * d * p.1) v = 0) :
    v.2.1 = v.1 * p.1 ∧ v.2.2 = d * v.1 * p.2 ∧
      selfPairing (rankOneForm d) v = -2 * d * v.1 ^ 2 * height p := by
  have hre := congrArg Complex.re hv
  have him := congrArg Complex.im hv
  rw [re_normalizedCharge, Complex.zero_re] at hre
  rw [im_normalizedCharge, Complex.zero_im] at him
  obtain ⟨r, c, s⟩ := v
  simp only [rankOneForm_apply, map_zero, LinearMap.zero_apply, add_zero] at hre him
  have hc : c = r * p.1 := by
    have : 2 * d * (c - r * p.1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linarith : d = 0) hd
    · linarith
  refine ⟨hc, by linarith, ?_⟩
  simp only [selfPairing_mk, rankOneForm_apply, height]
  have hs : s = d * r * p.2 := by linarith
  rw [hc, hs]
  ring

/-- **The support property of the normalized charge** at a point `p` with `d·height(p) > 1`, on the
integral classes of square at least `-2`. -/
theorem exists_supportProperty_normalizedCharge {d : ℤ} (hd : 0 < d) {p : ℝ × ℝ}
    (hp : 1 < d * height p) :
    ∃ D, SupportProperty (normalizedCharge (rankOneForm (d : ℝ)) (d * p.2) 0 1 (2 * d * p.1))
      {w | w ∈ Set.range (realModel intCast) ∧ -2 ≤ selfPairing (rankOneForm (d : ℝ)) w} D := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hh : 0 < height p := by
    by_contra h
    push Not at h
    nlinarith
  refine exists_supportProperty (mukaiForm (rankOneForm (d : ℝ))) _ ?_
    (finite_range_realModel_norm_le finite_intCast_norm_le) ?_
  · intro v hv hv0
    obtain ⟨hc, hs, hsq⟩ := ker_normalizedCharge hd'.ne' hv
    have hr : v.1 ≠ 0 := by
      intro hr
      apply hv0
      obtain ⟨r, c, s⟩ := v
      simp only at hr hc hs
      simp [hr, hc, hs]
    change selfPairing (rankOneForm (d : ℝ)) v < 0
    rw [hsq]
    have : 0 < v.1 ^ 2 := by positivity
    have : 0 < d * v.1 ^ 2 * height p := by positivity
    nlinarith
  · rintro _ ⟨v, rfl⟩ hw0 hw2 hZ
    obtain ⟨hc, hs, hsq⟩ := ker_normalizedCharge hd'.ne' hZ
    obtain ⟨r, c, s⟩ := v
    simp only [realModel_apply] at hc hs hsq hw2 hw0
    have hr : r ≠ 0 := by
      intro hr
      apply hw0
      simp only [hr, Int.cast_zero, zero_mul, mul_zero] at hc hs
      simp [hr, hc, hs]
    have h1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by
      rw [← sq_abs, ← Int.cast_abs]
      exact one_le_pow₀ (by exact_mod_cast Int.one_le_abs hr)
    change -2 ≤ selfPairing (rankOneForm (d : ℝ)) _ at hw2
    rw [hsq] at hw2
    nlinarith

/-- `‖z'‖ ≤ (1 + (|b| + 1)/a) ‖z‖` for `z = (Re z' + b Im z') + i a Im z'` and `a > 0`. -/
private lemma norm_le_of_eq_mk {z' : ℂ} {b a : ℝ} (ha : 0 < a) :
    ‖z'‖ ≤ (1 + (|b| + 1) / a) * ‖(⟨z'.re + b * z'.im, a * z'.im⟩ : ℂ)‖ := by
  set z : ℂ := ⟨z'.re + b * z'.im, a * z'.im⟩
  have him : |z'.im| ≤ ‖z‖ / a := by
    rw [le_div_iff₀ ha]
    have := Complex.abs_im_le_norm z
    simp only [z, abs_mul, abs_of_pos ha] at this
    linarith
  have hre : |z'.re| ≤ ‖z‖ + |b| * (‖z‖ / a) := by
    have h1 : z'.re = z.re - b * z'.im := by simp [z]
    rw [h1]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    exact add_le_add (Complex.abs_re_le_norm z)
      (mul_le_mul_of_nonneg_left him (abs_nonneg b))
  calc ‖z'‖ ≤ |z'.re| + |z'.im| := Complex.norm_le_abs_re_add_abs_im z'
    _ ≤ ‖z‖ + |b| * (‖z‖ / a) + ‖z‖ / a := add_le_add hre him
    _ = (1 + (|b| + 1) / a) * ‖z‖ := by field_simp; ring

/-- **The support property of the central charge in Picard rank one.** At a point `p` of the
model with `d·height(p) > 1` there is `D` with `‖v‖ ≤ D |Z_p(v)|` for every integral class `v`
with `⟨v, v⟩ ≥ -2`, the norm being the maximum of `|r|`, `|c|` and `|s|`. -/
theorem exists_supportProperty_modelCharge {d : ℤ} (hd : 0 < d) {p : ℝ × ℝ}
    (hp : 1 < d * height p) :
    ∃ D, ∀ v : MukaiVector ℤ, -2 ≤ pairing d v v →
      ‖v.toReal.toMukaiLattice‖ ≤ D * ‖modelCharge d p v.toReal‖ := by
  obtain ⟨D, hD⟩ := exists_supportProperty_normalizedCharge hd hp
  have hh : 0 < height p := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    by_contra h
    push Not at h
    nlinarith
  have hp' : p.1 ^ 2 ≤ p.2 := by rw [height] at hh; linarith
  set a := Real.sqrt (p.2 - p.1 ^ 2)
  have ha : 0 < a := Real.sqrt_pos.mpr (by rw [height] at hh; linarith)
  refine ⟨max D 0 * (1 + (|p.1| + 1) / a), fun v hv => ?_⟩
  have hw : v.toReal.toMukaiLattice = realModel intCast (v.r, v.c, v.s) := rfl
  have hmem : v.toReal.toMukaiLattice ∈ {w | w ∈ Set.range (realModel intCast) ∧
      -2 ≤ selfPairing (rankOneForm (d : ℝ)) w} := by
    refine ⟨⟨_, hw.symm⟩, ?_⟩
    rw [hw, selfPairing_realModel (rankOneForm_intCast d)]
    simp only [selfPairing_mk, rankOneForm_apply]
    have : -2 ≤ MukaiVector.pairing d v v := hv
    simp only [MukaiVector.pairing] at this
    exact_mod_cast (by linarith : (-2 : ℤ) ≤ 2 * d * (v.c * v.c) - 2 * (v.r * v.s))
  have key := (hD.mono_const (le_max_left D 0)).of_norm_le
    (Z' := fun w : MukaiLattice ℝ ℝ => modelCharge d p ⟨w.1, w.2.1, w.2.2⟩)
    (le_max_right _ _) fun w _ => by
      rw [modelCharge_eq_normalizedCharge (d : ℝ) hp']
      exact norm_le_of_eq_mk ha
  exact key _ hmem

/-- **Strata in Picard rank one are `A₁`.** Above the parabola, two roots whose charges vanish at
`p` are equal or opposite: both are multiples of the kernel vector `κ_p`, of the same square. -/
theorem eq_or_eq_neg_of_modelCharge_eq_zero {d : ℤ} (hd : 0 < d) {p : ℝ × ℝ}
    (hp : p.1 ^ 2 < p.2) {δ δ' : MukaiVector ℤ} (hδ : IsRoot d δ) (hδ' : IsRoot d δ')
    (hZ : modelCharge d p δ.toReal = 0) (hZ' : modelCharge d p δ'.toReal = 0) :
    δ' = δ ∨ δ' = -δ := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [modelCharge_eq_zero_iff hd' hp] at hZ hZ'
  have h1 := isRoot_toReal.mpr hδ
  have h2 := isRoot_toReal.mpr hδ'
  unfold IsRoot at h1 h2
  rw [hZ, MukaiVector.pairing_smul_left, MukaiVector.pairing_smul_right] at h1
  rw [hZ', MukaiVector.pairing_smul_left, MukaiVector.pairing_smul_right] at h2
  have hsq : (δ'.r : ℝ) ^ 2 = (δ.r : ℝ) ^ 2 := by
    have hκ : MukaiVector.pairing (d : ℝ) (kernelVector d p) (kernelVector d p) ≠ 0 := by
      intro h0
      rw [h0] at h1
      norm_num at h1
    apply mul_right_cancel₀ hκ
    simp only [toReal_r] at h1 h2
    linarith
  have hsq' : δ'.r ^ 2 = δ.r ^ 2 := by exact_mod_cast hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq' with h | h
  · left
    apply toReal_injective
    rw [hZ, hZ', toReal_r, toReal_r, h]
  · right
    apply toReal_injective
    rw [toReal_neg, hZ, hZ', toReal_r, toReal_r, h, Int.cast_neg, neg_smul]

end AlgebraicGeometry.K3.PicardRankOne
