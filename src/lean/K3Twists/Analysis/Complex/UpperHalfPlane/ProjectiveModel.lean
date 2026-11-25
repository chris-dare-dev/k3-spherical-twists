/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# The projective model of the upper half-plane

The map `z ↦ (Re z, |z|²)` identifies the upper half-plane `ℍ` with the region `t > b²` of the
`(b, t)`-plane lying above the parabola `t = b²`. In these coordinates the hyperbolic plane is a
projective (Beltrami–Klein) model whose boundary is the parabola together with one point at
infinity, and its geodesics are straight:

* `projectiveModel_injective`, `range_projectiveModel`: the map is a bijection onto `t > b²`;
  the height `t - b²` of the image of `z` is `(Im z)²`;
* `cosh_dist_eq`: with `B(p, q) = t_p + t_q - 2 b_p b_q`,
  `cosh d(z, w) = B(p, q) / (2 Im z Im w)` for the images `p`, `q` of `z`, `w`; the bilinear form
  `B` is (up to a factor) the Lorentzian form of which this is the projective model;
* `normSq_sub_ofReal`, `projectiveModel_snd_eq_iff`: the semicircles centred on the real axis
  are exactly the non-vertical straight lines meeting the model, and vertical lines stay
  vertical;
* `dist_add_dist_eq_iff`: a point `w` lies on the geodesic segment from `z` to `u`, that is
  `d(z, w) + d(w, u) = d(z, u)`, exactly when its image lies on the straight segment between the
  images of `z` and `u`.

The distance is Mathlib's hyperbolic distance on `ℍ` (`UpperHalfPlane.dist_eq`).
-/

noncomputable section

open Real Set

namespace UpperHalfPlane

/-- The point `(Re z, |z|²)` of the projective model of the hyperbolic plane. -/
def projectiveModel (z : ℍ) : ℝ × ℝ := (z.re, z.re ^ 2 + z.im ^ 2)

@[simp] lemma projectiveModel_fst (z : ℍ) : (projectiveModel z).1 = z.re := rfl

@[simp] lemma projectiveModel_snd (z : ℍ) : (projectiveModel z).2 = z.re ^ 2 + z.im ^ 2 := rfl

/-- The second coordinate is `|z|²`. -/
lemma projectiveModel_snd_eq_normSq (z : ℍ) :
    (projectiveModel z).2 = Complex.normSq (z : ℂ) := by
  simp [Complex.normSq_apply, sq]

/-- The height of the image of `z` above the parabola `t = b²` is `(Im z)²`. -/
lemma projectiveModel_snd_sub_sq (z : ℍ) :
    (projectiveModel z).2 - (projectiveModel z).1 ^ 2 = z.im ^ 2 := by
  simp

lemma projectiveModel_mem (z : ℍ) : (projectiveModel z).1 ^ 2 < (projectiveModel z).2 := by
  have := z.im_pos
  simp only [projectiveModel_fst, projectiveModel_snd]
  nlinarith

lemma projectiveModel_injective : Function.Injective projectiveModel := by
  intro z w h
  simp only [projectiveModel, Prod.mk.injEq] at h
  obtain ⟨hre, h2⟩ := h
  rw [hre] at h2
  have hz := z.im_pos
  have hw := w.im_pos
  refine ext_re_im hre ?_
  nlinarith

/-- The inverse of the projective model: the point `b + i√(t - b²)` over `(b, t)`. -/
def ofProjectiveModel (p : ℝ × ℝ) (hp : p.1 ^ 2 < p.2) : ℍ :=
  ⟨⟨p.1, √(p.2 - p.1 ^ 2)⟩, by simpa using sub_pos.mpr hp⟩

@[simp] lemma ofProjectiveModel_re (p : ℝ × ℝ) (hp : p.1 ^ 2 < p.2) :
    (ofProjectiveModel p hp).re = p.1 := rfl

@[simp] lemma ofProjectiveModel_im (p : ℝ × ℝ) (hp : p.1 ^ 2 < p.2) :
    (ofProjectiveModel p hp).im = √(p.2 - p.1 ^ 2) := rfl

@[simp] lemma projectiveModel_ofProjectiveModel (p : ℝ × ℝ) (hp : p.1 ^ 2 < p.2) :
    projectiveModel (ofProjectiveModel p hp) = p := by
  ext
  · simp
  · simp [sq_sqrt (sub_pos.mpr hp).le]

/-- The image of the projective model is the region `t > b²` above the parabola. -/
theorem range_projectiveModel : range projectiveModel = {p : ℝ × ℝ | p.1 ^ 2 < p.2} := by
  ext p
  exact ⟨fun ⟨z, hz⟩ => hz ▸ projectiveModel_mem z,
    fun hp => ⟨ofProjectiveModel p hp, projectiveModel_ofProjectiveModel p hp⟩⟩

/-! ### Distance -/

/-- The bilinear form of the model: `B(p, q) = t_p + t_q - 2 b_p b_q`, so `B(p, p) = 2(t_p - b_p²)`.
It is `-1/d` times the Mukai pairing of the kernel vectors `(1, b, dt)` of a K3 surface of degree
`2d` and Picard rank one. -/
def modelForm (p q : ℝ × ℝ) : ℝ := p.2 + q.2 - 2 * p.1 * q.1

lemma modelForm_comm (p q : ℝ × ℝ) : modelForm p q = modelForm q p := by
  unfold modelForm; ring

/-- In the projective model, `cosh d(z, w) = B(p, q) / (2 Im z Im w)`. -/
theorem cosh_dist_eq (z w : ℍ) :
    cosh (dist z w) = modelForm (projectiveModel z) (projectiveModel w) / (2 * z.im * w.im) := by
  have hz := z.im_pos
  have hw := w.im_pos
  rw [cosh_dist, Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, coe_re, coe_im, modelForm, projectiveModel_fst,
    projectiveModel_snd]
  field_simp
  ring

/-- The same formula in terms of the model alone: `cosh d = B(p, q) / √(B(p, p) B(q, q))`. -/
theorem cosh_dist_eq_modelForm (z w : ℍ) :
    cosh (dist z w) = modelForm (projectiveModel z) (projectiveModel w) /
      √(modelForm (projectiveModel z) (projectiveModel z) *
        modelForm (projectiveModel w) (projectiveModel w)) := by
  rw [cosh_dist_eq]
  congr 1
  have hz := z.im_pos
  have hw := w.im_pos
  rw [show modelForm (projectiveModel z) (projectiveModel z) *
      modelForm (projectiveModel w) (projectiveModel w) = (2 * z.im * w.im) ^ 2 by
    simp only [modelForm, projectiveModel_fst, projectiveModel_snd]; ring]
  rw [sqrt_sq (by positivity)]

/-! ### Geodesic lines -/

/-- `|z - m|² = t - 2mb + m²`. So the semicircle `|z - m| = R` about a real point `m` is the
straight line `t = 2mb + R² - m²` of the model. -/
theorem normSq_sub_ofReal (z : ℍ) (m : ℝ) :
    Complex.normSq ((z : ℂ) - m) =
      (projectiveModel z).2 - 2 * m * (projectiveModel z).1 + m ^ 2 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, coe_re, coe_im,
    Complex.ofReal_re, Complex.ofReal_im, projectiveModel_fst, projectiveModel_snd]
  ring

/-- A non-vertical straight line `t = αb + β` of the model is the semicircle about the real point
`α/2` with squared radius `β + α²/4`. -/
theorem projectiveModel_snd_eq_iff (z : ℍ) (α β : ℝ) :
    (projectiveModel z).2 = α * (projectiveModel z).1 + β ↔
      Complex.normSq ((z : ℂ) - (α / 2 : ℝ)) = β + α ^ 2 / 4 := by
  rw [normSq_sub_ofReal]
  constructor <;> intro h <;> linarith

/-- A straight line `t = αb + β` meets the model exactly when `β + α²/4 > 0`, the squared radius
of the corresponding semicircle. -/
theorem exists_projectiveModel_snd_eq_iff (α β : ℝ) :
    (∃ z : ℍ, (projectiveModel z).2 = α * (projectiveModel z).1 + β) ↔ 0 < β + α ^ 2 / 4 := by
  constructor
  · rintro ⟨z, hz⟩
    have h := projectiveModel_mem z
    nlinarith [sq_nonneg ((projectiveModel z).1 - α / 2)]
  · intro h
    have hp : (α / 2) ^ 2 < α * (α / 2) + β := by nlinarith
    refine ⟨ofProjectiveModel (α / 2, α * (α / 2) + β) hp, ?_⟩
    simp

/-! ### Geodesic segments -/

/-- The image of `w` lies on the straight line through the images of `z` and `u`:
the determinant `(b_w - b_z)(t_u - t_z) - (t_w - t_z)(b_u - b_z)` vanishes. -/
private def collinearDet (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- **Straight segments are geodesic.** If the image of `w` lies on the straight segment between
the images of `z` and `u`, then `d(z, w) + d(w, u) = d(z, u)`. -/
theorem dist_add_dist_eq_of_mem_segment {z w u : ℍ}
    (h : projectiveModel w ∈ segment ℝ (projectiveModel z) (projectiveModel u)) :
    dist z w + dist w u = dist z u := by
  obtain ⟨l, m, hl, hm, hlm, hw⟩ := h
  have hb : w.re = l * z.re + m * u.re := by
    have := congrArg Prod.fst hw; simp at this; linarith
  have ht : w.re ^ 2 + w.im ^ 2 = l * (z.re ^ 2 + z.im ^ 2) + m * (u.re ^ 2 + u.im ^ 2) := by
    have := congrArg Prod.snd hw; simp at this; linarith
  have hz := z.im_pos
  have hw' := w.im_pos
  have hu := u.im_pos
  set x := dist z w
  set y := dist w u
  set D := dist z u
  have hx0 : 0 ≤ x := dist_nonneg
  have hy0 : 0 ≤ y := dist_nonneg
  have hD0 : 0 ≤ D := dist_nonneg
  have cx := cosh_dist_eq z w
  have cy := cosh_dist_eq w u
  have cD := cosh_dist_eq z u
  simp only [modelForm, projectiveModel_fst, projectiveModel_snd] at cx cy cD
  -- `sinh x = m (Im u / Im w) sinh D` and `sinh y = l (Im z / Im w) sinh D`
  have sD : 0 ≤ sinh D := sinh_nonneg_iff.mpr hD0
  have hl' : l = 1 - m := by linarith
  subst hl'
  have key1 : (cosh x) ^ 2 - 1 = (m * u.im / w.im) ^ 2 * ((cosh D) ^ 2 - 1) := by
    rw [cx, cD, hb]
    field_simp
    have : w.im ^ 2 = (1 - m) * (z.re ^ 2 + z.im ^ 2) + m * (u.re ^ 2 + u.im ^ 2) -
        ((1 - m) * z.re + m * u.re) ^ 2 := by rw [← hb]; linarith
    rw [this]
    ring
  have key2 : (cosh y) ^ 2 - 1 = ((1 - m) * z.im / w.im) ^ 2 * ((cosh D) ^ 2 - 1) := by
    rw [cy, cD, hb]
    field_simp
    have : w.im ^ 2 = (1 - m) * (z.re ^ 2 + z.im ^ 2) + m * (u.re ^ 2 + u.im ^ 2) -
        ((1 - m) * z.re + m * u.re) ^ 2 := by rw [← hb]; linarith
    rw [this]
    ring
  have sx : sinh x = m * u.im / w.im * sinh D := by
    have h1 : 0 ≤ sinh x := sinh_nonneg_iff.mpr hx0
    have h2 : 0 ≤ m * u.im / w.im * sinh D := by positivity
    rw [← sq_eq_sq₀ h1 h2, sinh_sq, mul_pow, sinh_sq, key1]
  have sy : sinh y = (1 - m) * z.im / w.im * sinh D := by
    have h1 : 0 ≤ sinh y := sinh_nonneg_iff.mpr hy0
    have h2 : 0 ≤ (1 - m) * z.im / w.im * sinh D := by
      have : 0 ≤ 1 - m := hl
      positivity
    rw [← sq_eq_sq₀ h1 h2, sinh_sq, mul_pow, sinh_sq, key2]
  have hcosh : cosh (x + y) = cosh D := by
    rw [cosh_add, sx, sy]
    have hsD : sinh D ^ 2 = cosh D ^ 2 - 1 := sinh_sq D
    calc cosh x * cosh y + m * u.im / w.im * sinh D * ((1 - m) * z.im / w.im * sinh D)
        = cosh x * cosh y + m * (1 - m) * u.im * z.im / w.im ^ 2 * (cosh D ^ 2 - 1) := by
          rw [← hsD]; ring
      _ = cosh D := by
          rw [cx, cy, cD, hb]
          field_simp
          have : w.im ^ 2 = (1 - m) * (z.re ^ 2 + z.im ^ 2) + m * (u.re ^ 2 + u.im ^ 2) -
              ((1 - m) * z.re + m * u.re) ^ 2 := by rw [← hb]; linarith
          rw [this]
          ring
  exact cosh_injOn (mem_Ici.mpr (add_nonneg hx0 hy0)) (mem_Ici.mpr hD0) hcosh

/-- The defect of the triangle inequality is the square of the collinearity determinant:
`sinh² x sinh² y - (cosh D - cosh x cosh y)² = Det² / (4 (Im z Im w Im u)²)` for the three
sides `x = d(z, w)`, `y = d(w, u)`, `D = d(z, u)`. -/
private lemma triangle_defect (z w u : ℍ) :
    (cosh (dist z w) ^ 2 - 1) * (cosh (dist w u) ^ 2 - 1) -
        (cosh (dist z u) - cosh (dist z w) * cosh (dist w u)) ^ 2 =
      collinearDet (projectiveModel z) (projectiveModel w) (projectiveModel u) ^ 2 /
        (4 * z.im ^ 2 * w.im ^ 2 * u.im ^ 2) := by
  have hz := z.im_pos
  have hw := w.im_pos
  have hu := u.im_pos
  rw [cosh_dist_eq, cosh_dist_eq, cosh_dist_eq]
  simp only [collinearDet, modelForm, projectiveModel_fst, projectiveModel_snd]
  field_simp
  ring

/-- **Geodesic segments are straight.** If `d(z, w) + d(w, u) = d(z, u)`, then the image of `w`
lies on the straight segment between the images of `z` and `u`. -/
theorem mem_segment_of_dist_add_dist_eq {z w u : ℍ} (h : dist z w + dist w u = dist z u) :
    projectiveModel w ∈ segment ℝ (projectiveModel z) (projectiveModel u) := by
  have hz := z.im_pos
  have hw := w.im_pos
  have hu := u.im_pos
  -- The three images are collinear.
  have hcol : collinearDet (projectiveModel z) (projectiveModel w) (projectiveModel u) = 0 := by
    have hadd : sinh (dist z w) * sinh (dist w u) =
        cosh (dist z u) - cosh (dist z w) * cosh (dist w u) := by
      rw [← h, cosh_add]; ring
    have h0 := triangle_defect z w u
    rw [← sinh_sq, ← sinh_sq, ← hadd, sub_eq_zero_of_eq (mul_pow _ _ 2).symm, eq_comm,
      div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact pow_eq_zero_iff two_ne_zero |>.mp h0
    · exact absurd h0 (by positivity)
  -- Write `p_w = p_z + s (p_u - p_z)` and show `0 ≤ s ≤ 1`.
  by_cases hzu : projectiveModel z = projectiveModel u
  · obtain rfl := projectiveModel_injective hzu
    have hzw : dist z w = 0 := by
      rw [dist_self, dist_comm w z] at h
      have := dist_nonneg (x := z) (y := w)
      linarith
    rw [(dist_eq_zero.mp hzw).symm]
    exact left_mem_segment ℝ _ _
  obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ, (projectiveModel w).1 - (projectiveModel z).1 =
      s * ((projectiveModel u).1 - (projectiveModel z).1) ∧
      (projectiveModel w).2 - (projectiveModel z).2 =
      s * ((projectiveModel u).2 - (projectiveModel z).2) := by
    simp only [collinearDet] at hcol
    by_cases h1 : (projectiveModel u).1 = (projectiveModel z).1
    · have h2 : (projectiveModel u).2 - (projectiveModel z).2 ≠ 0 := by
        intro h2; exact hzu (Prod.ext h1.symm (by linarith))
      refine ⟨((projectiveModel w).2 - (projectiveModel z).2) /
        ((projectiveModel u).2 - (projectiveModel z).2), ?_, by field_simp⟩
      rw [h1, sub_self, mul_zero] at hcol ⊢
      rw [sub_zero] at hcol
      exact (mul_eq_zero.mp hcol).resolve_right h2
    · have h1' : (projectiveModel u).1 - (projectiveModel z).1 ≠ 0 := sub_ne_zero.mpr h1
      refine ⟨((projectiveModel w).1 - (projectiveModel z).1) /
        ((projectiveModel u).1 - (projectiveModel z).1), by field_simp, ?_⟩
      field_simp
      linarith
  have hp : projectiveModel w = (1 - s) • projectiveModel z + s • projectiveModel u := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] <;> linarith
  have hD : dist z u = dist z w + dist w u := h.symm
  rcases lt_or_ge s 0 with hs | hs
  · -- `p_z` lies between `p_w` and `p_u`, so `d(w, z) + d(z, u) = d(w, u)` and `w = z`.
    exfalso
    have hne : 1 - s ≠ 0 := by linarith
    have hmem : projectiveModel z ∈ segment ℝ (projectiveModel w) (projectiveModel u) := by
      refine ⟨1 / (1 - s), -s / (1 - s), by apply div_nonneg <;> linarith,
        by apply div_nonneg <;> linarith, by field_simp; ring, ?_⟩
      rw [hp]
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] <;> field_simp <;> ring
    have h' := dist_add_dist_eq_of_mem_segment hmem
    rw [dist_comm w z] at h'
    have hzw : dist z w = 0 := by
      have := dist_nonneg (x := z) (y := w)
      linarith
    rw [← dist_eq_zero.mp hzw, sub_self] at hs1 hs2
    have h1 : (projectiveModel u).1 - (projectiveModel z).1 = 0 :=
      (mul_eq_zero.mp hs1.symm).resolve_left hs.ne
    have h2 : (projectiveModel u).2 - (projectiveModel z).2 = 0 :=
      (mul_eq_zero.mp hs2.symm).resolve_left hs.ne
    exact hzu (Prod.ext (by linarith) (by linarith))
  rcases le_or_gt s 1 with hs' | hs'
  · exact ⟨1 - s, s, by linarith, hs, by ring, hp.symm⟩
  · -- `p_u` lies between `p_z` and `p_w`, so `d(z, u) + d(u, w) = d(z, w)` and `w = u`.
    exfalso
    have hne : s ≠ 0 := by linarith
    have hmem : projectiveModel u ∈ segment ℝ (projectiveModel z) (projectiveModel w) := by
      refine ⟨1 - 1 / s, 1 / s, ?_, by positivity, by ring, ?_⟩
      · rw [sub_nonneg, div_le_one (by linarith)]; exact hs'.le
      rw [hp]
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] <;> field_simp <;> ring
    have h' := dist_add_dist_eq_of_mem_segment hmem
    rw [dist_comm u w] at h'
    have hwu : dist w u = 0 := by
      have := dist_nonneg (x := w) (y := u)
      linarith
    rw [dist_eq_zero.mp hwu] at hs1 hs2
    have h1 : (1 - s) * ((projectiveModel u).1 - (projectiveModel z).1) = 0 := by linarith
    have h2 : (1 - s) * ((projectiveModel u).2 - (projectiveModel z).2) = 0 := by linarith
    have hs1' : 1 - s ≠ 0 := by linarith
    have h1' := (mul_eq_zero.mp h1).resolve_left hs1'
    have h2' := (mul_eq_zero.mp h2).resolve_left hs1'
    exact hzu (Prod.ext (by linarith) (by linarith))

/-- **Geodesic segments of the half-plane are the straight segments of the projective model.**
`w` lies on the geodesic segment from `z` to `u`, that is `d(z, w) + d(w, u) = d(z, u)`, exactly
when its image lies on the straight segment between the images of `z` and `u`. -/
theorem dist_add_dist_eq_iff {z w u : ℍ} :
    dist z w + dist w u = dist z u ↔
      projectiveModel w ∈ segment ℝ (projectiveModel z) (projectiveModel u) :=
  ⟨mem_segment_of_dist_add_dist_eq, dist_add_dist_eq_of_mem_segment⟩

end UpperHalfPlane
