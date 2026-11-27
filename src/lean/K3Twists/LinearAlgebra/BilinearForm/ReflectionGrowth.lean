/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Matrix.SLTwoRate
import K3Twists.Combinatorics.Quiver.Kronecker.CartanMatrix
import K3Twists.LinearAlgebra.BilinearForm.Eichler

/-!
# Exponential growth of two reflections at pairing `|g| ≥ 3`

Let `B` be a symmetric bilinear form, `a`, `b` spherical classes (`B(a, a) = B(b, b) = -2`) of
pairing `g = B(a, b)`, and `T = ρ_b ρ_a` the product of their reflections. The product satisfies
the cubic `(T - 1)(T² - (g² - 2)T + 1) = 0` (`BilinearForm.reflectHom_mul_reflectHom_cubic`), but
an annihilating polynomial does not show that the quadratic factor acts nontrivially. This file
shows that it does and computes the rate:

* `T` preserves the plane of `a` and `b` and acts on it, in the basis `(a, b)`, by the matrix
  `[[-1, g], [-g, g² - 1]] = s₁ s₀` of the two simple reflections of the rank-two wall
  (`BilinearForm.reflectHom_mul_reflectHom_smul_add_smul`, and its powers
  `reflectHom_mul_reflectHom_pow_smul_add_smul`). It has determinant one and trace `g² - 2`
  (`Quiver.Kronecker.trace_reflection_mul_reflection`).
* On the plane the quadratic factor vanishes, `T² a = (g² - 2) T a - a`
  (`reflectHom_mul_reflectHom_sq_apply_left`), so the pairings `c_n = B(a, Tⁿ a)` satisfy
  `c_{n+2} = (g² - 2) c_{n+1} - c_n` with `c₀ = -2`, `c₁ = 2 - g²`.
* For `|g| > 2`, with `λ = sl2Rate (g² - 2) > 1` the larger root of `x² - (g² - 2) x + 1`:
  `|B(a, Tⁿ a)| = λⁿ + λ⁻ⁿ` (`abs_map_apply_reflectHom_mul_reflectHom_pow`), so
  `|B(a, Tⁿ a)|^{1/n} → λ` (`tendsto_abs_map_apply_reflectHom_mul_reflectHom_pow`); the matrix of
  `T` on the plane has Gelfand radius `λ` (`gelfandRadius_reflectionProductMatrix`, the `SL₂` rate
  lemma); and on a finite-dimensional real space `‖Tⁿ a‖^{1/n} → λ`
  (`tendsto_norm_reflectHom_mul_reflectHom_pow`).
* On the whole space, `T` fixes every vector orthogonal to `a` and `b`
  (`reflectHom_mul_reflectHom_apply_of_apply_eq_zero`), and for `g² ≠ 4` every vector is a
  combination of `a` and `b` plus such a vector, since the Gram matrix of `a` and `b` has
  determinant `4 - g²`. So `‖Tⁿ x‖ ≤ K (‖(s₁ s₀)ⁿ‖ + 1) ‖x‖`
  (`exists_norm_pow_reflectHom_mul_reflectHom_apply_le`), and for `|g| > 2` the map `T` itself has
  Gelfand radius `λ`: as a continuous linear map on a real normed space with a bounded form
  (`gelfandRadius_reflectHom_mul_reflectHom_of_bound`), on every finite-dimensional real space
  (`gelfandRadius_toContinuousLinearMap_reflectHom_mul_reflectHom`), and as the matrix of `T` in a
  basis of a free module, read in `ℝ` through a ring homomorphism
  (`gelfandRadius_map_toMatrix_reflectHom_mul_reflectHom`), whose complexification has spectral
  radius `λ` (`spectralRadius_map_toMatrix_reflectHom_mul_reflectHom`).

The pairing statements hold over any commutative ring with a ring homomorphism to `ℝ`; for the
Mukai lattice of a K3 surface, with the cast `ℤ → ℝ` and spherical objects `S_a`, `S_b` with
`|χ(S_a, S_b)| ≥ 3`, they say `|χ(S_a, (T_{S_b} T_{S_a})ⁿ S_a)| = λⁿ + λ⁻ⁿ`, and the matrix
statement says that `T_{S_b} T_{S_a}` has spectral radius `λ` on the Mukai lattice tensored
with `ℝ`. The two examples of
the library, the rate of `Ψ = T_{𝒪_X} T_L` on a K3 surface of Picard rank one
(`AlgebraicGeometry.K3.PicardRankOne.psi_eigenvalue`) and the Barbacovi–Kim number `7 + 4√3`
(`AlgebraicGeometry.K3.EllipticWithSection.barbacoviKim_four_root`), are the Gelfand radii of
`s₁ s₀` at pairings `-(d + 2)` and `4`.
-/

open Filter Topology

namespace BilinearForm

open Module Matrix
open scoped Matrix.Norms.Operator

/-! ### The matrix of `ρ_b ρ_a` on the plane of `a` and `b` -/

/-- The matrix `s₁ s₀ = [[1, 0], [g, -1]] [[-1, g], [0, 1]]` of `ρ_b ρ_a` on the plane of two
spherical classes of pairing `g`, in the basis `(a, b)`: the product of the two simple reflections
of the rank-two wall. -/
def reflectionProductMatrix {R : Type*} [CommRing R] (g : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; g, -1] * !![-1, g; 0, 1]

section Matrix

variable {R : Type*} [CommRing R]

lemma reflectionProductMatrix_eq (g : R) :
    reflectionProductMatrix g = !![-1, g; -g, g ^ 2 - 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflectionProductMatrix]
  ring

lemma det_reflectionProductMatrix (g : R) : (reflectionProductMatrix g).det = 1 := by
  rw [reflectionProductMatrix_eq, det_fin_two_of]
  ring

/-- The trace `g² - 2` of `s₁ s₀`, from the wall-matrix lemma
`Quiver.Kronecker.trace_reflection_mul_reflection` for `s₀ s₁`. -/
lemma trace_reflectionProductMatrix (g : R) : (reflectionProductMatrix g).trace = g ^ 2 - 2 := by
  rw [reflectionProductMatrix, trace_mul_comm]
  exact Quiver.Kronecker.trace_reflection_mul_reflection g

end Matrix

/-! ### The action on the plane -/

section Plane

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {B : M →ₗ[R] M →ₗ[R] R} (hB : ∀ x y, B x y = B y x) {a b : M} (ha : B a a = -2)
  (hb : B b b = -2)
include hB ha hb

/-- **`ρ_b ρ_a` on the plane of `a` and `b`**: in the basis `(a, b)` it acts by
`s₁ s₀ = [[-1, g], [-g, g² - 1]]`, `g = B(a, b)`. -/
theorem reflectHom_mul_reflectHom_smul_add_smul (x y : R) :
    (reflectHom B b * reflectHom B a) (x • a + y • b) =
      (reflectionProductMatrix (B a b) *ᵥ ![x, y]) 0 • a +
        (reflectionProductMatrix (B a b) *ᵥ ![x, y]) 1 • b := by
  have hba : B b a = B a b := hB b a
  rw [reflectionProductMatrix_eq]
  simp only [mul_apply_eq_comp, reflectHom_apply, reflect_apply, map_add, map_smul, ha, hb, hba,
    mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one]
  module

/-- **The powers of `ρ_b ρ_a` on the plane** are the powers of `s₁ s₀`. -/
theorem reflectHom_mul_reflectHom_pow_smul_add_smul (n : ℕ) (x y : R) :
    ((reflectHom B b * reflectHom B a) ^ n) (x • a + y • b) =
      ((reflectionProductMatrix (B a b) ^ n) *ᵥ ![x, y]) 0 • a +
        ((reflectionProductMatrix (B a b) ^ n) *ᵥ ![x, y]) 1 • b := by
  induction n with
  | zero =>
    simp [one_apply_eq_self]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, reflectHom_mul_reflectHom_smul_add_smul hB ha hb,
      pow_succ', ← mulVec_mulVec]
    congr 3 <;> ext i <;> fin_cases i <;> rfl

omit hB hb in
/-- `ρ_b ρ_a a = -a - g b`. -/
theorem reflectHom_mul_reflectHom_apply_left :
    (reflectHom B b * reflectHom B a) a = -a - B a b • b := by
  simp only [mul_apply_eq_comp, reflectHom_apply, reflect_apply, map_add, map_smul, ha]
  module

/-- **The quadratic factor of the cubic vanishes on the plane**: `T² a = (g² - 2) T a - a` for
`T = ρ_b ρ_a`. -/
theorem reflectHom_mul_reflectHom_sq_apply_left :
    (reflectHom B b * reflectHom B a) ((reflectHom B b * reflectHom B a) a) =
      (B a b ^ 2 - 2) • (reflectHom B b * reflectHom B a) a - a := by
  have hba : B b a = B a b := hB b a
  simp only [mul_apply_eq_comp, reflectHom_apply, reflect_apply, map_add, map_smul, ha, hb, hba]
  module

/-- The orbit of `a` satisfies the Chebyshev recursion `T^{n+2} a = (g² - 2) T^{n+1} a - Tⁿ a`. -/
theorem reflectHom_mul_reflectHom_pow_add_two_apply_left (n : ℕ) :
    ((reflectHom B b * reflectHom B a) ^ (n + 2)) a =
      (B a b ^ 2 - 2) • ((reflectHom B b * reflectHom B a) ^ (n + 1)) a -
        ((reflectHom B b * reflectHom B a) ^ n) a := by
  let T := reflectHom B b * reflectHom B a
  have h : T (T a) = (B a b ^ 2 - 2) • T a - a := reflectHom_mul_reflectHom_sq_apply_left hB ha hb
  calc (T ^ (n + 2)) a = (T ^ n * T * T) a := by rw [pow_succ, pow_succ]
    _ = (T ^ n) (T (T a)) := rfl
    _ = (B a b ^ 2 - 2) • (T ^ n * T) a - (T ^ n) a := by
        rw [h, map_sub, map_smul]
        rfl
    _ = (B a b ^ 2 - 2) • (T ^ (n + 1)) a - (T ^ n) a := by rw [← pow_succ]

/-- **The pairing recursion.** `c_n = B(a, Tⁿ a)` satisfies `c_{n+2} = (g² - 2) c_{n+1} - c_n`. -/
theorem apply_reflectHom_mul_reflectHom_pow_add_two (n : ℕ) :
    B a (((reflectHom B b * reflectHom B a) ^ (n + 2)) a) =
      (B a b ^ 2 - 2) * B a (((reflectHom B b * reflectHom B a) ^ (n + 1)) a) -
        B a (((reflectHom B b * reflectHom B a) ^ n) a) := by
  rw [reflectHom_mul_reflectHom_pow_add_two_apply_left hB ha hb, map_sub, map_smul, smul_eq_mul]

omit hB hb in
theorem apply_reflectHom_mul_reflectHom_apply_left :
    B a ((reflectHom B b * reflectHom B a) a) = -(B a b ^ 2 - 2) := by
  rw [reflectHom_mul_reflectHom_apply_left ha, map_sub, map_neg, map_smul, ha, smul_eq_mul]
  ring

end Plane

/-! ### The rate at `|g| > 2` -/

lemma _root_.Real.four_lt_sq_of_two_lt_abs {g : ℝ} (hg : 2 < |g|) : 4 < g ^ 2 := by
  have := sq_abs g
  nlinarith [abs_nonneg g]

/-- A sequence with `c₀ = 2`, `c₁ = l + l⁻¹` and `c_{n+2} = (l + l⁻¹) c_{n+1} - c_n` is
`c_n = lⁿ + l⁻ⁿ`. -/
lemma _root_.Real.eq_pow_add_inv_pow_of_rec {c : ℕ → ℝ} {l : ℝ} (hl : l ≠ 0) (h0 : c 0 = 2)
    (h1 : c 1 = l + l⁻¹) (hrec : ∀ n, c (n + 2) = (l + l⁻¹) * c (n + 1) - c n) (n : ℕ) :
    c n = l ^ n + l⁻¹ ^ n := by
  have hll : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  suffices ∀ n, c n = l ^ n + l⁻¹ ^ n ∧ c (n + 1) = l ^ (n + 1) + l⁻¹ ^ (n + 1) from (this n).1
  intro n
  induction n with
  | zero => exact ⟨by rw [h0]; norm_num, by rw [h1]; ring⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [hrec, ih.1, ih.2]
    linear_combination (l ^ n + l⁻¹ ^ n) * hll

section Rate

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {B : M →ₗ[R] M →ₗ[R] R} (hB : ∀ x y, B x y = B y x) {a b : M} (ha : B a a = -2)
  (hb : B b b = -2)
include hB ha hb

/-- **The pairings along the orbit, exactly.** For a ring homomorphism `φ : R → ℝ` with
`|φ(g)| > 2`, `g = B(a, b)`, and `λ = sl2Rate (φ(g)² - 2)`,
`φ(B(a, Tⁿ a)) = -(λⁿ + λ⁻ⁿ)` for `T = ρ_b ρ_a`. -/
theorem map_apply_reflectHom_mul_reflectHom_pow (φ : R →+* ℝ) (hg : 2 < |φ (B a b)|) (n : ℕ) :
    φ (B a (((reflectHom B b * reflectHom B a) ^ n) a)) =
      -(Matrix.sl2Rate (φ (B a b) ^ 2 - 2) ^ n + (Matrix.sl2Rate (φ (B a b) ^ 2 - 2))⁻¹ ^ n) := by
  set t := φ (B a b) ^ 2 - 2 with ht
  have ht2 : 2 ≤ t := by
    have := Real.four_lt_sq_of_two_lt_abs hg
    linarith
  set l := Matrix.sl2Rate t
  have hl : l + l⁻¹ = t := Matrix.sl2Rate_add_inv ht2
  have hl0 : l ≠ 0 := (Matrix.sl2Rate_pos ht2).ne'
  have key := Real.eq_pow_add_inv_pow_of_rec
    (c := fun n => -φ (B a (((reflectHom B b * reflectHom B a) ^ n) a))) hl0
    (by simp [ha, map_ofNat φ 2]) (by
      rw [pow_one, apply_reflectHom_mul_reflectHom_apply_left ha, hl, ht]
      simp [map_ofNat φ 2])
    (fun n => by
      rw [apply_reflectHom_mul_reflectHom_pow_add_two hB ha hb, hl, ht]
      simp only [map_sub, map_mul, map_pow, map_ofNat φ 2]
      ring) n
  linarith

/-- `|B(a, Tⁿ a)| = λⁿ + λ⁻ⁿ`, read through `φ`. -/
theorem abs_map_apply_reflectHom_mul_reflectHom_pow (φ : R →+* ℝ) (hg : 2 < |φ (B a b)|)
    (n : ℕ) :
    |φ (B a (((reflectHom B b * reflectHom B a) ^ n) a))| =
      Matrix.sl2Rate (φ (B a b) ^ 2 - 2) ^ n + (Matrix.sl2Rate (φ (B a b) ^ 2 - 2))⁻¹ ^ n := by
  rw [map_apply_reflectHom_mul_reflectHom_pow hB ha hb φ hg n, abs_neg, abs_of_nonneg]
  have : 0 < Matrix.sl2Rate (φ (B a b) ^ 2 - 2) := Matrix.sl2Rate_pos (by
    have := Real.four_lt_sq_of_two_lt_abs hg
    linarith)
  positivity

/-- **Exponential growth of two reflections at `|g| > 2`.** For spherical `a`, `b` of pairing
`g` with `|φ(g)| > 2`, `|φ(B(a, Tⁿ a))|^{1/n} → λ = sl2Rate (φ(g)² - 2)`, the larger root of
`x² - (φ(g)² - 2) x + 1`, and `λ > 1`. -/
theorem tendsto_abs_map_apply_reflectHom_mul_reflectHom_pow (φ : R →+* ℝ)
    (hg : 2 < |φ (B a b)|) :
    Tendsto (fun n : ℕ => |φ (B a (((reflectHom B b * reflectHom B a) ^ n) a))| ^ (n : ℝ)⁻¹)
      atTop (𝓝 (Matrix.sl2Rate (φ (B a b) ^ 2 - 2))) := by
  set t := φ (B a b) ^ 2 - 2
  have ht2 : 2 ≤ t := by
    have := Real.four_lt_sq_of_two_lt_abs hg
    show 2 ≤ φ (B a b) ^ 2 - 2
    linarith
  set l := Matrix.sl2Rate t
  have hl1 : 1 ≤ l := Matrix.one_le_sl2Rate ht2
  have hl0 : 0 < l := one_pos.trans_le hl1
  have hinv : 0 ≤ l⁻¹ ^ 1 := by positivity
  refine Real.tendsto_rpow_inv_of_bounds (H := fun n => l ^ n) (c := 1) (C := 2) one_pos
    two_pos (fun n => by positivity) (Eventually.of_forall fun n => ?_)
    (Eventually.of_forall fun n => ?_) ?_
  · rw [abs_map_apply_reflectHom_mul_reflectHom_pow hB ha hb φ hg n, one_mul]
    have : 0 ≤ l⁻¹ ^ n := by positivity
    linarith
  · rw [abs_map_apply_reflectHom_mul_reflectHom_pow hB ha hb φ hg n]
    have : l⁻¹ ^ n ≤ l ^ n :=
      pow_le_pow_left₀ (by positivity) ((inv_le_one_of_one_le₀ hl1).trans hl1) n
    linarith
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (Real.pow_rpow_inv_natCast hl0.le hn).symm

end Rate

/-- **The rate on the plane.** For `|g| > 2` the matrix `s₁ s₀` of `ρ_b ρ_a` on the plane of `a`
and `b` has Gelfand radius `sl2Rate (g² - 2)`, by the `SL₂` rate lemma. -/
theorem gelfandRadius_reflectionProductMatrix {g : ℝ} (hg : 2 < |g|) :
    gelfandRadius (reflectionProductMatrix g) = Matrix.sl2Rate (g ^ 2 - 2) := by
  have h4 : 4 < g ^ 2 := Real.four_lt_sq_of_two_lt_abs hg
  rw [gelfandRadius_eq_sl2Rate _ (det_reflectionProductMatrix g)
    (by rw [trace_reflectionProductMatrix]; linarith), trace_reflectionProductMatrix]

theorem one_lt_gelfandRadius_reflectionProductMatrix {g : ℝ} (hg : 2 < |g|) :
    1 < gelfandRadius (reflectionProductMatrix g) := by
  have h4 : 4 < g ^ 2 := Real.four_lt_sq_of_two_lt_abs hg
  rw [gelfandRadius_reflectionProductMatrix hg]
  exact Matrix.one_lt_sl2Rate (by linarith)

/-- The Gelfand radius `ρ` of `s₁ s₀` is a root of the quadratic factor
`x² - (g² - 2) x + 1` of the cubic of two reflections. -/
theorem gelfandRadius_reflectionProductMatrix_root {g : ℝ} (hg : 2 < |g|) :
    gelfandRadius (reflectionProductMatrix g) ^ 2 -
      (g ^ 2 - 2) * gelfandRadius (reflectionProductMatrix g) + 1 = 0 := by
  have h4 : 4 < g ^ 2 := Real.four_lt_sq_of_two_lt_abs hg
  have := gelfandRadius_sq_sub_trace_mul_add_one _ (det_reflectionProductMatrix g)
    (by rw [trace_reflectionProductMatrix]; linarith)
  rwa [trace_reflectionProductMatrix] at this

/-! ### Norms on a real space -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} (hB : ∀ x y, B x y = B y x) {a b : E} (ha : B a a = -2)
  (hb : B b b = -2)
include hB ha hb

/-- **`‖Tⁿ a‖^{1/n} → λ`** for a bounded symmetric form on a real normed space: if
`|B(x, y)| ≤ C ‖x‖ ‖y‖` and `a`, `b` are spherical with `|B(a, b)| > 2`, then
`‖(ρ_b ρ_a)ⁿ a‖^{1/n} → sl2Rate (B(a, b)² - 2)`. The lower bound is the pairing with `a`,
`|B(a, Tⁿ a)| = λⁿ + λ⁻ⁿ`; the upper bound is the matrix of `T` on the plane. -/
theorem tendsto_norm_reflectHom_mul_reflectHom_pow_of_bound {C : ℝ}
    (hC : ∀ x y, |B x y| ≤ C * ‖x‖ * ‖y‖) (hg : 2 < |B a b|) :
    Tendsto (fun n : ℕ => ‖((reflectHom B b * reflectHom B a) ^ n) a‖ ^ (n : ℝ)⁻¹) atTop
      (𝓝 (Matrix.sl2Rate (B a b ^ 2 - 2))) := by
  set T := reflectHom B b * reflectHom B a with hT
  set l := Matrix.sl2Rate (B a b ^ 2 - 2) with hl
  set P := reflectionProductMatrix (B a b) with hP
  have ht2 : 2 ≤ B a b ^ 2 - 2 := by
    have := Real.four_lt_sq_of_two_lt_abs hg
    linarith
  have hl1 : 1 ≤ l := Matrix.one_le_sl2Rate ht2
  have hl0 : 0 < l := one_pos.trans_le hl1
  -- `C ‖a‖ > 0`, from `2 = |B(a, a)| ≤ C ‖a‖²`
  have hCa : 0 < C * ‖a‖ := by
    have h2 := hC a a
    rw [ha, abs_neg, abs_two] at h2
    by_contra hle
    have := mul_le_mul_of_nonneg_right (not_lt.1 hle) (norm_nonneg a)
    linarith
  -- the lower bound `lⁿ ≤ C ‖a‖ ‖Tⁿ a‖`
  have hlow : ∀ n : ℕ, l ^ n / (C * ‖a‖) ≤ ‖(T ^ n) a‖ := by
    intro n
    have h1 := abs_map_apply_reflectHom_mul_reflectHom_pow hB ha hb (RingHom.id ℝ) hg n
    simp only [RingHom.id_apply] at h1
    have h2 := hC a ((T ^ n) a)
    rw [h1] at h2
    rw [div_le_iff₀ hCa]
    have : 0 ≤ l⁻¹ ^ n := by positivity
    nlinarith
  -- the upper bound `‖Tⁿ a‖ ≤ (‖a‖ + ‖b‖) ‖Pⁿ‖`
  have hup : ∀ n : ℕ, ‖(T ^ n) a‖ ≤ (‖a‖ + ‖b‖) * ‖P ^ n‖ := by
    intro n
    have e : (T ^ n) a = ((P ^ n) *ᵥ ![1, 0]) 0 • a + ((P ^ n) *ᵥ ![1, 0]) 1 • b := by
      rw [← reflectHom_mul_reflectHom_pow_smul_add_smul hB ha hb n 1 0, one_smul, zero_smul,
        add_zero]
    have hv : ‖(P ^ n) *ᵥ ![1, 0]‖ ≤ ‖P ^ n‖ := by
      refine (linfty_opNorm_mulVec _ _).trans ?_
      have : ‖(![1, 0] : Fin 2 → ℝ)‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
        fin_cases i <;> simp
      nlinarith [norm_nonneg (P ^ n)]
    have h0' : |((P ^ n) *ᵥ ![1, 0]) 0| ≤ ‖(P ^ n) *ᵥ ![1, 0]‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm ((P ^ n) *ᵥ ![1, 0]) 0
    have h1' : |((P ^ n) *ᵥ ![1, 0]) 1| ≤ ‖(P ^ n) *ᵥ ![1, 0]‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm ((P ^ n) *ᵥ ![1, 0]) 1
    have h0 := h0'.trans hv
    have h1 := h1'.trans hv
    rw [e]
    calc ‖((P ^ n) *ᵥ ![1, 0]) 0 • a + ((P ^ n) *ᵥ ![1, 0]) 1 • b‖
        ≤ |((P ^ n) *ᵥ ![1, 0]) 0| * ‖a‖ + |((P ^ n) *ᵥ ![1, 0]) 1| * ‖b‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖P ^ n‖ * ‖a‖ + ‖P ^ n‖ * ‖b‖ := by gcongr
      _ = (‖a‖ + ‖b‖) * ‖P ^ n‖ := by ring
  have hgr : gelfandRadius P = l := gelfandRadius_reflectionProductMatrix hg
  -- squeeze
  have hK : 0 < ‖a‖ + ‖b‖ := by
    have ha0 : a ≠ 0 := fun h => by
      rw [h] at ha
      simp at ha
    linarith [norm_pos_iff.2 ha0, norm_nonneg b]
  have hlo_lim : Tendsto (fun n : ℕ => (l ^ n / (C * ‖a‖)) ^ (n : ℝ)⁻¹) atTop (𝓝 l) := by
    have h := (Real.tendsto_const_rpow_inv (inv_pos.2 hCa)).mul_const l
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [div_eq_mul_inv, mul_comm, Real.mul_rpow (by positivity) (by positivity),
      Real.pow_rpow_inv_natCast hl0.le hn]
  have hhi_lim : Tendsto (fun n : ℕ => ((‖a‖ + ‖b‖) * ‖P ^ n‖) ^ (n : ℝ)⁻¹) atTop (𝓝 l) := by
    have h := (Real.tendsto_const_rpow_inv hK).mul (tendsto_gelfandRadius P)
    rw [one_mul, hgr] at h
    refine h.congr fun n => ?_
    rw [Real.mul_rpow hK.le (norm_nonneg _)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo_lim hhi_lim (fun n => ?_) (fun n => ?_)
  · exact Real.rpow_le_rpow (by positivity) (hlow n) (by positivity)
  · exact Real.rpow_le_rpow (norm_nonneg _) (hup n) (by positivity)

/-- **`‖Tⁿ a‖^{1/n} → λ` on a finite-dimensional real space**, for every norm: a bilinear form
there is bounded. -/
theorem tendsto_norm_reflectHom_mul_reflectHom_pow [FiniteDimensional ℝ E]
    (hg : 2 < |B a b|) :
    Tendsto (fun n : ℕ => ‖((reflectHom B b * reflectHom B a) ^ n) a‖ ^ (n : ℝ)⁻¹) atTop
      (𝓝 (Matrix.sl2Rate (B a b ^ 2 - 2))) := by
  let B' : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ).toLinearMap ∘ₗ B)
  refine tendsto_norm_reflectHom_mul_reflectHom_pow_of_bound hB ha hb (C := ‖B'‖)
    (fun x y => ?_) hg
  have := B'.le_opNorm₂ x y
  simpa [B', Real.norm_eq_abs] using this

end Normed

/-! ### The rate on the whole space -/

section Orthogonal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : M →ₗ[R] M →ₗ[R] R}
  {a b : M}

/-- `ρ_b ρ_a` fixes every vector orthogonal to `a` and `b`. -/
theorem reflectHom_mul_reflectHom_apply_of_apply_eq_zero {q : M} (hqa : B q a = 0)
    (hqb : B q b = 0) : (reflectHom B b * reflectHom B a) q = q := by
  simp only [mul_apply_eq_comp, reflectHom_apply, reflect_apply, hqa, zero_smul, add_zero, hqb]

/-- The powers of `ρ_b ρ_a` fix every vector orthogonal to `a` and `b`. -/
theorem reflectHom_mul_reflectHom_pow_apply_of_apply_eq_zero {q : M} (hqa : B q a = 0)
    (hqb : B q b = 0) (n : ℕ) : ((reflectHom B b * reflectHom B a) ^ n) q = q := by
  rw [pow_apply_eq_iterate]
  exact Function.iterate_fixed (reflectHom_mul_reflectHom_apply_of_apply_eq_zero hqa hqb) n

end Orthogonal

section WholeSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} (hB : ∀ x y, B x y = B y x) {a b : E} (ha : B a a = -2)
  (hb : B b b = -2)
include hB ha hb

/-- **The powers of `ρ_b ρ_a` on the whole space** are those of `s₁ s₀` up to a bounded error.
For a bounded symmetric form and `g = B(a, b)` with `g² ≠ 4`, every `x` is `α a + β b + q` with
`q` orthogonal to `a` and `b`, since the Gram matrix `[[-2, g], [g, -2]]` of `a` and `b` has
determinant `4 - g² ≠ 0`. The powers of `T = ρ_b ρ_a` act on `α a + β b` by those of `s₁ s₀` and
fix `q`, so `‖Tⁿ x‖ ≤ K (‖(s₁ s₀)ⁿ‖ + 1) ‖x‖`. -/
theorem exists_norm_pow_reflectHom_mul_reflectHom_apply_le {C : ℝ}
    (hC : ∀ x y, |B x y| ≤ C * ‖x‖ * ‖y‖) (hg : B a b ^ 2 ≠ 4) :
    ∃ K, ∀ (n : ℕ) (x : E), ‖((reflectHom B b * reflectHom B a) ^ n) x‖ ≤
      K * (‖reflectionProductMatrix (B a b) ^ n‖ + 1) * ‖x‖ := by
  set g := B a b with hg_def
  set P := reflectionProductMatrix g with hP
  have hba : B b a = g := hB b a
  have hD : (4 - g ^ 2) ≠ 0 := fun h => hg (by linarith)
  have hD' : 0 < |4 - g ^ 2| := abs_pos.2 hD
  -- `C ≥ 0`, from `2 = |B(a, a)| ≤ C ‖a‖²`
  have hC0 : 0 ≤ C := by
    have h2 := hC a a
    rw [ha, abs_neg, abs_two] at h2
    by_contra hneg
    have : C * ‖a‖ * ‖a‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (not_le.1 hneg).le
        (norm_nonneg a)) (norm_nonneg a)
    linarith
  -- the coordinates of `x` along `a` and `b`
  let α : E → ℝ := fun x => (-2 * B x a - g * B x b) / (4 - g ^ 2)
  let β : E → ℝ := fun x => (-g * B x a - 2 * B x b) / (4 - g ^ 2)
  have hqa : ∀ x, B (x - α x • a - β x • b) a = 0 := by
    intro x
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, ha,
      hba, α, β]
    field_simp
    ring
  have hqb : ∀ x, B (x - α x • a - β x • b) b = 0 := by
    intro x
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hb,
      ← hg_def, α, β]
    field_simp
    ring
  -- `Tⁿ x = Tⁿ (α a + β b) + q`
  have hdec : ∀ (n : ℕ) (x : E), ((reflectHom B b * reflectHom B a) ^ n) x =
      ((P ^ n) *ᵥ ![α x, β x]) 0 • a + ((P ^ n) *ᵥ ![α x, β x]) 1 • b +
        (x - α x • a - β x • b) := by
    intro n x
    have hx : x = (α x • a + β x • b) + (x - α x • a - β x • b) := by abel
    conv_lhs => rw [hx]
    rw [map_add, reflectHom_mul_reflectHom_pow_smul_add_smul hB ha hb,
      reflectHom_mul_reflectHom_pow_apply_of_apply_eq_zero (hqa x) (hqb x)]
  -- bounds on the coordinates
  set Kc := (2 * C * ‖a‖ + |g| * C * ‖b‖ + (|g| * C * ‖a‖ + 2 * C * ‖b‖)) / |4 - g ^ 2|
    with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  have hcoord : ∀ x, |α x| ≤ Kc * ‖x‖ ∧ |β x| ≤ Kc * ‖x‖ := by
    intro x
    have h1 : |B x a| ≤ C * ‖x‖ * ‖a‖ := hC x a
    have h2 : |B x b| ≤ C * ‖x‖ * ‖b‖ := hC x b
    have e1 : |-2 * B x a - g * B x b| ≤ (2 * C * ‖a‖ + |g| * C * ‖b‖) * ‖x‖ := by
      calc |-2 * B x a - g * B x b| ≤ |-2 * B x a| + |g * B x b| := abs_sub _ _
        _ = 2 * |B x a| + |g| * |B x b| := by rw [abs_mul, abs_mul, abs_neg, abs_two]
        _ ≤ 2 * (C * ‖x‖ * ‖a‖) + |g| * (C * ‖x‖ * ‖b‖) := by gcongr
        _ = (2 * C * ‖a‖ + |g| * C * ‖b‖) * ‖x‖ := by ring
    have e2 : |-g * B x a - 2 * B x b| ≤ (|g| * C * ‖a‖ + 2 * C * ‖b‖) * ‖x‖ := by
      calc |-g * B x a - 2 * B x b| ≤ |-g * B x a| + |2 * B x b| := abs_sub _ _
        _ = |g| * |B x a| + 2 * |B x b| := by rw [abs_mul, abs_mul, abs_neg, abs_two]
        _ ≤ |g| * (C * ‖x‖ * ‖a‖) + 2 * (C * ‖x‖ * ‖b‖) := by gcongr
        _ = (|g| * C * ‖a‖ + 2 * C * ‖b‖) * ‖x‖ := by ring
    have hx0 := norm_nonneg x
    have hA2 : 0 ≤ (|g| * C * ‖a‖ + 2 * C * ‖b‖) * ‖x‖ := by positivity
    have hA1 : 0 ≤ (2 * C * ‖a‖ + |g| * C * ‖b‖) * ‖x‖ := by positivity
    have hKx : Kc * ‖x‖ = ((2 * C * ‖a‖ + |g| * C * ‖b‖) * ‖x‖ +
        (|g| * C * ‖a‖ + 2 * C * ‖b‖) * ‖x‖) / |4 - g ^ 2| := by
      rw [hKc]
      ring
    constructor
    · simp only [α]
      rw [abs_div, hKx]
      gcongr
      linarith
    · simp only [β]
      rw [abs_div, hKx]
      gcongr
      linarith
  refine ⟨Kc * (‖a‖ + ‖b‖) + 1, fun n x => ?_⟩
  obtain ⟨hα, hβ⟩ := hcoord x
  have hv : ‖(![α x, β x] : Fin 2 → ℝ)‖ ≤ Kc * ‖x‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    fin_cases i
    · simpa [Real.norm_eq_abs] using hα
    · simpa [Real.norm_eq_abs] using hβ
  have hPv : ‖(P ^ n) *ᵥ ![α x, β x]‖ ≤ ‖P ^ n‖ * (Kc * ‖x‖) :=
    (linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
  have h0 : |((P ^ n) *ᵥ ![α x, β x]) 0| ≤ ‖P ^ n‖ * (Kc * ‖x‖) :=
    (by simpa [Real.norm_eq_abs] using norm_le_pi_norm ((P ^ n) *ᵥ ![α x, β x]) 0 :
      |((P ^ n) *ᵥ ![α x, β x]) 0| ≤ ‖(P ^ n) *ᵥ ![α x, β x]‖).trans hPv
  have h1 : |((P ^ n) *ᵥ ![α x, β x]) 1| ≤ ‖P ^ n‖ * (Kc * ‖x‖) :=
    (by simpa [Real.norm_eq_abs] using norm_le_pi_norm ((P ^ n) *ᵥ ![α x, β x]) 1 :
      |((P ^ n) *ᵥ ![α x, β x]) 1| ≤ ‖(P ^ n) *ᵥ ![α x, β x]‖).trans hPv
  have hq : ‖x - α x • a - β x • b‖ ≤ (1 + Kc * (‖a‖ + ‖b‖)) * ‖x‖ := by
    calc ‖x - α x • a - β x • b‖ ≤ ‖x‖ + |α x| * ‖a‖ + |β x| * ‖b‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          refine (norm_sub_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖x‖ + Kc * ‖x‖ * ‖a‖ + Kc * ‖x‖ * ‖b‖ := by gcongr
      _ = (1 + Kc * (‖a‖ + ‖b‖)) * ‖x‖ := by ring
  rw [hdec]
  have hPn := norm_nonneg (P ^ n)
  calc ‖((P ^ n) *ᵥ ![α x, β x]) 0 • a + ((P ^ n) *ᵥ ![α x, β x]) 1 • b +
          (x - α x • a - β x • b)‖
      ≤ |((P ^ n) *ᵥ ![α x, β x]) 0| * ‖a‖ + |((P ^ n) *ᵥ ![α x, β x]) 1| * ‖b‖ +
          ‖x - α x • a - β x • b‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖P ^ n‖ * (Kc * ‖x‖) * ‖a‖ + ‖P ^ n‖ * (Kc * ‖x‖) * ‖b‖ +
          (1 + Kc * (‖a‖ + ‖b‖)) * ‖x‖ := by gcongr
    _ ≤ (Kc * (‖a‖ + ‖b‖) + 1) * (‖P ^ n‖ + 1) * ‖x‖ := by
        have : 0 ≤ Kc * ‖x‖ * (‖a‖ + ‖b‖) := by positivity
        nlinarith [norm_nonneg x, norm_nonneg a, norm_nonneg b]

/-- **The Gelfand radius of `ρ_b ρ_a` on the whole space.** For a bounded symmetric form on a real
normed space and spherical `a`, `b` with `|B(a, b)| > 2`, a continuous linear map acting as
`T = ρ_b ρ_a` has Gelfand radius `λ = sl2Rate (B(a, b)² - 2)`, the rate of `s₁ s₀`. The upper
bound is `exists_norm_pow_reflectHom_mul_reflectHom_apply_le`, the lower bound the orbit of `a`
(`tendsto_norm_reflectHom_mul_reflectHom_pow_of_bound`). -/
theorem gelfandRadius_reflectHom_mul_reflectHom_of_bound {C : ℝ}
    (hC : ∀ x y, |B x y| ≤ C * ‖x‖ * ‖y‖) (hg : 2 < |B a b|) {T : E →L[ℝ] E}
    (hT : (T : E →ₗ[ℝ] E) = reflectHom B b * reflectHom B a) :
    gelfandRadius T = Matrix.sl2Rate (B a b ^ 2 - 2) := by
  set P := reflectionProductMatrix (B a b) with hP
  have h4 : 4 < B a b ^ 2 := Real.four_lt_sq_of_two_lt_abs hg
  have hpow : ∀ (n : ℕ) (x : E), (T ^ n) x = ((reflectHom B b * reflectHom B a) ^ n) x := by
    intro n x
    rw [← ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap_pow, hT]
  have hgr : gelfandRadius P = Matrix.sl2Rate (B a b ^ 2 - 2) :=
    gelfandRadius_reflectionProductMatrix hg
  -- `‖Pⁿ‖ ≥ 1`, since `P` has Gelfand radius at least one
  have hP1 : ∀ n : ℕ, 1 ≤ ‖P ^ n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have h1 : 1 ≤ gelfandRadius P := (one_lt_gelfandRadius_reflectionProductMatrix hg).le
      exact (one_le_pow₀ h1).trans (gelfandRadius_pow_le_norm_pow P hn)
  obtain ⟨K, hK⟩ := exists_norm_pow_reflectHom_mul_reflectHom_apply_le hB ha hb hC h4.ne'
  refine le_antisymm ?_ ?_
  · -- the upper bound
    rw [← hgr]
    refine gelfandRadius_le_of_norm_pow_le (2 * max K 0) fun n => ?_
    refine (T ^ n).opNorm_le_bound (by positivity [hP1 n]) fun x => ?_
    rw [hpow]
    have hPn := hP1 n
    calc ‖((reflectHom B b * reflectHom B a) ^ n) x‖ ≤ K * (‖P ^ n‖ + 1) * ‖x‖ := hK n x
      _ ≤ max K 0 * (‖P ^ n‖ + 1) * ‖x‖ := by gcongr; exact le_max_left K 0
      _ ≤ 2 * max K 0 * ‖P ^ n‖ * ‖x‖ := by
        have : 0 ≤ max K 0 * ‖x‖ := by positivity
        nlinarith
  · -- the lower bound, from the orbit of `a`
    have ha0 : 0 < ‖a‖ := norm_pos_iff.2 fun h => by rw [h] at ha; simp at ha
    have hlim := tendsto_norm_reflectHom_mul_reflectHom_pow_of_bound hB ha hb hC hg
    have hup : Tendsto (fun n : ℕ => (‖T ^ n‖ * ‖a‖) ^ (n : ℝ)⁻¹) atTop
        (𝓝 (gelfandRadius T)) := by
      have h := (tendsto_gelfandRadius T).mul (Real.tendsto_const_rpow_inv ha0)
      rw [mul_one] at h
      refine h.congr fun n => ?_
      rw [Real.mul_rpow (norm_nonneg _) ha0.le]
    refine le_of_tendsto_of_tendsto' hlim hup fun n => ?_
    refine Real.rpow_le_rpow (norm_nonneg _) ?_ (by positivity)
    rw [← hpow]
    exact (T ^ n).le_opNorm a

/-- **The Gelfand radius of `ρ_b ρ_a` on a finite-dimensional real space**, for every norm: for
spherical `a`, `b` with `|B(a, b)| > 2` it is `λ = sl2Rate (B(a, b)² - 2)`. -/
theorem gelfandRadius_toContinuousLinearMap_reflectHom_mul_reflectHom [FiniteDimensional ℝ E]
    (hg : 2 < |B a b|) :
    gelfandRadius (LinearMap.toContinuousLinearMap (reflectHom B b * reflectHom B a)) =
      Matrix.sl2Rate (B a b ^ 2 - 2) := by
  let B' : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ).toLinearMap ∘ₗ B)
  refine gelfandRadius_reflectHom_mul_reflectHom_of_bound hB ha hb (C := ‖B'‖)
    (fun x y => ?_) hg (LinearMap.coe_toContinuousLinearMap _)
  have := B'.le_opNorm₂ x y
  simpa [B', Real.norm_eq_abs] using this

end WholeSpace

section Basis

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
variable {B : M →ₗ[R] M →ₗ[R] R} (hB : ∀ x y, B x y = B y x) {a b : M} (ha : B a a = -2)
  (hb : B b b = -2)
include hB ha hb

/-- **The Gelfand radius of `ρ_b ρ_a` in a basis.** Let `M` be a free module with a finite basis
over a commutative ring with a homomorphism `φ` to `ℝ`, and `a`, `b` spherical with
`|φ(B(a, b))| > 2`. The matrix of `T = ρ_b ρ_a` in the basis, read in `ℝ` through `φ`, has
Gelfand radius `λ = sl2Rate (φ(B(a, b))² - 2)`. For the Mukai lattice `Λ` of a K3 surface and the
cast `ℤ → ℝ` this is the Gelfand radius of `T` on `Λ ⊗ ℝ`. The proof reads `B` in the coordinates
of the basis, where `T` becomes the product of the two reflections of the real form with Gram
matrix `φ(B(e_i, e_j))`, and applies
`gelfandRadius_toContinuousLinearMap_reflectHom_mul_reflectHom`. -/
theorem gelfandRadius_map_toMatrix_reflectHom_mul_reflectHom (φ : R →+* ℝ)
    (e : Module.Basis ι R M) (hg : 2 < |φ (B a b)|) :
    gelfandRadius ((LinearMap.toMatrix e e (reflectHom B b * reflectHom B a)).map φ) =
      Matrix.sl2Rate (φ (B a b) ^ 2 - 2) := by
  -- the real coordinates of a vector, and the real form with Gram matrix `φ(B(e_i, e_j))`
  let r : M → ι → ℝ := fun x i => φ (e.repr x i)
  let B' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] ℝ :=
    Matrix.toLinearMap₂' ℝ (Matrix.of fun i j => φ (B (e i) (e j)))
  have hB'apply : ∀ x y, B' x y = ∑ i, ∑ j, x i * (y j * φ (B (e i) (e j))) := by
    intro x y
    simp only [B', Matrix.toLinearMap₂'_apply, Matrix.of_apply, smul_eq_mul]
  have hB'r : ∀ x y, B' (r x) (r y) = φ (B x y) := by
    intro x y
    have hxy : B x y = ∑ i, ∑ j, e.repr x i • e.repr y j • B (e i) (e j) := by
      conv_lhs => rw [← Matrix.toLinearMap₂_toMatrix₂ e e B]
      rw [Matrix.toLinearMap₂_apply]
      simp only [LinearMap.toMatrix₂_apply]
    rw [hxy, hB'apply]
    simp only [map_sum, smul_eq_mul, map_mul, r]
  have hB'symm : ∀ x y, B' x y = B' y x := by
    intro x y
    rw [hB'apply, hB'apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hB (e j) (e i)]
    ring
  have hr_add : ∀ x y, r (x + y) = r x + r y := fun x y => by
    funext i
    simp [r]
  have hr_smul : ∀ (c : R) x, r (c • x) = φ c • r x := fun c x => by
    funext i
    simp [r]
  have hrefl : ∀ s x, r (reflectHom B s x) = reflectHom B' (r s) (r x) := by
    intro s x
    rw [reflectHom_apply, reflectHom_apply, reflect_apply, reflect_apply, hr_add, hr_smul, hB'r]
  set T' := reflectHom B' (r b) * reflectHom B' (r a) with hT'
  have hT : ∀ x, r ((reflectHom B b * reflectHom B a) x) = T' (r x) := by
    intro x
    simp only [T', mul_apply_eq_comp, hrefl]
  have hej : ∀ j, r (e j) = Pi.single j 1 := by
    intro j
    funext k
    rcases eq_or_ne k j with rfl | hkj
    · simp [r]
    · simp [r, hkj]
  have hmat : (LinearMap.toMatrix e e (reflectHom B b * reflectHom B a)).map φ =
      LinearMap.toMatrix' T' := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix'_apply, ← hej, ← hT]
  have ha' : B' (r a) (r a) = -2 := by rw [hB'r, ha, map_neg, map_ofNat]
  have hb' : B' (r b) (r b) = -2 := by rw [hB'r, hb, map_neg, map_ofNat]
  have hab' : B' (r a) (r b) = φ (B a b) := hB'r a b
  have key := gelfandRadius_toContinuousLinearMap_reflectHom_mul_reflectHom hB'symm ha' hb'
    (by rwa [hab'])
  rw [hab'] at key
  rw [hmat, ← key]
  refine gelfandRadius_eq_of_norm_pow_eq fun n => ?_
  have h1 : LinearMap.toMatrix' T' ^ n = LinearMap.toMatrixAlgEquiv' (T' ^ n) := by
    rw [map_pow]
    rfl
  have h2 : T' ^ n = ((LinearMap.toContinuousLinearMap T' ^ n : (ι → ℝ) →L[ℝ] ι → ℝ) :
      (ι → ℝ) →ₗ[ℝ] ι → ℝ) := by
    rw [ContinuousLinearMap.toLinearMap_pow, LinearMap.coe_toContinuousLinearMap]
  rw [h1, h2]
  exact Matrix.linfty_opNorm_toMatrix _

/-- **The spectral radius of `ρ_b ρ_a`**: under the hypotheses of
`gelfandRadius_map_toMatrix_reflectHom_mul_reflectHom`, the complexified matrix of `T` has
spectral radius `λ = sl2Rate (φ(B(a, b))² - 2)`. -/
theorem spectralRadius_map_toMatrix_reflectHom_mul_reflectHom (φ : R →+* ℝ)
    (e : Module.Basis ι R M) (hg : 2 < |φ (B a b)|) :
    spectralRadius ℂ (((LinearMap.toMatrix e e (reflectHom B b * reflectHom B a)).map φ).map
      Complex.ofReal) = ENNReal.ofReal (Matrix.sl2Rate (φ (B a b) ^ 2 - 2)) := by
  rw [Matrix.spectralRadius_map_ofReal,
    gelfandRadius_map_toMatrix_reflectHom_mul_reflectHom hB ha hb φ e hg]

end Basis

end BilinearForm
