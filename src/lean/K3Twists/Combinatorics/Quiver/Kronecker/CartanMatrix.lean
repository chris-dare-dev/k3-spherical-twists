/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Combinatorics.Quiver.Kronecker.RealRoots
import K3Twists.LinearAlgebra.Matrix.ZMatrix.Isotropic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The symmetric Cartan matrix of the Kronecker quiver

At a wall with two spherical stable objects `S₀`, `S₁` of one phase and `g = dim Ext¹(S₀, S₁)`,
the wall matrix `Aᵢⱼ = χ(Sᵢ, Sⱼ)` is `[[2, -g], [-g, 2]]`, the symmetric Cartan matrix
`Quiver.Kronecker.cartanMatrix g` of the `g`-Kronecker quiver. Its form is twice the Tits form
`kroneckerForm` (`dotProduct_mulVec_cartanMatrix_eq_kroneckerForm`).

* `cartanMatrix_posDef_iff`: over an ordered field, positive definite iff `|g| < 2`;
* `cartanMatrix_isotropic_iff`: over a field with `2 ≠ 0`, a nonzero isotropic vector exists iff
  `g² - 4` is a square;
* `rank_two_trichotomy`: for `g ∈ ℕ`, decided by certificates and null vectors: of finite type
  iff `g ≤ 1` (certificate `(1, 1)`), of affine type iff `g = 2` (null vector `(1, 1)`, isotropic
  integer vectors `ℤ(1, 1)`, `cartanMatrix_two_isotropic_eq_zsmul`), indefinite iff `g ≥ 3`, and
  then `ℚ`-anisotropic (`cartanMatrix_anisotropic`, from `no_null_vector`);
* `noIsotropicSphereSum_cartanMatrix_iff`: two spheres have an isotropic sum only at `g = 2`, and
  `noIsotropicSphereSum_cartanMatrix_iff_anisotropic`: for two spheres this `ℕ`-cone notion agrees
  with `ℚ`-anisotropy of their span;
* `trace_reflection_mul_reflection`: the product of the two simple reflections has trace
  `g² - 2`.
-/

namespace Quiver.Kronecker

open Matrix

/-- The symmetric Cartan matrix `[[2, -g], [-g, 2]]` of the `g`-Kronecker quiver: the wall matrix
of two spherical objects with `g = dim Ext¹` between them. -/
def cartanMatrix {R : Type*} [Ring R] (g : R) : Matrix (Fin 2) (Fin 2) R :=
  !![2, -g; -g, 2]

section CommRing

variable {R : Type*} [CommRing R]

lemma cartanMatrix_isSymm (g : R) : (cartanMatrix g).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cartanMatrix]

lemma dotProduct_mulVec_cartanMatrix (g : R) (x : Fin 2 → R) :
    x ⬝ᵥ cartanMatrix g *ᵥ x = 2 * (x 0 ^ 2 - g * x 0 * x 1 + x 1 ^ 2) := by
  simp [cartanMatrix, dotProduct, mulVec, Fin.sum_univ_two]
  ring

/-- The form of the Cartan matrix is twice the Tits form of the Kronecker quiver. -/
lemma dotProduct_mulVec_cartanMatrix_eq_kroneckerForm (g a b : ℤ) :
    ![a, b] ⬝ᵥ cartanMatrix g *ᵥ ![a, b] = 2 * kroneckerForm g a b := by
  rw [dotProduct_mulVec_cartanMatrix, kroneckerForm]
  simp only [cons_val_zero, cons_val_one]
  ring

lemma cartanMatrix_mulVec_one (g : R) : cartanMatrix g *ᵥ (fun _ => 1) = fun _ => 2 - g := by
  ext i
  fin_cases i <;> simp [cartanMatrix, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

lemma isIndecomposable_cartanMatrix {g : R} (hg : g ≠ 0) : (cartanMatrix g).IsIndecomposable := by
  rw [isIndecomposable_iff_reflTransGen]
  intro i j
  fin_cases i <;> fin_cases j
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (by simpa [cartanMatrix] using hg)
  · exact Relation.ReflTransGen.single (by simpa [cartanMatrix] using hg)
  · exact Relation.ReflTransGen.refl

/-- **The reflection product.** In the basis of simple roots the two simple reflections of the
rank-two wall are `s₀ = [[-1, g], [0, 1]]` and `s₁ = [[1, 0], [g, -1]]`; `s₀s₁` has trace
`g² - 2` (and determinant one). -/
theorem trace_reflection_mul_reflection (g : R) :
    (!![-1, g; 0, 1] * !![1, 0; g, -1] : Matrix (Fin 2) (Fin 2) R).trace = g ^ 2 - 2 := by
  simp [Matrix.trace_fin_two]
  ring

end CommRing

lemma isZMatrix_cartanMatrix {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] {g : R}
    (hg : 0 ≤ g) : (cartanMatrix g).IsZMatrix := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [cartanMatrix]

/-! ### Over fields -/

/-- Over a field with `2 ≠ 0`, the rank-two wall has a nonzero isotropic vector iff `g² - 4` is a
square. -/
theorem cartanMatrix_isotropic_iff {K : Type*} [Field K] [NeZero (2 : K)] (g : K) :
    (∃ x : Fin 2 → K, x ≠ 0 ∧ x ⬝ᵥ cartanMatrix g *ᵥ x = 0) ↔ IsSquare (g ^ 2 - 4) := by
  constructor
  · rintro ⟨x, hx, hq⟩
    rw [dotProduct_mulVec_cartanMatrix] at hq
    have hq' : x 0 ^ 2 - g * x 0 * x 1 + x 1 ^ 2 = 0 :=
      (mul_eq_zero.mp hq).resolve_left (NeZero.ne 2)
    have hx1 : x 1 ≠ 0 := by
      intro h1
      rw [h1] at hq'
      have : x 0 = 0 := by simpa using hq'
      exact hx (funext fun i => by fin_cases i <;> simp [this, h1])
    refine ⟨(2 * x 0 - g * x 1) / x 1, ?_⟩
    field_simp
    linear_combination (-4 : K) * hq'
  · rintro ⟨s, hs⟩
    refine ⟨![g + s, 2], fun h => NeZero.ne (2 : K) (by simpa using congr_fun h 1), ?_⟩
    rw [dotProduct_mulVec_cartanMatrix]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (-2 : K) * hs

/-- Over an ordered field the rank-two wall is positive definite iff `|g| < 2`. -/
theorem cartanMatrix_posDef_iff {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [StarRing 𝕜] [TrivialStar 𝕜] (g : 𝕜) : (cartanMatrix g).PosDef ↔ |g| < 2 := by
  rw [(cartanMatrix_isSymm g).posDef_iff_dotProduct_mulVec_pos]
  constructor
  · intro h
    have h1 := h ![1, 1] fun h0 => by simpa using congr_fun h0 0
    have h2 := h ![1, -1] fun h0 => by simpa using congr_fun h0 0
    rw [dotProduct_mulVec_cartanMatrix] at h1 h2
    simp at h1 h2
    rw [abs_lt]
    constructor <;> nlinarith
  · intro hg x hx
    rw [dotProduct_mulVec_cartanMatrix]
    rw [abs_lt] at hg
    by_cases hb : x 1 = 0
    · have ha : x 0 ≠ 0 := fun ha => hx (funext fun i => by fin_cases i <;> simp [ha, hb])
      have := sq_pos_of_ne_zero ha
      rw [hb]
      nlinarith
    · have h4 : 0 < 4 - g ^ 2 := by nlinarith
      have h5 : 0 < (4 - g ^ 2) * x 1 ^ 2 := mul_pos h4 (sq_pos_of_ne_zero hb)
      nlinarith [sq_nonneg (2 * x 0 - g * x 1)]

/-- **Anisotropy for `|g| ≥ 3`.** The rank-two wall has no nonzero rational isotropic vector. -/
theorem cartanMatrix_anisotropic {g : ℤ} (hg : 3 ≤ |g|) {x : Fin 2 → ℚ}
    (hx : x ⬝ᵥ cartanMatrix (g : ℚ) *ᵥ x = 0) : x = 0 := by
  rw [dotProduct_mulVec_cartanMatrix] at hx
  have h' : x 0 ^ 2 + ((-g : ℤ) : ℚ) * x 0 * x 1 + x 1 ^ 2 = 0 := by
    push_cast
    linear_combination hx / 2
  obtain ⟨h0, h1⟩ := no_null_vector (g := -g) (by rwa [abs_neg]) h'
  funext i
  fin_cases i <;> simp [h0, h1]

/-! ### The trichotomy for `g ∈ ℕ` -/

/-- **Finite type.** For `g ∈ ℕ` the rank-two wall is positive definite iff `g ≤ 1`; the
certificate is `(1, 1)`. -/
theorem posDef_cartanMatrix_iff (g : ℕ) : (cartanMatrix (g : ℤ)).PosDef ↔ g ≤ 1 := by
  rw [(isZMatrix_cartanMatrix (Nat.cast_nonneg g)).posDef_iff_int_certificate
    (cartanMatrix_isSymm _)]
  constructor
  · rintro ⟨p, hp, hAp⟩
    have h0 := hAp 0
    have h1 := hAp 1
    simp [cartanMatrix, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    by_contra hg
    push Not at hg
    have hg2 : (2 : ℤ) ≤ g := by exact_mod_cast hg
    nlinarith [mul_nonneg (sub_nonneg.mpr hg2) (add_pos (hp 0) (hp 1)).le]
  · intro hg
    have hg1 : (g : ℤ) ≤ 1 := by exact_mod_cast hg
    refine ⟨fun _ => 1, fun _ => one_pos, fun i => ?_⟩
    rw [cartanMatrix_mulVec_one]
    simp only
    omega

/-- The null vector `(1, 1)` of the wall of pairing two. -/
lemma cartanMatrix_two_mulVec_one : cartanMatrix (2 : ℤ) *ᵥ (fun _ => 1) = 0 := by
  rw [cartanMatrix_mulVec_one]
  ext
  simp

/-- **The affine kernel at `g = 2`.** The isotropic integer vectors of `[[2, -2], [-2, 2]]` are
the multiples of `(1, 1)`. -/
theorem cartanMatrix_two_isotropic_eq_zsmul {x : Fin 2 → ℤ}
    (hx : x ⬝ᵥ cartanMatrix (2 : ℤ) *ᵥ x = 0) : x = x 0 • fun _ => 1 :=
  (isZMatrix_cartanMatrix (by norm_num)).isotropic_int_eq_zsmul_of_eq_one
    (cartanMatrix_isSymm _) (isIndecomposable_cartanMatrix (by norm_num))
    (fun _ => one_pos) cartanMatrix_two_mulVec_one rfl hx

/-- **Affine type.** For `g ∈ ℕ` the rank-two wall is positive semidefinite and not positive
definite iff `g = 2`. -/
theorem posSemidef_and_not_posDef_cartanMatrix_iff (g : ℕ) :
    (cartanMatrix (g : ℤ)).PosSemidef ∧ ¬(cartanMatrix (g : ℤ)).PosDef ↔ g = 2 := by
  constructor
  · rintro ⟨hpsd, hnpd⟩
    have h1 := (cartanMatrix_isSymm _).posSemidef_iff_dotProduct_mulVec_nonneg.mp hpsd
      (fun _ => 1)
    rw [dotProduct_mulVec_cartanMatrix] at h1
    have hle : (g : ℤ) ≤ 2 := by simp at h1; linarith
    have hge : ¬g ≤ 1 := fun h => hnpd ((posDef_cartanMatrix_iff g).mpr h)
    omega
  · rintro rfl
    exact (isZMatrix_cartanMatrix (by norm_num)).posSemidef_and_not_posDef_of_int_null
      (cartanMatrix_isSymm _) (fun _ => one_pos) cartanMatrix_two_mulVec_one

/-- **Indefinite type.** For `g ∈ ℕ` the rank-two wall is not positive semidefinite iff `g ≥ 3`;
then `(1, 1)` has negative square. -/
theorem not_posSemidef_cartanMatrix_iff (g : ℕ) :
    ¬(cartanMatrix (g : ℤ)).PosSemidef ↔ 3 ≤ g := by
  constructor
  · intro h
    by_contra hg
    push Not at hg
    rcases Nat.lt_or_ge g 2 with hg2 | hg2
    · exact h ((posDef_cartanMatrix_iff g).mpr (by omega)).posSemidef
    · exact h ((posSemidef_and_not_posDef_cartanMatrix_iff g).mpr (by omega)).1
  · intro hg hpsd
    have h1 := (cartanMatrix_isSymm _).posSemidef_iff_dotProduct_mulVec_nonneg.mp hpsd
      (fun _ => 1)
    rw [dotProduct_mulVec_cartanMatrix] at h1
    have : (3 : ℤ) ≤ g := by exact_mod_cast hg
    simp at h1
    linarith

/-- **The rank-two trichotomy.** For `g ∈ ℕ` the wall matrix `[[2, -g], [-g, 2]]` is of finite
type iff `g ≤ 1`, of affine type iff `g = 2`, and indefinite iff `g ≥ 3`. -/
theorem rank_two_trichotomy (g : ℕ) :
    ((cartanMatrix (g : ℤ)).PosDef ↔ g ≤ 1) ∧
      ((cartanMatrix (g : ℤ)).PosSemidef ∧ ¬(cartanMatrix (g : ℤ)).PosDef ↔ g = 2) ∧
      (¬(cartanMatrix (g : ℤ)).PosSemidef ↔ 3 ≤ g) :=
  ⟨posDef_cartanMatrix_iff g, posSemidef_and_not_posDef_cartanMatrix_iff g,
    not_posSemidef_cartanMatrix_iff g⟩

/-! ### Isotropic sums of two spheres -/

/-- Two spheres of pairing `|g| ≥ 3` have no isotropic sum. -/
theorem noIsotropicSphereSum_cartanMatrix {g : ℤ} (hg : 3 ≤ |g|) :
    (cartanMatrix g).NoIsotropicSphereSum := by
  intro a _ ha _ hiso
  apply ha
  have h := cartanMatrix_anisotropic hg (x := fun i => (a i : ℚ)) (by
    have : ((a ⬝ᵥ cartanMatrix g *ᵥ a : ℤ) : ℚ) = 0 := by rw [hiso]; simp
    rw [intCast_dotProduct_mulVec] at this
    convert this using 3
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cartanMatrix])
  funext i
  simpa using congr_fun h i

/-- At `g = 2` the sum `S₀ + S₁` is isotropic. -/
theorem not_noIsotropicSphereSum_cartanMatrix_two : ¬(cartanMatrix (2 : ℤ)).NoIsotropicSphereSum :=
  not_noIsotropicSphereSum (fun _ => 1) (fun _ => zero_le_one)
    (fun h => by simpa using congr_fun h 0)
    (fun i => by fin_cases i <;> simp [cartanMatrix]) (by decide)

/-- For `g ∈ ℕ`, two spheres of pairing `g` have an isotropic sum iff `g = 2`. -/
theorem noIsotropicSphereSum_cartanMatrix_iff (g : ℕ) :
    (cartanMatrix (g : ℤ)).NoIsotropicSphereSum ↔ g ≠ 2 := by
  refine ⟨fun h hg => not_noIsotropicSphereSum_cartanMatrix_two (by simpa [hg] using h),
    fun hg => ?_⟩
  rcases Nat.lt_or_ge g 2 with hg2 | hg2
  · exact noIsotropicSphereSum_of_posDef (cartanMatrix_isSymm _)
      ((posDef_cartanMatrix_iff g).mpr (by omega))
  · exact noIsotropicSphereSum_cartanMatrix (by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast (show 3 ≤ g by omega))

/-- **For two spheres the two notions of anisotropy agree.** For `g ∈ ℕ`, no nonzero `ℕ`-sum of
two spheres of pairing `g` is isotropic iff their rational span has no nonzero isotropic vector;
both hold exactly when `g ≠ 2`. -/
theorem noIsotropicSphereSum_cartanMatrix_iff_anisotropic (g : ℕ) :
    (cartanMatrix (g : ℤ)).NoIsotropicSphereSum ↔
      ∀ x : Fin 2 → ℚ, x ⬝ᵥ cartanMatrix (g : ℚ) *ᵥ x = 0 → x = 0 := by
  rw [noIsotropicSphereSum_cartanMatrix_iff]
  constructor
  · intro hg x hx
    rcases Nat.lt_or_ge g 2 with hg2 | hg2
    · have hPD := (cartanMatrix_posDef_iff (g : ℚ)).mpr (by
        rw [abs_of_nonneg (by positivity)]
        exact_mod_cast hg2)
      by_contra hx0
      exact (((cartanMatrix_isSymm _).posDef_iff_dotProduct_mulVec_pos.mp hPD) x hx0).ne' hx
    · exact cartanMatrix_anisotropic (g := g) (by
        rw [abs_of_nonneg (by positivity)]
        exact_mod_cast (show 3 ≤ g by omega)) (by exact_mod_cast hx)
  · rintro h rfl
    have := h (fun _ => 1) (by rw [dotProduct_mulVec_cartanMatrix]; norm_num)
    simpa using congr_fun this 0

end Quiver.Kronecker
