/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Mass
import K3Twists.CategoryTheory.MassProfile.ClassInfimum
import K3Twists.LinearAlgebra.Lattice.Mukai.Basic

/-!
# The cusp point is not a mass profile

On the Mukai lattice `MukaiLattice ℤ N = ℤ × N × ℤ` of a lattice `(N, b)`, the line bundles
`𝒪(jH)` of a class `H` with `H² = 2q` have the classes `(1, jH, j² q + 1)`. For an additive charge
`Z`, `Z(1, jH, j² q + 1) = Z(1, 0, 1) + j Z(0, H, 0) + j² q Z(0, 0, 1)` is a quadratic polynomial in
`j`. If it is bounded and `q ≠ 0`, the charge kills the class of a point `(0, 0, 1)` and the class
`(0, H, 0)` (`Mukai.charge_eq_zero_of_bounded`). The class of a point is isotropic, and the kernel
of the charge of a stability condition on a K3 surface contains no nonzero isotropic class: it is
negative definite over `ℝ` (`Mukai.negDef_ker_realCharge`, for a positive period). So:

* `AlgebraicGeometry.K3.not_bddAbove_mass_lineBundle`: at every prestability condition whose
  charge kills no nonzero isotropic class, the masses of objects of the classes
  `(1, jH, j² q + 1)` are unbounded;
* `AlgebraicGeometry.K3.not_exists_mass_eq_mul_rank`: the rank functional `R`, which is `1` on line
  bundles, is not a multiple of the mass on them. The cusp point `[R]`, the limit of the masses at
  large volume, is not the projective class of a mass profile, not even on spherical objects, in
  every Picard rank.

The class infimum of `R` over spherical objects is the absolute rank. `R` is the fibre-functor
profile of the derived fibre at a point, with class `w = (0, 0, 1)` and `⟨w, (r, c, s)⟩ = -r`, so
`d_R(γ) ≥ |rk γ|` with the parity of `rk γ`, with equality on every class that has a spherical
representative on which `R` is `|rk γ|`, such as a shifted spherical sheaf
(`FibreFunctorProfile.classInf_eq_abs_rank`). The square `d_R² = (rk γ)²` is the square of one
linear form, that of an isotropic vector.
-/

open Filter Topology

/-! ### Bounded quadratic polynomials -/

/-- A complex quadratic polynomial bounded on the natural numbers is constant:
`‖a + j b + j² c‖ ≤ M` for all `j` gives `b = 0` and `c = 0`. -/
theorem Complex.eq_zero_of_norm_quadratic_le {a b c : ℂ} {M : ℝ}
    (h : ∀ j : ℕ, ‖a + j * b + (j : ℂ) ^ 2 * c‖ ≤ M) : b = 0 ∧ c = 0 := by
  have hc : c = 0 := by
    by_contra hc
    have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
    obtain ⟨j, hj⟩ := exists_nat_gt ((‖a‖ + ‖b‖ + |M| + 1) / ‖c‖ + 1)
    have hq : 0 ≤ (‖a‖ + ‖b‖ + |M| + 1) / ‖c‖ := by positivity
    have hj1 : (1 : ℝ) ≤ j := by linarith
    have hjc : ‖a‖ + ‖b‖ + |M| + 1 < j * ‖c‖ := by
      have := (div_lt_iff₀ hc').1 (by linarith : (‖a‖ + ‖b‖ + |M| + 1) / ‖c‖ < j)
      linarith
    have key : ‖(j : ℂ) ^ 2 * c‖ ≤ ‖a + j * b + (j : ℂ) ^ 2 * c‖ + ‖a‖ + ‖(j : ℂ) * b‖ :=
      calc ‖(j : ℂ) ^ 2 * c‖ = ‖(a + j * b + (j : ℂ) ^ 2 * c) - a - j * b‖ := by
            congr 1; ring
        _ ≤ ‖(a + j * b + (j : ℂ) ^ 2 * c) - a‖ + ‖(j : ℂ) * b‖ := norm_sub_le _ _
        _ ≤ ‖a + j * b + (j : ℂ) ^ 2 * c‖ + ‖a‖ + ‖(j : ℂ) * b‖ := by
            gcongr
            exact norm_sub_le _ _
    rw [norm_mul, norm_pow, Complex.norm_natCast, norm_mul, Complex.norm_natCast] at key
    have hprod := mul_lt_mul_of_pos_left hjc (by linarith : (0 : ℝ) < j)
    nlinarith [h j, le_abs_self M, norm_nonneg a, norm_nonneg b, abs_nonneg M]
  subst hc
  refine ⟨?_, rfl⟩
  by_contra hb
  have hb' : 0 < ‖b‖ := norm_pos_iff.2 hb
  obtain ⟨j, hj⟩ := exists_nat_gt ((‖a‖ + |M| + 1) / ‖b‖)
  have hjb : ‖a‖ + |M| + 1 < j * ‖b‖ := (div_lt_iff₀ hb').1 hj
  have key : ‖(j : ℂ) * b‖ ≤ ‖a + j * b + (j : ℂ) ^ 2 * 0‖ + ‖a‖ :=
    calc ‖(j : ℂ) * b‖ = ‖(a + j * b + (j : ℂ) ^ 2 * 0) - a‖ := by congr 1; ring
      _ ≤ ‖a + j * b + (j : ℂ) ^ 2 * 0‖ + ‖a‖ := norm_sub_le _ _
  rw [norm_mul, Complex.norm_natCast] at key
  linarith [h j, le_abs_self M]

namespace Mukai

variable {N : Type*} [AddCommGroup N]

/-- The class of `𝒪(jH)` is `(1, 0, 1) + j (0, H, 0) + j² q (0, 0, 1)`. -/
lemma lineClass_eq (H : N) (q j : ℤ) :
    ((1 : ℤ), j • H, j ^ 2 * q + 1) =
      ((1 : ℤ), (0 : N), (1 : ℤ)) + j • ((0 : ℤ), H, (0 : ℤ)) +
        (j ^ 2 * q) • ((0 : ℤ), (0 : N), (1 : ℤ)) := by
  ext <;> simp [add_comm]

/-- **A charge bounded on the line bundles of `H` kills the point.** For an additive charge
`Z` on `MukaiLattice ℤ N`, a class `H` with `q ≠ 0` and a bound on `|Z(1, jH, j² q + 1)|` over all
natural `j`, `Z` kills the class of a point `(0, 0, 1)` and the class `(0, H, 0)`. -/
theorem charge_eq_zero_of_bounded (Z : MukaiLattice ℤ N →+ ℂ) (H : N) {q : ℤ} (hq : q ≠ 0)
    {M : ℝ} (hM : ∀ j : ℕ, ‖Z ((1 : ℤ), (j : ℤ) • H, (j : ℤ) ^ 2 * q + 1)‖ ≤ M) :
    Z ((0 : ℤ), (0 : N), (1 : ℤ)) = 0 ∧ Z ((0 : ℤ), H, (0 : ℤ)) = 0 := by
  have h : ∀ j : ℕ, ‖Z ((1 : ℤ), (0 : N), (1 : ℤ)) + j * Z ((0 : ℤ), H, (0 : ℤ)) +
      (j : ℂ) ^ 2 * ((q : ℂ) * Z ((0 : ℤ), (0 : N), (1 : ℤ)))‖ ≤ M := fun j ↦ by
    have := hM j
    rw [lineClass_eq, map_add, map_add, map_zsmul, map_zsmul] at this
    convert this using 2
    simp only [zsmul_eq_mul]
    push_cast
    ring
  obtain ⟨hb, hc⟩ := Complex.eq_zero_of_norm_quadratic_le h
  exact ⟨(mul_eq_zero.1 hc).resolve_left (by exact_mod_cast hq), hb⟩

/-- The class of a point `(0, 0, 1)` is isotropic. -/
lemma pairing_point_self {R : Type*} [CommRing R] [Module R N] (b : N →ₗ[R] N →ₗ[R] R) :
    pairing b ((0 : R), (0 : N), (1 : R)) ((0 : R), (0 : N), (1 : R)) = 0 := by
  simp [pairing]

end Mukai

/-! ### The cusp point and the mass -/

namespace AlgebraicGeometry.K3

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u v u'

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {N : Type u'} [AddCommGroup N] {v : K₀ C →+ MukaiLattice ℤ N}

/-- **The masses of line bundles are unbounded.** Let `σ` be a prestability condition with classes
in the Mukai lattice of `(N, b)` whose charge kills no nonzero isotropic class (as for every
stability condition on a K3 surface: the kernel of a positive period is negative definite), and let
`L j` be objects of the classes `(1, jH, j² q + 1)` of the line bundles `𝒪(jH)`, `q = H²/2 ≠ 0`.
Then `j ↦ m_σ(L j)` is unbounded. -/
theorem not_bddAbove_mass_lineBundle (σ : PreStabilityCondition.WithClassMap C v)
    (b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ)
    (hker : ∀ x, σ.Z x = 0 → Mukai.pairing b x x = 0 → x = 0) (H : N) {q : ℤ} (hq : q ≠ 0)
    (L : ℕ → C) (hL : ∀ j : ℕ, classOf C v (L j) = ((1 : ℤ), (j : ℤ) • H, (j : ℤ) ^ 2 * q + 1)) :
    ¬ BddAbove (Set.range fun j ↦ σ.mass (L j)) := by
  rintro ⟨M, hM⟩
  have hbound : ∀ j : ℕ, ‖σ.Z ((1 : ℤ), (j : ℤ) • H, (j : ℤ) ^ 2 * q + 1)‖ ≤ M := fun j ↦ by
    rw [← hL j]
    exact (σ.norm_charge_le_mass (L j)).trans (hM ⟨j, rfl⟩)
  have h0 := (Mukai.charge_eq_zero_of_bounded σ.Z H hq hbound).1
  have h1 := congrArg (fun x : MukaiLattice ℤ N ↦ x.2.2) (hker _ h0 (Mukai.pairing_point_self b))
  simp at h1

/-- **The cusp point is not a mass profile.** Under the hypotheses of
`not_bddAbove_mass_lineBundle`, if a functional `R` takes the value `1` on the objects `L j` (as the
rank functional does on line bundles), then `m_σ` is not a multiple of `R` on them: `[R]` is not
the projective class of the mass of any stability condition. -/
theorem not_exists_mass_eq_mul_rank (σ : PreStabilityCondition.WithClassMap C v)
    (b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ)
    (hker : ∀ x, σ.Z x = 0 → Mukai.pairing b x x = 0 → x = 0) (H : N) {q : ℤ} (hq : q ≠ 0)
    (L : ℕ → C) (hL : ∀ j : ℕ, classOf C v (L j) = ((1 : ℤ), (j : ℤ) • H, (j : ℤ) ^ 2 * q + 1))
    (R : C → ℝ) (hR : ∀ j, R (L j) = 1) : ¬ ∃ c : ℝ, ∀ j, σ.mass (L j) = c * R (L j) := by
  rintro ⟨c, hc⟩
  refine not_bddAbove_mass_lineBundle σ b hker H hq L hL ⟨c, ?_⟩
  rintro _ ⟨j, rfl⟩
  simp [hc j, hR j]

end AlgebraicGeometry.K3

/-! ### The class infimum of the rank functional -/

namespace FibreFunctorProfile

open Profile

variable {Obj Λ : Type*} [AddCommGroup Λ] {B : LinearMap.BilinForm ℤ Λ}
  (F : FibreFunctorProfile Obj Λ B)

/-- **Equality in the fibre-functor bound.** If the fibre of `γ` has an object `S` with
`μ_F(S) = |⟨w_F, γ⟩|`, the class infimum of `μ_F` is `|⟨w_F, γ⟩|`. -/
theorem classInf_eq_abs (𝒮 : Set Obj) {γ : Λ} {S : Obj} (hS : S ∈ classFibre 𝒮 F.cls γ)
    (hSeq : (F.mass S : ℤ) = |B F.w γ|) :
    (classInf 𝒮 F.cls F.toProfile γ : ℝ) = ((|B F.w γ| : ℤ) : ℝ) := by
  have h2 := F.abs_le_classInf 𝒮 (γ := γ) ⟨S, hS⟩
  have h1 : (classInf 𝒮 F.cls F.toProfile γ : ℝ) ≤ ((|B F.w γ| : ℤ) : ℝ) := by
    have h := NNReal.coe_le_coe.2 (classInf_le_of_mem (μ := F.toProfile) hS)
    refine h.trans_eq ?_
    rw [toProfile_apply, NNReal.coe_natCast]
    exact_mod_cast hSeq
  exact le_antisymm h1 (by rw [Int.cast_abs]; exact h2)

/-- **The class infimum of the rank functional is the absolute rank.** For a fibre-functor profile
on the Mukai lattice with the class of a point `w = (0, 0, 1)` (the rank functional
`R = Σ_j rk 𝓗^j`, through the derived fibre at a point), on a class `γ = (r, c, s)` with an object
`S` of `𝒮` of class `γ` and `μ_F(S) = |r|` (a shifted spherical sheaf), `d_R(γ) = |r|`. -/
theorem classInf_eq_abs_rank {N : Type*} [AddCommGroup N] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ}
    (F : FibreFunctorProfile Obj (MukaiLattice ℤ N) (Mukai.mukaiForm b))
    (hw : F.w = ((0 : ℤ), (0 : N), (1 : ℤ))) (𝒮 : Set Obj) {γ : MukaiLattice ℤ N} {S : Obj}
    (hS : S ∈ classFibre 𝒮 F.cls γ) (hSeq : (F.mass S : ℤ) = |γ.1|) :
    (classInf 𝒮 F.cls F.toProfile γ : ℝ) = ((|γ.1| : ℤ) : ℝ) := by
  have hB : Mukai.mukaiForm b F.w γ = -γ.1 := by
    rw [hw, Mukai.mukaiForm_apply]
    simp [Mukai.pairing]
  rw [F.classInf_eq_abs 𝒮 hS (by rw [hB, abs_neg]; exact hSeq), hB, abs_neg]

end FibreFunctorProfile
