/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl
import K3Twists.LinearAlgebra.Matrix.Cartan.Determinant

/-!
# A consistency model for the affine roots of an `A₂` fibre

The lattice `N = ℤ²` with the form `-A₂`, `b(x, y) = -2x₀y₀ + x₀y₁ + x₁y₀ - 2x₁y₁`, and the two
curves `C₀ = e₀`, `C₁ = e₁` with fundamental cycle `Θ = C₀ + C₁`, is a `Mukai.FundamentalCycle`
(`a2Fibre`), and every class orthogonal to `H = 0` is supported on it, so the Riemann–Roch
membership field holds there (`a2Fibre_riemannRochMembership`). Both structures are therefore
consistent.

**The converse of the fundamental-alcove theorem fails.** At `β·Cᵢ = 3/4`, `Z(α₀) = β·Θ - 1 = 1/2 > 0`,
so `β` is outside the fundamental alcove; yet no rank-zero root of the fibre lies in `ker Z`. At
`β·Cᵢ = 1/4` the alcove inequalities hold and the theorem applies.

Also: the determinants of `A₁`, …, `A₄` and `D₄`, `D₅` from the general lemmas.

Built by `lake test`.
-/

namespace K3TwistsTest.AffineWeylModel

open Mukai Mukai.FundamentalCycle

/-- The form `-A₂` on `ℤ²`. -/
def a2Form : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun x y => -2 * x 0 * y 0 + x 0 * y 1 + x 1 * y 0 - 2 * x 1 * y 1)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)

@[simp]
theorem a2Form_apply (x y : Fin 2 → ℤ) :
    a2Form x y = -2 * x 0 * y 0 + x 0 * y 1 + x 1 * y 0 - 2 * x 1 * y 1 :=
  rfl

theorem a2Form_comm (x y : Fin 2 → ℤ) : a2Form x y = a2Form y x := by
  simp only [a2Form_apply]
  ring

/-- `∑ dᵢ eᵢ = d` in `ℤ²`. -/
theorem sum_smul_single (d : Fin 2 → ℤ) : ∑ i, d i • (Pi.single i 1 : Fin 2 → ℤ) = d := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_two]

/-- **The `A₂` fibre**: `C₀ = e₀`, `C₁ = e₁`, `Θ = C₀ + C₁`. -/
def a2Fibre : FundamentalCycle a2Form (Fin 2) where
  curve i := Pi.single i 1
  mult _ := 1
  curve_self i := by fin_cases i <;> simp
  curve_nonneg i j h := by fin_cases i <;> fin_cases j <;> simp at h ⊢
  negDef d hd := by
    rw [sum_smul_single, a2Form_apply]
    have : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
      by_contra h
      simp only [not_or, not_not] at h
      exact hd (funext fun j => by fin_cases j <;> simp [h.1, h.2])
    rcases this with h | h
    · have := mul_self_pos.mpr h
      nlinarith [sq_nonneg (d 0 - 2 * d 1), sq_nonneg (d 0)]
    · have := mul_self_pos.mpr h
      nlinarith [sq_nonneg (2 * d 0 - d 1), sq_nonneg (d 1)]
  connected := by
    rw [Matrix.isIndecomposable_iff_reflTransGen]
    have h01 : Relation.ReflTransGen (fun i j : Fin 2 =>
        Matrix.of (fun i j : Fin 2 => a2Form (Pi.single i 1) (Pi.single j 1)) i j ≠ 0) 0 1 :=
      Relation.ReflTransGen.single (by simp)
    have h10 : Relation.ReflTransGen (fun i j : Fin 2 =>
        Matrix.of (fun i j : Fin 2 => a2Form (Pi.single i 1) (Pi.single j 1)) i j ≠ 0) 1 0 :=
      Relation.ReflTransGen.single (by simp)
    intro i j
    fin_cases i <;> fin_cases j
    · exact Relation.ReflTransGen.refl
    · exact h01
    · exact h10
    · exact Relation.ReflTransGen.refl
  mult_nonneg _ := zero_le_one
  cycle_self := by simp [Fin.sum_univ_two]
  cycle_curve_nonpos i := by fin_cases i <;> simp [Fin.sum_univ_two]

theorem a2Fibre_cycle : a2Fibre.cycle = ![1, 1] := by
  ext j
  fin_cases j <;> simp [cycle, a2Fibre]

/-- Every class of `ℤ²` is supported on the fibre. -/
theorem mem_rootLattice (c : Fin 2 → ℤ) : c ∈ a2Fibre.rootLattice :=
  ⟨c, by rw [combination_apply]; exact sum_smul_single c⟩

/-- **The Riemann–Roch membership field is consistent**: it holds at `H = 0`. -/
theorem a2Fibre_riemannRochMembership : a2Fibre.RiemannRochMembership 0 where
  mem c _ _ := mem_rootLattice c

/-- The marks of `Ã₂` are a null vector of the extended Dynkin matrix. -/
example : Matrix.mulVec a2Fibre.affineCartan a2Fibre.nullMult = 0 :=
  a2Fibre.affineCartan_mulVec_nullMult

/-! ### The `A₂` test: `β·Cᵢ = 3/4` -/

/-- `β(x) = 3/4 (x₀ + x₁)`, so `β·Cᵢ = 3/4`. -/
noncomputable def beta : (Fin 2 → ℤ) →+ ℝ where
  toFun x := 3 / 4 * ((x 0 : ℝ) + x 1)
  map_zero' := by simp
  map_add' x y := by simp; ring

/-- **`Z(α₀) = β·Θ - 1 = 1/2 > 0`.** -/
example : fibreCharge beta (a2Fibre.affineRoot none) = 1 / 2 := by
  rw [fibreCharge_affineRoot_none, a2Fibre_cycle]
  simp [beta]
  norm_num

/-- `β` is outside the fundamental alcove. -/
example : ¬a2Fibre.IsInFundamentalAlcove beta := by
  rintro ⟨-, h⟩
  rw [a2Fibre_cycle] at h
  simp [beta] at h
  norm_num at h

/-- **No root of the `A₂` fibre lies in `ker Z` at `β·Cᵢ = 3/4`.** -/
example {v : MukaiLattice ℤ (Fin 2 → ℤ)} (hv : a2Fibre.IsRoot v) : fibreCharge beta v ≠ 0 := by
  obtain ⟨r, c, s⟩ := v
  obtain ⟨-, -, hc⟩ := hv
  simp only [a2Form_apply] at hc
  simp only [fibreCharge_mk, beta, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  intro hZ
  have hZ' : (3 * (c 0 + c 1) : ℝ) = (4 * s : ℝ) := by linarith
  have hint : 3 * (c 0 + c 1) = 4 * s := by exact_mod_cast hZ'
  have h0 : c 0 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (c 0 - 2 * c 1)]
  have h1 : c 1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * c 0 - c 1)]
  have b0 : -1 ≤ c 0 ∧ c 0 ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have b1 : -1 ≤ c 1 ∧ c 1 ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  obtain ⟨b0l, b0u⟩ := b0
  obtain ⟨b1l, b1u⟩ := b1
  interval_cases (c 0) <;> interval_cases (c 1) <;> omega

/-! ### Inside the alcove: `β·Cᵢ = 1/4` -/

/-- `β(x) = 1/4 (x₀ + x₁)`. -/
noncomputable def betaIn : (Fin 2 → ℤ) →+ ℝ where
  toFun x := 1 / 4 * ((x 0 : ℝ) + x 1)
  map_zero' := by simp
  map_add' x y := by simp; ring

example : a2Fibre.IsInFundamentalAlcove betaIn := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [a2Fibre, betaIn]
  · rw [a2Fibre_cycle]
    simp [betaIn]
    norm_num

/-! ### Cartan determinants -/

example : (CartanMatrix.A 4).det = 5 := by
  rw [CartanMatrix.A_det]
  norm_num

example : (CartanMatrix.D 5).det = 4 := CartanMatrix.D_det (by norm_num)

example : (CartanMatrix.D 4).det = 4 := CartanMatrix.D_det (by norm_num)

end K3TwistsTest.AffineWeylModel
