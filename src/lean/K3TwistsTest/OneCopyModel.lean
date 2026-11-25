/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Kronecker.TwoExtensions

/-!
# The one-copy lemma on an explicit representation

* Why the exact endomorphism count is needed at `c = 2`: the inequality `finrank_End_ge` only
  gives `ab + p(g - a - b) ≤ 1`, which `(a, b, g, p) = (2, 0, 2, 2)` satisfies, while the
  identity `ab + p(g - a - b) = 1` with `p ≥ 2` forces `ab ≠ 0`.
* A semirigid wall object with one copy of a spherical simple, in rank-one form: `p = 3`, `g = 2`,
  `A_i = α_i φ` with `φ` the first coordinate and `α = (1, 0)`, `B_i 1 = β_i e₁` with
  `β = (0, 1)`. It satisfies the preprojective relations, and `oneCopy_of_rankOne` gives
  `dim End M = 1 + (p - 1)² = 5`.
-/

open Module Quiver.Kronecker

/-- The old inequality leaves the rigid-type configuration `(a, b, g, p) = (2, 0, 2, 2)`. -/
example : (2 : ℤ) * 0 + 2 * (2 - 2 - 0) ≤ 1 := by norm_num

/-- The exact identity at `c = 2` with `p ≥ 2` excludes every configuration with `ab = 0`. -/
example (a b p g : ℤ) (hp : 2 ≤ p) (hg : 0 ≤ g - a - b)
    (h : a * b + p * (g - a - b) = 1) : a * b ≠ 0 := by
  intro h0
  rw [h0, zero_add] at h
  have : 1 ≤ g - a - b := by
    rcases lt_or_ge (g - a - b) 1 with h1 | h1
    · have : g - a - b = 0 := by omega
      rw [this, mul_zero] at h; omega
    · exact h1
  nlinarith

/-- `α = (1, 0)`. -/
def α₀ : Fin 2 → ℚ := ![1, 0]

/-- `β = (0, 1)`, orthogonal to `α` for `∑ α_i β_i`. -/
def β₀ : Fin 2 → ℚ := ![0, 1]

/-- The first coordinate of `ℚ³`. -/
def φ₀ : (Fin 3 → ℚ) →ₗ[ℚ] ℚ := LinearMap.proj 0

/-- The second basis vector of `ℚ³`, killed by `φ₀`. -/
def w₀ : Fin 3 → ℚ := Pi.single 1 1

/-- The representation `A_i = α_i φ`, `B_i t = t β_i w`. -/
noncomputable def rankOneRep : DoubledRep ℚ (Fin 2) (Fin 3 → ℚ) ℚ where
  A i := α₀ i • φ₀
  B i := β₀ i • LinearMap.toSpanSingleton ℚ _ w₀

lemma rankOneRep_isPreprojective : rankOneRep.IsPreprojective := by
  refine ⟨LinearMap.ext fun v ↦ ?_, LinearMap.ext fun t ↦ ?_⟩
  · simp [rankOneRep, Fin.sum_univ_two, α₀, β₀]
  · simp [rankOneRep, Fin.sum_univ_two, α₀, β₀, φ₀, w₀]

/-- `dim End = 1 + (p - 1)² = 5` for `p = 3`, `g = 2`: the semirigid count. -/
example : finrank ℚ (DoubledRep.Hom rankOneRep rankOneRep) = 5 := by
  have h := rankOneRep.oneCopy_of_rankOne φ₀ α₀ w₀ β₀
    (fun h ↦ by simpa [φ₀] using LinearMap.congr_fun h (Pi.single 0 1))
    (fun h ↦ by simpa [α₀] using congrFun h 0)
    (fun h ↦ by simpa [w₀] using congrFun h 1)
    (fun h ↦ by simpa [β₀] using congrFun h 1)
    (fun i v ↦ by simp [rankOneRep])
    (fun i ↦ by simp [rankOneRep])
  simp only [Fintype.card_fin, Module.finrank_fin_fun] at h
  omega
