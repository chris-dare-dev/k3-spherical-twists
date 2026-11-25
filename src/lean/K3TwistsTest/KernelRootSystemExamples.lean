/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.Slice
import K3Twists.LinearAlgebra.Lattice.Mukai.Support
import K3Twists.LinearAlgebra.RootSystem.Spherical
import Mathlib.LinearAlgebra.RootSystem.OfBilinear

/-!
# The kernel root system: counterexamples

Regression tests for `LinearAlgebra/RootSystem/Spherical.lean`.

* **Over `ℤ` the spherical pairing is not a root system** in Mathlib's sense: on the `A₁` lattice
  `⟨-2⟩ = (ℤ, -2xy)` the coroots `∓2·id` span `2ℤ`, not the dual `ℤ`. So the integral object is a
  finite, reduced, simply laced root pairing, and the root system lives over `ℚ`
  (`RootPairing.latticeRootSystem`).
* **`RootPairing.ofBilinear` is a different object.** It indexes every reflective vector: on
  `A₁` both `1` and `2` (`B(2, 2) = -8` divides `2B(2, y) = -8y`), so its pairing is the
  non-reduced `BC₁`; on `D₄` (Gram matrix minus the Cartan matrix) it indexes the norm `-4`
  vector `α₀ + α₂`, on which the coroot of the central root takes the value `-2`, so it is not
  simply laced.
* **The Mukai lattice of Picard rank one** (`H² = 2`) has infinitely many roots `(1, m, m² + 1)`,
  so `RootPairing.mk'`, which asks for finitely many, could not build its pairing; the spherical
  pairing is reduced.
-/

namespace K3TwistsTest.KernelRootSystemExamples

open Module Set Function RootPairing

/-! ### The `A₁` lattice -/

/-- The `A₁` lattice: `ℤ` with `B(x, y) = -2xy`. -/
def bA1 : ℤ →ₗ[ℤ] ℤ →ₗ[ℤ] ℤ := (-2 : ℤ) • LinearMap.mul ℤ ℤ

@[simp] theorem bA1_apply (x y : ℤ) : bA1 x y = -2 * (x * y) := by
  simp [bA1]

theorem bA1_symm : ∀ x y, bA1 x y = bA1 y x := fun x y => by simp [mul_comm]

theorem bA1_negDef : ∀ v, v ≠ 0 → bA1 v v < 0 := fun v hv => by
  simp only [bA1_apply]
  have := mul_self_pos.mpr hv
  linarith

/-- Over `ℤ`, the spherical pairing of `A₁` is not a root system: its coroots span `2ℤ`. -/
theorem not_isRootSystem_A1 :
    ¬(sphericalPairing bA1_symm (injective_of_negDef bA1_negDef)).IsRootSystem := by
  intro h
  have htop := h.span_coroot_eq_top
  let S : Submodule ℤ (Dual ℤ ℤ) :=
    { carrier := {f | (2 : ℤ) ∣ f 1}
      add_mem' := fun {f g} hf hg => by
        change (2 : ℤ) ∣ (f + g) 1
        rw [LinearMap.add_apply]
        exact dvd_add hf hg
      zero_mem' := by simp
      smul_mem' := fun c f hf => by
        change (2 : ℤ) ∣ (c • f) 1
        rw [LinearMap.smul_apply, smul_eq_mul]
        exact dvd_mul_of_dvd_right hf c }
  have hle : Submodule.span ℤ (range (sphericalPairing bA1_symm
      (injective_of_negDef bA1_negDef)).coroot) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change (2 : ℤ) ∣ -bA1 i.1 1
    simp only [bA1_apply]
    exact ⟨i.1, by ring⟩
  rw [htop] at hle
  have : (LinearMap.id : Dual ℤ ℤ) ∈ S := hle Submodule.mem_top
  change (2 : ℤ) ∣ (1 : ℤ) at this
  omega

theorem two_isReflective_A1 : LinearMap.IsReflective bA1 (2 : ℤ) where
  regular := IsRegular.of_ne_zero (by simp)
  dvd_two_mul y := ⟨y, by simp; ring⟩

theorem one_isReflective_A1 : LinearMap.IsReflective bA1 (1 : ℤ) where
  regular := IsRegular.of_ne_zero (by simp)
  dvd_two_mul y := ⟨2 * y, by simp⟩

theorem bA1_nondegenerate : LinearMap.Nondegenerate bA1 := by
  constructor
  · intro x hx
    have := hx 1
    simp at this
    exact this
  · intro y hy
    have := hy 1
    simp at this
    exact this

/-- `RootPairing.ofBilinear` is not reduced on `A₁`: it indexes both `1` and `2`. -/
theorem not_isReduced_ofBilinear_A1 :
    ¬(RootPairing.ofBilinear bA1 bA1_nondegenerate ⟨fun x y => by simp [mul_comm]⟩
      (IsRegular.of_ne_zero (by norm_num))).IsReduced := by
  intro h
  have := h.eq_or_eq_neg ⟨1, one_isReflective_A1⟩ ⟨2, two_isReflective_A1⟩ (by
    rw [LinearIndependent.pair_iff]
    push Not
    exact ⟨2, -1, by change (2 : ℤ) * 1 + -1 * 2 = 0; norm_num, by simp⟩)
  change (1 : ℤ) = 2 ∨ (1 : ℤ) = -2 at this
  omega

/-! ### `D₄` -/

/-- The Cartan matrix of `D₄`, central node `1`. -/
def cartanD4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -1, -1; 0, -1, 2, 0; 0, -1, 0, 2]

/-- The `D₄` lattice: Gram matrix minus the Cartan matrix. -/
def bD4 : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) →ₗ[ℤ] ℤ := -(Matrix.toLinearMap₂' ℤ cartanD4)

lemma bD4_apply (v w : Fin 4 → ℤ) : bD4 v w =
    -(v 0 * (2 * w 0 - w 1) + v 1 * (-w 0 + 2 * w 1 - w 2 - w 3) + v 2 * (-w 1 + 2 * w 2)
      + v 3 * (-w 1 + 2 * w 3)) := by
  simp [bD4, cartanD4, Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  ring

/-- `α₀ + α₂`, of norm `-4`. -/
def xD4 : Fin 4 → ℤ := ![1, 0, 1, 0]

/-- The central root `α₁`. -/
def a1D4 : Fin 4 → ℤ := ![0, 1, 0, 0]

lemma xD4_sq : bD4 xD4 xD4 = -4 := by simp [bD4_apply, xD4]

lemma a1D4_sq : bD4 a1D4 a1D4 = -2 := by simp [bD4_apply, a1D4]

/-- `ofBilinear` indexes the norm `-4` vector `α₀ + α₂`. -/
lemma xD4_isReflective : LinearMap.IsReflective bD4 xD4 where
  regular := IsRegular.of_ne_zero (by rw [xD4_sq]; norm_num)
  dvd_two_mul y := ⟨y 0 - y 1 + y 2, by rw [xD4_sq]; simp [bD4_apply, xD4]; ring⟩

lemma a1D4_isReflective : LinearMap.IsReflective bD4 a1D4 :=
  LinearMap.IsReflective.of_dvd_two bD4 (by rw [a1D4_sq]; norm_num)

/-- The coroot of `α₁` takes the value `-2` on `α₀ + α₂`: `ofBilinear` is not simply laced on
`D₄`. -/
example : LinearMap.IsReflective.coroot bD4 a1D4_isReflective xD4 = -2 := by
  have h := LinearMap.IsReflective.apply_self_mul_coroot_apply bD4 a1D4_isReflective (y := xD4)
  rw [a1D4_sq] at h
  have h2 : bD4 a1D4 xD4 = 2 := by simp [bD4_apply, a1D4, xD4]
  rw [h2] at h
  omega

/-! ### The Mukai lattice of Picard rank one -/

/-- The Mukai form of `(ℤ, 2xy)`, the lattice of a K3 surface of Picard rank one with `H² = 2`. -/
abbrev bRankOne : LinearMap.BilinForm ℤ (MukaiLattice ℤ ℤ) := Mukai.mukaiForm (Mukai.rankOneForm 1)

lemma bRankOne_comm (x y : MukaiLattice ℤ ℤ) : bRankOne x y = bRankOne y x :=
  Mukai.mukaiForm_comm _ (fun a b => by simp [mul_comm]) x y

lemma bRankOne_injective : Injective bRankOne := by
  intro v w h
  rw [← sub_eq_zero]
  refine Mukai.eq_zero_of_forall_pairing_eq_zero (b := Mukai.rankOneForm (1 : ℤ))
    (fun x hx => by simpa using hx 1) fun y => ?_
  have := LinearMap.congr_fun h y
  rw [Mukai.mukaiForm_apply, Mukai.mukaiForm_apply] at this
  rw [Mukai.pairing_sub_left, this, sub_self]

/-- The spherical pairing of the Picard-rank-one Mukai lattice is reduced. -/
example : (sphericalPairing bRankOne_comm bRankOne_injective).IsReduced :=
  sphericalPairing_isReduced _ _

/-- It has infinitely many roots, `(1, m, m² + 1)`. -/
example : (sphericalRoots bRankOne).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℤ => ((1 : ℤ), m, m ^ 2 + 1))
    (fun m n h => by simp only [Prod.mk.injEq, true_and] at h; exact h.1) fun m => ?_
  change Mukai.selfPairing (Mukai.rankOneForm 1) _ = -2
  simp only [Mukai.selfPairing_mk, Mukai.rankOneForm_apply]
  ring

end K3TwistsTest.KernelRootSystemExamples
