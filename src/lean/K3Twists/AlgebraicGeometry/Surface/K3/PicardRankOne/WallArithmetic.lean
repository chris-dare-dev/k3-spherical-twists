/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Combinatorics.Quiver.Kronecker.RealRoots
import K3Twists.LinearAlgebra.BilinearForm.Gram
import K3Twists.LinearAlgebra.Lattice.Mukai.PicardRankOne

/-!
# The integer arithmetic of walls with two spherical simples on a K3 surface

The statements of the article's section on walls that need the Mukai lattice:

* `span_roots_anisotropic`: two spherical classes of pairing `±g`, `|g| ≥ 3`, span no
  isotropic class, so a point factor cannot dissolve into two spherical wall simples;
* `square_roots_plus_isotropic`, `twoExtensions_numerics`: the numerical step of the lemma on
  the wall group carrying the point, which leaves `N = U` or one of the two universal
  extensions;
* `rigid_example`: the numbers of the example of a rigid wall at `g = 3`.

The two lattice statements are the Tits identity `BilinearForm.apply_smul_add_smul_self` for two
classes, read on the Mukai form of Picard rank one.
-/

namespace AlgebraicGeometry.K3.PicardRankOne

open Quiver.Kronecker

/-- For two spherical classes `s₀, s₁` of Mukai pairing `⟨s₀, s₁⟩ = g` with `|g| ≥ 3`, no nonzero
rational combination is isotropic. -/
theorem span_roots_anisotropic {d : ℚ} {s₀ s₁ : MukaiVector ℚ} (h₀ : MukaiVector.IsRoot d s₀)
    (h₁ : MukaiVector.IsRoot d s₁) {g : ℤ} (hg : 3 ≤ |g|) (h01 : MukaiVector.pairing d s₀ s₁ = g)
    {x y : ℚ} (hiso : MukaiVector.IsIsotropic d (x • s₀ + y • s₁)) : x = 0 ∧ y = 0 := by
  rw [MukaiVector.IsIsotropic, ← MukaiVector.mukaiForm_apply,
    BilinearForm.apply_smul_add_smul_self] at hiso
  simp only [MukaiVector.mukaiForm_apply, MukaiVector.pairing_comm d s₁ s₀, h01] at hiso
  rw [h₀, h₁] at hiso
  exact no_null_vector (g := -g) (by rwa [abs_neg]) (by push_cast; linear_combination -hiso / 2)

/-! ### The wall group that carries the point -/

/-- The square of `v(N) = q·v(S) + v(U)` for a spherical `S` and an isotropic `U` with
`⟨v(S), v(U)⟩ = g` is `2q(g - q)`. -/
lemma square_roots_plus_isotropic {R : Type*} [CommRing R] {d : R} {s w : MukaiVector R}
    (hs : MukaiVector.IsRoot d s) (hw : MukaiVector.IsIsotropic d w) {g : R}
    (hsw : MukaiVector.pairing d s w = g)
    (q : R) : MukaiVector.pairing d (q • s + w) (q • s + w) = 2 * q * (g - q) := by
  rw [← one_smul R w, ← MukaiVector.mukaiForm_apply, BilinearForm.apply_smul_add_smul_self]
  simp only [MukaiVector.mukaiForm_apply, MukaiVector.pairing_comm d w s, hsw]
  rw [hs, hw]
  ring

/-- **The numerical step of the two-extension lemma.** If a wall object `N` has filtration
`S^a, U, S^b` with `q = a + b ≤ g`, then `e(N) ≥ 2 + 2ab + 2q(g - q)`; the bound `e(N) ≤ 2`
leaves only `ab = 0` and `q ∈ {0, g}`, that is `N = U` or one of the two universal extensions
`T_S U`, `T_S⁻¹ U`. -/
theorem twoExtensions_numerics {a b g e : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hqg : a + b ≤ g)
    (he : 2 + 2 * a * b + 2 * (a + b) * (g - (a + b)) ≤ e) (he2 : e ≤ 2) :
    a * b = 0 ∧ (a + b = 0 ∨ a + b = g) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hq : 0 ≤ (a + b) * (g - (a + b)) := mul_nonneg (by linarith) (by linarith)
  have hab0 : a * b = 0 := by nlinarith
  have hq0 : (a + b) * (g - (a + b)) = 0 := by nlinarith
  refine ⟨hab0, ?_⟩
  rcases mul_eq_zero.mp hq0 with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-! ### The example of a rigid wall at `g = 3` -/

/-- At `g = 3`: `u = 0, 1, 3, 8, 21, …`. -/
lemma u_three_values : u 3 2 = 3 ∧ u 3 3 = 8 := by
  have h2 : u 3 2 = 3 := by simp
  refine ⟨h2, ?_⟩
  have := u_add_one 3 2
  rw [show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num, h2, u_one] at this
  rw [this]; norm_num

/-- The example of a rigid wall object at `g = 3` with multiplicities `(9, 3)`:
`dim End = 9² + 3² - 3·9·3 = 9`, and the stable roots on its two boundaries,
`(8, 3) = R₂` and `(1, 3) = L₁`, are real roots. -/
theorem rigid_example :
    kroneckerForm 3 9 3 = 9 ∧ kroneckerForm 3 8 3 = 1 ∧ kroneckerForm 3 1 3 = 1 ∧
      (u 3 3, u 3 2) = ((8 : ℤ), (3 : ℤ)) ∧ (u 3 1, u 3 2) = ((1 : ℤ), (3 : ℤ)) := by
  obtain ⟨h2, h3⟩ := u_three_values
  refine ⟨by norm_num [kroneckerForm], by norm_num [kroneckerForm], by norm_num [kroneckerForm],
    by rw [h3, h2], by rw [u_one, h2]⟩

end AlgebraicGeometry.K3.PicardRankOne
