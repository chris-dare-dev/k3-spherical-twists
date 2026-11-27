/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.Eichler
import Mathlib.Algebra.Module.Projective
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Int.ModEq
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Period recovery from the moduli of a central charge on roots

For a stability condition `σ` on a K3 surface with central charge `Z`, the infimum of the mass of
`σ` over the spherical objects of a root class `γ` is `|Z(γ)|` (Kikuta–Koseki–Ouchi,
arXiv:2504.12253, Corollary 3.5). Kikuta, Koseki and Ouchi recover `Z` from these numbers
(arXiv:2504.12253, Proposition 3.10). This file proves the lattice part of their argument, in
three steps, for an arbitrary real vector space `V` with a symmetric bilinear form `B`.

* **The squared modulus is a quadratic form.** For a real-linear `Z : V → ℂ`,
  `|Z(x)|² = (Re Z(x))² + (Im Z(x))²` is a real quadratic form on `V` (`Mukai.periodForm`).
* **Polarization on roots.** Let `δ₁, …, δₙ` be roots (`B(δᵢ, δᵢ) = -2`) spanning `V` with
  pairwise nonzero pairings. The classes `δⱼ + B(δᵢ, δⱼ) δᵢ` are the reflections of `δⱼ` in `δᵢ`,
  hence again roots, and a quadratic form `q` is determined by its values at the `δᵢ` and at
  these reflections (`QuadraticMap.eq_of_eq_on_roots`). The mixed entry carries the weight `c²`:
  for the symmetric form `β` with `q(x) = β(x, x)` and `c = B(δᵢ, δⱼ) ≠ 0`,

  ```
  β(δᵢ, δⱼ) = [q(δⱼ + c δᵢ) - q(δⱼ) - c² q(δᵢ)] / (2c),
  ```

  because `q(δⱼ + c δᵢ) = q(δⱼ) + 2c β(δᵢ, δⱼ) + c² q(δᵢ)` (`QuadraticMap.map_add_smul`,
  `QuadraticMap.polar_eq_inv_smul`). Subtracting `q(δᵢ)` in place of `c² q(δᵢ)` gives the right
  number only when `c = ±1`. Over any field with `2 ≠ 0` and for any nonzero scalars `cᵢⱼ` in
  place of the pairings, the `n(n + 1)/2` values at the `δᵢ` and at the `δⱼ + cᵢⱼ δᵢ`, `i < j`,
  already determine `q` (`QuadraticMap.eq_of_eq_add_smul`).
* **The charge from its modulus.** If `|Z'(x)| = c |Z(x)|` for every `x`, with `c > 0` and `Z`
  surjective, then `Z' = c A Z` for an orthogonal map `A` of `ℂ = ℝ²`, which is a rotation or a
  rotation composed with complex conjugation (`Mukai.exists_linearIsometryEquiv_of_norm_eq`,
  `Mukai.exists_circle_of_norm_eq`, from `linear_isometry_complex`).

Together: if `|Z'(δ)| = c |Z(δ)|` for every root `δ`, then `|Z'|² = c² |Z|²` as quadratic forms,
and `Z' = c A Z` (`Mukai.exists_linearIsometryEquiv_of_norm_eq_roots`).

## The spanning roots

Kikuta–Koseki–Ouchi (arXiv:2504.12253, Lemma 3.8) take `C, D₁, …, D_{ρ-1}` in `NS(X)` with
`C² > 0`, `C · Dᵢ = Dᵢ · Dⱼ = 0` and `Dᵢ² < -4`, and the classes `v(𝒪(Dᵢ))`, `v(𝒪)`,
`v(𝒪(-C))`, `v(𝒪(2C))`. With `v(𝒪(D)) = (1, D, D²/2 + 1)` two line bundles pair to

```
⟪v(𝒪(D)), v(𝒪(D'))⟫ = -(D - D')²/2 - 2
```

(`Mukai.pairing_lineBundle`). For `C · D = 0` the pairing of `v(𝒪(D))` and `v(𝒪(-C))` is therefore
`-(D² + C²)/2 - 2`, and that of `v(𝒪(D))` and `v(𝒪(2C))` is `-(D² + 4C²)/2 - 2`
(`Mukai.pairing_lineBundle_neg_of_polarBilin_eq_zero`,
`Mukai.pairing_lineBundle_two_smul_of_polarBilin_eq_zero`). **The printed basis can fail its own
condition that distinct members pair to nonzero numbers:** the first pairing is zero for
`NS(X) = ⟨2⟩ ⊕ ⟨-6⟩` (`C² = 2`, `D² = -6`), and the second for `NS(X) = ⟨2⟩ ⊕ ⟨-12⟩`
(`C² = 2`, `D² = -12`); both choices satisfy `C² > 0`, `C · D = 0` and `D² < -4`. This is a
direct computation, checked in `K3TwistsTest/PeriodRecoveryExamples.lean`.

**The repair doubles the classes.** If `D - D' = 2u`, the pairing is `-2u² - 2`, which is
`≡ 2 mod 4` on an even lattice and so never zero (`Mukai.pairing_lineBundle_modEq_two`). For any
classes `e₁, …, e_ρ` of `NS(X)` spanning `NS(X)_ℝ` with `e₁² ≠ 0`, the classes

```
v(𝒪), v(𝒪(2e₁)), …, v(𝒪(2e_ρ)), v(𝒪(-2e₁))
```

(`Mukai.doubledLineBundles`) are roots with pairwise nonzero pairings
(`Mukai.pairing_doubledLineBundles_ne_zero`) that span the real Mukai lattice
(`Mukai.span_doubledLineBundles`): with `w(D) = v(𝒪(D)) - v(𝒪) = (0, D, D²/2)`, the sum
`w(2e₁) + w(-2e₁) = (0, 0, 4e₁²)` gives the point class, then `w(2eᵢ)` gives `(0, eᵢ, 0)`, and
`v(𝒪)` gives `(1, 0, 0)`. When the `eᵢ` are a basis of `NS(X)_ℚ`, these are `ρ + 2` spanning roots,
a real basis: the repaired form of their Lemma 3.8. The pairings are integers, so the reflections
of these roots in each other are integral roots, and the moduli at integral roots already recover
the charge (`Mukai.exists_linearIsometryEquiv_of_norm_eq_doubledLineBundles`).

## Conventions

* The Mukai pairing is `⟪(r, c, s), (r', c', s')⟫ = b(c, c') - rs' - r's` (`Mukai.pairing`). The
  lattice `N` carries a quadratic map `q` and `b = polarBilin q`, so `b(x, x) = 2q(x)`: an even
  lattice `D² = 2q(D)` enters over `ℤ` without division, and `v(𝒪(D)) = (1, D, q(D) + 1)`
  (`Mukai.lineBundle`).
* A **root** of a bilinear form `B` is a vector `x` with `B(x, x) = -2`; for the Mukai form this is
  `Mukai.IsSpherical`. The reflection is `BilinearForm.reflect`, `ρ_s(v) = v + B(v, s) s`.
* A charge is a real-linear map `Z : V → ℂ`, and `c > 0` is the factor between the two moduli.
* Nothing here uses a surface or a stability condition. The geometry (the mass infimum and the
  spherical objects in every root class) enters only through the hypotheses on the moduli.

## Main definitions

* `Mukai.lineBundle q D`: the vector `(1, D, q(D) + 1)`, the Mukai vector of `𝒪(D)`.
* `Mukai.doubledLineBundles q e i₀`: `v(𝒪)`, `v(𝒪(-2e_{i₀}))` and the `v(𝒪(2eᵢ))`.
* `Mukai.periodForm Z`: the quadratic form `x ↦ ‖Z x‖²`.

## Main results

* `QuadraticMap.map_add_smul`, `QuadraticMap.polar_eq_inv_smul`: polarization along a line, with
  the weight `c²`.
* `QuadraticMap.eq_of_eq_add_smul`: recovery of a quadratic map from `n(n + 1)/2` values.
* `BilinearForm.add_smul_eq_reflect`, `BilinearForm.apply_add_smul_self_eq_neg_two`,
  `QuadraticMap.eq_of_eq_on_roots`: the classes used are reflections, hence roots, and a
  quadratic map is determined by its values on roots.
* `Mukai.pairing_lineBundle`, `Mukai.isSpherical_lineBundle`,
  `Mukai.pairing_lineBundle_of_sub_eq_two_smul`, `Mukai.pairing_lineBundle_ne_zero`,
  `Mukai.pairing_lineBundle_modEq_two`: the pairings of line bundles and of doubled classes.
* `Mukai.isSpherical_doubledLineBundles`, `Mukai.pairing_doubledLineBundles_ne_zero`,
  `Mukai.span_doubledLineBundles`: the repaired spanning roots.
* `Mukai.exists_linearIsometryEquiv_of_norm_eq`, `Mukai.exists_circle_of_norm_eq`: the charge
  from its modulus.
* `Mukai.exists_linearIsometryEquiv_of_norm_eq_add_smul`,
  `Mukai.exists_linearIsometryEquiv_of_norm_eq_roots`,
  `Mukai.exists_linearIsometryEquiv_of_norm_eq_doubledLineBundles`: **period recovery**.

## References

* K. Kikuta, N. Koseki, G. Ouchi, *Stability conditions on K3 surfaces via mass of spherical
  objects*, arXiv:2504.12253, Corollary 3.5, Lemma 3.8 and Proposition 3.10.
-/

open Set Submodule

/-! ### Polarization along a line -/

namespace QuadraticMap

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N]

/-- **Polarization along a line.** `Q(y + c x) = Q(y) + c · polar Q x y + c² Q(x)`. -/
theorem map_add_smul (Q : QuadraticMap R M N) (c : R) (x y : M) :
    Q (y + c • x) = Q y + c • polar Q x y + (c * c) • Q x := by
  rw [QuadraticMap.map_add Q y (c • x), Q.map_smul, polar_smul_right, polar_comm Q y x]
  abel

/-- A quadratic map over a ring in which `2` is a unit is determined by its polar form on a
spanning family. -/
theorem eq_of_polar_eq {ι : Type*} (h2 : IsUnit (2 : R)) {δ : ι → M}
    (hδ : span R (range δ) = ⊤) {Q Q' : QuadraticMap R M N}
    (h : ∀ i j, polar Q (δ i) (δ j) = polar Q' (δ i) (δ j)) : Q = Q' := by
  refine polarBilin_injective h2 ?_
  refine LinearMap.ext_on_range hδ fun i => LinearMap.ext_on_range hδ fun j => ?_
  simpa using h i j

end CommRing

section Field

variable {K M N : Type*} [Field K] [AddCommGroup M] [AddCommGroup N] [Module K M] [Module K N]

/-- **The mixed entry carries the weight `c²`.** For `c ≠ 0`,
`polar Q x y = c⁻¹ (Q(y + c x) - Q(y) - c² Q(x))`. -/
theorem polar_eq_inv_smul (Q : QuadraticMap K M N) {c : K} (hc : c ≠ 0) (x y : M) :
    polar Q x y = c⁻¹ • (Q (y + c • x) - Q y - (c * c) • Q x) := by
  have h : Q (y + c • x) - Q y - (c * c) • Q x = c • polar Q x y := by
    rw [map_add_smul]
    abel
  rw [h, inv_smul_smul₀ hc]

/-- **Recovery from `n(n + 1)/2` values.** Over a field with `2 ≠ 0`, let `δ` span `M` and let
`c i j ≠ 0` for `i < j`. Two quadratic maps that agree at every `δ i` and at every
`δ j + c i j • δ i` with `i < j` are equal. -/
theorem eq_of_eq_add_smul {ι : Type*} [LinearOrder ι] (h2 : (2 : K) ≠ 0) {δ : ι → M}
    (hδ : span K (range δ) = ⊤) {c : ι → ι → K} (hc : ∀ i j, i < j → c i j ≠ 0)
    {Q Q' : QuadraticMap K M N} (h₁ : ∀ i, Q (δ i) = Q' (δ i))
    (h₂ : ∀ i j, i < j → Q (δ j + c i j • δ i) = Q' (δ j + c i j • δ i)) : Q = Q' := by
  have key : ∀ i j, i < j → polar Q (δ i) (δ j) = polar Q' (δ i) (δ j) := fun i j hij => by
    rw [polar_eq_inv_smul Q (hc i j hij), polar_eq_inv_smul Q' (hc i j hij), h₁ i, h₁ j,
      h₂ i j hij]
  refine eq_of_polar_eq h2.isUnit hδ fun i j => ?_
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact key i j hij
  · rw [polar_self, polar_self, h₁]
  · rw [polar_comm Q, polar_comm Q', key j i hji]

/-- **Recovery from a family and its reflections.** Over a field with `2 ≠ 0`, let `δ` span `M`
with `B(δ i, δ j) ≠ 0` for `i ≠ j`. Two quadratic maps that agree at every `δ i` and at every
reflection `ρ_{δ i}(δ j) = δ j + B(δ j, δ i) δ i` with `i ≠ j` are equal. Neither symmetry of `B`
nor a root condition is needed: `B` only supplies the nonzero scalars. -/
theorem eq_of_eq_reflect {ι : Type*} (h2 : (2 : K) ≠ 0) (B : LinearMap.BilinForm K M)
    {δ : ι → M} (hδ : span K (range δ) = ⊤) (hne : ∀ i j, i ≠ j → B (δ i) (δ j) ≠ 0)
    {Q Q' : QuadraticMap K M N} (h₁ : ∀ i, Q (δ i) = Q' (δ i))
    (h₂ : ∀ i j, i ≠ j →
      Q (BilinearForm.reflect B (δ i) (δ j)) = Q' (BilinearForm.reflect B (δ i) (δ j))) :
    Q = Q' := by
  refine eq_of_polar_eq h2.isUnit hδ fun i j => ?_
  rcases eq_or_ne i j with rfl | hij
  · rw [polar_self, polar_self, h₁]
  · have h := h₂ i j hij
    rw [BilinearForm.reflect_apply] at h
    rw [polar_eq_inv_smul Q (hne j i hij.symm), polar_eq_inv_smul Q' (hne j i hij.symm), h₁ i,
      h₁ j, h]

end Field

end QuadraticMap

/-! ### Roots -/

namespace BilinearForm

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (B : M →ₗ[R] M →ₗ[R] R)

/-- For a symmetric form, `v + B(s, v) s` is the reflection `ρ_s(v) = v + B(v, s) s`. -/
theorem add_smul_eq_reflect (hB : ∀ x y, B x y = B y x) (s v : M) :
    v + B s v • s = reflect B s v := by
  rw [reflect_apply, hB s v]

/-- For a symmetric form and `B(s, s) = -2`, the class `v + B(s, v) s` has the square of `v`. -/
theorem apply_add_smul_self (hB : ∀ x y, B x y = B y x) {s : M} (hs : B s s = -2) (v : M) :
    B (v + B s v • s) (v + B s v • s) = B v v := by
  rw [add_smul_eq_reflect B hB, self_reflect B hB s hs]

/-- **The reflected root.** For a symmetric form and roots `s` and `v`, the class
`v + B(s, v) s` is a root. -/
theorem apply_add_smul_self_eq_neg_two (hB : ∀ x y, B x y = B y x) {s v : M} (hs : B s s = -2)
    (hv : B v v = -2) : B (v + B s v • s) (v + B s v • s) = -2 := by
  rw [apply_add_smul_self B hB hs, hv]

end BilinearForm

namespace QuadraticMap

variable {K M N : Type*} [Field K] [AddCommGroup M] [AddCommGroup N] [Module K M] [Module K N]

/-- **A quadratic map is determined by its values on roots.** Over a field with `2 ≠ 0`, let `B`
be symmetric and let `δ` be roots of `B` spanning `M` with `B(δ i, δ j) ≠ 0` for `i ≠ j`. Two
quadratic maps that agree at every root of `B` are equal. -/
theorem eq_of_eq_on_roots {ι : Type*} (h2 : (2 : K) ≠ 0) (B : LinearMap.BilinForm K M)
    (hB : ∀ x y, B x y = B y x) {δ : ι → M} (hroot : ∀ i, B (δ i) (δ i) = -2)
    (hδ : span K (range δ) = ⊤) (hne : ∀ i j, i ≠ j → B (δ i) (δ j) ≠ 0)
    {Q Q' : QuadraticMap K M N} (h : ∀ x, B x x = -2 → Q x = Q' x) : Q = Q' :=
  eq_of_eq_reflect h2 B hδ hne (fun i => h _ (hroot i)) fun i j _ =>
    h _ (by rw [BilinearForm.self_reflect B hB _ (hroot i), hroot j])

end QuadraticMap

namespace Mukai

/-! ### Line bundles -/

section CommRing

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] (q : QuadraticMap R N R)

/-- The Mukai vector `v(𝒪(D)) = (1, D, q(D) + 1)` of a line bundle on a quadratic module
`(N, q)`. For the polar form `b = polarBilin q` the number `q(D)` is `D²/2`. -/
def lineBundle (D : N) : MukaiLattice R N := (1, D, q D + 1)

/-- Unfolding `lineBundle`. -/
theorem lineBundle_def (D : N) : lineBundle q D = (1, D, q D + 1) :=
  rfl

/-- `v(𝒪) = (1, 0, 1)`. -/
theorem lineBundle_zero : lineBundle q 0 = (1, 0, 1) := by
  simp [lineBundle]

/-- The Mukai quadratic form `q(c) - rs` is `-1` on `v(𝒪(D))`. -/
theorem quadraticForm_lineBundle (D : N) : quadraticForm q (lineBundle q D) = -1 := by
  simp only [quadraticForm_apply, lineBundle]
  ring

/-- Tensoring with `𝒪(D)` sends `v(𝒪(D'))` to `v(𝒪(D + D'))`. -/
theorem tensorLine_lineBundle (D D' : N) :
    tensorLine q.polarBilin D (q D) (lineBundle q D') = lineBundle q (D + D') := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp [lineBundle, add_comm]
  · simp only [tensorLine_apply, lineBundle, QuadraticMap.polarBilin_apply_apply, one_mul,
      QuadraticMap.map_add q D D', QuadraticMap.polar_comm q D' D]
    ring

/-- **The pairing of two line bundles.** `⟪v(𝒪(D)), v(𝒪(D'))⟫ = -q(D - D') - 2`, that is
`-(D - D')²/2 - 2`. -/
theorem pairing_lineBundle (D D' : N) :
    pairing q.polarBilin (lineBundle q D) (lineBundle q D') = -q (D - D') - 2 := by
  have h : q (D - D') = q D + q D' - QuadraticMap.polar q D D' := by
    rw [sub_eq_add_neg, QuadraticMap.map_add q D (-D'), QuadraticMap.map_neg,
      QuadraticMap.polar_neg_right]
    abel
  rw [lineBundle, lineBundle, pairing_mk, QuadraticMap.polarBilin_apply_apply, h]
  ring

/-- Every `v(𝒪(D))` is a root. -/
theorem isSpherical_lineBundle (D : N) : IsSpherical q.polarBilin (lineBundle q D) := by
  rw [IsSpherical, selfPairing_eq_pairing, pairing_lineBundle, sub_self, map_zero, neg_zero,
    zero_sub]

/-- **Doubled classes.** If `D - D' = 2u` then `⟪v(𝒪(D)), v(𝒪(D'))⟫ = -4 q(u) - 2`. -/
theorem pairing_lineBundle_of_sub_eq_two_smul {D D' u : N} (h : D - D' = (2 : R) • u) :
    pairing q.polarBilin (lineBundle q D) (lineBundle q D') = -4 * q u - 2 := by
  rw [pairing_lineBundle, h, QuadraticMap.map_smul, smul_eq_mul]
  ring

/-- **Doubled classes pair to a nonzero number.** If `D - D' = 2u` and `q(u)` is an integer, in
characteristic zero, then `⟪v(𝒪(D)), v(𝒪(D'))⟫ = -4 q(u) - 2 ≠ 0`. -/
theorem pairing_lineBundle_ne_zero [CharZero R] {D D' u : N} (h : D - D' = (2 : R) • u) {n : ℤ}
    (hn : q u = n) : pairing q.polarBilin (lineBundle q D) (lineBundle q D') ≠ 0 := by
  rw [pairing_lineBundle_of_sub_eq_two_smul q h, hn]
  exact_mod_cast (by omega : -4 * n - 2 ≠ 0)

/-- **The printed basis, first pairing.** If `b(C, D) = 0`, then
`⟪v(𝒪(D)), v(𝒪(-C))⟫ = -(q(D) + q(C)) - 2`, that is `-(D² + C²)/2 - 2`. -/
theorem pairing_lineBundle_neg_of_polarBilin_eq_zero {C D : N} (hCD : q.polarBilin C D = 0) :
    pairing q.polarBilin (lineBundle q D) (lineBundle q (-C)) = -(q D + q C) - 2 := by
  rw [pairing_lineBundle, sub_neg_eq_add, QuadraticMap.map_add q D C, QuadraticMap.polar_comm,
    ← QuadraticMap.polarBilin_apply_apply, hCD]
  ring

/-- **The printed basis, second pairing.** If `b(C, D) = 0`, then
`⟪v(𝒪(D)), v(𝒪(2C))⟫ = -(q(D) + 4 q(C)) - 2`, that is `-(D² + 4C²)/2 - 2`. -/
theorem pairing_lineBundle_two_smul_of_polarBilin_eq_zero {C D : N}
    (hCD : q.polarBilin C D = 0) :
    pairing q.polarBilin (lineBundle q D) (lineBundle q ((2 : R) • C)) =
      -(q D + 4 * q C) - 2 := by
  have h : QuadraticMap.polar q D ((2 : R) • C) = 0 := by
    rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_comm,
      ← QuadraticMap.polarBilin_apply_apply, hCD, smul_zero]
  rw [pairing_lineBundle, sub_eq_add_neg D, QuadraticMap.map_add q D, QuadraticMap.map_neg,
    QuadraticMap.polar_neg_right, h, QuadraticMap.map_smul, smul_eq_mul]
  ring

/-! ### The doubled family -/

variable {ι : Type*}

/-- **The doubled family** `v(𝒪)`, `v(𝒪(-2e_{i₀}))` and `v(𝒪(2eᵢ))` for every `i`, indexed by
`none`, `some none` and `some (some i)`. -/
def doubledLineBundles (e : ι → N) (i₀ : ι) : Option (Option ι) → MukaiLattice R N
  | none => lineBundle q 0
  | some none => lineBundle q (-((2 : R) • e i₀))
  | some (some i) => lineBundle q ((2 : R) • e i)

/-- The member `v(𝒪)` of the doubled family. -/
@[simp]
theorem doubledLineBundles_none (e : ι → N) (i₀ : ι) :
    doubledLineBundles q e i₀ none = lineBundle q 0 :=
  rfl

/-- The member `v(𝒪(-2e_{i₀}))` of the doubled family. -/
@[simp]
theorem doubledLineBundles_some_none (e : ι → N) (i₀ : ι) :
    doubledLineBundles q e i₀ (some none) = lineBundle q (-((2 : R) • e i₀)) :=
  rfl

/-- The member `v(𝒪(2eᵢ))` of the doubled family. -/
@[simp]
theorem doubledLineBundles_some_some (e : ι → N) (i₀ i : ι) :
    doubledLineBundles q e i₀ (some (some i)) = lineBundle q ((2 : R) • e i) :=
  rfl

/-- Every member of the doubled family is a root. -/
theorem isSpherical_doubledLineBundles (e : ι → N) (i₀ : ι) (k : Option (Option ι)) :
    IsSpherical q.polarBilin (doubledLineBundles q e i₀ k) := by
  rcases k with _ | _ | i <;> exact isSpherical_lineBundle q _

/-- Every member of the doubled family is `v(𝒪(2u))` for a class `u` of the lattice spanned by
`e`. -/
theorem exists_doubledLineBundles_eq (e : ι → N) (i₀ : ι) (k : Option (Option ι)) :
    ∃ u ∈ span ℤ (range e), doubledLineBundles q e i₀ k = lineBundle q ((2 : R) • u) := by
  rcases k with _ | _ | i
  · exact ⟨0, zero_mem _, by simp⟩
  · exact ⟨-e i₀, neg_mem (subset_span ⟨i₀, rfl⟩), by simp⟩
  · exact ⟨e i, subset_span ⟨i, rfl⟩, rfl⟩

/-- Members of the doubled family pair to `-4n - 2` for an integer `n`, when `q` takes integer
values on the lattice spanned by `e`. -/
theorem exists_pairing_doubledLineBundles_eq {e : ι → N}
    (hint : ∀ u ∈ span ℤ (range e), ∃ n : ℤ, q u = n) (i₀ : ι) (k l : Option (Option ι)) :
    ∃ n : ℤ, pairing q.polarBilin (doubledLineBundles q e i₀ k) (doubledLineBundles q e i₀ l) =
      -4 * n - 2 := by
  obtain ⟨u, hu, hk⟩ := exists_doubledLineBundles_eq q e i₀ k
  obtain ⟨u', hu', hl⟩ := exists_doubledLineBundles_eq q e i₀ l
  obtain ⟨n, hn⟩ := hint (u - u') (sub_mem hu hu')
  refine ⟨n, ?_⟩
  rw [hk, hl, pairing_lineBundle_of_sub_eq_two_smul q (smul_sub _ _ _).symm, hn]

/-- **The doubled family has pairwise nonzero pairings**, in characteristic zero, when `q` takes
integer values on the lattice spanned by `e`. -/
theorem pairing_doubledLineBundles_ne_zero [CharZero R] {e : ι → N}
    (hint : ∀ u ∈ span ℤ (range e), ∃ n : ℤ, q u = n) (i₀ : ι) (k l : Option (Option ι)) :
    pairing q.polarBilin (doubledLineBundles q e i₀ k) (doubledLineBundles q e i₀ l) ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_pairing_doubledLineBundles_eq q hint i₀ k l
  rw [hn]
  exact_mod_cast (by omega : -4 * n - 2 ≠ 0)

end CommRing

section Int

variable {N : Type*} [AddCommGroup N] (q : QuadraticMap ℤ N ℤ)

/-- **Doubled classes over `ℤ`.** If `D - D' = 2u`, then `⟪v(𝒪(D)), v(𝒪(D'))⟫ ≡ 2 mod 4`. -/
theorem pairing_lineBundle_modEq_two {D D' u : N} (h : D - D' = (2 : ℤ) • u) :
    pairing q.polarBilin (lineBundle q D) (lineBundle q D') ≡ 2 [ZMOD 4] := by
  rw [pairing_lineBundle_of_sub_eq_two_smul q h, Int.modEq_iff_dvd]
  exact ⟨q u + 1, by ring⟩

/-- Over `ℤ`, any two doubled classes `v(𝒪(2u))` and `v(𝒪(2u'))` pair to a nonzero number. -/
theorem pairing_lineBundle_two_smul_ne_zero (u u' : N) :
    pairing q.polarBilin (lineBundle q ((2 : ℤ) • u)) (lineBundle q ((2 : ℤ) • u')) ≠ 0 :=
  pairing_lineBundle_ne_zero q (smul_sub (2 : ℤ) u u').symm Int.cast_id.symm

end Int

section Field

variable {K N ι : Type*} [Field K] [AddCommGroup N] [Module K N] (q : QuadraticMap K N K)

/-- **The doubled family spans.** Over a field with `2 ≠ 0`, if `e` spans `N` and
`q(e_{i₀}) ≠ 0`, then `v(𝒪)`, `v(𝒪(-2e_{i₀}))` and the `v(𝒪(2eᵢ))` span the Mukai lattice. -/
theorem span_doubledLineBundles (h2 : (2 : K) ≠ 0) {e : ι → N} (he : span K (range e) = ⊤)
    {i₀ : ι} (h₀ : q (e i₀) ≠ 0) : span K (range (doubledLineBundles q e i₀)) = ⊤ := by
  set S := span K (range (doubledLineBundles q e i₀))
  have hmem : ∀ k, doubledLineBundles q e i₀ k ∈ S := fun k => subset_span ⟨k, rfl⟩
  have hw : ∀ k, doubledLineBundles q e i₀ k - lineBundle q 0 ∈ S := fun k =>
    S.sub_mem (hmem k) (hmem none)
  have h8 : (8 : K) ≠ 0 := by
    have : (8 : K) = 2 * 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero h2 h2) h2
  -- `w(2e_{i₀}) + w(-2e_{i₀}) = (0, 0, 8 q(e_{i₀}))` gives the point class
  have hpt : ((0 : K), (0 : N), (1 : K)) ∈ S := by
    convert S.smul_mem (8 * q (e i₀))⁻¹ (S.add_mem (hw (some (some i₀))) (hw (some none)))
      using 1
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp [lineBundle]
    · simp [lineBundle]
    · simp only [doubledLineBundles_some_some, doubledLineBundles_some_none, lineBundle,
        Prod.smul_snd, Prod.snd_add, Prod.snd_sub, QuadraticMap.map_neg, QuadraticMap.map_smul,
        map_zero, smul_eq_mul]
      field_simp
      ring
  have hrank : ((1 : K), (0 : N), (0 : K)) ∈ S := by
    convert S.sub_mem (hmem none) hpt using 1
    simp [lineBundle]
  -- `w(2eᵢ) - 4 q(eᵢ) (0, 0, 1) = (0, 2eᵢ, 0)`
  have hmid : ∀ n : N, ((0 : K), n, (0 : K)) ∈ S := by
    let j : N →ₗ[K] MukaiLattice K N := LinearMap.inr K K (N × K) ∘ₗ LinearMap.inl K N K
    have he' : ∀ i, e i ∈ S.comap j := by
      intro i
      rw [mem_comap]
      convert S.smul_mem (2 : K)⁻¹
        (S.sub_mem (hw (some (some i))) (S.smul_mem (4 * q (e i)) hpt)) using 1
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp [j, lineBundle]
      · simp [j, lineBundle, smul_smul, inv_mul_cancel₀ h2]
      · simp only [j, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
          doubledLineBundles_some_some, lineBundle, Prod.smul_snd, Prod.snd_sub,
          QuadraticMap.map_smul, map_zero, smul_eq_mul]
        ring
    have hle : span K (range e) ≤ S.comap j := span_le.mpr (range_subset_iff.mpr he')
    rw [he] at hle
    exact fun n => hle (mem_top : n ∈ ⊤)
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨r, n, s⟩ := v
  have hv : ((r, n, s) : MukaiLattice K N) =
      r • ((1 : K), (0 : N), (0 : K)) + ((0 : K), n, (0 : K)) +
        s • ((0 : K), (0 : N), (1 : K)) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  rw [hv]
  exact S.add_mem (S.add_mem (S.smul_mem r hrank) (hmid n)) (S.smul_mem s hpt)

end Field

/-! ### The central charge from its modulus -/

section CentralCharge

open ComplexConjugate

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The central charge from its modulus.** If `Z` is surjective and `‖Z' x‖ = c ‖Z x‖` for
every `x`, with `c > 0`, then `Z' = c • A ∘ Z` for a linear isometry `A` of `ℂ = ℝ²`. -/
theorem exists_linearIsometryEquiv_of_norm_eq {Z Z' : V →ₗ[ℝ] ℂ} (hZ : Function.Surjective Z)
    {c : ℝ} (hc : 0 < c) (h : ∀ x, ‖Z' x‖ = c * ‖Z x‖) :
    ∃ A : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ x, Z' x = c • A (Z x) := by
  obtain ⟨g, hg⟩ := Z.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hZ)
  have hgZ : ∀ z, Z (g z) = z := fun z => by simpa using LinearMap.congr_fun hg z
  -- `Z'` vanishes on the kernel of `Z`
  have hker : ∀ x, Z' (g (Z x)) = Z' x := by
    intro x
    have h0 : ‖Z' (g (Z x) - x)‖ = 0 := by rw [h, map_sub, hgZ, sub_self, norm_zero, mul_zero]
    rwa [norm_eq_zero, map_sub, sub_eq_zero] at h0
  let L : ℂ →ₗ[ℝ] ℂ := c⁻¹ • (Z' ∘ₗ g)
  have hL : ∀ z, ‖L z‖ = ‖z‖ := fun z => by
    simp only [L, LinearMap.smul_apply, LinearMap.comp_apply, norm_smul, h, hgZ, norm_inv,
      Real.norm_of_nonneg hc.le]
    rw [inv_mul_cancel_left₀ hc.ne']
  refine ⟨(⟨L, hL⟩ : ℂ →ₗᵢ[ℝ] ℂ).toLinearIsometryEquiv rfl, fun x => ?_⟩
  simp only [LinearIsometry.toLinearIsometryEquiv_apply, LinearIsometry.coe_mk, L,
    LinearMap.smul_apply, LinearMap.comp_apply, hker, smul_inv_smul₀ hc.ne']

/-- **The central charge from its modulus, explicitly.** In the setting of
`Mukai.exists_linearIsometryEquiv_of_norm_eq`, there is `a` on the unit circle with `Z' = c a Z`
or `Z' = c a Z̄` (`linear_isometry_complex`). -/
theorem exists_circle_of_norm_eq {Z Z' : V →ₗ[ℝ] ℂ} (hZ : Function.Surjective Z) {c : ℝ}
    (hc : 0 < c) (h : ∀ x, ‖Z' x‖ = c * ‖Z x‖) :
    ∃ a : Circle, (∀ x, Z' x = c * a * Z x) ∨ ∀ x, Z' x = c * a * conj (Z x) := by
  obtain ⟨A, hA⟩ := exists_linearIsometryEquiv_of_norm_eq hZ hc h
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex A
  · exact ⟨a, Or.inl fun x => by rw [hA, ha, rotation_apply, Complex.real_smul, mul_assoc]⟩
  · refine ⟨a, Or.inr fun x => ?_⟩
    rw [hA, ha, LinearIsometryEquiv.trans_apply, Complex.conjLIE_apply, rotation_apply,
      Complex.real_smul, mul_assoc]

/-! ### Period recovery -/

/-- The **period form** `x ↦ ‖Z x‖² = (Re Z x)² + (Im Z x)²` of a real-linear charge, a real
quadratic form. -/
def periodForm (Z : V →ₗ[ℝ] ℂ) : QuadraticMap ℝ V ℝ :=
  QuadraticMap.linMulLin (Complex.reLm ∘ₗ Z) (Complex.reLm ∘ₗ Z) +
    QuadraticMap.linMulLin (Complex.imLm ∘ₗ Z) (Complex.imLm ∘ₗ Z)

/-- The period form is the squared modulus. -/
@[simp]
theorem periodForm_apply (Z : V →ₗ[ℝ] ℂ) (x : V) : periodForm Z x = ‖Z x‖ ^ 2 := by
  simp [periodForm, Complex.sq_norm, Complex.normSq_apply]

/-- Period forms in the ratio `c²`, with `c ≥ 0`, give moduli in the ratio `c`. -/
theorem norm_eq_of_periodForm_eq {Z Z' : V →ₗ[ℝ] ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : periodForm Z' = c ^ 2 • periodForm Z) (x : V) : ‖Z' x‖ = c * ‖Z x‖ := by
  have hx := QuadraticMap.congr_fun h x
  rw [smul_apply, periodForm_apply, periodForm_apply, smul_eq_mul, ← mul_pow] at hx
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) two_ne_zero).mp hx

/-- Moduli in the ratio `c` at `x` give period forms in the ratio `c²` at `x`. -/
theorem periodForm_apply_eq_of_norm_eq {Z Z' : V →ₗ[ℝ] ℂ} {c : ℝ} {x : V}
    (h : ‖Z' x‖ = c * ‖Z x‖) : periodForm Z' x = (c ^ 2 • periodForm Z) x := by
  rw [smul_apply, periodForm_apply, periodForm_apply, h, smul_eq_mul, mul_pow]

/-- **Period recovery from `n(n + 1)/2` moduli.** Let `δ` span `V` and `t i j ≠ 0` for `i < j`.
If `‖Z' x‖ = c ‖Z x‖`, with `c > 0`, at every `δ i` and at every `δ j + t i j • δ i` with
`i < j`, and `Z` is surjective, then `Z' = c • A ∘ Z` for a linear isometry `A` of `ℂ`. -/
theorem exists_linearIsometryEquiv_of_norm_eq_add_smul {ι : Type*} [LinearOrder ι] {δ : ι → V}
    (hδ : span ℝ (range δ) = ⊤) {t : ι → ι → ℝ} (ht : ∀ i j, i < j → t i j ≠ 0)
    {Z Z' : V →ₗ[ℝ] ℂ} (hZ : Function.Surjective Z) {c : ℝ} (hc : 0 < c)
    (h₁ : ∀ i, ‖Z' (δ i)‖ = c * ‖Z (δ i)‖)
    (h₂ : ∀ i j, i < j → ‖Z' (δ j + t i j • δ i)‖ = c * ‖Z (δ j + t i j • δ i)‖) :
    ∃ A : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ x, Z' x = c • A (Z x) :=
  exists_linearIsometryEquiv_of_norm_eq hZ hc <| norm_eq_of_periodForm_eq hc.le <|
    QuadraticMap.eq_of_eq_add_smul two_ne_zero hδ ht
      (fun i => periodForm_apply_eq_of_norm_eq (h₁ i))
      fun i j hij => periodForm_apply_eq_of_norm_eq (h₂ i j hij)

/-- **Period recovery** (Kikuta–Koseki–Ouchi, arXiv:2504.12253, Proposition 3.10, the lattice
step). Let `B` be a symmetric bilinear form on `V` and `δ` roots of `B` spanning `V` with
`B(δ i, δ j) ≠ 0` for `i ≠ j`. If `Z` is surjective and `‖Z' x‖ = c ‖Z x‖`, with `c > 0`, for
every root `x`, then `Z' = c • A ∘ Z` for a linear isometry `A` of `ℂ`. -/
theorem exists_linearIsometryEquiv_of_norm_eq_roots {ι : Type*} (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) {δ : ι → V} (hroot : ∀ i, B (δ i) (δ i) = -2)
    (hδ : span ℝ (range δ) = ⊤) (hne : ∀ i j, i ≠ j → B (δ i) (δ j) ≠ 0) {Z Z' : V →ₗ[ℝ] ℂ}
    (hZ : Function.Surjective Z) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, B x x = -2 → ‖Z' x‖ = c * ‖Z x‖) :
    ∃ A : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ x, Z' x = c • A (Z x) :=
  exists_linearIsometryEquiv_of_norm_eq hZ hc <| norm_eq_of_periodForm_eq hc.le <|
    QuadraticMap.eq_of_eq_on_roots two_ne_zero B hB hroot hδ hne fun x hx =>
      periodForm_apply_eq_of_norm_eq (h x hx)

/-- **Period recovery on the Mukai lattice from integral roots.** Let `q` take integer values on
the lattice spanned by a family `e` spanning `N`, with `q(e_{i₀}) ≠ 0`. If `Z` is surjective and
`‖Z' v‖ = c ‖Z v‖`, with `c > 0`, for every root `v` in the lattice spanned by the doubled family,
then `Z' = c • A ∘ Z` for a linear isometry `A` of `ℂ`. The roots used are the doubled family
and its reflections in itself. -/
theorem exists_linearIsometryEquiv_of_norm_eq_doubledLineBundles {N ι : Type*} [AddCommGroup N]
    [Module ℝ N] (q : QuadraticMap ℝ N ℝ) {e : ι → N} (he : span ℝ (range e) = ⊤)
    (hint : ∀ u ∈ span ℤ (range e), ∃ n : ℤ, q u = n) {i₀ : ι} (h₀ : q (e i₀) ≠ 0)
    {Z Z' : MukaiLattice ℝ N →ₗ[ℝ] ℂ} (hZ : Function.Surjective Z) {c : ℝ} (hc : 0 < c)
    (h : ∀ v ∈ span ℤ (range (doubledLineBundles q e i₀)), IsSpherical q.polarBilin v →
      ‖Z' v‖ = c * ‖Z v‖) :
    ∃ A : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ v, Z' v = c • A (Z v) := by
  set δ := doubledLineBundles q e i₀
  have hsph := isSpherical_doubledLineBundles q e i₀
  have hδZ : ∀ k, δ k ∈ span ℤ (range δ) := fun k => subset_span ⟨k, rfl⟩
  refine exists_linearIsometryEquiv_of_norm_eq hZ hc <| norm_eq_of_periodForm_eq hc.le <|
    QuadraticMap.eq_of_eq_reflect two_ne_zero (mukaiForm q.polarBilin)
      (span_doubledLineBundles q two_ne_zero he h₀)
      (fun k l _ => pairing_doubledLineBundles_ne_zero q hint i₀ k l)
      (fun k => periodForm_apply_eq_of_norm_eq (h _ (hδZ k) (hsph k))) fun k l _ => ?_
  have hb : ∀ x y : N, q.polarBilin x y = q.polarBilin y x := fun x y =>
    QuadraticMap.polar_comm q x y
  refine periodForm_apply_eq_of_norm_eq (h _ ?_ ((hsph k).reflect q.polarBilin hb (hsph l)))
  -- the reflection `δ l + ⟪δ l, δ k⟫ δ k` is an integral combination
  obtain ⟨n, hn⟩ := exists_pairing_doubledLineBundles_eq q hint i₀ l k
  rw [BilinearForm.reflect_apply, mukaiForm_apply, hn]
  refine add_mem (hδZ l) ?_
  rw [show ((-4 * n - 2 : ℝ)) = ((-4 * n - 2 : ℤ) : ℝ) by push_cast; ring, Int.cast_smul_eq_zsmul]
  exact zsmul_mem (hδZ k) _

end CentralCharge

end Mukai
