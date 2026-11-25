/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.BilinearForm.Reflection
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Eichler transvections and products of two reflections

For a module `M` over a commutative ring `R` with a bilinear form `B`, the **Eichler
transvection** at `e` with direction `x` and parameter `q` is

```
E(e, x, q)(v) = v + B(v, e) x - B(v, x) e - q B(v, e) e.
```

When `B` is symmetric, `e` is isotropic, `x ⊥ e` and `2q = B(x, x)`, it is an isometry
(`eichler_isometry`), unipotent of index at most three (`eichler_sub_one_pow_three`), and the maps
at one `e` compose by `E(e, x, q) E(e, y, q') = E(e, x + y, q + q' + B(x, y))` (`eichler_mul`).
The parameter `q` stands for `B(x, x)/2` and is free so that no `1/2` is needed; with a quadratic
form `Q` the choice `q = Q(x)` is forced (`eichlerQ`), and `x ↦ E(e, x, Q x)` is a group
homomorphism from `e^⊥` to the automorphisms of `M`, landing in isometries (`eichlerHom`,
`eichlerQ_isometry`). It descends to `e^⊥/Re` when `Q e = 0` (`eichlerQ_add_smul`); in
characteristic two `B(e, e) = 0` does not suffice (a test). Injectivity, hence an isomorphism with
`e^⊥/Re`, is not claimed.

## The convention

`E(e, x, q)(v) = v + B(v, e) x - B(v, x) e - q B(v, e) e`, with `B(v, e)` first. In the Mukai
lattice, tensoring with a line bundle is `⊗𝒪(D) = E(pt, (0, -D, 0), D²/2)` at the class
`pt = (0, 0, 1)` of a point (`Mukai.tensorLine_eq_eichler`).

## Products of two reflections

The reflection `ρ_s(v) = v + B(v, s) s` of `BilinearForm/Reflection.lean` gives, for any `a`, `b`:

* **Pairing two.** `ρ_b ρ_a = E(a + b, b, -1)` as soon as `B(a, b) = 2`; neither sphericity nor
  symmetry is used (`reflectHom_mul_reflectHom_of_apply_eq_two`).
* **The pair law.** `ρ_{a + kδ} ρ_a = E(δ, k a, -k²)` for `B(a, a) = -2` and `B(a, δ) = 0`; `δ` need
  not be isotropic (`reflectHom_add_smul_mul_reflectHom`). At `k = -1` it is the translation
  `ρ_{δ - a} ρ_a = E(δ, -a, -1)` of an affine Weyl group by a root `a` orthogonal to the null root
  `δ` (`reflectHom_sub_mul_reflectHom`).
* **One cubic at every pairing.** For spherical `a`, `b` and symmetric `B`, with `g = B(a, b)`,
  `T = ρ_b ρ_a` satisfies `(T - 1)(T² - (g² - 2) T + 1) = 0` on all of `M`
  (`reflectHom_mul_reflectHom_cubic`). At `g = ±2` the product is unipotent with powers quadratic
  in `n` (`reflectHom_mul_reflectHom_pow`). An annihilating polynomial does not show that the
  quadratic factor acts nontrivially, so exponential growth at `|g| ≥ 3` is not claimed here.

## Main results

* `eichler_add_smul` — `E(e, x + te, q) = E(e, x, q)`, with no hypothesis.
* `eichler_smul_left` — `E(te, x, q) = E(e, tx, t²q)`.
* `eichler_mul` — the group law at an isotropic `e`.
* `eichler_isometry` — `E(e, x, q)` preserves `B` when `2q = B(x, x)` (one direction only: the
  converse fails when `B(·, e) = 0`).
* `eichler_pow` — `E(e, x, q)ⁿ = E(e, nx, n²q)` when `2q = B(x, x)`; without it the power is
  `E(e, nx, nq + C(n, 2) B(x, x))` (`eichler_pow_eq`).
* `eichler_sub_one_sq_apply`, `eichler_sub_one_pow_three` — `E - 1` is nilpotent of index three.
* `conj_eichler` — `g E(e, x, q) g⁻¹ = E(ge, gx, q)` for an isometry `g`.
* `eichlerQ_mul`, `eichlerQ_isometry`, `map_eichlerQ`, `eichlerQ_add_smul`, `eichlerHom` — the
  quadratic-form version and the Eichler homomorphism at `e`.

## References

M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Springer, 1952, for the
transvections; V. G. Kac, *Infinite dimensional Lie algebras*, §6.5, for the translations of an
affine Weyl group.
-/

namespace BilinearForm

open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : M →ₗ[R] M →ₗ[R] R)

/-! ### The transvection -/

/-- The Eichler transvection `E(e, x, q)(v) = v + B(v, e) x - B(v, x) e - q B(v, e) e`. It is the
transvection of the isotropic vector `e` in the direction `x` when `B` is symmetric, `e` is
isotropic, `x ⊥ e` and `2q = B(x, x)`; it is defined for all data. -/
def eichler (e x : M) (q : R) : Module.End R M :=
  LinearMap.id + (B.flip e).smulRight x - (B.flip x).smulRight e - q • (B.flip e).smulRight e

theorem eichler_apply (e x : M) (q : R) (v : M) :
    eichler B e x q v = v + B v e • x - B v x • e - (q * B v e) • e := by
  simp [eichler, mul_smul]

@[simp]
theorem eichler_zero_zero (e : M) : eichler B e 0 0 = 1 := by
  ext v
  simp [eichler_apply]

/-- The direction only matters modulo `e`. No hypothesis. -/
theorem eichler_add_smul (e x : M) (q t : R) : eichler B e (x + t • e) q = eichler B e x q := by
  ext v
  simp only [eichler_apply, map_add, map_smul, smul_eq_mul]
  module

/-- Rescaling the isotropic vector: `E(te, x, q) = E(e, tx, t²q)`. No hypothesis. -/
theorem eichler_smul_left (e x : M) (q t : R) :
    eichler B (t • e) x q = eichler B e (t • x) (t ^ 2 * q) := by
  ext v
  simp only [eichler_apply, map_smul, smul_eq_mul]
  module

/-- **The group law** at an isotropic `e`: `E(e, x, q) E(e, y, q') = E(e, x + y, q + q' + B(x, y))`
for symmetric `B` and `x, y ⊥ e`. -/
theorem eichler_mul (hB : ∀ x y, B x y = B y x) {e x y : M} (he : B e e = 0) (hx : B x e = 0)
    (hy : B y e = 0) (q q' : R) :
    eichler B e x q * eichler B e y q' = eichler B e (x + y) (q + q' + B x y) := by
  have hex : B e x = 0 := by rw [hB]; exact hx
  have hey : B e y = 0 := by rw [hB]; exact hy
  have hyx : B y x = B x y := hB y x
  ext v
  simp only [mul_apply_eq_comp, eichler_apply, map_add, map_sub, map_smul, he, hy, hex, hyx,
    mul_zero]
  module

/-- **`E(e, x, q)` is an isometry** when `B` is symmetric, `e` is isotropic, `x ⊥ e` and
`2q = B(x, x)`. Only this direction holds: when `B(·, e) = 0` every `E(e, x, q)` is the identity,
an isometry for every `q`. -/
theorem eichler_isometry (hB : ∀ x y, B x y = B y x) {e x : M} (he : B e e = 0)
    (hx : B x e = 0) {q : R} (hq : 2 * q = B x x) (v w : M) :
    B (eichler B e x q v) (eichler B e x q w) = B v w := by
  have hex : B e x = 0 := by rw [hB]; exact hx
  have h1 := hB e w
  have h2 := hB x w
  simp only [eichler_apply, map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, he, hx, hex, h1, h2]
  linear_combination (-(B v e * B w e)) * hq

/-- `E(e, x, q)` and `E(e, -x, q)` are inverse when `2q = B(x, x)`. -/
theorem eichler_mul_eichler_neg (hB : ∀ x y, B x y = B y x) {e x : M} (he : B e e = 0)
    (hx : B x e = 0) {q : R} (hq : 2 * q = B x x) :
    eichler B e x q * eichler B e (-x) q = 1 := by
  rw [eichler_mul B hB he hx (by rw [map_neg, LinearMap.neg_apply, hx, neg_zero]), add_neg_cancel,
    map_neg, show q + q + -B x x = 2 * q - B x x by ring, hq, sub_self, eichler_zero_zero]

/-! ### Powers and unipotence -/

/-- **Powers in general**: `E(e, x, q)ⁿ = E(e, nx, nq + C(n, 2) B(x, x))`. -/
theorem eichler_pow_eq (hB : ∀ x y, B x y = B y x) {e x : M} (he : B e e = 0) (hx : B x e = 0)
    (q : R) (n : ℕ) :
    eichler B e x q ^ n = eichler B e ((n : R) • x) (n * q + (n.choose 2 : R) * B x x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnx : B ((n : R) • x) e = 0 := by simp [hx]
    rw [pow_succ, ih, eichler_mul B hB he hnx hx]
    congr 1
    · push_cast
      module
    · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Nat.choose_succ_succ',
        Nat.choose_one_right]
      push_cast
      ring

/-- **Powers**: `E(e, x, q)ⁿ = E(e, nx, n²q)` when `2q = B(x, x)`. The hypothesis is needed: with
`x = 0` the power is `E(e, 0, nq)`. -/
theorem eichler_pow (hB : ∀ x y, B x y = B y x) {e x : M} (he : B e e = 0)
    (hx : B x e = 0) {q : R} (hq : 2 * q = B x x) (n : ℕ) :
    eichler B e x q ^ n = eichler B e ((n : R) • x) ((n : R) ^ 2 * q) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnx : B ((n : R) • x) e = 0 := by simp [hx]
    rw [pow_succ, ih, eichler_mul B hB he hnx hx]
    congr 1
    · push_cast
      module
    · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      push_cast
      linear_combination (-(n : R)) * hq

/-- **Unipotence.** `(E - 1)² v = -B(x, x) B(v, e) e`, for `e` isotropic and `x ⊥ e` on both
sides; no symmetry and no condition on `q`. -/
theorem eichler_sub_one_sq_apply {e x : M} (he : B e e = 0) (hx : B x e = 0)
    (hex : B e x = 0) (q : R) (v : M) :
    ((eichler B e x q - 1 : Module.End R M) ^ 2) v = -(B x x * B v e) • e := by
  rw [sq, mul_apply_eq_comp]
  simp only [LinearMap.sub_apply, one_apply_eq_self, eichler_apply, map_add, map_sub,
    map_smul, he, hx, hex]
  module

/-- **`E - 1` is nilpotent of index at most three.** -/
theorem eichler_sub_one_pow_three {e x : M} (he : B e e = 0) (hx : B x e = 0)
    (hex : B e x = 0) (q : R) : (eichler B e x q - 1 : Module.End R M) ^ 3 = 0 := by
  ext v
  rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one, mul_apply_eq_comp,
    eichler_sub_one_sq_apply B he hx hex]
  simp [eichler_apply, he, hex]

/-! ### Conjugation -/

/-- **Conjugation.** For an isometric automorphism `g`, `g E(e, x, q) g⁻¹ = E(ge, gx, q)`. -/
theorem conj_eichler (g : M ≃ₗ[R] M) (hg : ∀ u v, B (g u) (g v) = B u v) (e x : M) (q : R) :
    g.conj (eichler B e x q) = eichler B (g e) (g x) q := by
  ext v
  have h1 : B v (g e) = B (g.symm v) e := by rw [← hg (g.symm v) e, g.apply_symm_apply]
  have h2 : B v (g x) = B (g.symm v) x := by rw [← hg (g.symm v) x, g.apply_symm_apply]
  simp only [LinearEquiv.conj_apply_apply, eichler_apply, map_add, map_sub, map_smul,
    g.apply_symm_apply, h1, h2]

/-! ### Products of two reflections -/

/-- **Two reflections at pairing two** are an Eichler transvection: `ρ_b ρ_a = E(a + b, b, -1)`.
Only `B(a, b) = 2` is used: neither `B(a, a) = -2`, nor `B(b, b) = -2`, nor symmetry. -/
theorem reflectHom_mul_reflectHom_of_apply_eq_two {a b : M} (hab : B a b = 2) :
    reflectHom B b * reflectHom B a = eichler B (a + b) b (-1) := by
  ext v
  simp only [mul_apply_eq_comp, reflectHom_apply, reflect_apply, eichler_apply, map_add,
    map_smul, hab]
  module

@[simp]
theorem reflectHom_neg (s : M) : reflectHom B (-s) = reflectHom B s := by
  ext v
  simp

/-- **The pair law.** For `B(a, a) = -2` and `B(a, δ) = 0`, `ρ_{a + kδ} ρ_a = E(δ, k a, -k²)`.
Neither symmetry nor isotropy of `δ` is used. -/
theorem reflectHom_add_smul_mul_reflectHom {a δ : M} (ha : B a a = -2) (haδ : B a δ = 0)
    (k : R) : reflectHom B (a + k • δ) * reflectHom B a = eichler B δ (k • a) (-k ^ 2) := by
  have h : B a (-(a + k • δ)) = 2 := by
    simp only [map_neg, map_add, map_smul, ha, haδ, smul_eq_mul, mul_zero, add_zero, neg_neg]
  rw [← reflectHom_neg B (a + k • δ), reflectHom_mul_reflectHom_of_apply_eq_two B h,
    show a + -(a + k • δ) = (-k) • δ by module, eichler_smul_left,
    show (-k) • -(a + k • δ) = k • a + k ^ 2 • δ by module, eichler_add_smul]
  congr 1
  ring

/-- **Affine translations**: for a root `a` with `B(a, δ) = 0`, `ρ_{δ - a} ρ_a = E(δ, -a, -1)`, the
translation by `a` in the affine Weyl group at the null root `δ`. -/
theorem reflectHom_sub_mul_reflectHom {a δ : M} (ha : B a a = -2) (haδ : B a δ = 0) :
    reflectHom B (δ - a) * reflectHom B a = eichler B δ (-a) (-1) := by
  rw [← reflectHom_neg B (δ - a), show -(δ - a) = a + (-1 : R) • δ by module,
    reflectHom_add_smul_mul_reflectHom B ha haδ, neg_one_smul]
  congr 1
  ring

/-- **One cubic at every pairing.** For spherical `a`, `b` and symmetric `B`, with `g = B(a, b)`,
the product `T = ρ_b ρ_a` satisfies `(T - 1)(T² - (g² - 2)T + 1) = 0` on all of `M`. -/
theorem reflectHom_mul_reflectHom_cubic (hB : ∀ x y, B x y = B y x) {a b : M}
    (ha : B a a = -2) (hb : B b b = -2) :
    (reflectHom B b * reflectHom B a - 1) *
        ((reflectHom B b * reflectHom B a) ^ 2 - (B a b ^ 2 - 2) • (reflectHom B b * reflectHom B a)
          + 1) = 0 := by
  set T := reflectHom B b * reflectHom B a with hT
  have hba : B b a = B a b := hB b a
  have key : ∀ v, T (T (T v)) - (B a b ^ 2 - 1) • T (T v) + (B a b ^ 2 - 1) • T v - v = 0 := by
    intro v
    simp only [hT, mul_apply_eq_comp, reflectHom_apply, reflect_apply, map_add, map_smul, ha, hb,
      hba]
    module
  ext v
  rw [LinearMap.zero_apply, ← key v]
  simp only [mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    one_apply_eq_self, sq, map_sub, map_add, map_smul]
  module

/-- **Unipotent powers at pairing two**: for spherical `a`, `b` with `B(a, b) = 2` and symmetric
`B`, `(ρ_b ρ_a)ⁿ = E(a + b, nb, -n²)`, quadratic in `n`. -/
theorem reflectHom_mul_reflectHom_pow (hB : ∀ x y, B x y = B y x) {a b : M} (ha : B a a = -2)
    (hb : B b b = -2) (hab : B a b = 2) (n : ℕ) :
    (reflectHom B b * reflectHom B a) ^ n = eichler B (a + b) ((n : R) • b) (-(n : R) ^ 2) := by
  have hba : B b a = 2 := by rw [hB]; exact hab
  have he : B (a + b) (a + b) = 0 := by
    simp only [map_add, LinearMap.add_apply, ha, hb, hab, hba]
    norm_num
  have hx : B b (a + b) = 0 := by
    simp only [map_add, hba, hb]
    norm_num
  rw [reflectHom_mul_reflectHom_of_apply_eq_two B hab, eichler_pow B hB he hx (by rw [hb]; ring)]
  congr 1
  ring

/-- The same at pairing `-2`: `(ρ_b ρ_a)ⁿ = E(a - b, -nb, -n²)`, since `ρ_b = ρ_{-b}`. -/
theorem reflectHom_mul_reflectHom_pow_of_apply_eq_neg_two (hB : ∀ x y, B x y = B y x) {a b : M}
    (ha : B a a = -2) (hb : B b b = -2) (hab : B a b = -2) (n : ℕ) :
    (reflectHom B b * reflectHom B a) ^ n = eichler B (a - b) (-((n : R) • b)) (-(n : R) ^ 2) := by
  rw [← reflectHom_neg B b, reflectHom_mul_reflectHom_pow B hB ha (by simpa using hb)
    (by simp [hab]) n, sub_eq_add_neg, smul_neg]

/-- At pairing `±2` the product of two reflections is unipotent of index at most three. -/
theorem reflectHom_mul_reflectHom_sub_one_pow_three (hB : ∀ x y, B x y = B y x) {a b : M}
    (ha : B a a = -2) (hb : B b b = -2) (hab : B a b = 2) :
    (reflectHom B b * reflectHom B a - 1) ^ 3 = 0 := by
  have hba : B b a = 2 := by rw [hB]; exact hab
  have he : B (a + b) (a + b) = 0 := by
    simp only [map_add, LinearMap.add_apply, ha, hb, hab, hba]
    norm_num
  have hx : B b (a + b) = 0 := by
    simp only [map_add, hba, hb]
    norm_num
  rw [reflectHom_mul_reflectHom_of_apply_eq_two B hab]
  exact eichler_sub_one_pow_three B he hx (by rw [hB]; exact hx) _

/-! ### The quadratic-form version and the Eichler homomorphism -/

section Quadratic

variable (Q : QuadraticForm R M)

/-- The Eichler transvection of a quadratic form: `E_Q(e, x) = E(e, x, Q x)` for the polar form,
so that the parameter is `B(x, x)/2` with no division. -/
def eichlerQ (e x : M) : Module.End R M :=
  eichler Q.polarBilin e x (Q x)

theorem eichlerQ_apply (e x v : M) :
    eichlerQ Q e x v =
      v + QuadraticMap.polar Q v e • x - QuadraticMap.polar Q v x • e -
        (Q x * QuadraticMap.polar Q v e) • e :=
  eichler_apply _ e x (Q x) v

@[simp]
theorem eichlerQ_zero (e : M) : eichlerQ Q e 0 = 1 := by
  rw [eichlerQ, QuadraticMap.map_zero, eichler_zero_zero]

variable {Q}

/-- **Multiplicativity**: `E_Q(e, x) E_Q(e, y) = E_Q(e, x + y)` for `x, y ⊥ e`, `e` isotropic for
the polar form. -/
theorem eichlerQ_mul {e x y : M} (he : Q.polarBilin e e = 0) (hx : Q.polarBilin x e = 0)
    (hy : Q.polarBilin y e = 0) : eichlerQ Q e x * eichlerQ Q e y = eichlerQ Q e (x + y) := by
  rw [eichlerQ, eichlerQ, eichlerQ,
    eichler_mul _ (fun a b => QuadraticMap.polar_comm Q a b) he hx hy]
  congr 1
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  ring

/-- `E_Q(e, x)` preserves the polar form. -/
theorem eichlerQ_isometry {e x : M} (he : Q.polarBilin e e = 0) (hx : Q.polarBilin x e = 0)
    (v w : M) :
    Q.polarBilin (eichlerQ Q e x v) (eichlerQ Q e x w) = Q.polarBilin v w :=
  eichler_isometry _ (fun a b => QuadraticMap.polar_comm Q a b) he hx
    (by simp [QuadraticMap.polar_self, two_smul, two_mul]) v w

/-- `E_Q(e, x)` preserves `Q` itself when `Q e = 0`. -/
theorem map_eichlerQ {e x : M} (hQe : Q e = 0) (hx : QuadraticMap.polar Q x e = 0) (v : M) :
    Q (eichlerQ Q e x v) = Q v := by
  have hex : QuadraticMap.polar Q e x = 0 := by rw [QuadraticMap.polar_comm]; exact hx
  set a := QuadraticMap.polar Q v e
  set c := QuadraticMap.polar Q v x
  rw [eichlerQ_apply, show v + a • x - c • e - (Q x * a) • e = v + (a • x + (-(c + Q x * a)) • e)
    by module, QuadraticMap.map_add (⇑Q), QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul,
    QuadraticMap.map_smul, hQe, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
    hx]
  simp only [smul_eq_mul]
  ring

/-- **Descent to `e^⊥/Re`.** When `Q e = 0`, `E_Q(e, x + te) = E_Q(e, x)` for `x ⊥ e`. In
characteristic two `B(e, e) = 2Q(e) = 0` does not give `Q e = 0`, and the descent fails. -/
theorem eichlerQ_add_smul {e x : M} (hQe : Q e = 0) (hx : Q.polarBilin x e = 0) (t : R) :
    eichlerQ Q e (x + t • e) = eichlerQ Q e x := by
  unfold eichlerQ
  have hQ : Q (x + t • e) = Q x := by
    rw [QuadraticMap.map_add Q x (t • e), QuadraticMap.map_smul, hQe,
      QuadraticMap.polar_smul_right]
    simp only [QuadraticMap.polarBilin_apply_apply] at hx
    rw [hx]
    simp
  rw [hQ, eichler_add_smul]

variable (Q) in
/-- **The Eichler homomorphism** at a class `e` isotropic for the polar form: `x ↦ E_Q(e, x)` is
a group homomorphism from the orthogonal complement `e^⊥` to the units of `End M`, and each
`E_Q(e, x)` is an isometry of the polar form (`eichlerQ_isometry`). It is not claimed to be
injective. -/
def eichlerHom (e : M) (he : Q.polarBilin e e = 0) :
    Multiplicative (LinearMap.ker (Q.polarBilin.flip e)) →* (Module.End R M)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun x => eichlerQ Q e (Multiplicative.toAdd x).1
      map_one' := by simp
      map_mul' := fun x y => by
        have hx : Q.polarBilin (Multiplicative.toAdd x).1 e = 0 := (Multiplicative.toAdd x).2
        have hy : Q.polarBilin (Multiplicative.toAdd y).1 e = 0 := (Multiplicative.toAdd y).2
        rw [toAdd_mul, Submodule.coe_add, eichlerQ_mul he hx hy] }

@[simp]
theorem coe_eichlerHom_apply (e : M) (he : Q.polarBilin e e = 0)
    (x : Multiplicative (LinearMap.ker (Q.polarBilin.flip e))) :
    (eichlerHom Q e he x : Module.End R M) = eichlerQ Q e (Multiplicative.toAdd x).1 :=
  rfl

end Quadratic

end BilinearForm
