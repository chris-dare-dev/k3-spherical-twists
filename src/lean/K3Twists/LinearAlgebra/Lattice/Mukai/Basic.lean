/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.BilinearForm.Hyperbolic
import K3Twists.LinearAlgebra.Lattice.Arithmetic.TorsionFree
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The Mukai lattice of a bilinear module

Given a module `N` over a commutative ring `R` carrying an `R`-bilinear form `b`,
the **Mukai lattice** of `(N, b)` is `MukaiLattice R N = R × N × R` with

```
⟪(r, c, s), (r', c', s')⟫ = b c c' - r * s' - r' * s,
```

bundled as the bilinear form `Mukai.mukaiForm b`. It is the one Mukai lattice of
the library: the integral lattice of a K3 surface is `MukaiLattice ℤ NS`, the
complexified one used for central charges is `MukaiLattice ℂ (NS ⊗ ℂ)`, and the
Picard-rank-one lattice `MukaiVector R` is `MukaiLattice R R` with
`b x y = 2dxy` (`Lattice/Mukai/Slice.lean`).

**This is not the Mukai lattice of a K3 surface.** It is the abstract lattice
that lattice is an instance of. Taking `N = NS(X)` with the intersection form
recovers the algebraic Mukai lattice `H⁰ ⊕ NS ⊕ H⁴`, but that identification
needs `D^b(Coh X)`, Chern characters and Hirzebruch–Riemann–Roch, none of which
exist in Mathlib at the pin. It is geometry, and nothing here asserts it,
discharges it or depends on it.

Every theorem below is a theorem about **an arbitrary bilinear module over a
commutative ring**, and is true whether or not any surface exists.

## Naming

`expectedDim v = ⟪v, v⟫ + 2` is a **definition**, not the Mukai dimension
theorem. The statement that a moduli space of stable objects with primitive
Mukai vector `v` has dimension `⟪v, v⟫ + 2` is geometry and is not asserted.
The name records which numerical quantity is being tracked, nothing more.

## Main definitions

* `MukaiLattice R N` — the carrier `R × N × R`.
* `Mukai.mukaiForm b` — the Mukai pairing as a bundled `R`-bilinear form; its
  value is `Mukai.pairing b` by `rfl`.

## Main results

* `pairing_comm` — the lattice is symmetric when `b` is.
* `even_selfPairing` — the Mukai lattice of an even lattice is even.
* `pairing_rankUnit_corankUnit` — the rank/co-rank plane is a hyperbolic plane:
  two isotropic generators pairing to `-1`.

## Deprecated names

`Mukai.MukaiLattice N` was the integral carrier `ℤ × N × ℤ` and
`Mukai.pairingBilin` its bundled form over `ℤ`; they are deprecated aliases of
`MukaiLattice ℤ N` and `Mukai.mukaiForm`.
-/

/-- The carrier of the Mukai lattice of an `R`-module `N`: triples `(r, c, s)`, read as
rank, first Chern class and `ch₂ + r` in the K3 case.

The name is suggestive of the K3 case; the module docstring records that the
identification with any geometric lattice is **not** made here. -/
abbrev MukaiLattice (R N : Type*) : Type _ := R × N × R

namespace Mukai

/-- The integral Mukai lattice `ℤ × N × ℤ`. -/
@[deprecated MukaiLattice +typeChanged (since := "2026-11-25")]
protected abbrev MukaiLattice (N : Type*) : Type _ := _root_.MukaiLattice ℤ N

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
variable (b : N →ₗ[R] N →ₗ[R] R)

/-! ### Bilinearity

Proved directly from the definition rather than inherited, so that every
downstream rewrite has a named lemma to hit.

`linter.unusedSimpArgs` is disabled for this section, and the suppression is
load-bearing rather than cosmetic. It flags `LinearMap.add_apply` and its
siblings in the four *left*-hand lemmas as unused; removing them on that advice
makes all four fail. The reason is asymmetry in the definition: on the right,
`b u.2.1 (v.2.1 + w.2.1)` is closed by `map_add` on the applied form alone,
whereas on the left `b (u.2.1 + v.2.1) w.2.1` first becomes `(b u.2.1 + b v.2.1) w.2.1`
and needs `LinearMap.add_apply` to reach a goal `ring` can see. The linter
judges the `simp only` call in isolation and does not know a `ring` follows it.
Re-check this if the pin moves; do not delete the arguments on the warning
alone. -/

set_option linter.unusedSimpArgs false in
theorem pairing_add_left (u v w : MukaiLattice R N) :
    pairing b (u + v) w = pairing b u w + pairing b v w := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
  ring

theorem pairing_add_right (u v w : MukaiLattice R N) :
    pairing b u (v + w) = pairing b u v + pairing b u w := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, map_add]
  ring

set_option linter.unusedSimpArgs false in
theorem pairing_smul_left (a : R) (v w : MukaiLattice R N) :
    pairing b (a • v) w = a * pairing b v w := by
  simp only [pairing, Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  ring

theorem pairing_smul_right (a : R) (v w : MukaiLattice R N) :
    pairing b v (a • w) = a * pairing b v w := by
  simp only [pairing, Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul]
  ring

set_option linter.unusedSimpArgs false in
theorem pairing_neg_left (v w : MukaiLattice R N) :
    pairing b (-v) w = -pairing b v w := by
  simp only [pairing, Prod.fst_neg, Prod.snd_neg, map_neg, LinearMap.neg_apply]
  ring

theorem pairing_neg_right (v w : MukaiLattice R N) :
    pairing b v (-w) = -pairing b v w := by
  simp only [pairing, Prod.fst_neg, Prod.snd_neg, map_neg]
  ring

set_option linter.unusedSimpArgs false in
theorem pairing_sub_left (u v w : MukaiLattice R N) :
    pairing b (u - v) w = pairing b u w - pairing b v w := by
  simp only [pairing, Prod.fst_sub, Prod.snd_sub, map_sub, LinearMap.sub_apply]
  ring

theorem pairing_sub_right (u v w : MukaiLattice R N) :
    pairing b u (v - w) = pairing b u v - pairing b u w := by
  simp only [pairing, Prod.fst_sub, Prod.snd_sub, map_sub]
  ring

@[simp]
theorem pairing_zero_left (w : MukaiLattice R N) : pairing b 0 w = 0 := by
  simp [pairing]

@[simp]
theorem pairing_zero_right (v : MukaiLattice R N) : pairing b v 0 = 0 := by
  simp [pairing]

/-! ### The quadratic refinement

`selfPairing` itself lives in `BilinearForm/Hyperbolic.lean`; these are the
lattice facts about it. -/

theorem selfPairing_smul (a : R) (v : MukaiLattice R N) :
    selfPairing b (a • v) = a ^ 2 * selfPairing b v := by
  simp only [selfPairing_eq_pairing, pairing_smul_left, pairing_smul_right]
  ring

@[simp]
theorem selfPairing_zero : selfPairing b (0 : MukaiLattice R N) = 0 := by
  simp [selfPairing_eq_pairing]

theorem selfPairing_neg (v : MukaiLattice R N) :
    selfPairing b (-v) = selfPairing b v := by
  simp only [selfPairing_eq_pairing, pairing_neg_left, pairing_neg_right, neg_neg]

/-- The Mukai extension of an **even** lattice is even.

For a K3 surface the intersection form on `NS(X)` is even, and this is the
lattice-theoretic reason `⟪v, v⟫` is always even there. The hypothesis is
stated, never assumed from geometry. -/
theorem even_selfPairing (heven : ∀ x : N, Even (b x x)) (v : MukaiLattice R N) :
    Even (selfPairing b v) := by
  obtain ⟨k, hk⟩ := heven v.2.1
  refine ⟨k - v.1 * v.2.2, ?_⟩
  simp only [selfPairing, pairing, hk]
  ring

/-! ### Distinguished classes

`IsSpherical` and `IsIsotropic` are the two numerical conditions the
wall-classification literature is organised around. Both are conditions on a
lattice vector alone. -/

/-- `⟪v, v⟫ = -2`. In the K3 case these are the classes of spherical objects;
here it is a numerical condition and nothing more. -/
def IsSpherical (v : MukaiLattice R N) : Prop := selfPairing b v = -2

/-- `⟪v, v⟫ = 0`. -/
def IsIsotropic (v : MukaiLattice R N) : Prop := selfPairing b v = 0

theorem isSpherical_iff (v : MukaiLattice R N) :
    IsSpherical b v ↔ selfPairing b v = -2 := Iff.rfl

theorem isIsotropic_iff (v : MukaiLattice R N) :
    IsIsotropic b v ↔ selfPairing b v = 0 := Iff.rfl

theorem IsSpherical.neg {v : MukaiLattice R N} (h : IsSpherical b v) :
    IsSpherical b (-v) := by
  rw [IsSpherical, selfPairing_neg]; exact h

theorem IsIsotropic.neg {v : MukaiLattice R N} (h : IsIsotropic b v) :
    IsIsotropic b (-v) := by
  rw [IsIsotropic, selfPairing_neg]; exact h

/-- No class is both spherical and isotropic, once `2 ≠ 0` (over `ℤ`, say). In
characteristic two `-2 = 0` and every isotropic class is spherical. -/
theorem not_isSpherical_and_isIsotropic [NeZero (2 : R)] (v : MukaiLattice R N) :
    ¬(IsSpherical b v ∧ IsIsotropic b v) := by
  rintro ⟨hs, hi⟩
  rw [IsSpherical, hi, zero_eq_neg] at hs
  exact two_ne_zero hs

/-- The numerical quantity `⟪v, v⟫ + 2`.

**A definition, not the Mukai dimension theorem.** See the module docstring. -/
def expectedDim (v : MukaiLattice R N) : R := selfPairing b v + 2

theorem expectedDim_eq_zero_iff (v : MukaiLattice R N) :
    expectedDim b v = 0 ↔ IsSpherical b v := by
  rw [expectedDim, IsSpherical, add_eq_zero_iff_eq_neg]

theorem expectedDim_eq_two_iff (v : MukaiLattice R N) :
    expectedDim b v = 2 ↔ IsIsotropic b v := by
  rw [expectedDim, IsIsotropic, add_eq_right]

/-! ### The hyperbolic plane in the rank / co-rank coordinates

The two outer summands span a copy of the hyperbolic plane `U`, independently
of `b`. This is the lattice-theoretic content of "the Mukai lattice contains
`H⁰ ⊕ H⁴`". -/

/-- `(1, 0, 0)`. -/
def rankUnit : MukaiLattice R N := (1, 0, 0)

/-- `(0, 0, 1)`. -/
def corankUnit : MukaiLattice R N := (0, 0, 1)

/-- Not `@[simp]`: `pairing_mk` together with `map_zero` already puts the
left-hand side in normal form, and marking this would fail `simpNF`. It is kept
as a readable statement of the outer-plane pairing. -/
theorem pairing_outer (r s r' s' : R) :
    pairing b ((r, (0 : N), s)) ((r', (0 : N), s')) = -(r * s' + r' * s) := by
  simp [pairing]
  ring

theorem isIsotropic_rankUnit : IsIsotropic b (rankUnit : MukaiLattice R N) := by
  simp [IsIsotropic, selfPairing_eq_pairing, rankUnit]

theorem isIsotropic_corankUnit : IsIsotropic b (corankUnit : MukaiLattice R N) := by
  simp [IsIsotropic, selfPairing_eq_pairing, corankUnit]

/-- The two isotropic generators pair to `-1`: the outer plane is hyperbolic. -/
theorem pairing_rankUnit_corankUnit :
    pairing b (rankUnit : MukaiLattice R N) corankUnit = -1 := by
  simp [rankUnit, corankUnit, pairing]

/-! ### Bundled form

The pairing packaged as an `R`-bilinear form, for use with Mathlib's
bilinear/quadratic-form API. -/

/-- **The Mukai form** `⟪(r, c, s), (r', c', s')⟫ = b c c' - r * s' - r' * s` on
`MukaiLattice R N`, as a bundled `R`-bilinear form. -/
def mukaiForm : LinearMap.BilinForm R (MukaiLattice R N) :=
  LinearMap.mk₂ R (pairing b)
    (pairing_add_left b)
    (fun a v w => by rw [pairing_smul_left, smul_eq_mul])
    (pairing_add_right b)
    (fun a v w => by rw [pairing_smul_right, smul_eq_mul])

@[simp]
theorem mukaiForm_apply (v w : MukaiLattice R N) :
    mukaiForm b v w = pairing b v w :=
  rfl

theorem mukaiForm_comm (hb : ∀ x y : N, b x y = b y x) (v w : MukaiLattice R N) :
    mukaiForm b v w = mukaiForm b w v :=
  pairing_comm b hb v w

theorem mukaiForm_self (v : MukaiLattice R N) : mukaiForm b v v = selfPairing b v :=
  rfl

@[deprecated (since := "2026-11-25")] alias pairingBilin := mukaiForm

@[deprecated (since := "2026-11-25")] alias pairingBilin_apply := mukaiForm_apply

end Mukai
