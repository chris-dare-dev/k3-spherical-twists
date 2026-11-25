/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Data.Int.Interval
import Mathlib.Data.Pi.Interval
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.LinearAlgebra.RootSystem.BaseChange
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-!
# The kernel root system

For a symmetric bilinear form `B` on a module `M`, the reflection in a `(-2)`-vector `r` is
`s ↦ s + B(r, s) r`. This file builds the root pairings of `(-2)`-vectors, with roots `r` and
coroots `-B(r, ·)`, and the root system of a stratum of the root arrangement of a Mukai lattice.

## The general construct

* `pairingOfClosed`: over any commutative ring, a set `Φ` of `(-2)`-vectors closed under the
  reflections `s ↦ s + B(r, s) r` and separated by `B` is a `RootPairing Φ R M (Dual R M)`. It is
  built with the raw constructor: `RootPairing.mk'` asks for finitely many roots, and an
  indefinite lattice such as the Mukai lattice has infinitely many. `pairingOfClosed_isReduced`:
  over `ℤ` it is reduced, with no definiteness.
* `sphericalPairing`: the instance at all `(-2)`-vectors of a nondegenerate symmetric
  `ℤ`-lattice, indefinite ones included; closure under reflections needs only integrality.

## Definite lattices

On a negative-definite finitely generated lattice the pairing is finite (integer
Cauchy–Schwarz against a finite generating set, `sq_le_mul`, `finite_setOf_neg_le`) and simply
laced: two distinct non-opposite roots pair to `-1`, `0` or `1` (`pairing_mem`). Together:
`sphericalPairing_finite_isReduced_simplyLaced`, a finite, reduced, simply laced root pairing.
Over `ℤ` every root pairing is crystallographic, so that property carries no content here.

For a base of it the Cartan matrix is simply laced in Mathlib's sense
(`cartanMatrix_isSimplyLaced`, `Matrix.IsSimplyLaced`) and positive definite
(`cartanMatrix_pos`): it is minus the Gram matrix of linearly independent roots of a
negative-definite lattice. The classification of such matrices as `ADE` is a theorem of the
literature (Bourbaki, *Groupes et algèbres de Lie*, chapitre VI), not formalized: Mathlib has no
classification of simply laced Dynkin diagrams.

## Not a root system over `ℤ`, a root system over `ℚ`

Over `ℤ` the pairing is not a Mathlib `RootPairing.IsRootSystem` in general: for `A₁` the
coroots span `2ℤ`, not the dual (`K3TwistsTest/KernelRootSystemExamples.lean`). On the span of
the roots of a `ℤ`-lattice in a definite `ℚ`-space it is one (`latticeRootSystem`,
`latticeRootSystem_isRootSystem`). Mathlib's `RootPairing.ofBilinear` is a different object: it
indexes all reflective vectors, so on `A₁` it is the non-reduced `BC₁` (tests).

## The kernel root system

At a period `Z : N →+ W` the roots of the kernel are
`R_* = {δ | B(δ, δ) = -2, Z(δ) = 0}` (`kernelRoots`). If `B` is negative on the nonzero lattice
points of `ker Z` they are finitely many (`finite_kernelRoots`), and for a free `N` they are the
roots of the **kernel root system** `kernelRootPairing`, the spherical pairing of the lattice
`ker Z ∩ N`: finite, reduced and simply laced (`kernelRootPairing_finite_isReduced_simplyLaced`).
Definiteness is needed only on the lattice points of the kernel, and evenness only to say that a
nonzero kernel vector of square at least `-2` is a root (`eq_neg_two_of_even`).
-/

open Module Set Function

namespace RootPairing

/-! ### The general construct -/

section Closed

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {B : M →ₗ[R] M →ₗ[R] R}

/-- The reflection in a `(-2)`-vector is an involution. -/
theorem reflect_reflect_of_eq_neg_two {r : M} (hr : B r r = -2) (s : M) :
    (s + B r s • r) + B r (s + B r s • r) • r = s := by
  simp only [map_add, map_smul, smul_eq_mul, hr]
  rw [add_assoc, ← add_smul]
  have : B r s + (B r s + B r s * -2) = 0 := by ring
  rw [this, zero_smul, add_zero]

variable (Φ : Set M) (hΦ : ∀ r ∈ Φ, B r r = -2) (hcl : ∀ r ∈ Φ, ∀ s ∈ Φ, s + B r s • r ∈ Φ)

/-- The reflection in a root, as a permutation of a reflection-closed set of `(-2)`-vectors. -/
def reflPermOn (i : Φ) : Φ ≃ Φ where
  toFun j := ⟨j.1 + B i.1 j.1 • i.1, hcl i.1 i.2 j.1 j.2⟩
  invFun j := ⟨j.1 + B i.1 j.1 • i.1, hcl i.1 i.2 j.1 j.2⟩
  left_inv j := Subtype.ext (reflect_reflect_of_eq_neg_two (hΦ i.1 i.2) j.1)
  right_inv j := Subtype.ext (reflect_reflect_of_eq_neg_two (hΦ i.1 i.2) j.1)

/-- **The root pairing of a reflection-closed set of `(-2)`-vectors.** Over any commutative ring,
a set `Φ` of `(-2)`-vectors of a symmetric form `B` on a reflexive module, closed under
`s ↦ s + B(r, s) r` and separated by `B`, is a root pairing with roots `r` and coroots `-B(r, ·)`.
No finiteness and no sign of `B` is needed. -/
noncomputable def pairingOfClosed (hB : ∀ x y, B x y = B y x) [IsReflexive R M]
    (hN : InjOn B Φ) : RootPairing Φ R M (Dual R M) where
  toLinearMap := Dual.eval R M
  root := ⟨Subtype.val, Subtype.val_injective⟩
  coroot := ⟨fun i => -B i.1, fun i j h => Subtype.ext (hN i.2 j.2 (neg_injective h))⟩
  root_coroot_two i := by
    change -B i.1 i.1 = 2
    rw [hΦ i.1 i.2, neg_neg]
  reflectionPerm := reflPermOn Φ hΦ hcl
  reflectionPerm_root i j := by
    change j.1 - (-B i.1 j.1) • i.1 = j.1 + B i.1 j.1 • i.1
    rw [neg_smul, sub_neg_eq_add]
  reflectionPerm_coroot i j := by
    ext x
    change -B j.1 x - (-B j.1 i.1) * (-B i.1 x) = -B (j.1 + B i.1 j.1 • i.1) x
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB j.1 i.1]
    ring

variable {Φ hΦ hcl}

@[simp]
theorem pairingOfClosed_root (hB : ∀ x y, B x y = B y x) [IsReflexive R M] (hN : InjOn B Φ)
    (i : Φ) : (pairingOfClosed Φ hΦ hcl hB hN).root i = i.1 :=
  rfl

@[simp]
theorem pairingOfClosed_coroot (hB : ∀ x y, B x y = B y x) [IsReflexive R M] (hN : InjOn B Φ)
    (i : Φ) : (pairingOfClosed Φ hΦ hcl hB hN).coroot i = -B i.1 :=
  rfl

/-- The pairing of roots `i` and `j` is `-B(j, i)`. -/
theorem pairingOfClosed_pairing (hB : ∀ x y, B x y = B y x) [IsReflexive R M] (hN : InjOn B Φ)
    (i j : Φ) : (pairingOfClosed Φ hΦ hcl hB hN).pairing i j = -B j.1 i.1 :=
  rfl

end Closed

/-- **Reducedness needs no definiteness.** Over `ℤ`, the root pairing of a reflection-closed set of
`(-2)`-vectors is reduced: `a r = b s` forces `a² = b²` by comparing squares, then torsion-freeness
gives `r = ±s`. -/
theorem pairingOfClosed_isReduced {L : Type*} [AddCommGroup L] [IsReflexive ℤ L]
    {B : L →ₗ[ℤ] L →ₗ[ℤ] ℤ} {Φ : Set L} {hΦ : ∀ r ∈ Φ, B r r = -2}
    {hcl : ∀ r ∈ Φ, ∀ s ∈ Φ, s + B r s • r ∈ Φ} (hB : ∀ x y, B x y = B y x) (hN : InjOn B Φ) :
    (pairingOfClosed Φ hΦ hcl hB hN).IsReduced := by
  constructor
  intro i j h
  change ¬ LinearIndependent ℤ ![i.1, j.1] at h
  rw [LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨a, b, hab, hne⟩ := h
  have hi := hΦ i.1 i.2
  have hj := hΦ j.1 j.2
  have hsq : a ^ 2 = b ^ 2 := by
    have h1 : a • i.1 = -(b • j.1) := eq_neg_of_add_eq_zero_left hab
    have h2 := congrArg (fun v => B v v) h1
    simp only [map_smul, map_neg, LinearMap.smul_apply, LinearMap.neg_apply, smul_eq_mul,
      hi, hj] at h2
    nlinarith
  have ha : a ≠ 0 := by
    rintro rfl
    have : b = 0 := by nlinarith
    exact hne rfl this
  have hreg : IsSMulRegular L a := Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero ha)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with rfl | rfl
  · right
    apply hreg
    change a • i.1 = a • -j.1
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left hab
  · left
    apply hreg
    change -b • i.1 = -b • j.1
    rw [neg_smul, neg_smul, neg_inj]
    have := eq_neg_of_add_eq_zero_left hab
    rw [neg_smul] at this
    exact neg_injective this

/-! ### The spherical pairing of a `ℤ`-lattice -/

section Spherical

variable {L : Type*} [AddCommGroup L] (B : L →ₗ[ℤ] L →ₗ[ℤ] ℤ)

/-- The `(-2)`-vectors of a `ℤ`-lattice. -/
def sphericalRoots : Set L := {v | B v v = -2}

variable {B}

/-- The reflection of a root in a root is a root (symmetry only). -/
theorem reflect_mem_sphericalRoots (hB : ∀ x y, B x y = B y x) {r s : L}
    (hr : r ∈ sphericalRoots B) (hs : s ∈ sphericalRoots B) :
    s + B r s • r ∈ sphericalRoots B := by
  change B (s + B r s • r) (s + B r s • r) = -2
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hB s r, show B r r = -2 from hr, show B s s = -2 from hs]
  ring

/-- **The spherical pairing.** The `(-2)`-vectors of a nondegenerate symmetric `ℤ`-lattice, with
their reflections: `pairingOfClosed` at all `(-2)`-vectors. No definiteness and no finiteness: the
Mukai lattice, with infinitely many roots, is an instance. -/
noncomputable def sphericalPairing (hB : ∀ x y, B x y = B y x) [IsReflexive ℤ L]
    (hN : Injective B) : RootPairing (sphericalRoots B) ℤ L (Dual ℤ L) :=
  pairingOfClosed (sphericalRoots B) (fun _ h => h)
    (fun _ hr _ hs => reflect_mem_sphericalRoots hB hr hs) hB hN.injOn

/-- The spherical pairing is reduced, with no definiteness. -/
theorem sphericalPairing_isReduced (hB : ∀ x y, B x y = B y x) [IsReflexive ℤ L]
    (hN : Injective B) : (sphericalPairing hB hN).IsReduced :=
  pairingOfClosed_isReduced hB hN.injOn

end Spherical

/-! ### Definite lattices -/

section Definite

variable {L : Type*} [AddCommGroup L] {B : L →ₗ[ℤ] L →ₗ[ℤ] ℤ}

theorem self_nonpos_of_negDef (hD : ∀ v, v ≠ 0 → B v v < 0) (v : L) : B v v ≤ 0 := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (hD v hv).le

/-- A negative-definite form is nondegenerate. -/
theorem injective_of_negDef (hD : ∀ v, v ≠ 0 → B v v < 0) : Injective B := by
  intro v w h
  by_contra hne
  have := hD (v - w) (sub_ne_zero.mpr hne)
  have h0 : B (v - w) = 0 := by rw [map_sub, h, sub_self]
  rw [h0, LinearMap.zero_apply] at this
  exact lt_irrefl _ this

/-- **Integer Cauchy–Schwarz** for a negative-definite symmetric form:
`B(bx - cy, bx - cy) = b(ab - c²) ≤ 0`, with no division. -/
theorem sq_le_mul (hB : ∀ x y, B x y = B y x) (hD : ∀ v, v ≠ 0 → B v v < 0) (x y : L) :
    B x y ^ 2 ≤ B x x * B y y := by
  have key := self_nonpos_of_negDef hD (B y y • x - B x y • y)
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    hB y x] at key
  by_cases hy : y = 0
  · simp [hy]
  · have hyy := hD y hy
    nlinarith

/-- **Bounded sets of a definite lattice are finite**: `{v | B v v ≥ -n}` for a finitely generated
lattice. Evaluate against a finite generating set: Cauchy–Schwarz puts the values in a box, and
definiteness makes the evaluation injective. -/
theorem finite_setOf_neg_le (hB : ∀ x y, B x y = B y x) (hD : ∀ v, v ≠ 0 → B v v < 0)
    [Module.Finite ℤ L] (n : ℤ) : {v : L | -n ≤ B v v}.Finite := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := L)
  let φ : L → (s → ℤ) := fun v g => B v g
  let c : s → ℤ := fun g => n * (-B g.1 g.1)
  have hbox : φ '' {v : L | -n ≤ B v v} ⊆ Set.Icc (-c) c := by
    rintro _ ⟨v, hv, rfl⟩
    change -n ≤ B v v at hv
    constructor <;> intro g <;> simp only [Pi.neg_apply, φ, c]
    all_goals
      have cs := sq_le_mul hB hD v g.1
      have h1 := self_nonpos_of_negDef hD v
      have h2 := self_nonpos_of_negDef hD g.1
      have h3 : |B v g.1| ≤ B v g.1 ^ 2 := by
        rcases eq_or_ne (B v g.1) 0 with h0 | h0
        · simp [h0]
        · have := Int.one_le_abs h0
          nlinarith [abs_nonneg (B v g.1), sq_abs (B v g.1)]
      have h4 : B v v * B g.1 g.1 ≤ n * (-B g.1 g.1) := by nlinarith
    · nlinarith [neg_abs_le (B v g.1)]
    · nlinarith [le_abs_self (B v g.1)]
  have hinj : InjOn φ {v : L | -n ≤ B v v} := by
    intro v _ w _ hvw
    have hzero : B (v - w) = 0 := by
      refine LinearMap.ext_on hs ?_
      intro g hg
      have := congrFun hvw ⟨g, hg⟩
      simp only [φ] at this
      simp [map_sub, this]
    exact sub_eq_zero.mp (injective_of_negDef hD (by rw [hzero, map_zero]))
  exact Set.Finite.of_finite_image ((Set.finite_Icc (-c) c).subset hbox) hinj

/-- **The roots of a definite lattice are finitely many.** -/
theorem finite_sphericalRoots (hB : ∀ x y, B x y = B y x) (hD : ∀ v, v ≠ 0 → B v v < 0)
    [Module.Finite ℤ L] : (sphericalRoots B).Finite :=
  (finite_setOf_neg_le hB hD 2).subset fun v (hv : B v v = -2) => show -2 ≤ B v v by omega

/-- **Simply laced**: distinct non-opposite roots of a definite lattice pair to `-1`, `0` or `1`,
since `B(r ± s, r ± s) = -4 ± 2B(r, s) < 0`. -/
theorem pairing_mem (hB : ∀ x y, B x y = B y x) (hD : ∀ v, v ≠ 0 → B v v < 0) {r s : L}
    (hr : B r r = -2) (hs : B s s = -2) (h1 : r ≠ s) (h2 : r ≠ -s) :
    B r s = -1 ∨ B r s = 0 ∨ B r s = 1 := by
  have p := hD (r + s) (fun h => h2 (eq_neg_of_add_eq_zero_left h))
  have m := hD (r - s) (sub_ne_zero.mpr h1)
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, hr, hs, hB s r] at p m
  omega

/-- Simply laced, in `RootPairing` vocabulary. -/
theorem sphericalPairing_pairing_mem [IsReflexive ℤ L] (hB : ∀ x y, B x y = B y x)
    (hD : ∀ v, v ≠ 0 → B v v < 0) (i j : sphericalRoots B) (h1 : i ≠ j)
    (h2 : (i : L) ≠ -(j : L)) :
    (sphericalPairing hB (injective_of_negDef hD)).pairing i j ∈ ({-1, 0, 1} : Set ℤ) := by
  change -B j.1 i.1 ∈ ({-1, 0, 1} : Set ℤ)
  rcases pairing_mem hB hD j.2 i.2 (fun h => h1 (Subtype.ext h.symm))
    (fun h => h2 (by rw [h, neg_neg])) with h | h | h <;> simp [h]

/-- **A definite lattice gives a finite, reduced, simply laced root pairing.** For a finitely
generated reflexive `ℤ`-lattice with a negative-definite symmetric form, the `(-2)`-vectors with
their reflections form a finite, reduced root pairing whose distinct non-opposite roots pair to
`-1`, `0` or `1`. Evenness is not needed. -/
theorem sphericalPairing_finite_isReduced_simplyLaced [Module.Finite ℤ L] [IsReflexive ℤ L]
    (hB : ∀ x y, B x y = B y x) (hD : ∀ v, v ≠ 0 → B v v < 0) :
    Finite (sphericalRoots B) ∧ (sphericalPairing hB (injective_of_negDef hD)).IsReduced ∧
      ∀ i j : sphericalRoots B, i ≠ j → (i : L) ≠ -(j : L) →
        (sphericalPairing hB (injective_of_negDef hD)).pairing i j ∈ ({-1, 0, 1} : Set ℤ) :=
  ⟨(finite_sphericalRoots hB hD).to_subtype, sphericalPairing_isReduced hB _,
    fun i j h1 h2 => sphericalPairing_pairing_mem hB hD i j h1 h2⟩

/-- Evenness is used only here: in an even definite lattice every nonzero vector of square at
least `-2` is a root. -/
theorem eq_neg_two_of_even (hD : ∀ v, v ≠ 0 → B v v < 0) (hE : ∀ v, Even (B v v)) {v : L}
    (hv : v ≠ 0) (h : -2 ≤ B v v) : B v v = -2 := by
  have := hD v hv
  obtain ⟨k, hk⟩ := hE v
  omega

/-! ### Cartan matrices of a base -/

/-- **The Cartan matrix of a base is simply laced.** Its off-diagonal entries are pairings of
distinct non-opposite roots, so lie in `{-1, 0, 1}`, and are nonpositive. -/
theorem cartanMatrix_isSimplyLaced [Module.Finite ℤ L] [IsReflexive ℤ L]
    (hB : ∀ x y, B x y = B y x) (hD : ∀ v, v ≠ 0 → B v v < 0)
    (b : (sphericalPairing hB (injective_of_negDef hD)).Base) :
    b.cartanMatrix.IsSimplyLaced := by
  have : Finite (sphericalRoots B) := (finite_sphericalRoots hB hD).to_subtype
  intro i j hij
  have hle := b.cartanMatrix_le_zero_of_ne i j hij
  have hli := b.linearIndepOn_root
  have hij' : (i : sphericalRoots B) ≠ j := fun h => hij (Subtype.ext h)
  have hneg : ((i : sphericalRoots B) : L) ≠ -((j : sphericalRoots B) : L) := by
    intro h
    have hinj : Injective ![i, j] := by
      intro a c hac
      fin_cases a <;> fin_cases c <;> simp_all [Ne.symm hij]
    have h2 : LinearIndependent ℤ
        ![((i : sphericalRoots B) : L), ((j : sphericalRoots B) : L)] := by
      convert (show LinearIndependent ℤ fun k : b.support => ((k : sphericalRoots B) : L) from
        hli).comp ![i, j] hinj using 1
      funext k
      fin_cases k <;> rfl
    have h0 := LinearIndependent.pair_iff.mp h2 1 1 (by rw [one_smul, one_smul, h, neg_add_cancel])
    exact one_ne_zero h0.1
  have hmem := sphericalPairing_pairing_mem hB hD i j hij' hneg
  have heq : b.cartanMatrix i j = (sphericalPairing hB (injective_of_negDef hD)).pairing i j := by
    rw [Base.cartanMatrix, Base.cartanMatrixIn_def]
    have := algebraMap_pairingIn (sphericalPairing hB (injective_of_negDef hD)) ℤ i j
    rwa [Algebra.algebraMap_self, RingHom.id_apply] at this
  rw [heq] at hle ⊢
  rcases hmem with h | h | h
  · right; exact h
  · left; exact h
  · rw [h] at hle; norm_num at hle

open Matrix in
/-- **The Cartan matrix of a base is positive definite**: `xᵀ C x = -B(v, v) > 0` for
`v = Σ x_i r_i`, which is nonzero by linear independence of the simple roots. -/
theorem cartanMatrix_pos [IsReflexive ℤ L]
    (hB : ∀ x y, B x y = B y x) (hD : ∀ v, v ≠ 0 → B v v < 0)
    (b : (sphericalPairing hB (injective_of_negDef hD)).Base) {x : b.support → ℤ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (b.cartanMatrix *ᵥ x) := by
  set v : L := ∑ i : b.support, x i • ((i : sphericalRoots B) : L)
  have hv : v ≠ 0 := by
    intro hv0
    have hli : LinearIndependent ℤ fun i : b.support => ((i : sphericalRoots B) : L) :=
      b.linearIndepOn_root
    apply hx
    funext i
    exact Fintype.linearIndependent_iff.mp hli x hv0 i
  have hC : ∀ i j : b.support, b.cartanMatrix i j = -B ((j : sphericalRoots B) : L)
      ((i : sphericalRoots B) : L) := fun i j => by
    rw [Base.cartanMatrix, Base.cartanMatrixIn_def]
    have := algebraMap_pairingIn (sphericalPairing hB (injective_of_negDef hD)) ℤ i j
    rwa [Algebra.algebraMap_self, RingHom.id_apply] at this
  have hBv : B v v = ∑ i : b.support, ∑ j : b.support,
      x i * (x j * B ((i : sphericalRoots B) : L) ((j : sphericalRoots B) : L)) := by
    simp only [v, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hval : x ⬝ᵥ (b.cartanMatrix *ᵥ x) = -B v v := by
    rw [hBv, ← Finset.sum_neg_distrib]
    simp only [dotProduct, Matrix.mulVec, hC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hB ((j : sphericalRoots B) : L)]
    ring
  rw [hval]
  linarith [hD v hv]

end Definite

/-! ### The kernel root system -/

section Kernel

variable {N W : Type*} [AddCommGroup N] [AddCommGroup W] (B : N →ₗ[ℤ] N →ₗ[ℤ] ℤ) (Z : N →+ W)

/-- The roots of the kernel of a period `Z`: `R_* = {δ | B(δ, δ) = -2, Z(δ) = 0}`. -/
def kernelRoots : Set N := {δ | B δ δ = -2 ∧ Z δ = 0}

/-- The lattice `ker Z ∩ N`. -/
abbrev kernelLattice : Submodule ℤ N := Z.ker.toIntSubmodule

/-- The form restricted to the lattice `ker Z ∩ N`. -/
def kernelForm : kernelLattice Z →ₗ[ℤ] kernelLattice Z →ₗ[ℤ] ℤ :=
  B.compl₁₂ (kernelLattice Z).subtype (kernelLattice Z).subtype

@[simp]
theorem kernelForm_apply (x y : kernelLattice Z) : kernelForm B Z x y = B x y :=
  rfl

variable {B Z}

/-- The kernel roots are the roots of the lattice `ker Z ∩ N`. -/
theorem kernelRoots_eq_image :
    kernelRoots B Z = Subtype.val '' sphericalRoots (kernelForm B Z) := by
  ext δ
  constructor
  · rintro ⟨hδ, hZ⟩
    exact ⟨⟨δ, hZ⟩, hδ, rfl⟩
  · rintro ⟨δ', hδ', rfl⟩
    exact ⟨hδ', δ'.2⟩

/-- **The root set at a stratum is finite** as soon as `B` is negative on the nonzero lattice
points of `ker Z`: no evenness, no signature of `N` and no definiteness on the real span enter. -/
theorem finite_kernelRoots [Module.Finite ℤ N] (hB : ∀ x y, B x y = B y x)
    (hD : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) : (kernelRoots B Z).Finite := by
  rw [kernelRoots_eq_image]
  exact (finite_sphericalRoots (B := kernelForm B Z) (fun x y => hB x.1 y.1)
    fun v hv => hD v.1 v.2 fun h => hv (Subtype.ext h)).image _

/-- **The kernel root system**: the spherical pairing of the definite lattice `ker Z ∩ N`. -/
noncomputable def kernelRootPairing [Module.Finite ℤ N] [Module.Free ℤ N]
    (hB : ∀ x y, B x y = B y x) (hD : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) :
    RootPairing (sphericalRoots (kernelForm B Z)) ℤ (kernelLattice Z)
      (Dual ℤ (kernelLattice Z)) :=
  sphericalPairing (B := kernelForm B Z) (fun x y => hB x.1 y.1)
    (injective_of_negDef fun v hv => hD v.1 v.2 fun h => hv (Subtype.ext h))

/-- **The kernel root system is finite, reduced and simply laced.** -/
theorem kernelRootPairing_finite_isReduced_simplyLaced [Module.Finite ℤ N] [Module.Free ℤ N]
    (hB : ∀ x y, B x y = B y x) (hD : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) :
    Finite (sphericalRoots (kernelForm B Z)) ∧ (kernelRootPairing hB hD).IsReduced ∧
      ∀ i j : sphericalRoots (kernelForm B Z), i ≠ j →
        (i : kernelLattice Z) ≠ -(j : kernelLattice Z) →
        (kernelRootPairing hB hD).pairing i j ∈ ({-1, 0, 1} : Set ℤ) :=
  sphericalPairing_finite_isReduced_simplyLaced (B := kernelForm B Z) (fun x y => hB x.1 y.1)
    fun v hv => hD v.1 v.2 fun h => hv (Subtype.ext h)

end Kernel

/-! ### Over `ℚ`: the root system on the span of the roots -/

section RationalLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ}

/-- The roots of a `ℤ`-lattice `Λ` of a `ℚ`-space. -/
def latticeRoots (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (Λ : Submodule ℤ V) : Set V :=
  {v | v ∈ Λ ∧ B v v = -2}

theorem latticeRoots_closed (hB : ∀ x y, B x y = B y x) (Λ : Submodule ℤ V)
    (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, B x y = n) :
    ∀ r ∈ latticeRoots B Λ, ∀ s ∈ latticeRoots B Λ, s + B r s • r ∈ latticeRoots B Λ := by
  rintro r ⟨hrΛ, hr⟩ s ⟨hsΛ, hs⟩
  obtain ⟨n, hn⟩ := hI r hrΛ s hsΛ
  refine ⟨?_, ?_⟩
  · rw [hn, Int.cast_smul_eq_zsmul]
    exact Λ.add_mem hsΛ (Λ.smul_mem n hrΛ)
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hB s r, hr, hs]
    ring

theorem injective_of_negDef_rat (hD : ∀ v, v ≠ 0 → B v v < 0) : Injective B := by
  intro v w h
  by_contra hne
  have := hD (v - w) (sub_ne_zero.mpr hne)
  have h0 : B (v - w) = 0 := by rw [map_sub, h, sub_self]
  rw [h0, LinearMap.zero_apply] at this
  exact lt_irrefl _ this

/-- The integer value of `B` on `Λ`. -/
noncomputable def intVal (Λ : Submodule ℤ V) (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, B x y = n)
    (x y : Λ) : ℤ :=
  (hI x.1 x.2 y.1 y.2).choose

theorem intVal_cast (Λ : Submodule ℤ V) (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, B x y = n)
    (x y : Λ) : ((intVal Λ hI x y : ℤ) : ℚ) = B x.1 y.1 :=
  (hI x.1 x.2 y.1 y.2).choose_spec.symm

/-- The `ℤ`-valued restriction of `B` to an integral lattice `Λ`. -/
noncomputable def intForm (Λ : Submodule ℤ V) (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, B x y = n) :
    Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (intVal Λ hI)
    (fun a b c => Int.cast_injective (α := ℚ) (by
      simp only [Int.cast_add, intVal_cast, Submodule.coe_add, map_add, LinearMap.add_apply]))
    (fun n a c => Int.cast_injective (α := ℚ) (by
      simp only [smul_eq_mul, Int.cast_mul, intVal_cast, Submodule.coe_smul, map_zsmul,
        LinearMap.smul_apply, zsmul_eq_mul]))
    (fun a b c => Int.cast_injective (α := ℚ) (by
      simp only [Int.cast_add, intVal_cast, Submodule.coe_add, map_add]))
    (fun n a c => Int.cast_injective (α := ℚ) (by
      simp only [smul_eq_mul, Int.cast_mul, intVal_cast, Submodule.coe_smul]
      rw [← Int.cast_smul_eq_zsmul ℚ, map_smul, smul_eq_mul]))

theorem intForm_cast (Λ : Submodule ℤ V) (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, B x y = n)
    (x y : Λ) : ((intForm Λ hI x y : ℤ) : ℚ) = B x.1 y.1 :=
  intVal_cast Λ hI x y

/-- The roots of a finitely generated integral lattice in a definite `ℚ`-space are finitely many,
by the `ℤ` statement for the restricted form. -/
theorem finite_latticeRoots (hB : ∀ x y, B x y = B y x) (hD : ∀ v, v ≠ 0 → B v v < 0)
    (Λ : Submodule ℤ V) (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, B x y = n) [Module.Finite ℤ Λ] :
    Finite (latticeRoots B Λ) := by
  have hBZ : ∀ x y, intForm Λ hI x y = intForm Λ hI y x := fun x y =>
    Int.cast_injective (α := ℚ) (by rw [intForm_cast, intForm_cast, hB])
  have hDZ : ∀ v, v ≠ 0 → intForm Λ hI v v < 0 := fun v hv => by
    have := hD v.1 (fun h => hv (Subtype.ext h))
    rw [← intForm_cast Λ hI] at this
    exact_mod_cast this
  have := (finite_sphericalRoots hBZ hDZ).to_subtype
  let f : latticeRoots B Λ → sphericalRoots (intForm Λ hI) := fun v =>
    ⟨⟨v.1, v.2.1⟩, Int.cast_injective (α := ℚ) (by rw [intForm_cast]; push_cast; exact v.2.2)⟩
  exact Finite.of_injective f (fun a b h => Subtype.ext (congrArg (fun x => x.1.1) h))

/-- The root pairing of the roots of an integral lattice in a definite `ℚ`-space. -/
noncomputable def latticePairing (hB : ∀ x y, B x y = B y x) (hD : ∀ v, v ≠ 0 → B v v < 0)
    [FiniteDimensional ℚ V] (Λ : Submodule ℤ V) (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, B x y = n) :
    RootPairing (latticeRoots B Λ) ℚ V (Dual ℚ V) :=
  pairingOfClosed (latticeRoots B Λ) (fun _ h => h.2) (latticeRoots_closed hB Λ hI) hB
    (injective_of_negDef_rat hD).injOn

/-- **The root system over `ℚ`**: the lattice pairing restricted to the `ℚ`-span of its roots, by
Mathlib's `RootPairing.restrictScalars'`. -/
noncomputable def latticeRootSystem (hB : ∀ x y, B x y = B y x) (hD : ∀ v, v ≠ 0 → B v v < 0)
    [FiniteDimensional ℚ V] (Λ : Submodule ℤ V) (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, B x y = n)
    [Module.Finite ℤ Λ] :
    RootPairing (latticeRoots B Λ) ℚ (Submodule.span ℚ (range (latticePairing hB hD Λ hI).root))
      (Submodule.span ℚ (range (latticePairing hB hD Λ hI).coroot)) :=
  haveI : Finite (latticeRoots B Λ) := finite_latticeRoots hB hD Λ hI
  haveI : Fintype (latticeRoots B Λ) := Fintype.ofFinite _
  (latticePairing hB hD Λ hI).restrictScalars' ℚ

instance latticeRootSystem_isRootSystem (hB : ∀ x y, B x y = B y x)
    (hD : ∀ v, v ≠ 0 → B v v < 0) [FiniteDimensional ℚ V] (Λ : Submodule ℤ V)
    (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, B x y = n) [Module.Finite ℤ Λ] :
    (latticeRootSystem hB hD Λ hI).IsRootSystem := by
  unfold latticeRootSystem
  infer_instance

end RationalLattice

end RootPairing
