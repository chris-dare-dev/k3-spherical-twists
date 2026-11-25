/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Combinatorics.Quiver.Kronecker.RealRoots
import K3Twists.LinearAlgebra.Lattice.Mukai.Reflection
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.ZMod.Basic

/-!
# The Mukai lattice of an elliptic K3 surface with a section

Let `X` be an elliptic K3 surface with a section `C` and fibre class `F` whose Néron–Severi
lattice is `NS(X) = ℤC ⊕ ℤF`, with `C² = -2`, `C·F = 1` and `F² = 0`. We write `(a, b)` for the
class `aC + bF`, so that `(a, b)·(a', b') = -2aa' + ab' + a'b`. The algebraic Mukai lattice is
the Mukai extension `ℤ ⊕ NS(X) ⊕ ℤ` of `Mukai/Basic.lean`, with pairing
`⟨(r, c, s), (r', c', s')⟩ = c·c' - rs' - r's`; on a K3 surface `χ(E, F) = -⟨v(E), v(F)⟩`, and a
sheaf of rank `r` with first Chern class `c` has Mukai vector `(r, c, ch₂ + r)`.

This file records the classes of the objects that the curve wall of `X` uses, and proves the
lattice statements about them:

* `v(𝒪_x) = (0, 0, 1)`, `v(𝒪_X(D)) = (1, D, D²/2 + 1)` and `v(𝒪_C(k)) = (0, C, k + 1)`, the last
  from `χ(𝒪_C(k)) = k + 1` on `C ≅ ℙ¹`. Mathlib has no Chern characters, so these are the
  definitions of the named classes (`point`, `lineBundle`, `curveSheaf`), as
  `MukaiVector.lineBundle` is in Picard rank one.
* **The wall of pairing two.** The spherical simples of the wall where `C` is contracted are
  `A = 𝒪_C` and `B = 𝒪_C(-1)[1]`, of classes `(0, C, 1)` and `(0, -C, 0)`. They pair to `2`,
  `v(A) + v(B) = v(𝒪_x)`, and a wall object of multiplicities `(a, b)` has
  `v² = -2(a - b)² = -2 q₂(a, b)`, where `q₂` is the Kronecker form at `g = 2`
  (`selfPairing_wallClass`).
* **Section evaluation.** `v(𝒪_C(j)) = (j + 1)v(A) + j v(B)`, the classes of
  `0 → A^{j+1} → 𝒪_C(j) → B^j → 0`; and `v(𝒪_X(D)) - v(𝒪_X(D - C)) = v(𝒪_C(C·D))`, the classes of
  the restriction sequence (`lineBundle_sub_lineBundle_sub_curve`).
* **The embedded-point family.** The curve with an embedded point `M_{d,x}` (the nonsplit
  extension of `𝒪_C(d)` by `𝒪_x`) has multiplicities `(d + 2, d + 1)` and square `-2`. The
  quotient `R_j = D(jC)/(I_x ⊗ D(-C))` is built from `M_{d,x}` by layers `𝒪_C(d - 2j)`
  (`idealQuotient_succ`), and for `D = K_ε(-rC)`, `d = 2r + ε`, it is the thickening
  `K_ε ⊗ 𝒪_X/(I_x I_C^{r+1})` of class `(0, (r + 1)C, (r + 1)(r + 1 + ε) + 1)`, of square
  `-2(r + 1)²` (`thickening_eq`).
* **Riemann–Roch on the wall.** `dim Ext¹(E, E) = 2 dim End(E) + v(E)²`: the count for
  multiplicities `(m, 1)` (`ext_one_count`, `ext_one_count_eq_two_iff`), the isotropic class
  `(2, 2)`, and semirigidity of `M_{d,x}` and of the thickening.
* **Twists and towers on classes.** `T_A` (and `T_A⁻¹`) act on classes by the reflection in
  `v(A)`: they fix `v(𝒪_x)`, send `v(𝒪_C(j))` to `(j - 1)v(A) + j v(B)`, and `T_A⁻¹` sends `B` to
  the class of `𝒪_C(1)`. The quotients of each HN tower add up to the class of the twisted point:
  the two towers of the thickening (`point_add_sum_curveSheaf`, `sum_A_side_odd`,
  `sum_A_side_even`), the one-letter word `T_{K_ε(-(r+1)C)}` (`reflect_lineBundle_point`), the
  two-letter word `T_{D(nF)}⁻¹ T_{D(-C)}` in every degree (`reflect_reflect_point`), the
  three-letter word, of class `(0, C + F, 3) = v(𝒪_{C+Γ}(C + 4F))` for the fibre `Γ` through the
  point (`reflect_threeLetter_point`), and the rank-two example (`reflect_rankTwo_point`).
* **Stable classes in charge coordinates** (`neg_two_le_selfPairing_iff`): with `p = 4 Re Z` and
  `q = Im Z` for the charge of the curve wall, `v² ≥ -2` is an ellipse condition on `(r, a)`.
* **The parity argument** (`not_isSpherical_sub_of_odd_rank`): a root of odd rank with
  `H·c - r = 2`, `H = C + 2F`, is not the sum of two roots with `H·c - r = 1`. It is the lattice
  step in the proofs that the tails `𝒪_X(-C - F)[1]` and the line bundles of `H`-slope `3` are
  stable at the curve wall.

The geometric facts that pick out these classes (that the objects exist, are spherical or
semirigid, and form the stated sequences and towers) are not formalized here; this file proves
that their classes are consistent with them.
-/

namespace AlgebraicGeometry.K3.EllipticWithSection

open Mukai

/-! ### The Néron–Severi lattice -/

/-- The Néron–Severi lattice `ℤC ⊕ ℤF`: the pair `(a, b)` stands for `aC + bF`. -/
abbrev NS : Type := ℤ × ℤ

/-- The intersection form `(a, b)·(a', b') = -2aa' + ab' + a'b`, that is `C² = -2`, `C·F = 1`,
`F² = 0`. -/
def intersection : NS →ₗ[ℤ] NS →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun x y => -2 * x.1 * y.1 + x.1 * y.2 + x.2 * y.1)
    (fun x y z => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun x y z => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

@[simp]
lemma intersection_apply (x y : NS) :
    intersection x y = -2 * x.1 * y.1 + x.1 * y.2 + x.2 * y.1 :=
  rfl

lemma intersection_comm (x y : NS) : intersection x y = intersection y x := by
  simp only [intersection_apply]; ring

/-- The lattice is even, as `NS` of a K3 surface is: `(aC + bF)² = 2a(b - a)`. -/
lemma intersection_self (x : NS) : intersection x x = 2 * (x.1 * (x.2 - x.1)) := by
  simp only [intersection_apply]; ring

/-- The section `C`. -/
def curve : NS := (1, 0)

/-- The fibre class `F`. -/
def fibre : NS := (0, 1)

/-- The polarization `H = C + 2F` of the curve wall. -/
def polarization : NS := (1, 2)

@[simp] lemma curve_fst : curve.1 = 1 := rfl
@[simp] lemma curve_snd : curve.2 = 0 := rfl
@[simp] lemma fibre_fst : fibre.1 = 0 := rfl
@[simp] lemma fibre_snd : fibre.2 = 1 := rfl
@[simp] lemma polarization_fst : polarization.1 = 1 := rfl
@[simp] lemma polarization_snd : polarization.2 = 2 := rfl

lemma polarization_eq : polarization = curve + (2 : ℤ) • fibre := by
  ext <;> simp

/-- `C² = -2`, `C·F = 1`, `F² = 0`. -/
lemma intersection_curve_fibre :
    intersection curve curve = -2 ∧ intersection curve fibre = 1 ∧
      intersection fibre fibre = 0 := by
  simp

/-- `H² = 2`, `H·C = 0` and `H·F = 1`: `H` contracts `C`. -/
lemma intersection_polarization :
    intersection polarization polarization = 2 ∧ intersection polarization curve = 0 ∧
      intersection polarization fibre = 1 := by
  simp

/-- `H·(aC + bF) = b`: the `H`-degree of a class is its fibre coefficient. -/
lemma intersection_polarization_apply (x : NS) : intersection polarization x = x.2 := by
  simp

/-- `C·(aC + bF) = b - 2a`: the degree on the section. -/
lemma intersection_curve_apply (x : NS) : intersection curve x = x.2 - 2 * x.1 := by
  simp; ring

/-- `F·(aC + bF) = a`. -/
lemma intersection_fibre_apply (x : NS) : intersection fibre x = x.1 := by
  simp

/-- **`H` contracts only `C`.** A class with nonnegative degree on `C` and on `F` has positive
`H`-degree unless it is zero. Every irreducible curve other than `C` has such a class, because
`C` is irreducible and `F` is nef; so `C` is the only irreducible curve that `H` contracts. -/
lemma intersection_polarization_pos {x : NS} (hC : 0 ≤ intersection curve x)
    (hF : 0 ≤ intersection fibre x) (hx : x ≠ 0) : 0 < intersection polarization x := by
  simp only [intersection_curve_apply, intersection_fibre_apply,
    intersection_polarization_apply] at hC hF ⊢
  by_contra h
  exact hx (Prod.ext (by simp; omega) (by simp; omega))

/-! ### Mukai vectors -/

/-- `v(𝒪_x) = (0, 0, 1)`. -/
def point : MukaiLattice ℤ NS := (0, 0, 1)

/-- `v(𝒪_X(D)) = (1, D, D²/2 + 1)`; for `D = aC + bF`, `D²/2 = a(b - a)`. -/
def lineBundle (D : NS) : MukaiLattice ℤ NS := (1, D, D.1 * (D.2 - D.1) + 1)

/-- `v(I_x ⊗ 𝒪_X(D)) = v(𝒪_X(D)) - v(𝒪_x)`. -/
def idealPoint (D : NS) : MukaiLattice ℤ NS := lineBundle D - point

/-- `v(𝒪_C(k)) = (0, C, k + 1)`, since `χ(𝒪_C(k)) = k + 1` on `C ≅ ℙ¹`. -/
def curveSheaf (k : ℤ) : MukaiLattice ℤ NS := (0, curve, k + 1)

@[simp] lemma point_def : point = (0, 0, 1) := rfl
@[simp] lemma lineBundle_def (D : NS) : lineBundle D = (1, D, D.1 * (D.2 - D.1) + 1) := rfl
@[simp] lemma idealPoint_def (D : NS) : idealPoint D = lineBundle D - point := rfl
@[simp] lemma curveSheaf_def (k : ℤ) : curveSheaf k = (0, curve, k + 1) := rfl

lemma isIsotropic_point : IsIsotropic intersection point := by
  simp [IsIsotropic]

lemma isSpherical_lineBundle (D : NS) : IsSpherical intersection (lineBundle D) := by
  simp only [IsSpherical, lineBundle_def, selfPairing_mk, intersection_apply]; ring

lemma isSpherical_curveSheaf (k : ℤ) : IsSpherical intersection (curveSheaf k) := by
  simp [IsSpherical]

/-- `χ(𝒪_x, 𝒪_X(D)) = 1`. -/
lemma pairing_point_lineBundle (D : NS) : pairing intersection point (lineBundle D) = -1 := by
  simp

/-- `χ(𝒪_C, 𝒪_X(D)) = 1 - C·D`: for `C·D = e ≥ 1`, `Hom = Ext² = 0` and `Ext¹(𝒪_C, 𝒪_X(D))`
has dimension `e - 1 = h⁰(𝒪_C(e - 2))`. -/
lemma pairing_curveSheaf_lineBundle (D : NS) :
    pairing intersection (curveSheaf 0) (lineBundle D) = intersection curve D - 1 := by
  simp

/-- **The restriction sequence on classes.** `0 → 𝒪_X(D - C) → 𝒪_X(D) → 𝒪_C(C·D) → 0`, so
`v(𝒪_X(D)) - v(𝒪_X(D - C)) = v(𝒪_C(C·D))`. -/
lemma lineBundle_sub_lineBundle_sub_curve (D : NS) :
    lineBundle D - lineBundle (D - curve) = curveSheaf (intersection curve D) := by
  ext <;> simp
  ring

/-! ### The wall of pairing two -/

/-- `A = 𝒪_C`, the first spherical simple of the curve wall. -/
def wallA : MukaiLattice ℤ NS := curveSheaf 0

/-- `B = 𝒪_C(-1)[1]`, the second; the shift negates the class. -/
def wallB : MukaiLattice ℤ NS := -curveSheaf (-1)

/-- The class `a v(A) + b v(B)` of a wall object with multiplicities `(a, b)`. -/
def wallClass (a b : ℤ) : MukaiLattice ℤ NS := a • wallA + b • wallB

@[simp]
lemma wallClass_eq (a b : ℤ) : wallClass a b = (0, (a - b, 0), a) := by
  ext <;> simp [wallClass, wallA, wallB]
  ring

lemma wallA_eq : wallA = wallClass 1 0 := by
  ext <;> simp [wallA]

lemma wallB_eq : wallB = wallClass 0 1 := by
  ext <;> simp [wallB]

lemma wallClass_add (a b a' b' : ℤ) :
    wallClass a b + wallClass a' b' = wallClass (a + a') (b + b') := by
  ext <;> simp
  ring

lemma isSpherical_wallA : IsSpherical intersection wallA := isSpherical_curveSheaf 0

lemma isSpherical_wallB : IsSpherical intersection wallB := by
  rw [wallB]; exact (isSpherical_curveSheaf (-1)).neg intersection

/-- **Pairing two.** `⟨v(A), v(B)⟩ = 2`, so `χ(A, B) = -2`; for two stable objects of one phase
this is `dim Ext¹(A, B) = dim Ext¹(B, A) = 2`. -/
lemma pairing_wallA_wallB : pairing intersection wallA wallB = 2 := by
  simp [wallA, wallB]

/-- `v(A) + v(B) = v(𝒪_x)`, the classes of `0 → 𝒪_C → 𝒪_x → 𝒪_C(-1)[1] → 0` in the wall heart. -/
lemma wallA_add_wallB : wallA + wallB = point := by
  ext <;> simp [wallA, wallB]

lemma point_eq_wallClass : point = wallClass 1 1 := by
  ext <;> simp

/-- **The Mukai form on the wall.** `v(aA + bB)² = -2(a - b)²`. -/
lemma selfPairing_wallClass (a b : ℤ) :
    selfPairing intersection (wallClass a b) = -2 * (a - b) ^ 2 := by
  simp; ring

/-- The Mukai form on the wall is `-2` times the Kronecker form `q₂(a, b) = a² + b² - 2ab` at
`g = 2`. -/
lemma selfPairing_wallClass_eq_kroneckerForm (a b : ℤ) :
    selfPairing intersection (wallClass a b) = -2 * Quiver.Kronecker.kroneckerForm 2 a b := by
  rw [selfPairing_wallClass, Quiver.Kronecker.kroneckerForm]; ring

/-- **Section evaluation on classes.** `0 → A^{j+1} → 𝒪_C(j) → B^j → 0`, so
`v(𝒪_C(j)) = (j + 1)v(A) + j v(B)`. -/
lemma curveSheaf_eq_wallClass (j : ℤ) : curveSheaf j = wallClass (j + 1) j := by
  ext <;> simp

/-! ### Riemann–Roch on the wall

For an object `E` with `dim End(E) = e`, Serre duality and Riemann–Roch on a K3 surface give
`dim Ext¹(E, E) = 2e + v(E)²`. On the wall this is `2e - 2(a - b)²`. -/

/-- **The `(m, 1)` count.** A wall object `D = D₀ ⊕ A^r` of multiplicities `(m, 1)`,
`m = p + q + r`, whose summand `D₀` has `q` copies of `A` below its `B` and `p` above, has
`dim End(D) = (1 + pq) + rp + rq + r²` and hence
`dim Ext¹(D, D) = 2(1 + pq) - 2(p + q - 1)² + 2r(2 - p - q)`. -/
lemma ext_one_count (p q r : ℤ) :
    2 * ((1 + p * q) + r * p + r * q + r ^ 2) +
        selfPairing intersection (wallClass (p + q + r) 1) =
      2 * (1 + p * q) - 2 * (p + q - 1) ^ 2 + 2 * r * (2 - p - q) := by
  rw [selfPairing_wallClass]; ring

/-- **Semirigid objects of multiplicities `(m, 1)`.** With `p + q ≤ 2` (the extension classes are
independent in the two-dimensional `Ext¹(B, A)`) and `m = p + q + r ≥ 2`, the count of
`ext_one_count` is `2` exactly when `p = q = 1`, that is for `M ⊕ A^{m-2}` with `M` the
length-three object. -/
theorem ext_one_count_eq_two_iff {p q r : ℤ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 2)
    (hm : 2 ≤ p + q + r) :
    2 * (1 + p * q) - 2 * (p + q - 1) ^ 2 + 2 * r * (2 - p - q) = 2 ↔ p = 1 ∧ q = 1 := by
  have hp2 : p ≤ 2 := by omega
  have hq2 : q ≤ 2 := by omega
  interval_cases p <;> interval_cases q <;> omega

/-- **No semirigid `(2, 2)` object.** Its class is isotropic, so `dim Ext¹ = 2 dim End`, and
semirigidity would force `dim End = 1`. -/
lemma selfPairing_wallClass_two_two : selfPairing intersection (wallClass 2 2) = 0 := by
  rw [selfPairing_wallClass]; ring

/-! ### The embedded-point family -/

/-- The class of `M_{d,x}`, the nonsplit extension `0 → 𝒪_x → M_{d,x} → 𝒪_C(d) → 0`; for `d = 0`
it is `𝒪_X/(I_C I_x)`, the curve with an embedded point. -/
def embeddedPoint (d : ℤ) : MukaiLattice ℤ NS := point + curveSheaf d

/-- `M_{d,x}` has wall multiplicities `(d + 2, d + 1)`. -/
lemma embeddedPoint_eq_wallClass (d : ℤ) : embeddedPoint d = wallClass (d + 2) (d + 1) := by
  ext <;> simp [embeddedPoint]
  ring

/-- `M_{d,x}` has square `-2`; with `dim End = 2` (the dual numbers) Riemann–Roch gives
`dim Ext¹ = 2`: it is semirigid. -/
lemma isSpherical_embeddedPoint (d : ℤ) : IsSpherical intersection (embeddedPoint d) := by
  rw [IsSpherical, embeddedPoint_eq_wallClass, selfPairing_wallClass]; ring

/-- The class of `D(jC)/(I_x ⊗ D(-C))`: the inclusions `I_x ⊗ D(-C) ⊂ D(-C) ⊂ D ⊂ D(jC)`. -/
def idealQuotient (D : NS) (j : ℤ) : MukaiLattice ℤ NS :=
  lineBundle (D + j • curve) - idealPoint (D - curve)

/-- `R₀ = D/(I_x ⊗ D(-C)) = M_{d,x}` with `d = C·D`. -/
lemma idealQuotient_zero (D : NS) :
    idealQuotient D 0 = embeddedPoint (intersection curve D) := by
  rw [idealQuotient, embeddedPoint, idealPoint, zero_smul, add_zero,
    ← lineBundle_sub_lineBundle_sub_curve]
  abel

/-- **The layers.** `0 → R_j → R_{j+1} → 𝒪_C(d - 2(j + 1)) → 0` with `d = C·D`, because
`C² = -2`. -/
lemma idealQuotient_succ (D : NS) (j : ℤ) :
    idealQuotient D (j + 1) =
      idealQuotient D j + curveSheaf (intersection curve D - 2 * (j + 1)) := by
  have h := lineBundle_sub_lineBundle_sub_curve (D + (j + 1) • curve)
  have e : D + (j + 1) • curve - curve = D + j • curve := by
    rw [add_smul, one_smul]; abel
  rw [e] at h
  have hd : intersection curve (D + (j + 1) • curve) = intersection curve D - 2 * (j + 1) := by
    simp; ring
  rw [hd] at h
  rw [idealQuotient, idealQuotient, ← h]
  abel

/-- `K_ε` for `ε ∈ {0, 1}`: `K₀ = 𝒪_X` and `K₁ = 𝒪_X(-C - F)`, written `(-ε, -ε)`. -/
def tailDivisor (ε : ℤ) : NS := (-ε, -ε)

/-- `D = K_ε(-rC)` has degree `d = 2r + ε` on `C` and `H`-degree `-ε`. -/
lemma intersection_tailDivisor_sub (ε r : ℤ) :
    intersection curve (tailDivisor ε - r • curve) = 2 * r + ε ∧
      intersection polarization (tailDivisor ε - r • curve) = -ε := by
  constructor <;> simp [tailDivisor]
  ring

/-- **The thickening.** For `D = K_ε(-rC)`, `R_r = K_ε ⊗ 𝒪_X/(I_x I_C^{r+1})` has class
`(0, (r + 1)C, (r + 1)(r + 1 + ε) + 1)`: multiplicities `a = (r + 1)(r + 1 + ε) + 1` and
`b = a - (r + 1)`. For `d = 2` (`r = 1`, `ε = 0`) this is the `(5, 3)` quotient
`𝒪_X/(I_x I_C²)`. -/
lemma thickening_eq (ε r : ℤ) :
    idealQuotient (tailDivisor ε - r • curve) r =
      (0, (r + 1, 0), (r + 1) * (r + 1 + ε) + 1) := by
  ext <;> simp [idealQuotient, tailDivisor] <;> ring

lemma thickening_eq_wallClass (ε r : ℤ) :
    idealQuotient (tailDivisor ε - r • curve) r =
      wallClass ((r + 1) * (r + 1 + ε) + 1) ((r + 1) * (r + 1 + ε) + 1 - (r + 1)) := by
  rw [thickening_eq]; ext <;> simp
  ring

/-- The thickening has square `-2m²`, `m = r + 1`. Its endomorphism algebra has dimension
`h⁰(𝒪_{mC}) + 1 = m² + 1`, so Riemann–Roch gives `dim Ext¹ = 2(m² + 1) - 2m² = 2`. -/
lemma selfPairing_thickening (ε r : ℤ) :
    selfPairing intersection (idealQuotient (tailDivisor ε - r • curve) r) = -2 * (r + 1) ^ 2 ∧
      2 * ((r + 1) ^ 2 + 1) +
        selfPairing intersection (idealQuotient (tailDivisor ε - r • curve) r) = 2 := by
  rw [thickening_eq_wallClass, selfPairing_wallClass]
  constructor <;> ring

/-- `h⁰(𝒪_{mC}) = m²`: the layers of `𝒪_{mC}` along `C` are `𝒪_C(2j)`, `0 ≤ j < m`, with
`h⁰ = 2j + 1` and `h¹ = 0`. -/
lemma sum_range_two_mul_add_one (m : ℕ) : ∑ j ∈ Finset.range m, (2 * j + 1) = m ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- The sum of `v(𝒪_C(d - 2i))` over `0 ≤ i < n`. -/
lemma sum_curveSheaf (d : ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range n, curveSheaf (d - 2 * i) =
      (0, ((n : ℤ), 0), n * (d + 1) - n * (n - 1)) := by
  induction n with
  | zero => ext <;> simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ext <;> simp
    ring

/-- **The `B`-higher tower on classes.** Its quotients are `𝒪_x`, then `𝒪_C(j)` for
`j = d, d - 2, …, ε`, then the tail; the phase-one part adds up to the thickening. -/
lemma point_add_sum_curveSheaf (ε r : ℕ) :
    point + ∑ i ∈ Finset.range (r + 1), curveSheaf (2 * r + ε - 2 * i) =
      idealQuotient (tailDivisor ε - (r : ℤ) • curve) r := by
  rw [thickening_eq, sum_curveSheaf]
  ext <;> simp
  ring

/-! ### Twists on classes -/

/-- `T_A` and `T_A⁻¹` fix the class of a point of `C`: `⟨v(𝒪_x), v(A)⟩ = 0`. So
`v(U_x) = v(T_A 𝒪_x) = v(𝒪_x)`, of multiplicities `(1, 1)`. -/
lemma reflect_wallA_point : reflect intersection wallA point = point := by
  apply reflect_of_pairing_eq_zero
  simp [wallA]

/-- `T_A` sends `v(𝒪_C(j))` to `(j - 1)v(A) + j v(B)`: `⟨v(𝒪_C(j)), v(A)⟩ = C² = -2`. -/
lemma reflect_wallA_curveSheaf (j : ℤ) :
    reflect intersection wallA (curveSheaf j) = wallClass (j - 1) j := by
  rw [reflect_apply]
  ext <;> simp [wallA]
  ring

/-- `T_A⁻¹` sends `B` to the class of `𝒪_C(1)` (the Euler sequence on `C`) and `A` to `A[1]`. -/
lemma reflect_wallA_wallB : reflect intersection wallA wallB = curveSheaf 1 := by
  rw [reflect_apply]
  ext <;> simp [wallA, wallB]

/-- **The `A`-higher tower on classes, `d` odd.** Its quotients are `A^{d+1}`, `U_x`, then
`T_A 𝒪_C(j)` for `j = d, d - 2, …, 1`, then the tail; the phase-one part adds up to the
thickening. -/
lemma sum_A_side_odd (r : ℕ) :
    ((2 * r + 1 + 1 : ℕ) : ℤ) • wallA + point +
        ∑ i ∈ Finset.range (r + 1), reflect intersection wallA (curveSheaf (2 * r + 1 - 2 * i)) =
      idealQuotient (tailDivisor 1 - (r : ℤ) • curve) r := by
  simp_rw [reflect_wallA_curveSheaf]
  rw [thickening_eq]
  have : ∀ n : ℕ, ∑ i ∈ Finset.range n, wallClass ((2 * r + 1 - 2 * i : ℤ) - 1)
      (2 * r + 1 - 2 * i) =
        ((0, (-(n : ℤ), 0), (n : ℤ) * (2 * r) - n * (n - 1)) : MukaiLattice ℤ NS) := by
    intro n
    induction n with
    | zero => ext <;> simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ext <;> simp <;> ring
  rw [this]
  ext <;> simp [wallA] <;> ring

/-- **The `A`-higher tower on classes, `d` even.** Its quotients are `A^{d+1}`, `U_x`, then
`T_A 𝒪_C(j)` for `j = d, d - 2, …, 2`, then the tail. -/
lemma sum_A_side_even (r : ℕ) :
    ((2 * r + 1 : ℕ) : ℤ) • wallA + point +
        ∑ i ∈ Finset.range r, reflect intersection wallA (curveSheaf (2 * r - 2 * i)) =
      idealQuotient (tailDivisor 0 - (r : ℤ) • curve) r := by
  simp_rw [reflect_wallA_curveSheaf]
  rw [thickening_eq]
  have : ∀ n : ℕ, ∑ i ∈ Finset.range n, wallClass ((2 * r - 2 * i : ℤ) - 1) (2 * r - 2 * i) =
      ((0, (-(n : ℤ), 0), (n : ℤ) * (2 * r - 1) - n * (n - 1)) : MukaiLattice ℤ NS) := by
    intro n
    induction n with
    | zero => ext <;> simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ext <;> simp <;> ring
  rw [this]
  ext <;> simp [wallA] <;> ring

/-- **The one-letter tower on classes.** For `L = K_ε(-(r + 1)C)`, the class of
`T_L 𝒪_x = (I_x ⊗ L)[1]` is that of its quotients: the wall quotient `R_r` and the tail
`K_ε[1]`. For `ε = r = 0` this is the tower `M_x`, `𝒪_X[1]` of `T_{𝒪_X(-C)} 𝒪_x`. -/
lemma reflect_lineBundle_point (ε r : ℤ) :
    reflect intersection (lineBundle (tailDivisor ε - (r + 1) • curve)) point =
      idealQuotient (tailDivisor ε - r • curve) r - lineBundle (tailDivisor ε) := by
  rw [reflect_apply, thickening_eq]
  ext <;> simp [tailDivisor]
  ring

/-- **The two-letter tower on classes.** For `D = K_ε(-rC)`, `d = 2r + ε`, `n = 2 + ε`,
`L = D(-C)`, `K = D(nF)` and `V = D((n + 1)F)`, the class of `T_K⁻¹ T_L 𝒪_x` is that of its
quotients `K[1]`, `M_{d,x}` and `V^{⊕n}`. -/
lemma reflect_reflect_point (ε r : ℤ) :
    reflect intersection (lineBundle (tailDivisor ε - r • curve + (2 + ε) • fibre))
        (reflect intersection (lineBundle (tailDivisor ε - r • curve - curve)) point) =
      -lineBundle (tailDivisor ε - r • curve + (2 + ε) • fibre) + embeddedPoint (2 * r + ε) +
        (2 + ε) • lineBundle (tailDivisor ε - r • curve + (3 + ε) • fibre) := by
  rw [reflect_apply, reflect_apply]
  ext <;> simp [tailDivisor, embeddedPoint] <;> ring

/-- **The rank-two example on classes.** Let `S` be the nonsplit extension of `𝒪_X(-C)` by
`K = 𝒪_X(-2C + 2F)`. The common class of `T_S 𝒪_x` and `T_S⁻¹ 𝒪_x` is that of the quotients of
either tower: `K[1], (I_x ⊗ K)[1], A^{⊕2}, 𝒪_X[1]^{⊕2}` and
`K[1]^{⊕2}, 𝒪_C(x) ⊕ A, 𝒪_X[1]^{⊕2}`. -/
lemma reflect_rankTwo_point :
    reflect intersection (lineBundle (-2, 2) + lineBundle (-1, 0)) point =
        -lineBundle (-2, 2) - idealPoint (-2, 2) + (2 : ℤ) • wallA - (2 : ℤ) • lineBundle 0 ∧
      reflect intersection (lineBundle (-2, 2) + lineBundle (-1, 0)) point =
        -((2 : ℤ) • lineBundle (-2, 2)) + (curveSheaf 1 + wallA) - (2 : ℤ) • lineBundle 0 := by
  constructor <;> rw [reflect_apply] <;> ext <;> simp [wallA]

/-- `v(𝒪_Γ(D)) = (0, F, k)` for a line bundle of degree `k` on a smooth fibre `Γ`, an elliptic
curve, where `χ(𝒪_Γ(D)) = k`. -/
def fibreSheaf (k : ℤ) : MukaiLattice ℤ NS := (0, fibre, k)

@[simp] lemma fibreSheaf_def (k : ℤ) : fibreSheaf k = (0, fibre, k) := rfl

/-- **The three-letter word on classes.** With `L = 𝒪_X(-2C)`, `K = 𝒪_X(-C + 2F)` and
`V = 𝒪_X(-C + 3F)`, the class of `T_V⁻¹ T_K⁻¹ T_L 𝒪_x` is `(0, C + F, 3)`. It is the class of
the line bundle `𝒪_{C+Γ}(C + 4F)` on the union of the section and the fibre `Γ` through `x`, and
of its HN quotients `𝒪_C(1)` and `𝒪_Γ(x)`. -/
lemma reflect_threeLetter_point :
    reflect intersection (lineBundle (-1, 3)) (reflect intersection (lineBundle (-1, 2))
        (reflect intersection (lineBundle (-2, 0)) point)) = (0, (1, 1), 3) ∧
      lineBundle (1, 4) - lineBundle (0, 3) = (0, (1, 1), 3) ∧
      curveSheaf 1 + fibreSheaf 1 = (0, (1, 1), 3) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [reflect_apply]
    ext <;> simp
  · ext <;> simp
  · ext <;> simp

/-- **The class of a stable object in charge coordinates.** For `v = (r, aC + bF, s)` put
`p = 12r - 4s + 2a - b` (four times the real part of the charge of the curve wall) and
`q = b - r` (its imaginary part). Then `v² ≥ -2` is equivalent to
`(43r - 2(p + 2q))² + 43(4a - r - 2q)² ≤ 4(p + 2q)² + 172q² + 688`: the difference of the two
sides is `344(v² + 2)`. For a bounded charge this confines `(r, a)` to an ellipse, and then
`4s = 11r + 2a - q - p`. -/
theorem neg_two_le_selfPairing_iff {r a b s p q : ℤ} (hp : p = 12 * r - 4 * s + 2 * a - b)
    (hq : q = b - r) :
    -2 ≤ selfPairing intersection (r, (a, b), s) ↔
      (43 * r - 2 * (p + 2 * q)) ^ 2 + 43 * (4 * a - r - 2 * q) ^ 2 ≤
        4 * (p + 2 * q) ^ 2 + 172 * q ^ 2 + 688 := by
  have key : 4 * (p + 2 * q) ^ 2 + 172 * q ^ 2 + 688 -
      ((43 * r - 2 * (p + 2 * q)) ^ 2 + 43 * (4 * a - r - 2 * q) ^ 2) =
      344 * (selfPairing intersection (r, (a, b), s) + 2) := by
    subst hp hq
    simp only [selfPairing_mk, intersection_apply]
    ring
  constructor <;> intro h <;> linarith

/-! ### The parity argument -/

/-- The parity computation behind `not_isSpherical_sub_of_odd_rank`, in `ℤ/2`. -/
private lemma parity_core :
    ∀ ρ α σ h t s : ZMod 2, ρ = 1 → α ^ 2 - α * (ρ + 2) + ρ * σ = 1 →
      t ^ 2 - t * (h + 1) + h * s = 1 →
      -2 * α * t + α * (h + 1) + (ρ + 2) * t - ρ * s - h * σ = -1 → False := by
  decide

/-- **The parity argument.** Let `v` be a root of odd rank with `H·c(v) - rk(v) = 2`. If `u` is a
root with `H·c(u) - rk(u) = 1`, then `v - u` is not a root. On the curve wall the imaginary part
of the charge is `H·c - rk`, so a nontrivial filtration of a stable-free object of class `v` by
stable spherical factors of positive imaginary part would need two roots of imaginary part one;
this excludes it. -/
theorem not_isSpherical_sub_of_odd_rank {v u : MukaiLattice ℤ NS}
    (hv : IsSpherical intersection v) (hodd : Odd v.1)
    (hv2 : intersection polarization v.2.1 - v.1 = 2) (hu : IsSpherical intersection u)
    (hu1 : intersection polarization u.2.1 - u.1 = 1) :
    ¬IsSpherical intersection (v - u) := by
  intro hvu
  obtain ⟨ρ, ⟨α, β⟩, σ⟩ := v
  obtain ⟨h, ⟨t, b⟩, s⟩ := u
  simp only [IsSpherical, selfPairing_mk, intersection_apply, Prod.mk_sub_mk, polarization_fst,
    polarization_snd] at hv hv2 hu hu1 hvu
  have hβ : β = ρ + 2 := by linarith
  have hb : b = h + 1 := by linarith
  subst hβ hb
  have e1 : α ^ 2 - α * (ρ + 2) + ρ * σ = 1 := by
    have : 2 * (α ^ 2 - α * (ρ + 2) + ρ * σ) = 2 * 1 := by linear_combination -hv
    exact mul_left_cancel₀ two_ne_zero this
  have e2 : t ^ 2 - t * (h + 1) + h * s = 1 := by
    have : 2 * (t ^ 2 - t * (h + 1) + h * s) = 2 * 1 := by linear_combination -hu
    exact mul_left_cancel₀ two_ne_zero this
  have e3 : -2 * α * t + α * (h + 1) + (ρ + 2) * t - ρ * s - h * σ = -1 := by
    have : 2 * (-2 * α * t + α * (h + 1) + (ρ + 2) * t - ρ * s - h * σ) = 2 * (-1) := by
      linear_combination hv + hu - hvu
    exact mul_left_cancel₀ two_ne_zero this
  refine parity_core ρ α σ h t s (ZMod.intCast_eq_one_iff_odd.mpr hodd) ?_ ?_ ?_
  · exact_mod_cast congrArg (Int.cast : ℤ → ZMod 2) e1
  · exact_mod_cast congrArg (Int.cast : ℤ → ZMod 2) e2
  · exact_mod_cast congrArg (Int.cast : ℤ → ZMod 2) e3

end AlgebraicGeometry.K3.EllipticWithSection
