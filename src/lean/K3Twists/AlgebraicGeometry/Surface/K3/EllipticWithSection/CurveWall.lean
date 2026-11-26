/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.Lattice
import K3Twists.LinearAlgebra.BilinearForm.ReflectionGrowth
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The curve wall of an elliptic K3 surface with a section

On the elliptic K3 surface `X` with `NS(X) = ℤC ⊕ ℤF` of `EllipticWithSection/Lattice.lean`, the
HN towers of twisted points that pass through the curve with an embedded point are computed at
one stability condition on the wall where the section `C` is contracted: the double tilt of
Tramel and Xia (arXiv:1702.06252, §§3 and 5 and Theorem 6.12) with `H = C + 2F`, `β = -C/4`,
`z = 2 - i` and curve cut `k = -1`. Its central charge is

  `Z(E) = -ch₂(E) + β·c₁(E) + 2 rk(E) + i (H·c₁(E) - rk(E))`,

which on a Mukai vector `(r, c, s)` (so `ch₂ = s - r`) is `charge`. That `Z` is the charge of a
stability condition, that `A = 𝒪_C` and `B = 𝒪_C(-1)[1]` are stable of phase one, and the heart
membership of the tails are the cited geometry and are not formalized. This file checks the
numbers those towers use, exactly:

* the inputs of the construction: `H² = 2`, `β·H = 0`, `β·C = 1/2` and `2 + 1/H² > -β²/2`
  (`beta_conditions`);
* the wall: `Z(aA + bB) = -(a + b)/2` (`charge_wallClass`), so every wall object has phase one;
  `Z(A) = Z(B) = -1/2`, `Z(𝒪_x) = -1`, `Z(𝒪_C(j)) = -(2j + 1)/2` and
  `Z(M_{d,x}) = -(2d + 3)/2`, which is `-3/2`, `-5/2`, `-7/2` for `d = 0, 1, 2`;
* the tails, of phase in `(1/2, 1)`: `Z(𝒪_X[1]) = -2 + i` and `Z(𝒪_X(-C - F)[1]) = -7/4 + 2i`;
* the line bundles of the two-letter word, `Z(𝒪_X(-C + 2F)) = 4 + i` and
  `Z(𝒪_X(-C + 3F)) = 19/4 + 2i`, and of the rank-two example, `Z(𝒪_X(-2C + 2F)) = 17/2 + i` and
  `Z(I_x ⊗ 𝒪_X(-2C + 2F)) = 19/2 + i`, all of phase in `(0, 1/2)`;
* the imaginary part is `H·c - r` (`im_charge`), so the parity argument of `Lattice.lean` gives
  the stability of `𝒪_X(-C - F)[1]` and of every line bundle of `H`-slope `3`
  (`not_split_tail_odd`, `not_split_slope_three`);
* near the wall the order of phases on wall objects is the order of their `B`-fractions
  (`cross_restrictedCharge`), with the fractions `j/(2j + 1)` of `𝒪_C(j)` and `j/(2j - 1)` of
  `T_A 𝒪_C(j)` ordered as the towers need;
* the first three words `T_{𝒪_X(-2C)}`, `T_{𝒪_X(-C + 2F)}⁻¹`, `T_{𝒪_X(-C + 3F)}⁻¹` applied to
  `𝒪_x`: the charges `-4 - i`, `-7/2`, `19/2 + 4i` of the two-letter tower add up to `2 + 3i`,
  and the masses at the wall are `4 + √5`, `(7/2)(1 + √17)` and `3/2 + √41/4`;
* the Euler characteristics behind the Ext dimensions of the towers, and the Barbacovi–Kim
  number `7 + 4√3` of the word `T_{𝒪_C} T_{𝒪_C(2)}` (arXiv:2107.06079, Theorem 4.0.1).
-/

namespace AlgebraicGeometry.K3.EllipticWithSection

open Complex Mukai
open scoped Real

/-! ### The charge -/

/-- `β·c` for `β = -C/4`. -/
def betaPairing (c : NS) : ℚ := -(intersection curve c : ℚ) / 4

/-- The hypotheses of the construction at `H = C + 2F`, `β = -C/4`: `H² = 2`, `β·H = 0`,
`β·C = 1/2` and `2 + 1/H² > -β²/2`, where `β² = C²/16 = -1/8`. -/
lemma beta_conditions :
    intersection polarization polarization = 2 ∧ betaPairing polarization = 0 ∧
      betaPairing curve = 1 / 2 ∧
      -((intersection curve curve : ℚ) / 16) / 2 <
        2 + 1 / (intersection polarization polarization) := by
  refine ⟨by simp, by simp [betaPairing], by norm_num [betaPairing], by norm_num⟩

/-- The central charge `Z(E) = -ch₂(E) + β·c₁(E) + 2 rk(E) + i (H·c₁(E) - rk(E))` of the
curve-wall stability condition, on Mukai vectors `(r, c, s)` with `ch₂ = s - r`. -/
noncomputable def charge : MukaiLattice ℤ NS →+ ℂ where
  toFun v := -((v.2.2 - v.1 : ℤ) : ℂ) - (intersection curve v.2.1 : ℂ) / 4 + 2 * (v.1 : ℂ) +
    I * ((intersection polarization v.2.1 : ℂ) - v.1)
  map_zero' := by simp
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Int.cast_add, Int.cast_sub]
    ring

lemma charge_apply (v : MukaiLattice ℤ NS) :
    charge v = -((v.2.2 - v.1 : ℤ) : ℂ) - (intersection curve v.2.1 : ℂ) / 4 + 2 * (v.1 : ℂ) +
      I * ((intersection polarization v.2.1 : ℂ) - v.1) :=
  rfl

/-- The imaginary part of the charge is `H·c - r`. -/
lemma im_charge (v : MukaiLattice ℤ NS) :
    (charge v).im = ((intersection polarization v.2.1 - v.1 : ℤ) : ℝ) := by
  simp [charge_apply]

/-- The real part of the charge is `-ch₂ + β·c + 2r = 3r - s - (C·c)/4`. -/
lemma re_charge (v : MukaiLattice ℤ NS) :
    (charge v).re = 3 * (v.1 : ℝ) - v.2.2 - (intersection curve v.2.1 : ℝ) / 4 := by
  simp [charge_apply]; ring

/-! ### The wall: phase one -/

/-- Every wall class is a negative real multiple of `1`: `Z(aA + bB) = -(a + b)/2`. -/
lemma charge_wallClass (a b : ℤ) : charge (wallClass a b) = -((a + b : ℤ) : ℂ) / 2 := by
  rw [charge_apply, wallClass_eq]
  simp only [intersection_curve_apply, intersection_polarization_apply]
  push_cast
  ring

lemma charge_wallA : charge wallA = -1 / 2 := by
  rw [wallA_eq, charge_wallClass]; norm_num

lemma charge_wallB : charge wallB = -1 / 2 := by
  rw [wallB_eq, charge_wallClass]; norm_num

lemma charge_point : charge point = -1 := by
  rw [point_eq_wallClass, charge_wallClass]; norm_num

lemma charge_curveSheaf (j : ℤ) : charge (curveSheaf j) = -(2 * j + 1) / 2 := by
  rw [curveSheaf_eq_wallClass, charge_wallClass]; push_cast; ring

/-- `Z(M_{d,x}) = -(2d + 3)/2`. -/
lemma charge_embeddedPoint (d : ℤ) : charge (embeddedPoint d) = -(2 * d + 3) / 2 := by
  rw [embeddedPoint_eq_wallClass, charge_wallClass]; push_cast; ring

/-- The charges at the wall of the first three members: `Z(M_x) = -3/2`, `Z(M_{1,x}) = -5/2`,
`Z(M_{2,x}) = -7/2`. -/
lemma charge_embeddedPoint_values :
    charge (embeddedPoint 0) = -3 / 2 ∧ charge (embeddedPoint 1) = -5 / 2 ∧
      charge (embeddedPoint 2) = -7 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [charge_embeddedPoint] <;> norm_num

/-- **Phase one.** A nonzero wall class with nonnegative multiplicities has charge on the
negative real axis: its phase is one. -/
lemma arg_charge_wallClass {a b : ℤ} (hab : 0 < a + b) : arg (charge (wallClass a b)) = π := by
  rw [arg_eq_pi_iff, charge_wallClass]
  have : (0 : ℝ) < ((a + b : ℤ) : ℝ) := by exact_mod_cast hab
  constructor
  · simp only [neg_div, neg_re, div_ofNat_re, intCast_re]; linarith
  · simp

/-! ### The tails and the line bundles of the words -/

/-- `Z(𝒪_X(aC + bF)) = -a(b - a) - (b - 2a)/4 + 2 + i(b - 1)`. -/
lemma charge_lineBundle (D : NS) :
    charge (lineBundle D) =
      -((D.1 * (D.2 - D.1) : ℤ) : ℂ) - ((D.2 - 2 * D.1 : ℤ) : ℂ) / 4 + 2 + I * ((D.2 : ℂ) - 1) := by
  rw [charge_apply]
  simp only [lineBundle_def, intersection_curve_apply, intersection_polarization_apply]
  push_cast
  ring

/-- `Z(𝒪_X[1]) = -2 + i`. -/
lemma charge_structureSheaf_shift : charge (-lineBundle 0) = -2 + I := by
  rw [map_neg, charge_lineBundle]; simp only [Prod.fst_zero, Prod.snd_zero]; push_cast; ring

/-- `Z(𝒪_X(-C - F)[1]) = -7/4 + 2i`. -/
lemma charge_tailOdd_shift : charge (-lineBundle (-1, -1)) = -7 / 4 + 2 * I := by
  rw [map_neg, charge_lineBundle]; push_cast; ring

/-- `Z(𝒪_X(-C + 2F)) = 4 + i` and `Z(𝒪_X(-C + 3F)) = 19/4 + 2i`: the line bundles `K` and `V` of
the two-letter word `T_K⁻¹ T_{𝒪_X(-2C)}`. -/
lemma charge_twoLetter :
    charge (lineBundle (-1, 2)) = 4 + I ∧ charge (lineBundle (-1, 3)) = 19 / 4 + 2 * I := by
  constructor <;> rw [charge_lineBundle] <;> push_cast <;> ring

/-- `Z(𝒪_X(-2C + 2F)) = 17/2 + i` and `Z(I_x ⊗ 𝒪_X(-2C + 2F)) = 19/2 + i`: the subbundle and its
ideal in the rank-two example. -/
lemma charge_rankTwo :
    charge (lineBundle (-2, 2)) = 17 / 2 + I ∧ charge (idealPoint (-2, 2)) = 19 / 2 + I := by
  refine ⟨?_, ?_⟩
  · rw [charge_lineBundle]; push_cast; ring
  · rw [idealPoint_def, map_sub, charge_lineBundle, charge_point]; push_cast; ring

/-- A charge with positive imaginary part has phase in `(0, 1)`. -/
lemma arg_mem_Ioo_of_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < arg z ∧ arg z < π := by
  refine ⟨lt_of_le_of_ne (arg_nonneg_iff.mpr hz.le) ?_, arg_lt_pi_iff.mpr (Or.inr hz.ne')⟩
  intro h
  exact hz.ne' (arg_eq_zero_iff.mp h.symm).2

/-- **The order of the tower of `T_{𝒪_X(-C)} 𝒪_x`.** `M_x` has phase one and the tail `𝒪_X[1]`
has phase `arg(-2 + i)/π`, strictly between `1/2` and `1`. -/
lemma arg_charge_structureSheaf_shift :
    π / 2 < arg (charge (-lineBundle 0)) ∧ arg (charge (-lineBundle 0)) < π ∧
      arg (charge (embeddedPoint 0)) = π := by
  rw [charge_structureSheaf_shift, embeddedPoint_eq_wallClass]
  refine ⟨?_, (arg_mem_Ioo_of_im_pos (by simp)).2, arg_charge_wallClass (by norm_num)⟩
  rw [← not_le, arg_le_pi_div_two_iff]
  norm_num

/-- `𝒪_X(-C - F)[1]` has phase strictly between `1/2` and `1`. -/
lemma arg_charge_tailOdd_shift :
    π / 2 < arg (charge (-lineBundle (-1, -1))) ∧ arg (charge (-lineBundle (-1, -1))) < π := by
  rw [charge_tailOdd_shift]
  refine ⟨?_, (arg_mem_Ioo_of_im_pos (by simp)).2⟩
  rw [← not_le, arg_le_pi_div_two_iff]
  norm_num

/-- `K = 𝒪_X(-C + 2F)` and `V = 𝒪_X(-C + 3F)` have phases in `(0, 1/2)`; with `M_{2,x}` of phase
one this is the order `φ(K[1]) > 1 = φ(M_{2,x}) > φ(V)` of the two-letter tower. -/
lemma arg_charge_twoLetter :
    0 < arg (charge (lineBundle (-1, 2))) ∧ arg (charge (lineBundle (-1, 2))) < π / 2 ∧
      0 < arg (charge (lineBundle (-1, 3))) ∧ arg (charge (lineBundle (-1, 3))) < π / 2 := by
  obtain ⟨hK, hV⟩ := charge_twoLetter
  rw [hK, hV]
  refine ⟨(arg_mem_Ioo_of_im_pos (by simp)).1, ?_, (arg_mem_Ioo_of_im_pos (by simp)).1, ?_⟩ <;>
    · rw [arg_lt_pi_div_two_iff]; left; norm_num

/-- The subbundle `𝒪_X(-2C + 2F)` and its ideal `I_x ⊗ 𝒪_X(-2C + 2F)` of the rank-two example
have phases in `(0, 1/2)`. -/
lemma arg_charge_rankTwo :
    0 < arg (charge (lineBundle (-2, 2))) ∧ arg (charge (lineBundle (-2, 2))) < π / 2 ∧
      0 < arg (charge (idealPoint (-2, 2))) ∧ arg (charge (idealPoint (-2, 2))) < π / 2 := by
  obtain ⟨hK, hI⟩ := charge_rankTwo
  rw [hK, hI]
  refine ⟨(arg_mem_Ioo_of_im_pos (by simp)).1, ?_, (arg_mem_Ioo_of_im_pos (by simp)).1, ?_⟩ <;>
    · rw [arg_lt_pi_div_two_iff]; left; norm_num

/-! ### Stability of the tails by parity -/

/-- **The odd tail is stable.** `𝒪_X(-C - F)[1]` is spherical with imaginary charge `2`; a
nontrivial filtration by stable spherical factors would need two roots of imaginary charge one,
which the parity argument excludes. -/
theorem not_split_tail_odd {u : MukaiLattice ℤ NS} (hu : IsSpherical intersection u)
    (hu1 : (charge u).im = 1) : ¬IsSpherical intersection (-lineBundle (-1, -1) - u) := by
  refine not_isSpherical_sub_of_odd_rank ((isSpherical_lineBundle _).neg intersection)
    ⟨-1, by simp⟩ (by simp) hu ?_
  rw [im_charge] at hu1
  exact_mod_cast hu1

/-- **Line bundles of `H`-slope `3` are stable.** `𝒪_X(aC + 3F)` has imaginary charge `2`, and
the parity argument excludes a splitting into two roots of imaginary charge one. -/
theorem not_split_slope_three (a : ℤ) {u : MukaiLattice ℤ NS} (hu : IsSpherical intersection u)
    (hu1 : (charge u).im = 1) : ¬IsSpherical intersection (lineBundle (a, 3) - u) := by
  refine not_isSpherical_sub_of_odd_rank (isSpherical_lineBundle _) ⟨0, by simp⟩ (by simp) hu ?_
  rw [im_charge] at hu1
  exact_mod_cast hu1

/-! ### The phase order near the wall -/

/-- **Phases near the wall are ordered by `B`-fractions.** Near the wall the charge of a wall
object of multiplicities `(a, b)` is `a z_A + b z_B`. The cross product of two such charges is
`(ab' - a'b)` times that of `z_A, z_B`; for charges in the upper half-plane its sign is the order
of the phases. So on the side where `B` has the larger phase, phase increases with the fraction
`b/(a + b)`, and on the other side it decreases. -/
lemma cross_restrictedCharge (zA zB : ℂ) (a b a' b' : ℝ) :
    ((a : ℂ) * zA + b * zB).re * ((a' : ℂ) * zA + b' * zB).im -
        ((a : ℂ) * zA + b * zB).im * ((a' : ℂ) * zA + b' * zB).re =
      (a * b' - a' * b) * (zA.re * zB.im - zA.im * zB.re) := by
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im]
  ring

/-- The `B`-fraction `j/(2j + 1)` of `𝒪_C(j)` increases strictly with `j`. -/
lemma curveSheaf_fraction_strictMono {j j' : ℕ} (h : j < j') :
    (j : ℚ) / (2 * j + 1) < j' / (2 * j' + 1) := by
  have h' : (j : ℚ) < j' := by exact_mod_cast h
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The `B`-fraction of `𝒪_C(j)` is below `1/2`, the fraction of `𝒪_x`. -/
lemma curveSheaf_fraction_lt_half (j : ℕ) : (j : ℚ) / (2 * j + 1) < 1 / 2 := by
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- The `B`-fraction `j/(2j - 1)` of `T_A 𝒪_C(j)` decreases strictly in `j ≥ 1` and stays above
`1/2`, the fraction of `U_x = T_A 𝒪_x`. -/
lemma twistCurveSheaf_fraction {j j' : ℕ} (hj : 1 ≤ j) (h : j < j') :
    (j' : ℚ) / (2 * j' - 1) < j / (2 * j - 1) ∧ (1 : ℚ) / 2 < j / (2 * j - 1) := by
  have hj' : (1 : ℚ) ≤ j := by exact_mod_cast hj
  have h' : (j : ℚ) < j' := by exact_mod_cast h
  constructor
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  · rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; linarith

/-- **The section-evaluation bound.** A proper subobject of `𝒪_C(d)` in the wall category whose
image in the `B`-copies has dimension `j > 0` meets the `A`-copies in a space containing both
variable multiples of that image, of dimension `i ≥ j + 1`; its `B`-fraction is at most
`j/(2j + 1)`, which is below `d/(2d + 1)` when `j < d`. -/
lemma subobject_fraction_le {i j : ℕ} (hij : j + 1 ≤ i) :
    (j : ℚ) / (i + j) ≤ j / (2 * j + 1) := by
  have h : (j : ℚ) + 1 ≤ i := by exact_mod_cast hij
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have : (0 : ℚ) < j := by exact_mod_cast hj
    exact div_le_div_of_nonneg_left this.le (by positivity) (by linarith)

/-! ### The first three words and their masses

`E = T_L 𝒪_x` with `L = 𝒪_X(-2C)` has HN quotients `R = 𝒪_X/(I_x I_C²)` and `𝒪_X[1]`;
`Y = T_K⁻¹ E` with `K = 𝒪_X(-C + 2F)` has `K[1]`, `M_{2,x}` and `V^{⊕2}`, `V = 𝒪_X(-C + 3F)`;
and `T_V⁻¹ Y = 𝒪_{C+Γ}(C + 4F)` has `𝒪_C(1)` and `𝒪_Γ(x)`. The mass at the wall is the sum of
the moduli of the charges of the HN quotients. -/

lemma norm_of_eq {z : ℂ} {x y : ℝ} (h : z = x + y * I) : ‖z‖ = √(x ^ 2 + y ^ 2) := by
  rw [h, norm_add_mul_I]

/-- `|Z(𝒪_X[1])| = |-2 + i| = √5`. -/
lemma norm_charge_structureSheaf_shift : ‖charge (-lineBundle 0)‖ = √5 := by
  rw [charge_structureSheaf_shift, norm_of_eq (x := -2) (y := 1) (by push_cast; ring)]
  norm_num

/-- `Z(𝒪_Γ(D)) = -k - 1/4 + i` for a line bundle of degree `k` on a smooth fibre `Γ`. -/
lemma charge_fibreSheaf (k : ℤ) : charge (fibreSheaf k) = -k - 1 / 4 + I := by
  rw [charge_apply]
  simp only [fibreSheaf_def, intersection_curve_apply, intersection_polarization_apply,
    fibre_fst, fibre_snd]
  push_cast
  ring

/-- **The two-letter tower.** Its quotients have charges `-4 - i`, `-7/2` and `19/2 + 4i`, in
strictly decreasing phase, adding up to `2 + 3i`, the charge of the class of `T_K⁻¹ T_L 𝒪_x`. -/
lemma charge_twoLetter_tower :
    charge (-lineBundle (-1, 2)) = -4 - I ∧ charge (embeddedPoint 2) = -7 / 2 ∧
      charge ((2 : ℤ) • lineBundle (-1, 3)) = 19 / 2 + 4 * I ∧
      charge (reflect intersection (lineBundle (-1, 2))
        (reflect intersection (lineBundle (-2, 0)) point)) = 2 + 3 * I := by
  obtain ⟨hK, hV⟩ := charge_twoLetter
  refine ⟨by rw [map_neg, hK]; ring, (charge_embeddedPoint_values).2.2, ?_, ?_⟩
  · rw [map_zsmul, hV, zsmul_eq_mul]; push_cast; ring
  · rw [reflect_apply, reflect_apply, charge_apply]
    simp
    ring

/-- **The mass of the one-letter tower** `R`, `𝒪_X[1]` at the wall: `4 + √5`. -/
lemma mass_oneLetter :
    ‖charge (idealQuotient (tailDivisor 0 - (1 : ℤ) • curve) 1)‖ +
      ‖charge (-lineBundle 0)‖ = 4 + √5 := by
  have hR : charge (idealQuotient (tailDivisor 0 - (1 : ℤ) • curve) 1) = -4 := by
    rw [thickening_eq_wallClass, charge_wallClass]; norm_num
  rw [hR, norm_charge_structureSheaf_shift]
  norm_num

/-- **The mass of the two-letter tower** `K[1]`, `M_{2,x}`, `V^{⊕2}` at the wall:
`√17 + 7/2 + 5√17/2 = (7/2)(1 + √17)`. -/
lemma mass_twoLetter :
    ‖charge (-lineBundle (-1, 2))‖ + ‖charge (embeddedPoint 2)‖ +
      2 * ‖charge (lineBundle (-1, 3))‖ = 7 / 2 * (1 + √17) := by
  have hK : ‖charge (-lineBundle (-1, 2))‖ = √17 := by
    rw [charge_twoLetter_tower.1, norm_of_eq (x := -4) (y := -1) (by push_cast; ring)]
    norm_num
  have hM : ‖charge (embeddedPoint 2)‖ = 7 / 2 := by
    rw [(charge_embeddedPoint_values).2.2]; norm_num
  have hV : ‖charge (lineBundle (-1, 3))‖ = 5 / 4 * √17 := by
    rw [(charge_twoLetter).2, norm_of_eq (x := 19 / 4) (y := 2) (by push_cast; ring),
      show (19 / 4 : ℝ) ^ 2 + 2 ^ 2 = (5 / 4) ^ 2 * 17 by norm_num,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [hK, hM, hV]
  ring

/-- **The mass of the three-letter tower** `𝒪_C(1)`, `𝒪_Γ(x)` at the wall: `3/2 + √41/4`. The
fibre term has charge `-5/4 + i`, of phase between `1/2` and `1`, below `𝒪_C(1)`. -/
lemma mass_threeLetter :
    ‖charge (curveSheaf 1)‖ + ‖charge (fibreSheaf 1)‖ = 3 / 2 + √41 / 4 ∧
      π / 2 < arg (charge (fibreSheaf 1)) ∧ arg (charge (fibreSheaf 1)) < π := by
  have hF : charge (fibreSheaf 1) = -5 / 4 + I := by rw [charge_fibreSheaf]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · have hC : ‖charge (curveSheaf 1)‖ = 3 / 2 := by
      rw [charge_curveSheaf]; norm_num
    have hΓ : ‖charge (fibreSheaf 1)‖ = 1 / 4 * √41 := by
      rw [hF, norm_of_eq (x := -5 / 4) (y := 1) (by push_cast; ring),
        show (-5 / 4 : ℝ) ^ 2 + 1 ^ 2 = (1 / 4) ^ 2 * 41 by norm_num,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [hC, hΓ]
    ring
  · rw [hF, ← not_le, arg_le_pi_div_two_iff]; norm_num
  · rw [hF]; exact (arg_mem_Ioo_of_im_pos (by simp)).2

/-- The presentation of `𝒪_X(-2C)[1]` by `𝒪_C(2)`, `A` and `𝒪_X[1]` bounds its mass by
`5/2 + 1/2 + √5 = 3 + √5`. -/
lemma mass_bound_shift :
    curveSheaf 2 + wallA - lineBundle 0 = -lineBundle (-2, 0) ∧
      ‖charge (curveSheaf 2)‖ + ‖charge wallA‖ + ‖charge (-lineBundle 0)‖ = 3 + √5 := by
  refine ⟨by ext <;> simp [wallA], ?_⟩
  have h2 : ‖charge (curveSheaf 2)‖ = 5 / 2 := by rw [charge_curveSheaf]; norm_num
  have hA : ‖charge wallA‖ = 1 / 2 := by rw [charge_wallA]; norm_num [norm_one]
  rw [h2, hA, norm_charge_structureSheaf_shift]
  ring

/-! ### Euler characteristics behind the towers

`χ(E, F) = -⟨v(E), v(F)⟩`. -/

/-- In the rank-two example, `χ(𝒪_X(-C), 𝒪_X(-2C + 2F)) = -1`, so `dim Ext¹ = 1` (both `Hom`
groups vanish), and the extension `S` has class `(2, -3C + 2F, -7)`, a root. -/
lemma rankTwo_classes :
    pairing intersection (lineBundle (-1, 0)) (lineBundle (-2, 2)) = 1 ∧
      lineBundle (-2, 2) + lineBundle (-1, 0) = (2, (-3, 2), -7) ∧
      IsSpherical intersection (lineBundle (-2, 2) + lineBundle (-1, 0)) ∧
      intersection (-1, 2) (-1, 2) = -6 := by
  refine ⟨by simp, by ext <;> simp, ?_, by simp⟩
  simp [IsSpherical]

/-- In the two-letter word, `I = I_x ⊗ 𝒪_X(-2C)` has `χ(I, 𝒪_X(-C + 2F)) = 2 = 3 - 1` and
`χ(I, 𝒪_C) = -3`. -/
lemma twoLetter_euler :
    pairing intersection (idealPoint (-2, 0)) (lineBundle (-1, 2)) = -2 ∧
      pairing intersection (idealPoint (-2, 0)) wallA = 3 := by
  constructor <;> simp [wallA]

/-- For the thickening `R`, `χ(R, 𝒪_C) = 2(r + 1)`; with `dim Hom(R, A) = 1 - ε` and
`dim Hom(A, R) = d + 1` this forces `Ext¹(R, A) = 0`. -/
lemma thickening_euler (ε r : ℤ) :
    pairing intersection (idealQuotient (tailDivisor ε - r • curve) r) wallA = -2 * (r + 1) := by
  rw [thickening_eq]; simp [wallA]

/-- `RHom(𝒪_C, 𝒪_C(2))` has dimensions `3, 1, 0`: `χ = 2`. -/
lemma euler_curve_two : pairing intersection wallA (curveSheaf 2) = -2 := by
  simp [wallA]

/-- **The Barbacovi–Kim number.** For `Φ = T_{𝒪_C} T_{𝒪_C(2)}` the total dimension of
`RHom(𝒪_C, 𝒪_C(2))` is `4`, and Barbacovi–Kim (arXiv:2107.06079, Theorem 4.0.1) give
`exp h_cat(Φ) = (4² - 2 + √(4⁴ - 4·4²))/2 = 7 + 4√3`, while a point off `C` is fixed by `Φ`. -/
lemma barbacoviKim_four : ((4 : ℝ) ^ 2 - 2 + √(4 ^ 4 - 4 * 4 ^ 2)) / 2 = 7 + 4 * √3 := by
  have h : √((4 : ℝ) ^ 4 - 4 * 4 ^ 2) = 8 * √3 := by
    rw [show (4 : ℝ) ^ 4 - 4 * 4 ^ 2 = 8 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [h]; ring

/-- `7 + 4√3` is the larger root of `x² - 14x + 1`: by `barbacoviKim_four` it is
`sl2Rate (4² - 2)`, the Gelfand radius of the product `s₁ s₀` of the two simple reflections of the
rank-two wall at pairing `4` (`BilinearForm.gelfandRadius_reflectionProductMatrix`), which is a
root of the quadratic factor `x² - (4² - 2)x + 1` of the cubic of two reflections
(`BilinearForm.gelfandRadius_reflectionProductMatrix_root`). -/
lemma barbacoviKim_four_root : (7 + 4 * √3 : ℝ) ^ 2 - 14 * (7 + 4 * √3) + 1 = 0 := by
  have h4 : (2 : ℝ) < |4| := by norm_num
  have h := BilinearForm.gelfandRadius_reflectionProductMatrix_root h4
  rw [BilinearForm.gelfandRadius_reflectionProductMatrix h4, Matrix.sl2Rate_sq_sub_two,
    barbacoviKim_four] at h
  linear_combination h

end AlgebraicGeometry.K3.EllipticWithSection
