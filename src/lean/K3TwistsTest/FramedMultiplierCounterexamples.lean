/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Combinatorics.DT.Inversion
import K3Twists.Combinatorics.DT.Quivers
import Mathlib.Data.ZMod.Basic

/-!
# The framed multiplier: counterexamples and checks

The hypotheses of the inversion theorems cannot be dropped, and two formulas fail outside their
range:

* over `ℤ/2`, `(1 - x)² = 1 - x²`, so `e ↦ S_e` is not injective without characteristic zero
  (`S_not_injective_zmod2`);
* over `ℚ` the series `1 + x/2` is no multiplier with integer exponents, so the big Witt
  bijection is a statement over `ℤ` (`not_surj_rat`);
* the `(1, 1)` formula `e_a e_b - e_{a+b}` needs `a ≠ b`: for `S_e = 1 - x` the coefficient of
  `x²` is `0`, not `1`;
* proportionality of the exponent to `p·α` is not the DT statement: `e_{2e₁}(p) = p₁` is additive
  in `p` but is not `Ω (p·α)` for an integer `Ω`.

It also evaluates the Tits form of `A_3` at a few vectors, and checks the table computation of
`K3Twists/Combinatorics/DT/TwoVertex.lean` against the symbolic `xy` coefficient of the affine
Kronecker multiplier.

Built by `lake test`.
-/

namespace MvPowerSeries.FramedMultiplier.Counterexamples

open MvPowerSeries MvPowerSeries.FramedMultiplier

/-- **Injectivity fails over `ℤ/2`**: `(1 - x)² = 1 - x²`. -/
theorem S_not_injective_zmod2 :
    ∃ e e' : (Unit →₀ ℕ) → ℤ, S (R := ZMod 2) e = S e' ∧ ∃ α : Pos Unit, e α.1 ≠ e' α.1 := by
  classical
  let a1 : Pos Unit := ⟨Finsupp.single () 1, by simp⟩
  let a2 : Pos Unit := ⟨Finsupp.single () 2, by simp⟩
  let e : (Unit →₀ ℕ) → ℤ := fun β => if β = Finsupp.single () 1 then 2 else 0
  let e' : (Unit →₀ ℕ) → ℤ := fun β => if β = Finsupp.single () 2 then 1 else 0
  have h12 : (Finsupp.single () 2 : Unit →₀ ℕ) ≠ Finsupp.single () 1 := by
    intro h
    have := congrArg (· ()) h
    simp at this
  refine ⟨e, e', ?_, a1, by simp [e, e', a1, h12.symm]⟩
  rw [S_eq_prod e {a1} (fun α hα => by
        simp only [Finset.mem_singleton] at hα
        simp only [e]
        rw [ite_eq_right_iff]
        intro h
        exact absurd (Subtype.ext h) hα),
      S_eq_prod e' {a2} (fun α hα => by
        simp only [Finset.mem_singleton] at hα
        simp only [e']
        rw [ite_eq_right_iff]
        intro h
        exact absurd (Subtype.ext h) hα)]
  simp only [Finset.prod_singleton, factor]
  have he1 : e a1.1 = 2 := by simp [e, a1]
  have he2 : e' a2.1 = 1 := by simp [e', a2]
  rw [he1, he2, zpow_one, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
    Units.val_pow_eq_pow_val, unitX_val, unitX_val]
  have h2 : (2 : MvPowerSeries Unit (ZMod 2)) = 0 := by
    rw [← map_ofNat (C (σ := Unit) (R := ZMod 2)) 2,
      show (OfNat.ofNat 2 : ZMod 2) = 0 from rfl, map_zero]
  have hm : (monomial (Finsupp.single () 1) (1 : ZMod 2)) ^ 2 =
      monomial (Finsupp.single () 2) 1 := by
    rw [monomial_pow]
    simp
  simp only [a1, a2]
  rw [sub_sq, hm, mul_one, h2, zero_mul, sub_zero, one_pow, sub_eq_add_neg, ← map_neg]
  congr 2

/-- **Surjectivity fails over `ℚ`**: `1 + x/2` is not `S_e` for integer exponents. -/
theorem not_surj_rat :
    ¬∃ e : (Unit →₀ ℕ) → ℤ, S (R := ℚ) e = 1 + monomial (Finsupp.single () 1) (1 / 2 : ℚ) := by
  classical
  rintro ⟨e, he⟩
  have hpos : Finsupp.single () 1 ≠ (0 : Unit →₀ ℕ) := by simp
  have h := coeff_S_single (R := ℚ) e ()
  rw [he] at h
  simp [coeff_one, hpos] at h
  have : (2 : ℚ) * (e (Finsupp.single () 1) : ℚ) = -1 := by linarith
  have hz : (2 : ℤ) * e (Finsupp.single () 1) = -1 := by exact_mod_cast this
  omega

/-- **The `(1, 1)` formula needs `a ≠ b`.** For `S_e = 1 - x` the coefficient of `x²` is `0`,
while `e_x e_x - e_{2x} = 1`. -/
example : coeff (Finsupp.single () 1 + Finsupp.single () 1)
    (S (R := ℤ) (fun β => if β = Finsupp.single () 1 then 1 else 0)) ≠ 1 := by
  classical
  have hpos : (Finsupp.single () 1 : Unit →₀ ℕ) ≠ 0 := by simp
  rw [S_eq_prod _ {⟨_, hpos⟩} (fun α hα => by
        simp only [Finset.mem_singleton] at hα
        rw [ite_eq_right_iff]
        intro h
        exact absurd (Subtype.ext h) hα)]
  simp only [Finset.prod_singleton, factor, ↓reduceIte, zpow_one, unitX_val]
  rw [map_sub, coeff_one, coeff_monomial]
  have h2 : (Finsupp.single () 1 + Finsupp.single () 1 : Unit →₀ ℕ) ≠ 0 := by simp
  have h3 : (Finsupp.single () 1 + Finsupp.single () 1 : Unit →₀ ℕ) ≠ Finsupp.single () 1 := by
    intro h
    have := congrArg (· ()) h
    simp at this
  simp [h2, h3]

/-- **Proportionality is not the DT statement.** The exponent `e_{2e₁}(p) = p₁` is additive in
`p` and proportional to `p·(2e₁) = 2p₁`, but it is not `Ω (p·α)` for an integer `Ω`. -/
example : ¬∃ Ω : ℤ, ∀ p : Unit → ℤ, p () = pair p (Finsupp.single () 2) * Ω := by
  rintro ⟨Ω, h⟩
  have := h 1
  rw [pair_single] at this
  simp at this
  omega

/-! ### The Tits form of `A_3` -/

open Quiver.TypeA in
example : titsForm (n := 3) ![1, 1, 1] = 1 ∧ titsForm (n := 3) ![1, 0, 1] = 2 ∧
    titsForm (n := 3) ![1, 2, 1] = 2 ∧ titsForm (n := 2) ![1, 1] = 1 := by
  decide

/-! ### The table computation agrees with the symbolic coefficient -/

/-- At framing `(4, -3)` (the curve-wall framing for `m = 3`) the table gives
`xy` coefficient `-10 = 2 - 3·4`, as `coeff_kronecker_one_one` does symbolically. -/
example : coeff (mk2 1 1) (framedS (R := ℤ) ![4, -3] kroneckerBPS) = -10 := by
  rw [framedS, coeff_S_mk2 _ (fun u v => (4 * u + -3 * v) * kroneckerIndex u v)
    (fun u v => by rw [kronecker_exponent])]
  decide

example : coeff (mk2 1 1) (framedS (R := ℤ) ![4, -3] kroneckerBPS) = -10 := by
  rw [coeff_kronecker_one_one]
  norm_num

end MvPowerSeries.FramedMultiplier.Counterexamples
