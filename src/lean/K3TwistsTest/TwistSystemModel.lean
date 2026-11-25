/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.GroupAction.TwistSystem
import Mathlib.Algebra.Group.Action.Option
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Twist-system models: what the axioms do not give

Two small models show that two inputs of the exponent theorem are independent of the others.

* **Sphericity is an input of its own.** The zero count `h = 0` on one object satisfies every
  field of `HomTwistSystem` (`T_S S = S[-1]` included), the lower bound (L) and directed
  connectivity, but `P_q = 0` for every `q`, so no logarithm of `P_q` is defined
  (`zeroModel_maxCount`). Positivity of `P_q` comes from `h(S, S) = 2`, which `zeroModel` fails.
* **The bound (U) for inverse letters needs more than (U) for the letters.** On `ℤ ∪ {∗}` with
  `ℤ` acting by translation, `h(u, v) = 1` if `v ≤ u` and `0` otherwise satisfies every field
  of `HomTwistSystem` for the letter `+1` with centre `∗`, but not (U) for the letter `-1`
  (`asymModel_not_upper_inv`). Symmetry of `h` supplies it (`HomTwistSystem₀.upper_inv`).

The real-object instance, with positive exponent, is
`AlgebraicGeometry.K3.PicardRankOne.eulerTwistSystem`.

Built by `lake test`.
-/

namespace K3TwistsTest.TwistSystemModel

/-- The zero count on one object, with the trivial group. -/
def zeroModel : HomTwistSystem Unit Unit Unit Unit where
  S _ := ()
  T _ := 1
  c _ := ()
  h _ _ := 0
  h_smul _ _ _ := rfl
  upper _ _ _ := by simp
  h_twist_centre _ _ := rfl

theorem zeroModel_lowerBound : zeroModel.toHomTwistSystem₀.LowerBound := fun _ _ _ => by
  simp [zeroModel]

theorem zeroModel_directedConnected : zeroModel.toHomTwistSystem₀.DirectedConnected 0 :=
  fun _ _ => ⟨(), [], rfl, rfl, le_rfl, List.isChain_singleton _⟩

theorem zeroModel_not_isSpherical : ¬ zeroModel.toHomTwistSystem₀.IsSpherical := fun h => by
  have := h ()
  simp [zeroModel] at this

/-- Every `P_q` of the zero model vanishes. -/
theorem zeroModel_maxCount (q : ℕ) : zeroModel.toHomTwistSystem₀.maxCount q = 0 := by
  unfold HomTwistSystem₀.maxCount
  simp [zeroModel]

/-- `h(u, v) = 1` if `v ≤ u`, else `0`, on `ℤ ∪ {∗}`; `∗` counts zero. -/
def asymH : Option (Multiplicative ℤ) → Option (Multiplicative ℤ) → ℕ
  | some u, some v => if Multiplicative.toAdd v - Multiplicative.toAdd u ≤ 0 then 1 else 0
  | _, _ => 0

/-- The letter `+1` with centre `∗` on `ℤ ∪ {∗}`. -/
def asymModel : HomTwistSystem (Multiplicative ℤ) (Option (Multiplicative ℤ)) Unit Unit where
  S _ := none
  T _ := Multiplicative.ofAdd 1
  c _ := ()
  h := asymH
  h_smul g U V := by
    cases U <;> cases V <;> simp [asymH, toAdd_mul]
  upper _ U V := by
    cases U <;> cases V <;> simp only [asymH, Option.smul_some, Option.smul_none, smul_eq_mul,
      toAdd_mul, toAdd_ofAdd, mul_zero, add_zero, zero_le]
    split_ifs <;> omega
  h_twist_centre _ U := by cases U <;> rfl

/-- (U) fails for the inverse letter of `asymModel`. -/
theorem asymModel_not_upper_inv :
    ¬ ∀ a U V, asymModel.h U ((asymModel.T a)⁻¹ • V) ≤
      asymModel.h U V + asymModel.h U (asymModel.S (asymModel.c a)) *
        asymModel.h (asymModel.S (asymModel.c a)) V := by
  intro h
  have := h () (some (Multiplicative.ofAdd 0)) (some (Multiplicative.ofAdd 1))
  simp [asymModel, asymH, Option.smul_some] at this

end K3TwistsTest.TwistSystemModel
