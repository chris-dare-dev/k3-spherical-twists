/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.PeriodRecovery

/-!
# Period recovery: examples

Regression tests for `LinearAlgebra/Lattice/Mukai/PeriodRecovery.lean`.

* **The basis printed in Kikuta–Koseki–Ouchi, arXiv:2504.12253, Lemma 3.8, can fail its
  condition (2).** On `N = ℤ²` with `q(a, b) = a² - 3b²` (`NS = ⟨2⟩ ⊕ ⟨-6⟩`), the classes
  `C = (1, 0)` and `D = (0, 1)` have `C² = 2 > 0`, `D² = -6 < -4` and `C · D = 0`, and
  `⟪v(𝒪(D)), v(𝒪(-C))⟫ = 0`. With `q(a, b) = a² - 6b²` (`⟨2⟩ ⊕ ⟨-12⟩`, `D² = -12`),
  `⟪v(𝒪(D)), v(𝒪(2C))⟫ = 0`. Both are computed directly from the definitions and again from
  the closed forms `-(D² + C²)/2 - 2` and `-(D² + 4C²)/2 - 2`.
* **The doubled classes do not fail.** On `⟨2⟩ ⊕ ⟨-6⟩` the six pairings of `v(𝒪)`, `v(𝒪(2C))`,
  `v(𝒪(2D))`, `v(𝒪(-2C))` are `-6, 10, -6, 6, -18, 6`, all `≡ 2 mod 4`; over `ℚ` the four
  classes span the Mukai lattice (`Mukai.span_doubledLineBundles`).
* **The mixed entry needs the weight `c²`.** For the quadratic form `P(r, c, s) = r² + s²` (the
  period form of the charge `r + is`) and the roots `δ = v(𝒪)`, `δ' = v(𝒪(2C))` of
  `⟨2⟩ ⊕ ⟨-6⟩`, with `c = ⟪δ, δ'⟫ = -6`: `P(δ' + cδ) - P(δ') - c² P(δ) = -72`, which is
  `c · polar P δ δ'`, while `P(δ' + cδ) - P(δ') - P(δ) = -2`. Divided by `2c`, the first gives
  the mixed entry `6` of `P` and the second gives `1/6`.

Built by `lake test`.
-/

namespace K3TwistsTest.PeriodRecoveryExamples

open Mukai

/-! ### The lattice `⟨2⟩ ⊕ ⟨-6⟩` -/

/-- `q(a, b) = a² - 3b²`: the even lattice `⟨2⟩ ⊕ ⟨-6⟩`, with `x² = 2 q(x)`. -/
def q3 : QuadraticMap ℤ (ℤ × ℤ) ℤ :=
  QuadraticMap.linMulLin (LinearMap.fst ℤ ℤ ℤ) (LinearMap.fst ℤ ℤ ℤ) -
    (3 : ℤ) • QuadraticMap.linMulLin (LinearMap.snd ℤ ℤ ℤ) (LinearMap.snd ℤ ℤ ℤ)

/-- Evaluating `q3`. -/
theorem q3_apply (x : ℤ × ℤ) : q3 x = x.1 * x.1 - 3 * (x.2 * x.2) := by
  simp [q3]

/-- `C² = 2`, `D² = -6` and `C · D = 0`. -/
example : q3.polarBilin (1, 0) (1, 0) = 2 ∧ q3.polarBilin (0, 1) (0, 1) = -6 ∧
    q3.polarBilin (1, 0) (0, 1) = 0 := by
  simp [QuadraticMap.polar, q3_apply]

/-- **The printed basis fails on `⟨2⟩ ⊕ ⟨-6⟩`:** `⟪v(𝒪(D)), v(𝒪(-C))⟫ = 0`, from the
definitions. -/
example : pairing q3.polarBilin (lineBundle q3 (0, 1)) (lineBundle q3 (-(1, 0))) = 0 := by
  simp [lineBundle, pairing, QuadraticMap.polar, q3_apply]

/-- The same zero from the closed form `-(q(D) + q(C)) - 2`. -/
example : pairing q3.polarBilin (lineBundle q3 (0, 1)) (lineBundle q3 (-(1, 0))) = 0 := by
  rw [pairing_lineBundle_neg_of_polarBilin_eq_zero q3 (by simp [QuadraticMap.polar, q3_apply])]
  simp [q3_apply]

/-- The basis `C = (1, 0)`, `D = (0, 1)` of `ℤ²`. -/
def e : Fin 2 → ℤ × ℤ := ![(1, 0), (0, 1)]

/-- **The doubled family on `⟨2⟩ ⊕ ⟨-6⟩`:** the six pairings of `v(𝒪)`, `v(𝒪(2C))`,
`v(𝒪(2D))` and `v(𝒪(-2C))`. -/
example :
    pairing q3.polarBilin (doubledLineBundles q3 e 0 none)
        (doubledLineBundles q3 e 0 (some (some 0))) = -6 ∧
      pairing q3.polarBilin (doubledLineBundles q3 e 0 none)
        (doubledLineBundles q3 e 0 (some (some 1))) = 10 ∧
      pairing q3.polarBilin (doubledLineBundles q3 e 0 none)
        (doubledLineBundles q3 e 0 (some none)) = -6 ∧
      pairing q3.polarBilin (doubledLineBundles q3 e 0 (some (some 0)))
        (doubledLineBundles q3 e 0 (some (some 1))) = 6 ∧
      pairing q3.polarBilin (doubledLineBundles q3 e 0 (some (some 0)))
        (doubledLineBundles q3 e 0 (some none)) = -18 ∧
      pairing q3.polarBilin (doubledLineBundles q3 e 0 (some (some 1)))
        (doubledLineBundles q3 e 0 (some none)) = 6 := by
  simp [pairing_lineBundle, e, q3_apply]

/-- Over `ℤ` every pairing in the doubled family is nonzero. -/
example (k l : Option (Option (Fin 2))) :
    pairing q3.polarBilin (doubledLineBundles q3 e 0 k) (doubledLineBundles q3 e 0 l) ≠ 0 :=
  pairing_doubledLineBundles_ne_zero q3 (fun u _ => ⟨q3 u, rfl⟩) 0 k l

/-! ### The lattice `⟨2⟩ ⊕ ⟨-12⟩` -/

/-- `q(a, b) = a² - 6b²`: the even lattice `⟨2⟩ ⊕ ⟨-12⟩`. -/
def q6 : QuadraticMap ℤ (ℤ × ℤ) ℤ :=
  QuadraticMap.linMulLin (LinearMap.fst ℤ ℤ ℤ) (LinearMap.fst ℤ ℤ ℤ) -
    (6 : ℤ) • QuadraticMap.linMulLin (LinearMap.snd ℤ ℤ ℤ) (LinearMap.snd ℤ ℤ ℤ)

/-- Evaluating `q6`. -/
theorem q6_apply (x : ℤ × ℤ) : q6 x = x.1 * x.1 - 6 * (x.2 * x.2) := by
  simp [q6]

/-- **The printed basis fails on `⟨2⟩ ⊕ ⟨-12⟩`:** `⟪v(𝒪(D)), v(𝒪(2C))⟫ = 0`, from the
definitions. -/
example : pairing q6.polarBilin (lineBundle q6 (0, 1)) (lineBundle q6 ((2 : ℤ) • (1, 0))) = 0 := by
  simp [lineBundle, pairing, QuadraticMap.polar, q6_apply]

/-- The same zero from the closed form `-(q(D) + 4 q(C)) - 2`. -/
example : pairing q6.polarBilin (lineBundle q6 (0, 1)) (lineBundle q6 ((2 : ℤ) • (1, 0))) = 0 := by
  rw [pairing_lineBundle_two_smul_of_polarBilin_eq_zero q6
    (by simp [QuadraticMap.polar, q6_apply])]
  simp [q6_apply]

/-! ### Spanning over `ℚ` -/

/-- `q(a, b) = a² - 3b²` on `ℚ²`. -/
def q3ℚ : QuadraticMap ℚ (ℚ × ℚ) ℚ :=
  QuadraticMap.linMulLin (LinearMap.fst ℚ ℚ ℚ) (LinearMap.fst ℚ ℚ ℚ) -
    (3 : ℚ) • QuadraticMap.linMulLin (LinearMap.snd ℚ ℚ ℚ) (LinearMap.snd ℚ ℚ ℚ)

/-- The doubled family of `⟨2⟩ ⊕ ⟨-6⟩` spans the rational Mukai lattice. -/
example : Submodule.span ℚ (Set.range (doubledLineBundles q3ℚ (Module.Basis.finTwoProd ℚ) 0)) = ⊤ :=
  span_doubledLineBundles q3ℚ two_ne_zero (Module.Basis.finTwoProd ℚ).span_eq (by simp [q3ℚ])

/-! ### The weight `c²` -/

/-- `P(r, c, s) = r² + s²`, the period form of the charge `(r, c, s) ↦ r + is`. -/
def P : QuadraticMap ℤ (MukaiLattice ℤ (ℤ × ℤ)) ℤ :=
  QuadraticMap.linMulLin (LinearMap.fst ℤ ℤ _) (LinearMap.fst ℤ ℤ _) +
    QuadraticMap.linMulLin (LinearMap.snd ℤ (ℤ × ℤ) ℤ ∘ₗ LinearMap.snd ℤ ℤ _)
      (LinearMap.snd ℤ (ℤ × ℤ) ℤ ∘ₗ LinearMap.snd ℤ ℤ _)

/-- Evaluating `P`. -/
theorem P_apply (v : MukaiLattice ℤ (ℤ × ℤ)) : P v = v.1 * v.1 + v.2.2 * v.2.2 := by
  simp [P]

/-- The roots `δ = v(𝒪) = (1, 0, 1)` and `δ' = v(𝒪(2C)) = (1, (2, 0), 5)` pair to `c = -6`,
and `δ' + cδ = (-5, (2, 0), -1)` is again a root. -/
example : lineBundle q3 0 = (1, 0, 1) ∧ lineBundle q3 ((2 : ℤ) • (1, 0)) = (1, (2, 0), 5) ∧
    pairing q3.polarBilin (lineBundle q3 0) (lineBundle q3 ((2 : ℤ) • (1, 0))) = -6 ∧
    IsSpherical q3.polarBilin ((-5, (2, 0), -1) : MukaiLattice ℤ (ℤ × ℤ)) := by
  refine ⟨by simp [lineBundle], by simp [lineBundle, q3_apply], by simp [pairing_lineBundle,
    q3_apply], ?_⟩
  simp [IsSpherical, QuadraticMap.polar, q3_apply]

/-- **With the weight `c²`** the polarization along `δ' + cδ` returns `c · polar P δ δ'`. -/
example :
    P (((1, (2, 0), 5) : MukaiLattice ℤ (ℤ × ℤ)) + (-6 : ℤ) • (1, 0, 1)) - P (1, (2, 0), 5) -
        ((-6) * (-6) : ℤ) • P (1, 0, 1) =
      (-6 : ℤ) • QuadraticMap.polar P (1, 0, 1) (1, (2, 0), 5) ∧
    (-6 : ℤ) • QuadraticMap.polar P (1, 0, 1) (1, (2, 0), 5) = -72 := by
  simp [QuadraticMap.polar, P_apply]

/-- **Without the weight** the same expression is `-2`, not `-72`. -/
example :
    P (((1, (2, 0), 5) : MukaiLattice ℤ (ℤ × ℤ)) + (-6 : ℤ) • (1, 0, 1)) - P (1, (2, 0), 5) -
        P (1, 0, 1) = -2 ∧
    P (((1, (2, 0), 5) : MukaiLattice ℤ (ℤ × ℤ)) + (-6 : ℤ) • (1, 0, 1)) - P (1, (2, 0), 5) -
        P (1, 0, 1) ≠ (-6 : ℤ) • QuadraticMap.polar P (1, 0, 1) (1, (2, 0), 5) := by
  simp [QuadraticMap.polar, P_apply]

end K3TwistsTest.PeriodRecoveryExamples
