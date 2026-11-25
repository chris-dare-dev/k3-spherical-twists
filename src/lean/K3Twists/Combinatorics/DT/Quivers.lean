/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Combinatorics.DT.TwoVertex
import K3Twists.Combinatorics.Quiver.Kronecker.RealRoots
import K3Twists.Combinatorics.Quiver.TypeA.Roots

/-!
# The framed multiplier of three quivers

For a quiver `Q` with Kac polynomials `A_α(q)` (the number of absolutely indecomposable
representations of dimension `α` over a field with `q` elements), the numerical framed series of
the tripled quiver of `Q` with framing `w ≥ 0`, in Mozgovoy's convention (arXiv:1107.6044,
Theorem 5.1 and Corollary 2.8), is a product of the form `∏_{α > 0} (1 - x^α)^{-(w·α) A_α(1)}`.
This file writes `Ω_α = -A_α(1)` and computes the framed multiplier with these exponents for three
quivers, from the values of their Kac polynomials. Those values and the identification with
framed moduli are cited, not formalized; that `-A_α(1)` are the BPS invariants of the nilpotent
locus is not derived here.

* **The Jordan quiver** (one vertex, one loop). `A_n(q) = q` for every `n ≥ 1`: an absolutely
  indecomposable `n × n` matrix is one Jordan block, with eigenvalue in the field. So `Ω_n = -1`.
  The dimension-one coefficient of `Z_w` is `(-1)^w w` (`coeff_atom_jordan`), and
  `Z_2(y) = Z_1(-y)² ≠ Z_1(y)²` (`jordan_Z_two_eq`, `jordan_Z_two_ne`): the sign twist between
  geometric and twisted variables cannot be dropped.
* **Type `A_n`.** By Gabriel's theorem (*Unzerlegbare Darstellungen I*, Manuscripta Math. 6,
  1972), `A_α = 1` on the positive roots of the Tits form and `0` elsewhere. The multiplier is
  the finite product over the positive roots, which are the intervals
  (`framedS_typeA`, `mem_positiveRoots_iff`).
* **The affine Kronecker quiver** (two vertices, two arrows). `A_α = 1` on the real roots
  `(n + 1, n)` and `(n, n + 1)` and `A_α = q + 1` on the imaginary roots `(n, n)`, `n ≥ 1`: the
  regular indecomposables of dimension `(n, n)` over an algebraically closed field are
  parametrized by the projective line (Kac, *Infinite root systems, representations of graphs
  and invariant theory*, Invent. Math. 56, 1980). With framing `(p, q)` the exponents are
  `-((n + 1)p + nq)`, `-(np + (n + 1)q)` and `-2n(p + q)` (`kronecker_exponent_R`,
  `kronecker_exponent_L`, `kronecker_exponent_diag`); the `xy` coefficient is `pq + 2(p + q)`
  (`coeff_kronecker_one_one`), and at framing `(1, 0)` the coefficient of `x²y²` is `8`
  (`coeff_kronecker_two_two`), computed from the coefficient tables of
  `K3Twists/Combinatorics/DT/TwoVertex.lean`.
  The three contributions are `4` from `(1 - x²y²)^{-4}`, `3` from `(1 - xy)^{-2}` and `1` from
  `x · xy²`.
-/

open Finset

namespace MvPowerSeries.FramedMultiplier

variable {R : Type*} [CommRing R]

/-! ### The Jordan quiver -/

section Jordan

/-- The BPS invariants of the Jordan quiver: `Ω_n = -A_n(1) = -1` in every degree. -/
def jordanBPS : (Unit →₀ ℕ) → ℤ := fun _ => -1

/-- Below a vertex, a series with constant coefficient one is `1 + c x`. -/
theorem coeffEqOn_atom {σ : Type*} (i : σ) (g : MvPowerSeries σ R) (hg : constantCoeff g = 1) :
    CoeffEqOn (Set.Iic (Finsupp.single i 1)) g
      (1 + monomial (Finsupp.single i 1) (coeff (Finsupp.single i 1) g)) := by
  classical
  intro β hβ
  rcases (Set.mem_Iic.1 hβ).lt_or_eq with h | h
  · obtain rfl := eq_zero_of_lt_single_one h
    have h0 : (0 : σ →₀ ℕ) ≠ Finsupp.single i 1 := Ne.symm (by simp)
    rw [← coeff_zero_eq_constantCoeff_apply] at hg
    rw [map_add, coeff_monomial, coeff_one, hg]
    simp [h0]
  · subst h
    have h0 : Finsupp.single i 1 ≠ (0 : σ →₀ ℕ) := by simp
    simp [coeff_one, h0]

/-- **The Jordan atom.** The coefficient of `y` in the geometric framed series of the Jordan
quiver with framing `w` is `(-1)^w w`, the signed Euler characteristic of `𝔸¹ × ℙ^{w-1}`. -/
theorem coeff_atom_jordan (w : ℕ) :
    coeff (Finsupp.single () 1) (Z (R := R) (fun _ => w) jordanBPS) = (-1) ^ w * w := by
  rw [coeff_atom_Z]
  simp [jordanBPS]

/-- `Z_2(y) = Z_1(-y)²`, from multiplicativity in geometric variables. -/
theorem jordan_Z_two_eq :
    Z (R := R) (σ := Unit) (1 + 1) jordanBPS =
      rescale (eps 1) (Z 1 jordanBPS) * rescale (eps 1) (Z 1 jordanBPS) :=
  Z_add 1 1 _

/-- **`Z_2 ≠ Z_1²`.** The framed series of framing `2` is not the square of that of framing `1`
in the geometric variables: their coefficients of `y` are `2` and `-2`. -/
theorem jordan_Z_two_ne :
    Z (R := ℤ) (σ := Unit) 2 jordanBPS ≠ Z 1 jordanBPS * Z 1 jordanBPS := by
  intro h
  have h1 : coeff (Finsupp.single () 1) (Z (R := ℤ) (σ := Unit) 2 jordanBPS) = 2 :=
    (coeff_atom_jordan 2).trans (by norm_num)
  have h2 : coeff (Finsupp.single () 1) (Z (R := ℤ) (σ := Unit) 1 jordanBPS) = -1 :=
    (coeff_atom_jordan 1).trans (by norm_num)
  have hc : constantCoeff (Z (R := ℤ) (σ := Unit) 1 jordanBPS) = 1 := by
    rw [Z, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale,
      coeff_zero_eq_constantCoeff_apply, framedS, constantCoeff_S]
    simp
  have hm := coeff_mul_of_coeffEqOn_first_order_self (Z (R := ℤ) (σ := Unit) 1 jordanBPS) _ _
    (coeffEqOn_atom () _ hc)
  rw [← h, h1, h2, hc] at hm
  norm_num at hm

end Jordan

/-! ### Type `A_n` -/

section TypeA

open Quiver.TypeA

variable {n : ℕ}

/-- The BPS invariants of a quiver of type `A_n`: `-1` on the positive roots of the Tits form
and `0` at every other class; by Gabriel's theorem this is `-A_α(1)`. -/
def typeABPS (n : ℕ) (α : Fin n →₀ ℕ) : ℤ :=
  if titsForm (fun k => (α k : ℤ)) = 1 then -1 else 0

/-- The positive roots of `A_n`, as positive classes: the classes below `(1, …, 1)` with Tits
form `1`. -/
noncomputable def positiveRoots (n : ℕ) : Finset (Pos (Fin n)) := by
  classical
  exact (box (Finsupp.equivFunOnFinite.symm 1)).filter fun α =>
    titsForm (fun k => (α.1 k : ℤ)) = 1

/-- A class is a positive root exactly when its Tits form is `1`. -/
theorem mem_positiveRoots {α : Pos (Fin n)} :
    α ∈ positiveRoots n ↔ titsForm (fun k => (α.1 k : ℤ)) = 1 := by
  classical
  simp only [positiveRoots, mem_filter, mem_box, and_iff_right_iff_imp]
  intro h
  obtain ⟨i, j, _, hij⟩ := (titsForm_eq_one_iff (fun k => α.1 k)).1 h
  intro k
  have := congrFun hij k
  simp only [Finsupp.coe_equivFunOnFinite_symm, Pi.one_apply]
  rw [this]
  unfold intervalRoot
  split_ifs <;> simp

/-- **The positive roots of `A_n` are the intervals.** -/
theorem mem_positiveRoots_iff {α : Pos (Fin n)} :
    α ∈ positiveRoots n ↔ ∃ i j, i ≤ j ∧ ⇑α.1 = intervalRoot i j := by
  rw [mem_positiveRoots]
  exact titsForm_eq_one_iff (fun k => α.1 k)

/-- **The framed multiplier of type `A_n`** is the finite product over the positive roots,
`S_{Ω,p} = ∏_{i ≤ j} (1 - x^{[i, j]})^{-(p·[i, j])}`. -/
theorem framedS_typeA (p : Fin n → ℤ) :
    framedS (R := R) p (typeABPS n) =
      ∏ α ∈ positiveRoots n, ((unitX (R := R) α ^ (-pair p α.1) : (MvPowerSeries (Fin n) R)ˣ) :
        MvPowerSeries (Fin n) R) := by
  rw [framedS, S_eq_prod _ (positiveRoots n) fun α hα => ?_]
  · refine prod_congr rfl fun α hα => ?_
    rw [mem_positiveRoots] at hα
    simp [factor, typeABPS, hα]
  · rw [mem_positiveRoots] at hα
    simp [typeABPS, hα]

end TypeA

/-! ### The affine Kronecker quiver -/

section Kronecker

open Quiver.Kronecker

/-- The BPS index of the class `(a, b)` of the affine Kronecker quiver: `-1` on the real roots
(Tits form `q₂(a, b) = 1`), `-2` on the imaginary roots `(n, n)`, `n ≥ 1`, and `0` elsewhere. -/
def kroneckerIndex (a b : ℕ) : ℤ :=
  if kroneckerForm 2 a b = 1 then -1 else if a = b ∧ a ≠ 0 then -2 else 0

/-- The BPS invariants of the affine Kronecker quiver, on exponent vectors. -/
def kroneckerBPS (α : Fin 2 →₀ ℕ) : ℤ := kroneckerIndex (α 0) (α 1)

@[simp]
theorem kroneckerBPS_mk2 (a b : ℕ) : kroneckerBPS (mk2 a b) = kroneckerIndex a b := by
  simp [kroneckerBPS]

theorem kroneckerForm_two (a b : ℤ) : kroneckerForm 2 a b = (a - b) ^ 2 := by
  unfold kroneckerForm
  ring

/-- **The real roots of the affine Kronecker quiver** are `(m + 1, m)` and `(m, m + 1)`; this is
the classification of real roots of the `g`-Kronecker quiver at `g = 2`, where `u_m = m`. -/
theorem kroneckerForm_two_eq_one_iff (a b : ℕ) :
    kroneckerForm 2 a b = 1 ↔ ∃ m : ℕ, (a = m + 1 ∧ b = m) ∨ (a = m ∧ b = m + 1) := by
  rw [realRoot_classification le_rfl (by positivity) (by positivity)]
  simp only [u_two_eq]
  constructor
  · rintro ⟨m, h | h⟩
    · exact ⟨m, Or.inl ⟨by omega, by omega⟩⟩
    · exact ⟨m, Or.inr ⟨by omega, by omega⟩⟩
  · rintro ⟨m, h | h⟩
    · exact ⟨m, Or.inl ⟨by omega, by omega⟩⟩
    · exact ⟨m, Or.inr ⟨by omega, by omega⟩⟩

theorem kroneckerIndex_eq (a b : ℕ) :
    kroneckerIndex a b =
      if a = b + 1 ∨ b = a + 1 then -1 else if a = b ∧ a ≠ 0 then -2 else 0 := by
  unfold kroneckerIndex
  rw [kroneckerForm_two]
  congr 1
  apply propext
  constructor
  · intro h
    have h' : ((a : ℤ) - b - 1) * ((a : ℤ) - b + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h'' | h'' <;> omega
  · rintro (h | h) <;> subst h <;> push_cast <;> ring

/-- The exponent of the multiplier with framing `(p, q)` at `(a, b)` is
`Ω_{(a, b)} (ap + bq)`. -/
theorem kronecker_exponent (p q : ℤ) (a b : ℕ) :
    pair ![p, q] (mk2 a b) * kroneckerBPS (mk2 a b) = (p * a + q * b) * kroneckerIndex a b := by
  simp [pair_mk2]

theorem kronecker_exponent_R (p q : ℤ) (n : ℕ) :
    pair ![p, q] (mk2 (n + 1) n) * kroneckerBPS (mk2 (n + 1) n) = -((n + 1) * p + n * q) := by
  rw [kronecker_exponent, kroneckerIndex_eq]
  simp only [true_or, ↓reduceIte]
  push_cast
  ring

theorem kronecker_exponent_L (p q : ℤ) (n : ℕ) :
    pair ![p, q] (mk2 n (n + 1)) * kroneckerBPS (mk2 n (n + 1)) = -(n * p + (n + 1) * q) := by
  rw [kronecker_exponent, kroneckerIndex_eq]
  simp only [or_true, ↓reduceIte]
  push_cast
  ring

theorem kronecker_exponent_diag (p q : ℤ) {n : ℕ} (hn : n ≠ 0) :
    pair ![p, q] (mk2 n n) * kroneckerBPS (mk2 n n) = -2 * n * (p + q) := by
  rw [kronecker_exponent, kroneckerIndex_eq]
  have h1 : ¬(n = n + 1 ∨ n = n + 1) := by omega
  simp only [h1, hn, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
  ring

/-- Off the roots the exponents vanish. -/
theorem kronecker_exponent_eq_zero (p q : ℤ) {a b : ℕ} (h1 : a ≠ b + 1) (h2 : b ≠ a + 1)
    (h3 : a ≠ b ∨ a = 0) :
    pair ![p, q] (mk2 a b) * kroneckerBPS (mk2 a b) = 0 := by
  rw [kronecker_exponent, kroneckerIndex_eq]
  have h4 : ¬(a = b + 1 ∨ b = a + 1) := by omega
  have h5 : ¬(a = b ∧ a ≠ 0) := by omega
  simp only [h4, h5, ↓reduceIte, mul_zero]

/-- **The `xy` coefficient** of the affine Kronecker multiplier with framing `(p, q)` is
`pq + 2(p + q)`. -/
theorem coeff_kronecker_one_one (p q : ℤ) :
    coeff (mk2 1 1) (framedS (R := R) ![p, q] kroneckerBPS) = ((p * q + 2 * (p + q) : ℤ) : R) := by
  rw [mk2, coeff_two_simple (by decide) _ _ 2]
  · simp
  · simpa [mk2] using kroneckerBPS_mk2 1 0 |>.trans (by rw [kroneckerIndex_eq]; simp)
  · simpa [mk2] using kroneckerBPS_mk2 0 1 |>.trans (by rw [kroneckerIndex_eq]; simp)
  · simpa [mk2] using kroneckerBPS_mk2 1 1 |>.trans (by rw [kroneckerIndex_eq]; simp)

/-- **The coefficient `8`.** At framing `(1, 0)` the coefficient of `x²y²` in the affine
Kronecker multiplier is `8 = 4 + 3 + 1`. -/
theorem coeff_kronecker_two_two :
    coeff (mk2 2 2) (framedS (R := ℤ) ![1, 0] kroneckerBPS) = 8 := by
  rw [framedS, coeff_S_mk2 _ (fun u v => (1 * u + 0 * v) * kroneckerIndex u v)
    (fun u v => by rw [kronecker_exponent])]
  decide

end Kronecker

end MvPowerSeries.FramedMultiplier
