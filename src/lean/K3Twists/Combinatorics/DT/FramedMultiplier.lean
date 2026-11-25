/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RingTheory.MvPowerSeries.LowerSet
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The framed multiplier product

For a commutative ring `R`, a type `σ` of vertices and integer exponents `e : (σ →₀ ℕ) → ℤ`,
the **framed multiplier** is the product of units of `MvPowerSeries σ R`

  `S_e = ∏_{α > 0} (1 - x^α)^{e_α}`

over all nonzero exponent vectors `α` (the positive classes). Below a given exponent only
finitely many factors differ from `1`, so `S_e` is defined by its finite truncations, and it is
the infinite product in the product topology (`hasProd_S`). Neither `σ` nor the support of `e`
need be finite.

A framing is a vector `p : σ → ℤ`, possibly signed, with pairing `p·α = Σ_i p_i α_i`; for an
external object `D` and wall simples `A_i` it is `p_i = χ(D, A_i)`. The numerical framed DT
statement for BPS invariants `Ω` is that the framed series is the multiplier with exponents

  `e_α(p) = Ω_α (p·α)`,

that is `framedS p Ω = S (fun α => (p·α) Ω_α)`. The statement with content is the equation
for the exponents: existence and integrality of exponents are automatic over `ℤ` (the big Witt
factorization, `K3Twists/Combinatorics/DT/Inversion.lean`), and proportionality of `e_α(p)` to
`p·α` alone is not enough, since for `α = 2e₁` the exponent `p₁` is proportional to `p·α = 2p₁`
with ratio `1/2`.

## Main results

All of these hold over every commutative ring.

* `S_add`: multiplicativity, `S_{e + e'} = S_e S_{e'}`; hence `framedS_add`, multiplicativity in
  the framing, and `Z_add`, its form `Z_{w+w'}(y) = Z_w(ε_{w'} y) Z_{w'}(ε_w y)` in the geometric
  variables;
* `hasProd_S`, `tprod_factor`: `S_e` is the infinite product of its factors;
* `S_eq_prod`: for finitely many nonzero exponents, `S_e` is the finite product;
* `coeff_S_sub`: **coefficient inversion.** If `e, e'` agree strictly below `α`, then
  `[x^α] S_e - [x^α] S_{e'} = -(e_α - e'_α)`; in particular `[x^α] S_e = -e_α` at a minimal
  class (`coeff_S_of_minimal`);
* `coeff_S_one_one`: the `(1, 1)` coefficient `[x_a x_b] S_e = e_a e_b - e_{a+b}` for `a ≠ b`,
  and `coeff_two_simple`, its value `p_a p_b + d(p_a + p_b)` at a wall with two simples joined by
  `d` arrows;
* `framedS_update_of_pair_eq_zero`: the framed series does not see `Ω_α` when `p·α = 0`;
  `pair_signed_blind`: the signed framing `(m + 1, -m)` of the curve wall has `p·(m, m + 1) = 0`.

Injectivity of `e ↦ S_e` and the recovery of `Ω` from one framing need characteristic zero; they
are in `K3Twists/Combinatorics/DT/Inversion.lean`, with the counterexample over `ℤ/2`.

## Conventions

The factor is `(1 - x^α)^{(p·α)Ω_α}` in the *twisted* variables `x`, which are related to the
geometric variables `y` of the framed moduli spaces by `x^α = (-1)^{w·α} y^α` (`Z`). With
`Ω_α = -A_α(1)`, `A_α` the Kac polynomial, the framed series of a quiver with a framing `w ≥ 0`
is Mozgovoy's framed generating function (arXiv:1107.6044, Theorem 5.1, Corollary 2.8,
Remark 2.9); in it a vertex simple moving freely along the affine line contributes `Ω = -1`, and
the dimension-one coefficient of `Z_w` is `(-1)^w w` (`coeff_atom_Z`). Other normalizations of
BPS invariants, such as that of Joyce and Song (arXiv:0810.5645), differ by signs; this file
fixes the one stated here.

## Scope

Only the formal multiplier is formalized: the product of units with integer exponents. That
covers the numerical DT formula, not the motivic one (a plethystic exponential with
`q`-dependent exponents), and not the automorphism of the twisted torus algebra it induces or
the analytic Riemann–Hilbert problem (Bridgeland, arXiv:1611.03697, Proposition 4.2). That the
framed series of a quiver is this product, and the value `Ω = -A(1)`, are cited, not formalized.
-/

open Finset Filter Topology
open scoped MvPowerSeries.WithPiTopology

namespace MvPowerSeries.FramedMultiplier

/-! ### The factors -/

section Factors

variable {σ R : Type*} [CommRing R]

/-- The positive classes: nonzero exponent vectors. -/
abbrev Pos (σ : Type*) := {α : σ →₀ ℕ // α ≠ 0}

theorem isUnit_one_sub_monomial {α : σ →₀ ℕ} (hα : α ≠ 0) :
    IsUnit (1 - monomial α (1 : R)) := by
  classical
  rw [isUnit_iff_constantCoeff, map_sub, map_one, ← coeff_zero_eq_constantCoeff_apply,
    coeff_monomial, ite_eq_right_iff.2 (fun h => absurd h.symm hα), sub_zero]
  exact isUnit_one

/-- The unit `1 - x^α` of a positive class. -/
noncomputable def unitX (α : Pos σ) : (MvPowerSeries σ R)ˣ :=
  (isUnit_one_sub_monomial (R := R) α.2).unit

theorem unitX_val (α : Pos σ) :
    ((unitX α : (MvPowerSeries σ R)ˣ) : MvPowerSeries σ R) = 1 - monomial α.1 1 :=
  IsUnit.unit_spec _

/-- The factor `(1 - x^α)^{e_α}`, an integer power in the unit group. -/
noncomputable def factor (e : (σ →₀ ℕ) → ℤ) (α : Pos σ) : MvPowerSeries σ R :=
  ↑((unitX α : (MvPowerSeries σ R)ˣ) ^ e α.1)

theorem factor_of_eq_zero {e : (σ →₀ ℕ) → ℤ} {α : Pos σ} (h : e α.1 = 0) :
    factor (R := R) e α = 1 := by
  simp [factor, h]

/-- Below `2α`, the factor is `1 - e_α x^α`. -/
theorem factor_coeffEqOn_first_order (e : (σ →₀ ℕ) → ℤ) (α : Pos σ) {s : Set (σ →₀ ℕ)}
    (hs : IsLowerSet s) (hα : α.1 + α.1 ∉ s) :
    CoeffEqOn s (factor (R := R) e α) (1 + monomial α.1 (-(e α.1 : R))) := by
  have := coeffEqOn_zpow_first_order hs hα (unitX α) (-1 : R) (by
    rw [unitX_val, sub_eq_add_neg, ← map_neg]) (e α.1)
  simpa [factor] using this

/-- On a lower set that does not contain `α`, the factor agrees with `1`. -/
theorem factor_coeffEqOn_one (e : (σ →₀ ℕ) → ℤ) (α : Pos σ) {s : Set (σ →₀ ℕ)}
    (hs : IsLowerSet s) (hα : α.1 ∉ s) : CoeffEqOn s (factor (R := R) e α) 1 := by
  classical
  have h2 : α.1 + α.1 ∉ s := fun h => hα (hs le_self_add h)
  refine (factor_coeffEqOn_first_order e α hs h2).trans ?_
  intro d hd
  have : d ≠ α.1 := fun h => hα (h ▸ hd)
  simp [coeff_monomial, this]

end Factors

/-! ### The multiplier -/

section Multiplier

variable {σ R : Type*} [CommRing R]

/-- The box of positive classes below `d`. -/
noncomputable def box (d : σ →₀ ℕ) : Finset (Pos σ) := by
  classical exact (Finset.Iic d).subtype (· ≠ 0)

theorem mem_box {d : σ →₀ ℕ} {α : Pos σ} : α ∈ box d ↔ α.1 ≤ d := by
  classical
  simp [box]

/-- **The framed multiplier** `S_e = ∏_{α > 0} (1 - x^α)^{e_α}`. Its coefficient at `d` is that
of the finite product over the box below `d`; `hasProd_S` shows that it is the infinite
product. -/
noncomputable def S (e : (σ →₀ ℕ) → ℤ) : MvPowerSeries σ R :=
  ofCoeff fun d => coeff d (∏ α ∈ box d, factor (R := R) e α)

theorem factor_coeffEqOn_box (e : (σ →₀ ℕ) → ℤ) (d : σ →₀ ℕ) (α : Pos σ) (hα : α ∉ box d) :
    CoeffEqOn (Set.Iic d) (factor (R := R) e α) 1 :=
  factor_coeffEqOn_one e α (isLowerSet_Iic d) (by simpa [mem_box] using hα)

/-- `S_e` is the (unconditional) infinite product of its factors, in the product topology. -/
theorem hasProd_S [TopologicalSpace R] (e : (σ →₀ ℕ) → ℤ) :
    HasProd (factor (R := R) e) (S e) :=
  hasProd_of_coeffEqOn_one _ box fun d α hα => factor_coeffEqOn_box e d α hα

/-- `∏' α, (1 - x^α)^{e_α} = S_e`. -/
theorem tprod_factor [TopologicalSpace R] [T2Space R] (e : (σ →₀ ℕ) → ℤ) :
    ∏' α, factor (R := R) e α = S e :=
  (hasProd_S e).tprod_eq

/-- **Truncation.** Below `d`, `S_e` agrees with every finite product over a set of positive
classes that contains the box below `d`. -/
theorem S_coeffEqOn_prod (e : (σ →₀ ℕ) → ℤ) (d : σ →₀ ℕ) (t : Finset (Pos σ))
    (ht : box d ⊆ t) : CoeffEqOn (Set.Iic d) (S (R := R) e) (∏ α ∈ t, factor e α) := by
  classical
  intro d' hd'
  have hsub : box d' ⊆ t := fun α hα => ht (mem_box.2 (le_trans (mem_box.1 hα) hd'))
  rw [S, coeff_ofCoeff]
  exact (coeffEqOn_prod_sdiff (factor e) d' (box d') t hsub
    (fun α hα => factor_coeffEqOn_box e d' α hα) d' (Set.mem_Iic.2 le_rfl)).symm

theorem box_zero : box (0 : σ →₀ ℕ) = ∅ := by
  ext α
  simp only [mem_box, Finset.notMem_empty, iff_false, nonpos_iff_eq_zero]
  exact α.2

@[simp]
theorem constantCoeff_S (e : (σ →₀ ℕ) → ℤ) : constantCoeff (S (R := R) e) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simpa [box_zero] using S_coeffEqOn_prod (R := R) e 0 (box 0) subset_rfl 0 (Set.mem_Iic.2 le_rfl)

theorem isUnit_S (e : (σ →₀ ℕ) → ℤ) : IsUnit (S (R := R) e) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_S]
  exact isUnit_one

/-- **Multiplicativity in the exponents**, `S_{e + e'} = S_e S_{e'}`. No topology is used: the
truncations do all the work. -/
theorem S_add (e e' : (σ →₀ ℕ) → ℤ) : S (R := R) (e + e') = S e * S e' := by
  ext d
  have hd : d ∈ Set.Iic d := Set.mem_Iic.2 le_rfl
  rw [S_coeffEqOn_prod (e + e') d (box d) subset_rfl d hd,
    ((S_coeffEqOn_prod e d (box d) subset_rfl).mul (isLowerSet_Iic d)
      (S_coeffEqOn_prod e' d (box d) subset_rfl)) d hd,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun α _ => ?_
  simp [factor, zpow_add]

@[simp]
theorem S_zero : S (R := R) (σ := σ) 0 = 1 := by
  ext d
  rw [S, coeff_ofCoeff]
  simp [factor]

/-- `S_{-e}` is the inverse of `S_e`. -/
theorem S_mul_S_neg (e : (σ →₀ ℕ) → ℤ) : S (R := R) e * S (-e) = 1 := by
  rw [← S_add, add_neg_cancel, S_zero]

/-- `S_e` depends only on the exponents at positive classes. -/
theorem S_congr {e e' : (σ →₀ ℕ) → ℤ} (h : ∀ α : Pos σ, e α.1 = e' α.1) :
    S (R := R) e = S e' := by
  unfold S
  congr 1
  funext d
  congr 1
  refine Finset.prod_congr rfl fun α _ => ?_
  simp [factor, h α]

/-- **Finitely many nonzero exponents.** If `e` vanishes at every positive class outside the
finite set `t`, then `S_e` is the finite product over `t`. -/
theorem S_eq_prod (e : (σ →₀ ℕ) → ℤ) (t : Finset (Pos σ))
    (ht : ∀ α : Pos σ, α ∉ t → e α.1 = 0) :
    S (R := R) e = ∏ α ∈ t, factor e α := by
  classical
  ext d
  rw [S_coeffEqOn_prod e d (box d ∪ t) Finset.subset_union_left d (Set.mem_Iic.2 le_rfl),
    ← Finset.prod_subset Finset.subset_union_right
      (fun α _ hα => factor_of_eq_zero (ht α hα))]

end Multiplier

/-! ### Coefficient inversion -/

section Inversion

variable {σ R : Type*} [CommRing R]

/-- If `g` vanishes at every positive class below `α`, then `S_g ≡ 1 - g_α x^α` below `α`. -/
theorem S_coeffEqOn_first_order (g : (σ →₀ ℕ) → ℤ) (α : Pos σ)
    (hg : ∀ β : Pos σ, β.1 < α.1 → g β.1 = 0) :
    CoeffEqOn (Set.Iic α.1) (S (R := R) g) (1 + monomial α.1 (-(g α.1 : R))) := by
  classical
  have h2 : α.1 + α.1 ∉ Set.Iic α.1 := by
    intro h
    have : α.1 + α.1 ≤ α.1 + 0 := by simpa using h
    exact α.2 (nonpos_iff_eq_zero.1 (le_of_add_le_add_left this))
  refine (S_coeffEqOn_prod g α.1 (box α.1) subset_rfl).trans ?_
  rw [← Finset.prod_erase_mul _ _ (mem_box.2 le_rfl)]
  have hrest : ∀ β ∈ (box α.1).erase α, factor (R := R) g β = 1 := by
    intro β hβ
    obtain ⟨hne, hβ⟩ := Finset.mem_erase.1 hβ
    exact factor_of_eq_zero (hg β (lt_of_le_of_ne (mem_box.1 hβ) fun h => hne (Subtype.ext h)))
  rw [Finset.prod_eq_one hrest, one_mul]
  exact factor_coeffEqOn_first_order g α (isLowerSet_Iic α.1) h2

/-- **Coefficient inversion.** `[x^α] S_e = -e_α + (a function of the `e_β`, `β < α`)`: if `e`
and `e'` agree strictly below `α`, their coefficients at `α` differ by `-(e_α - e'_α)`. -/
theorem coeff_S_sub (e e' : (σ →₀ ℕ) → ℤ) (α : Pos σ)
    (h : ∀ β : Pos σ, β.1 < α.1 → e β.1 = e' β.1) :
    coeff α.1 (S (R := R) e) = coeff α.1 (S (R := R) e') - ((e α.1 - e' α.1 : ℤ) : R) := by
  have hsplit : e = e' + (e - e') := by abel
  have hfo := S_coeffEqOn_first_order (R := R) (e - e') α (fun β hβ => by simp [h β hβ])
  conv_lhs => rw [hsplit, S_add]
  rw [coeff_mul_of_coeffEqOn_first_order_self _ _ _ hfo, constantCoeff_S]
  simp only [Pi.sub_apply, mul_one]
  push_cast
  ring

/-- At a class with no positive class strictly below it, the coefficient is `-e_α`. -/
theorem coeff_S_of_minimal (e : (σ →₀ ℕ) → ℤ) (α : Pos σ) (hmin : ∀ β : Pos σ, ¬β.1 < α.1) :
    coeff α.1 (S (R := R) e) = -(e α.1 : R) := by
  classical
  have h := coeff_S_sub (R := R) e 0 α (fun β hβ => absurd hβ (hmin β))
  rw [S_zero] at h
  simpa [coeff_one, α.2] using h

end Inversion

/-! ### The `(1, 1)` coefficient -/

section Coefficients

variable {σ R : Type*} [CommRing R]

/-- Nothing positive lies strictly below a vertex. -/
theorem eq_zero_of_lt_single_one {i : σ} {β : σ →₀ ℕ} (h : β < Finsupp.single i 1) : β = 0 := by
  have := Finsupp.degree_strictMono h
  rw [Finsupp.degree_single] at this
  exact (Finsupp.degree_eq_zero_iff β).1 (by omega)

/-- `[x_i] S_e = -e_{e_i}` at a vertex `i`. -/
theorem coeff_S_single (e : (σ →₀ ℕ) → ℤ) (i : σ) :
    coeff (Finsupp.single i 1) (S (R := R) e) = -(e (Finsupp.single i 1) : R) :=
  coeff_S_of_minimal e ⟨Finsupp.single i 1, Finsupp.single_ne_zero.2 one_ne_zero⟩
    fun β hβ => β.2 (eq_zero_of_lt_single_one hβ)

theorem le_pair_cases {a b : σ} (hab : a ≠ b) {β : σ →₀ ℕ}
    (h : β ≤ Finsupp.single a 1 + Finsupp.single b 1) :
    β = 0 ∨ β = Finsupp.single a 1 ∨ β = Finsupp.single b 1 ∨
      β = Finsupp.single a 1 + Finsupp.single b 1 := by
  classical
  have ha : β a ≤ 1 := by simpa [hab] using h a
  have hb : β b ≤ 1 := by simpa [Ne.symm hab] using h b
  have key : β = Finsupp.single a (β a) + Finsupp.single b (β b) := by
    ext i
    by_cases hia : i = a
    · subst hia; simp [hab]
    by_cases hib : i = b
    · subst hib; simp [Ne.symm hia]
    · have := h i
      simp [Ne.symm hia, Ne.symm hib] at this ⊢
      omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with h0 | h0 <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h1 | h1 <;>
  · rw [key, h0, h1]; simp

/-- **The `(1, 1)` coefficient**: `[x_a x_b] S_e = e_a e_b - e_{a+b}` for two distinct vertices.
For `a = b` it fails: the coefficient of `x²` in `S_e = 1 - x` is `0`. -/
theorem coeff_S_one_one {a b : σ} (hab : a ≠ b) (e : (σ →₀ ℕ) → ℤ) :
    coeff (Finsupp.single a 1 + Finsupp.single b 1) (S (R := R) e) =
      (e (Finsupp.single a 1) : R) * e (Finsupp.single b 1) -
        e (Finsupp.single a 1 + Finsupp.single b 1) := by
  classical
  set α := Finsupp.single a 1 + Finsupp.single b 1 with hα_def
  have ha0 : Finsupp.single a 1 ≠ 0 := by simp
  have hb0 : Finsupp.single b 1 ≠ 0 := by simp
  have hα0 : α ≠ 0 := by simp [hα_def]
  let pa : Pos σ := ⟨_, ha0⟩
  let pb : Pos σ := ⟨_, hb0⟩
  let pab : Pos σ := ⟨α, hα0⟩
  have hs := isLowerSet_Iic α
  -- `2β` lies outside the box for every positive `β` in it
  have htwo : ∀ β : Pos σ, β.1 ≤ α → β.1 + β.1 ∉ Set.Iic α := by
    intro β hβ h2
    rcases le_pair_cases hab hβ with h | h | h | h
    · exact β.2 h
    · have := (Set.mem_Iic.1 h2) a
      simp [h, hα_def, hab] at this
    · have := (Set.mem_Iic.1 h2) b
      simp [h, hα_def, Ne.symm hab] at this
    · have := (Set.mem_Iic.1 h2) a
      simp [h, hα_def, hab] at this
  have hbox : box α ⊆ {pa, pb, pab} := by
    intro β hβ
    rcases le_pair_cases hab (mem_box.1 hβ) with h | h | h | h
    · exact absurd h β.2
    · simp [pa, Subtype.ext_iff, h]
    · simp [pb, Subtype.ext_iff, h]
    · simp [pab, Subtype.ext_iff, h, hα_def]
  have hpa : pa ∉ ({pb, pab} : Finset (Pos σ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, pa, pb, pab, Subtype.ext_iff, α]
    refine not_or.2 ⟨fun h => hab ?_, fun h => ?_⟩
    · have := congrArg (· a) h; simp [hab] at this
    · have := congrArg (· b) h; simp [hab] at this
  have hpb : pb ∉ ({pab} : Finset (Pos σ)) := by
    simp only [Finset.mem_singleton, pb, pab, Subtype.ext_iff, α]
    intro h; have := congrArg (· a) h; simp [hab] at this
  have hprod := S_coeffEqOn_prod (R := R) e α _ hbox α (Set.mem_Iic.2 le_rfl)
  rw [hprod, Finset.prod_insert hpa, Finset.prod_insert hpb, Finset.prod_singleton,
    ← mul_assoc]
  rw [coeff_mul_of_coeffEqOn_first_order_self _ _ _
    (factor_coeffEqOn_first_order e pab hs (htwo pab le_rfl))]
  have hfa := factor_coeffEqOn_first_order (R := R) e pa hs
    (htwo pa (by simp only [pa, hα_def]; exact le_self_add))
  have hfb := factor_coeffEqOn_first_order (R := R) e pb hs
    (htwo pb (by simp only [pb, hα_def]; exact le_add_self))
  have hm := (hfa.mul hs hfb) α (Set.mem_Iic.2 le_rfl)
  have hm0 := (hfa.mul hs hfb) 0 (Set.mem_Iic.2 (by simp))
  rw [← coeff_zero_eq_constantCoeff_apply, hm, hm0]
  simp only [add_mul, one_mul, mul_add, mul_one, monomial_mul_monomial, map_add, coeff_monomial,
    coeff_one, pa, pb, pab, α]
  have h0ab : (0 : σ →₀ ℕ) ≠ Finsupp.single a 1 + Finsupp.single b 1 := Ne.symm hα0
  simp [Ne.symm ha0, Ne.symm hb0, h0ab]
  ring

end Coefficients

/-! ### Framings -/

section Framing

variable {σ R : Type*} [CommRing R]

/-- The pairing `p·α = Σ_i p_i α_i` of a framing vector `p`, possibly signed, with a class. For
an external object `D` and wall simples `A_i`, `p_i = χ(D, A_i)` and `p·α = χ(D, E)` for an
object `E` of class `α`. -/
def pair (p : σ → ℤ) (α : σ →₀ ℕ) : ℤ := α.sum fun i n => p i * n

theorem pair_add (p p' : σ → ℤ) (α : σ →₀ ℕ) : pair (p + p') α = pair p α + pair p' α := by
  simp [pair, add_mul, Finsupp.sum_add]

theorem pair_single (p : σ → ℤ) (i : σ) (n : ℕ) : pair p (Finsupp.single i n) = p i * n := by
  simp [pair]

@[simp]
theorem pair_zero_right (p : σ → ℤ) : pair p 0 = 0 := by
  simp [pair]

theorem pair_add_right (p : σ → ℤ) (α β : σ →₀ ℕ) : pair p (α + β) = pair p α + pair p β := by
  unfold pair
  rw [Finsupp.sum_add_index'] <;> intros <;> push_cast <;> ring

/-- **The framed multiplier** `S_{Ω,p} = ∏_{α>0} (1 - x^α)^{(p·α) Ω_α}`, in the twisted
variables `x`. -/
noncomputable def framedS (p : σ → ℤ) (Ω : (σ →₀ ℕ) → ℤ) : MvPowerSeries σ R :=
  S fun α => pair p α * Ω α

/-- Multiplicativity in the framing: `S_{Ω, p + p'} = S_{Ω, p} S_{Ω, p'}`. -/
theorem framedS_add (p p' : σ → ℤ) (Ω : (σ →₀ ℕ) → ℤ) :
    framedS (R := R) (p + p') Ω = framedS p Ω * framedS p' Ω := by
  rw [framedS, framedS, framedS, ← S_add]
  congr 1
  funext α
  simp [pair_add, add_mul]

/-- **A framing is blind where it pairs to zero**: the framed series does not depend on `Ω_α`
when `p·α = 0`. -/
theorem framedS_update_of_pair_eq_zero [DecidableEq (σ →₀ ℕ)] {p : σ → ℤ}
    (Ω : (σ →₀ ℕ) → ℤ) (α : σ →₀ ℕ) (hp : pair p α = 0) (c : ℤ) :
    framedS (R := R) p (Function.update Ω α c) = framedS p Ω := by
  unfold framedS
  congr 1
  funext β
  by_cases hβ : β = α
  · subst hβ; simp [hp]
  · simp [Function.update_of_ne hβ]

/-- **The curve-wall framing is blind to `(m, m + 1)`.** The signed framing `(m + 1, -m)`, which
the line bundles `D` with `C·D = -m` induce at the wall of a contracted `(-2)`-curve `C`, pairs
to zero with the real root `(m, m + 1)` of the affine Kronecker quiver. -/
theorem pair_signed_blind (m : ℕ) :
    pair (σ := Fin 2) ![(m : ℤ) + 1, -(m : ℤ)]
      (Finsupp.single 0 m + Finsupp.single 1 (m + 1)) = 0 := by
  rw [pair_add_right, pair_single, pair_single]
  simp
  ring

/-- **The two-simple wall.** If two vertices `a ≠ b` have `Ω_a = Ω_b = -1` and
`Ω_{a+b} = -d` (a wall with two spherical simples joined by `d` arrows, where the Kac polynomial
at `(1, 1)` takes the value `d` at `q = 1`), the `x_a x_b` coefficient of the framed multiplier
is `p_a p_b + d (p_a + p_b)`. -/
theorem coeff_two_simple {a b : σ} (hab : a ≠ b) (p : σ → ℤ) (Ω : (σ →₀ ℕ) → ℤ) (d : ℤ)
    (ha : Ω (Finsupp.single a 1) = -1) (hb : Ω (Finsupp.single b 1) = -1)
    (hd : Ω (Finsupp.single a 1 + Finsupp.single b 1) = -d) :
    coeff (Finsupp.single a 1 + Finsupp.single b 1) (framedS (R := R) p Ω) =
      ((p a * p b + d * (p a + p b) : ℤ) : R) := by
  rw [framedS, coeff_S_one_one hab, ha, hb, hd, pair_add_right, pair_single, pair_single]
  push_cast
  ring

/-! ### Geometric variables -/

/-- The sign `ε_w = ((-1)^{w_i})_i` relating the twisted and the geometric variables. -/
def eps (w : σ → ℕ) : σ → R := fun i => (-1) ^ w i

/-- **The geometric framed series** `Z_w(y) = S_{Ω, w}(ε_w y)` of a framing `w ≥ 0`, that is the
framed multiplier in the variables `y` with `x^α = (-1)^{w·α} y^α`. -/
noncomputable def Z (w : σ → ℕ) (Ω : (σ →₀ ℕ) → ℤ) : MvPowerSeries σ R :=
  rescale (eps w) (framedS (fun i => (w i : ℤ)) Ω)

/-- Multiplicativity in geometric variables: `Z_{w+w'}(y) = Z_w(ε_{w'} y) Z_{w'}(ε_w y)`. -/
theorem Z_add (w w' : σ → ℕ) (Ω : (σ →₀ ℕ) → ℤ) :
    Z (R := R) (w + w') Ω = rescale (eps w') (Z w Ω) * rescale (eps w) (Z w' Ω) := by
  have hp : (fun i => ((w + w') i : ℤ)) = (fun i => (w i : ℤ)) + (fun i => (w' i : ℤ)) := by
    funext i; simp
  have he : (eps (w + w') : σ → R) = eps w * eps w' := by
    funext i; simp [eps, pow_add]
  rw [Z, Z, Z, hp, framedS_add, he, map_mul, rescale_rescale, rescale_rescale,
    mul_comm (eps w')]

/-- `rescale ε_w` is an involution. -/
theorem rescale_eps_involutive (w : σ → ℕ) (f : MvPowerSeries σ R) :
    rescale (eps w) (rescale (eps w) f) = f := by
  rw [rescale_rescale]
  have : (eps w : σ → R) * eps w = 1 := by
    funext i; simp [eps, ← mul_pow]
  rw [this, rescale_one, RingHom.id_apply]

/-- The dimension-one coefficient of `Z_w` at a vertex `i` is `(-1)^{w_i} w_i (-Ω_{e_i})`; for
`Ω_{e_i} = -1` it is `(-1)^{w_i} w_i`. -/
theorem coeff_atom_Z (i : σ) (w : σ → ℕ) (Ω : (σ →₀ ℕ) → ℤ) :
    coeff (Finsupp.single i 1) (Z (R := R) w Ω) =
      (-1) ^ w i * ((w i : R) * -(Ω (Finsupp.single i 1) : R)) := by
  rw [Z, coeff_rescale, framedS, coeff_S_single]
  simp [eps, pair_single]

end Framing

end MvPowerSeries.FramedMultiplier
