/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.PiTopology

/-!
# Agreement of coefficients on a lower set of exponents

Two multivariate power series `f, g` *agree on* a set `s` of exponents, `CoeffEqOn s f g`, when
`coeff d f = coeff d g` for every `d ∈ s`. On a lower set this relation is a congruence for the
ring operations, because the coefficient of a product at `d` involves only coefficients at
exponents below `d`. Truncations of infinite products, first-order expansions of units and
coefficient inversion are all computations modulo such a congruence; this is how the framed
multiplier of `K3Twists/Combinatorics/DT/FramedMultiplier.lean` is handled.

## Main results

* `MvPowerSeries.CoeffEqOn.mul`: on a lower set, agreement is compatible with multiplication;
* `MvPowerSeries.CoeffEqOn.inv_of_mul`: the inverse of a unit agrees with any approximate inverse;
* `MvPowerSeries.coeffEqOn_zpow_first_order`: if `u ≡ 1 + c x^α` on a lower set that does not
  contain `2α`, then `u^n ≡ 1 + n c x^α` for every integer `n`;
* `MvPowerSeries.coeff_mul_of_coeffEqOn_first_order`: if `g ≡ 1 + c x^α` below `d`, then
  `[x^d](f g) = [x^d] f + c [x^{d - α}] f` (the last term only when `α ≤ d`);
* `MvPowerSeries.hasProd_of_coeffEqOn_one`: **locally finite products.** If below each exponent
  `d` all but finitely many factors agree with `1`, the product converges in the product topology
  to the series whose coefficient at `d` is that of the finite product.

Mathlib's convergence criteria for products of power series
(`MvPowerSeries.multipliable_one_add_of_tendsto_weightedOrder_atTop_nhds_top`) index the factors
by a linear order with finite lower intervals and ask the orders of the factors to tend to
infinity; the criterion here needs no order on the index type and also covers infinitely many
variables, where the orders of the factors need not tend to infinity.
-/

open Finset Filter Topology
open scoped MvPowerSeries.WithPiTopology

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

/-! ### The congruence -/

/-- `f` and `g` have the same coefficient at every exponent of `s`. -/
def CoeffEqOn (s : Set (σ →₀ ℕ)) (f g : MvPowerSeries σ R) : Prop :=
  ∀ d ∈ s, coeff d f = coeff d g

namespace CoeffEqOn

variable {s : Set (σ →₀ ℕ)} {f g f' g' h : MvPowerSeries σ R}

@[refl]
theorem refl (f : MvPowerSeries σ R) : CoeffEqOn s f f := fun _ _ => rfl

@[symm]
theorem symm (hf : CoeffEqOn s f g) : CoeffEqOn s g f := fun d hd => (hf d hd).symm

@[trans]
theorem trans (hf : CoeffEqOn s f g) (hg : CoeffEqOn s g h) : CoeffEqOn s f h :=
  fun d hd => (hf d hd).trans (hg d hd)

theorem add (hf : CoeffEqOn s f f') (hg : CoeffEqOn s g g') : CoeffEqOn s (f + g) (f' + g') := by
  intro d hd
  simp [hf d hd, hg d hd]

theorem mono {t : Set (σ →₀ ℕ)} (hts : t ⊆ s) (hf : CoeffEqOn s f g) : CoeffEqOn t f g :=
  fun d hd => hf d (hts hd)

/-- **Agreement on a lower set is compatible with multiplication.** -/
theorem mul (hs : IsLowerSet s) (hf : CoeffEqOn s f f') (hg : CoeffEqOn s g g') :
    CoeffEqOn s (f * g) (f' * g') := by
  classical
  intro d hd
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  have h1 : p.1 ∈ s := hs (show p.1 ≤ d from hp ▸ le_self_add) hd
  have h2 : p.2 ∈ s := hs (show p.2 ≤ d from hp ▸ le_add_self) hd
  rw [hf _ h1, hg _ h2]

/-- A finite product of factors that agree with `1` on a lower set agrees with `1` there. -/
theorem prod_one {ι : Type*} (hs : IsLowerSet s) (t : Finset ι) (F : ι → MvPowerSeries σ R)
    (hF : ∀ i ∈ t, CoeffEqOn s (F i) 1) : CoeffEqOn s (∏ i ∈ t, F i) 1 :=
  Finset.prod_induction F (fun x => CoeffEqOn s x 1)
    (fun a b ha hb => by simpa using ha.mul hs hb) (refl 1) hF

/-- The inverse of a unit agrees on a lower set with any approximate inverse there. -/
theorem inv_of_mul (hs : IsLowerSet s) (u : (MvPowerSeries σ R)ˣ) (w : MvPowerSeries σ R)
    (hw : CoeffEqOn s ((u : MvPowerSeries σ R) * w) 1) :
    CoeffEqOn s (↑u⁻¹ : MvPowerSeries σ R) w := by
  have := (refl (↑u⁻¹ : MvPowerSeries σ R)).mul hs hw.symm
  simpa [← mul_assoc] using this

end CoeffEqOn

/-- A lower interval `Set.Iic d` is a lower set. -/
theorem isLowerSet_Iic (d : σ →₀ ℕ) : IsLowerSet (Set.Iic d) :=
  fun _ _ hab hb => le_trans hab hb

/-! ### First order -/

/-- Below `2α`, multiplying `1 + c x^α` and `1 + c' x^α` adds the coefficients. -/
theorem coeffEqOn_mul_first_order {s : Set (σ →₀ ℕ)} {α : σ →₀ ℕ} (hα : α + α ∉ s) (c c' : R) :
    CoeffEqOn s ((1 + monomial α c) * (1 + monomial α c')) (1 + monomial α (c + c')) := by
  classical
  intro d hd
  have hne : d ≠ α + α := fun h => hα (h ▸ hd)
  simp only [add_mul, one_mul, mul_add, mul_one, monomial_mul_monomial, map_add, coeff_monomial,
    hne, ite_false]
  ring

/-- `u^n ≡ 1 + n c x^α` on a lower set that does not contain `2α`, for every integer `n`. -/
theorem coeffEqOn_zpow_first_order {s : Set (σ →₀ ℕ)} (hs : IsLowerSet s) {α : σ →₀ ℕ}
    (hα : α + α ∉ s) (u : (MvPowerSeries σ R)ˣ) (c : R)
    (hu : CoeffEqOn s (u : MvPowerSeries σ R) (1 + monomial α c)) (n : ℤ) :
    CoeffEqOn s (↑(u ^ n) : MvPowerSeries σ R) (1 + monomial α ((n : R) * c)) := by
  have hinv : CoeffEqOn s (↑u⁻¹ : MvPowerSeries σ R) (1 + monomial α (-c)) := by
    refine CoeffEqOn.inv_of_mul hs u _ ?_
    refine (hu.mul hs (CoeffEqOn.refl _)).trans ((coeffEqOn_mul_first_order hα c (-c)).trans ?_)
    simp [CoeffEqOn.refl]
  induction n using Int.induction_on with
  | zero => simpa using CoeffEqOn.refl (s := s) (1 : MvPowerSeries σ R)
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul]
    refine (ih.mul hs hu).trans ?_
    rw [show (((k : ℤ) + 1 : ℤ) : R) * c = ((k : ℤ) : R) * c + c by push_cast; ring]
    exact coeffEqOn_mul_first_order hα _ c
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul]
    refine (ih.mul hs hinv).trans ?_
    rw [show ((-(k : ℤ) - 1 : ℤ) : R) * c = ((-(k : ℤ) : ℤ) : R) * c + -c by push_cast; ring]
    exact coeffEqOn_mul_first_order hα _ (-c)

/-- If `g ≡ 1 + c x^α` below `d`, then `[x^d](f g) = [x^d] f + c [x^{d - α}] f`, where the last
term is present only when `α ≤ d`. -/
theorem coeff_mul_of_coeffEqOn_first_order {α d : σ →₀ ℕ} (f g : MvPowerSeries σ R) (c : R)
    (hg : CoeffEqOn (Set.Iic d) g (1 + monomial α c)) :
    coeff d (f * g) = coeff d f + if α ≤ d then c * coeff (d - α) f else 0 := by
  rw [(CoeffEqOn.refl f).mul (isLowerSet_Iic d) hg d (Set.mem_Iic.2 le_rfl), mul_add, mul_one,
    map_add, coeff_mul_monomial]
  split_ifs <;> simp [mul_comm]

/-- The special case `d = α`: `[x^α](f g) = [x^α] f + c f(0)`. -/
theorem coeff_mul_of_coeffEqOn_first_order_self {α : σ →₀ ℕ} (f g : MvPowerSeries σ R) (c : R)
    (hg : CoeffEqOn (Set.Iic α) g (1 + monomial α c)) :
    coeff α (f * g) = coeff α f + c * constantCoeff f := by
  simp [coeff_mul_of_coeffEqOn_first_order f g c hg, coeff_zero_eq_constantCoeff_apply]

/-! ### Locally finite products -/

/-- The power series with coefficient function `c`. -/
def ofCoeff (c : (σ →₀ ℕ) → R) : MvPowerSeries σ R := c

@[simp]
theorem coeff_ofCoeff (c : (σ →₀ ℕ) → R) (d : σ →₀ ℕ) : coeff d (ofCoeff c) = c d := by
  rw [coeff_apply]; rfl

/-- Below `d`, a finite product agrees with its subproduct over the factors that do not agree
with `1` below `d`. -/
theorem coeffEqOn_prod_sdiff {ι : Type*} [DecidableEq ι] (F : ι → MvPowerSeries σ R)
    (d : σ →₀ ℕ) (T t : Finset ι) (hTt : T ⊆ t)
    (hF : ∀ i, i ∉ T → CoeffEqOn (Set.Iic d) (F i) 1) :
    CoeffEqOn (Set.Iic d) (∏ i ∈ t, F i) (∏ i ∈ T, F i) := by
  rw [← Finset.prod_sdiff hTt]
  have hrest : CoeffEqOn (Set.Iic d) (∏ i ∈ t \ T, F i) 1 :=
    CoeffEqOn.prod_one (isLowerSet_Iic d) _ F fun i hi => hF i (Finset.mem_sdiff.1 hi).2
  simpa using hrest.mul (isLowerSet_Iic d) (CoeffEqOn.refl (∏ i ∈ T, F i))

/-- **Locally finite products.** If below each exponent `d` only the factors in the finite set
`T d` differ from `1`, the product converges, in the product topology, to the series whose
coefficient at `d` is that of the finite product over `T d`. There is no order on the index
type and no finiteness condition on `σ`. -/
theorem hasProd_of_coeffEqOn_one {ι : Type*} [TopologicalSpace R] (F : ι → MvPowerSeries σ R)
    (T : (σ →₀ ℕ) → Finset ι) (hT : ∀ d i, i ∉ T d → CoeffEqOn (Set.Iic d) (F i) 1) :
    HasProd F (ofCoeff fun d => coeff d (∏ i ∈ T d, F i)) := by
  classical
  unfold HasProd
  rw [SummationFilter.unconditional_filter, WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (T d)] with t ht
  rw [coeff_ofCoeff]
  exact (coeffEqOn_prod_sdiff F d (T d) t ht (hT d) d (Set.mem_Iic.2 le_rfl)).symm

end MvPowerSeries
