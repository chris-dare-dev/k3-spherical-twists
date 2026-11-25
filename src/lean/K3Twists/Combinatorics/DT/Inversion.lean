/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Combinatorics.DT.FramedMultiplier

/-!
# Inverting the framed multiplier

Over a ring of characteristic zero the framed multiplier `S_e = ∏_{α > 0} (1 - x^α)^{e_α}`
determines its exponents (`S_injective`). Over `ℤ` every power series with constant term one is
a framed multiplier in exactly one way (`S_bijective_int`): `e ↦ S_e` is a bijection from integer
exponent families on the positive classes onto `1 + 𝔪`. This is the multivariate cyclotomic
identity, the coordinates of big Witt vectors (Hazewinkel, *Witt vectors. Part 1*,
arXiv:0804.3888). So over `ℤ` the exponents of a framed series exist and are integers for
free, and the numerical framed DT statement is a statement about them: the exponent at `α` of the
series framed by `p` is the integer multiple `Ω_α (p·α)` of the pairing (`isFramedDT_iff`).

Recovering `Ω` needs characteristic zero and one framing that pairs to a nonzero number with
every positive class, for example a framing with every `p_i > 0` (`framedS_injective`); identities
in each chamber are not needed. Where `p·α = 0` the framed series does not see `Ω_α`
(`MvPowerSeries.FramedMultiplier.framedS_update_of_pair_eq_zero`).

## Main results

* `S_injective`: over a ring of characteristic zero, `S_e = S_{e'}` forces `e = e'` on positive
  classes;
* `wittExp`, `S_wittExp`, `S_bijective_int`: the big Witt factorization over `ℤ`;
* `framedS_determines`, `framedS_injective`: the framed series determines `Ω_α` where
  `p·α ≠ 0`, and all of `Ω` from one framing that pairs nonzero with every positive class;
* `exponents_additive`: a family of framed series that is multiplicative in the framing has
  exponents additive in the framing;
* `IsFramedDT`, `isFramedDT_iff`: the framed DT statement for a family of framed series over `ℤ`
  is the equation `e_α(p) = Ω_α (p·α)` for its Witt exponents.

Characteristic zero cannot be dropped: over `ℤ/2`, `(1 - x)² = 1 - x²`, so two exponent
families give the same series, and over `ℚ` the series `1 + x/2` is no `S_e` with integer
exponents. Both are tests in `K3TwistsTest/FramedMultiplierCounterexamples.lean`.
-/

open Finset

namespace MvPowerSeries.FramedMultiplier

variable {σ R : Type*} [CommRing R]

/-! ### Injectivity in characteristic zero -/

/-- **Injectivity of `e ↦ S_e`** over a ring of characteristic zero: the multiplier determines
every exponent at a positive class. The induction is on the pointwise order of exponent vectors,
which is well founded (`Finsupp.wellFoundedLT'`). -/
theorem S_injective [CharZero R] {e e' : (σ →₀ ℕ) → ℤ} (h : S (R := R) e = S e') :
    ∀ α : Pos σ, e α.1 = e' α.1 := by
  rintro ⟨α, hα⟩
  revert hα
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    intro hα
    have key := coeff_S_sub (R := R) e e' ⟨α, hα⟩ fun β hβ => ih β.1 hβ β.2
    rw [h] at key
    have h0 : ((e α - e' α : ℤ) : R) = 0 := sub_eq_self.1 key.symm
    exact sub_eq_zero.1 (Int.cast_eq_zero.1 h0)

/-! ### The big Witt factorization over `ℤ` -/

/-- The exponents of an integral power series, defined by recursion on the pointwise order: the
exponent at `α ≠ 0` is chosen so that the coefficient at `α` of the multiplier with the
exponents below `α` matches `f`. -/
noncomputable def wittExp (f : MvPowerSeries σ ℤ) : (σ →₀ ℕ) → ℤ := by
  classical
  exact wellFounded_lt.fix fun α rec =>
    if α = 0 then 0 else
      coeff α (S (R := ℤ) fun β => if h : β < α then rec β h else 0) - coeff α f

theorem wittExp_zero (f : MvPowerSeries σ ℤ) : wittExp f 0 = 0 := by
  classical
  rw [wittExp, WellFounded.fix_eq]
  simp

open Classical in
theorem wittExp_of_ne_zero (f : MvPowerSeries σ ℤ) {α : σ →₀ ℕ} (hα : α ≠ 0) :
    wittExp f α =
      coeff α (S (R := ℤ) fun β => if β < α then wittExp f β else 0) - coeff α f := by
  rw [wittExp, WellFounded.fix_eq]
  simp only [hα, ↓reduceIte, dite_eq_ite]

/-- **Existence of integer exponents.** Every integral power series with constant term `1` is
`∏_{α > 0} (1 - x^α)^{e_α}` for the exponents `e = wittExp f`. -/
theorem S_wittExp (f : MvPowerSeries σ ℤ) (hf : constantCoeff f = 1) : S (wittExp f) = f := by
  classical
  ext α
  by_cases hα : α = 0
  · subst hα
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, constantCoeff_S, hf]
  set e' : (σ →₀ ℕ) → ℤ := fun β => if β < α then wittExp f β else 0 with he'
  have key := coeff_S_sub (R := ℤ) (wittExp f) e' ⟨α, hα⟩ fun β hβ => by simp [he', hβ]
  have hα' : e' α = 0 := by simp [he']
  simp only at key
  rw [key, hα', wittExp_of_ne_zero f hα]
  simp [he']

/-- **The big Witt factorization.** Over `ℤ`, `e ↦ S_e` is a bijection between exponent families
on the positive classes and power series with constant term one. -/
theorem S_bijective_int :
    (∀ e e' : (σ →₀ ℕ) → ℤ, S (R := ℤ) e = S e' → ∀ α : Pos σ, e α.1 = e' α.1) ∧
      (∀ f : MvPowerSeries σ ℤ, constantCoeff f = 1 → ∃ e, S (R := ℤ) e = f) :=
  ⟨fun _ _ h => S_injective h, fun f hf => ⟨wittExp f, S_wittExp f hf⟩⟩

/-- The Witt exponents of a multiplier are its exponents. -/
theorem wittExp_S (e : (σ →₀ ℕ) → ℤ) (α : Pos σ) : wittExp (S (R := ℤ) e) α.1 = e α.1 :=
  S_injective (S_wittExp _ (constantCoeff_S e)) α

/-! ### Recovering `Ω` from one framing -/

/-- The framed series determines `Ω_α` wherever `p·α ≠ 0`, over a ring of characteristic
zero. -/
theorem framedS_determines [CharZero R] {p : σ → ℤ} {Ω Ω' : (σ →₀ ℕ) → ℤ}
    (h : framedS (R := R) p Ω = framedS p Ω') (α : Pos σ) (hp : pair p α.1 ≠ 0) :
    Ω α.1 = Ω' α.1 :=
  mul_left_cancel₀ hp (S_injective h α)

/-- A framing with every entry positive pairs positively with every positive class. -/
theorem pair_pos {p : σ → ℤ} (hp : ∀ i, 0 < p i) (α : Pos σ) : 0 < pair p α.1 := by
  unfold pair Finsupp.sum
  refine Finset.sum_pos (fun i hi => mul_pos (hp i) ?_)
    (Finsupp.support_nonempty_iff.2 α.2)
  exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hi)

/-- **One framing suffices.** If `p` pairs to a nonzero number with every positive class, for
example if every `p_i > 0`, the framed series determines `Ω` on all positive classes, over a
ring of characteristic zero. No identity in other chambers is needed. -/
theorem framedS_injective [CharZero R] {p : σ → ℤ} (hp : ∀ α : Pos σ, pair p α.1 ≠ 0)
    {Ω Ω' : (σ →₀ ℕ) → ℤ} (h : framedS (R := R) p Ω = framedS p Ω') (α : Pos σ) :
    Ω α.1 = Ω' α.1 :=
  framedS_determines h α (hp α)

/-- **Exponents are additive in the framing.** If a family `E` of exponent families gives
multipliers that are multiplicative in the framing, its exponents are additive, over a ring of
characteristic zero. -/
theorem exponents_additive [CharZero R] (E : (σ → ℤ) → (σ →₀ ℕ) → ℤ)
    (hE : ∀ p p', S (R := R) (E (p + p')) = S (E p) * S (E p')) (p p' : σ → ℤ) (α : Pos σ) :
    E (p + p') α.1 = E p α.1 + E p' α.1 := by
  simpa using S_injective (R := R) ((hE p p').trans (S_add (E p) (E p')).symm) α

/-! ### The framed DT statement -/

/-- **The numerical framed DT statement** for a family `F` of integral framed series, indexed by
framings: every `F p` is the framed multiplier `∏_{α > 0} (1 - x^α)^{(p·α) Ω_α}` of one family
`Ω` of BPS invariants. -/
def IsFramedDT (F : (σ → ℤ) → MvPowerSeries σ ℤ) (Ω : (σ →₀ ℕ) → ℤ) : Prop :=
  ∀ p, F p = framedS p Ω

/-- **The DT statement is a statement about exponents.** A family of framed series satisfies the
framed DT statement for `Ω` exactly when each series has constant term one and its Witt
exponents are `e_α(p) = Ω_α (p·α)`. -/
theorem isFramedDT_iff (F : (σ → ℤ) → MvPowerSeries σ ℤ) (Ω : (σ →₀ ℕ) → ℤ) :
    IsFramedDT F Ω ↔
      ∀ p, constantCoeff (F p) = 1 ∧ ∀ α : Pos σ, wittExp (F p) α.1 = pair p α.1 * Ω α.1 := by
  constructor
  · intro h p
    rw [h p, framedS]
    exact ⟨constantCoeff_S _, fun α => wittExp_S _ α⟩
  · intro h p
    rw [← S_wittExp (F p) (h p).1, framedS]
    exact S_congr (h p).2

/-- Under the framed DT statement, `Ω` is unique on every positive class that some framing
pairs with nonzero. -/
theorem IsFramedDT.unique {F : (σ → ℤ) → MvPowerSeries σ ℤ} {Ω Ω' : (σ →₀ ℕ) → ℤ}
    (h : IsFramedDT F Ω) (h' : IsFramedDT F Ω') (α : Pos σ) (p : σ → ℤ)
    (hp : pair p α.1 ≠ 0) : Ω α.1 = Ω' α.1 :=
  framedS_determines ((h p).symm.trans (h' p)) α hp

end MvPowerSeries.FramedMultiplier
