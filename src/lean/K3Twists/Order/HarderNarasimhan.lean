/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Order.Valuation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Order.WellFounded
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Harder–Narasimhan filtrations in a lattice with a charge function

Let `L` be a bounded lattice and `K` a linearly ordered field. A *charge function* on `L`
(`ChargeFunction`) is a rank `rk` and a degree `deg : L → K`, both valuations,

  `f (x ⊔ y) + f (x ⊓ y) = f x + f y`,

with `(rk, deg)` strictly monotone for the lexicographic order: `x < y` gives `rk x < rk y`, or
`rk x = rk y` and `deg x < deg y`. A step of the second kind is *vertical*.

The subobjects of an object of an abelian category with a stability function `Z` form such a
lattice, with `rk = Im Z` and `deg = -Re Z` (`CategoryTheory.Subobject.chargeFunction`); a
vertical step is a subquotient whose charge lies on the negative real axis, of phase one in
Bridgeland's normalization. The subrepresentations of a quiver representation form one, with
`rk` and `deg` linear in the dimension vector.

**Conventions.** The *phase* of an interval `x < y` is `(deg y - deg x) / (rk y - rk x)` in
`WithTop K`, and `⊤` when the interval is vertical. For `rk = Im Z`, `deg = -Re Z` and a charge
`Z = r e^{iπφ}` with `r > 0`, `0 < φ ≤ 1`, the phase is `-cot (πφ)`: it increases with `φ`, and
`φ = 1` is `⊤`. The *weight* of slope `θ : K` is `w_θ x = deg x - θ rk x`.

An interval `[x, y]` is *semistable* if `x < y` and no `z` with `x < z ≤ y` has a larger phase
from `x` (`ChargeFunction.isSemistable_iff_phase`); the definition compares cross products and
never divides. An *HN chain* of `[a, ⊤]` (`ChargeFunction.HNChain`) is a chain
`a = c₀ < c₁ < ⋯ < cₙ = ⊤` with semistable factors of strictly decreasing phases. A
*Harder–Narasimhan filtration* is an HN chain of `[⊥, ⊤]`.

## Main results

* `ChargeFunction.isModularLattice`: a lattice with a charge function is modular, since
  `(rk, deg)` is a valuation injective on comparable pairs (`isModularLattice_of_valuation`).
* `HNChain.weight_le`, `HNChain.eq_of_weight_eq`: the prefix `cₖ` with factor phases `≥ θ`
  below and `≤ θ` above maximizes `w_θ`, uniquely if the inequalities are strict.
* `HNChain.mem_range_chain_iff`: the prefixes of an HN filtration are `⊥` and the unique
  maximizers of the weights `w_θ`, `θ : K`. The disjunct `⊥` is needed: when the first factor is
  vertical, every element above `⊥` of the same rank has a larger weight than `⊥` for every `θ`.
* `HNChain.instSubsingleton`: an HN filtration is unique, with no finiteness hypothesis.
* `HNChain.factorPhase_zero_eq_top_iff`: the first factor is vertical if and only if some element
  above `⊥` has the rank of `⊥`. `HNChain.apply_chain_eq`: every map `L → L` preserving rank and
  degree fixes the prefixes.
* `ChargeFunction.nonempty_hnChain`, `ChargeFunction.nonempty_hnFiltration`: **existence**, from
  `WellFoundedGT L` and a maximal phase attained on every interval `[a, ⊤]`
  (`ChargeFunction.MaxPhaseAttained`). These hypotheses are sufficient, not necessary.
* `ChargeFunction.nonempty_hnFiltration_of_finite_range`: existence when `(rk, deg)` takes
  finitely many values. For a charge function this bounds the length of every chain
  (`ChargeFunction.card_le_of_finite_range`), so it is a statement about lattices of finite
  length. The main theorem also covers lattices of infinite length with the ascending chain
  condition, such as the subobjects of a line bundle `O(D)` in a Noetherian heart, where the
  chain `O(D) ⊃ I_Z(D) ⊃ ⋯` has constant rank and unbounded degree.
* `ChargeFunction.HNChain.ofPhaseOrder`: HN chains only depend on the order of phases.
* `SlopeFunction`: the case of a strictly monotone rank, with no vertical steps and slopes in
  `K`. `SlopeFunction.HNFiltration.toCharge` and `SlopeFunction.HNFiltration.ofCharge` translate
  its HN filtrations, and its uniqueness, extremality and existence statements are corollaries of
  the charge versions.

These are the Harder–Narasimhan filtrations described by maximizers of the weights, as in the HN
polytope of Baumann, Kamnitzer and Tingley (arXiv:1110.3661, §3.2), in the generality of a
lattice with valuations; the polytope is in `K3Twists.Order.HarderNarasimhan.Polytope`. The
existence induction splits off the greatest element of maximal phase, as in the proof of the
existence of Harder–Narasimhan filtrations for a stability function on an abelian category with
chain conditions (Bridgeland, arXiv:math/0212237, Proposition 2.4).

## Implementation notes

The chain is indexed by `Fin (n + 1)`, with the number of factors `n` part of the data: it has
exactly the entries `c₀, …, cₙ`, and the factor `[cᵢ, cᵢ₊₁]` is indexed by `i : Fin n` through
`Fin.castSucc` and `Fin.succ`. Filtrations of different lengths are terms of one type, which the
uniqueness statement compares. Proofs that induct on the index pass to the extension
`HNChain.seq : ℕ → L`, constant `⊤` after `n`. Relative chains of `[a, ⊤]` are forced by the
existence induction.
-/

namespace Order

/-! ### Charge functions -/

variable (L : Type*) [Lattice L] (K : Type*) [Field K] [LinearOrder K]

/-- A charge function on a lattice: a rank and a degree, both valuations, with `(rk, deg)`
strictly monotone for the lexicographic order. A step `x < y` with `rk x = rk y` is vertical. -/
structure ChargeFunction where
  /-- The rank, a monotone valuation (`ChargeFunction.rk_mono`). -/
  rk : L → K
  /-- The degree, a valuation, strictly monotone on vertical steps. -/
  deg : L → K
  lex_lt {x y : L} : x < y → rk x < rk y ∨ (rk x = rk y ∧ deg x < deg y)
  rk_sup_add_inf (x y : L) : rk (x ⊔ y) + rk (x ⊓ y) = rk x + rk y
  deg_sup_add_inf (x y : L) : deg (x ⊔ y) + deg (x ⊓ y) = deg x + deg y

namespace ChargeFunction

variable {L K} (c : ChargeFunction L K)

lemma strictMono_toLex : StrictMono fun x ↦ toLex (c.rk x, c.deg x) :=
  fun _ _ h ↦ Prod.Lex.toLex_lt_toLex.mpr (c.lex_lt h)

lemma rk_mono : Monotone c.rk := fun x y h ↦ by
  rcases h.lt_or_eq with h | rfl
  · rcases c.lex_lt h with h | h
    exacts [h.le, h.1.le]
  · exact le_rfl

/-- `(rk, deg)` is injective on comparable pairs. -/
lemma eq_of_le_of_eq {x y : L} (h : x ≤ y) (hr : c.rk x = c.rk y) (hd : c.deg x = c.deg y) :
    x = y := by
  by_contra hne
  rcases c.lex_lt (lt_of_le_of_ne h hne) with h' | h'
  · exact h'.ne hr
  · exact h'.2.ne hd

lemma deg_le_of_le_of_rk_eq {x y : L} (h : x ≤ y) (hr : c.rk x = c.rk y) :
    c.deg x ≤ c.deg y := by
  rcases h.lt_or_eq with h | rfl
  · rcases c.lex_lt h with h' | h'
    · exact absurd hr h'.ne
    · exact h'.2.le
  · exact le_rfl

include c in
/-- **Modularity is derived**, not assumed: `(rk, deg)` is a valuation injective on comparable
pairs. -/
theorem isModularLattice : IsModularLattice L :=
  isModularLattice_of_valuation (fun x ↦ (c.rk x, c.deg x))
    (fun x y ↦ Prod.ext (c.rk_sup_add_inf x y) (c.deg_sup_add_inf x y))
    (fun h e ↦ c.eq_of_le_of_eq h (congrArg Prod.fst e) (congrArg Prod.snd e))

/-- The weight of slope `θ`, `w_θ x = deg x - θ rk x`. -/
def weight (θ : K) (x : L) : K := c.deg x - θ * c.rk x

lemma weight_sup_add_inf (θ : K) (x y : L) :
    c.weight θ (x ⊔ y) + c.weight θ (x ⊓ y) = c.weight θ x + c.weight θ y := by
  simp only [weight]
  linear_combination c.deg_sup_add_inf x y - θ * c.rk_sup_add_inf x y

/-- The phase of the interval from `x` to `y`, in `WithTop K`: `(deg y - deg x) / (rk y - rk x)`,
or `⊤` when `rk x = rk y`. -/
noncomputable def phase (x y : L) : WithTop K :=
  if c.rk y - c.rk x = 0 then ⊤ else (((c.deg y - c.deg x) / (c.rk y - c.rk x) : K) : WithTop K)

/-- `[x, y]` is semistable: `x < y`, and every `z` with `x ≤ z ≤ y` satisfies
`(deg z - deg x)(rk y - rk x) ≤ (deg y - deg x)(rk z - rk x)`, that is, the phase of `[x, z]` is
at most that of `[x, y]` when `x < z` (`isSemistable_iff_phase`). -/
def IsSemistable (x y : L) : Prop :=
  x < y ∧ ∀ z, x ≤ z → z ≤ y →
    (c.deg z - c.deg x) * (c.rk y - c.rk x) ≤ (c.deg y - c.deg x) * (c.rk z - c.rk x)

section OrderedField

variable [IsStrictOrderedRing K] {x y z : L}

omit [IsStrictOrderedRing K] in
lemma phase_eq_top_iff : c.phase x y = ⊤ ↔ c.rk x = c.rk y := by
  unfold phase
  split_ifs with h0
  · simp only [true_iff]
    exact (sub_eq_zero.mp h0).symm
  · simp only [WithTop.coe_ne_top, false_iff]
    exact fun e ↦ h0 (by rw [e, sub_self])

lemma coe_le_phase_iff (h : x < y) (θ : K) :
    (θ : WithTop K) ≤ c.phase x y ↔ θ * (c.rk y - c.rk x) ≤ c.deg y - c.deg x := by
  unfold phase
  rcases c.lex_lt h with hr | ⟨hr, hd⟩
  · have hpos : 0 < c.rk y - c.rk x := sub_pos.mpr hr
    rw [ite_eq_right hpos.ne', WithTop.coe_le_coe, le_div_iff₀ hpos]
  · rw [ite_eq_left (by rw [hr, sub_self]), hr, sub_self, mul_zero]
    simp only [le_top, true_iff]
    linarith

lemma coe_lt_phase_iff (h : x < y) (θ : K) :
    (θ : WithTop K) < c.phase x y ↔ θ * (c.rk y - c.rk x) < c.deg y - c.deg x := by
  unfold phase
  rcases c.lex_lt h with hr | ⟨hr, hd⟩
  · have hpos : 0 < c.rk y - c.rk x := sub_pos.mpr hr
    rw [ite_eq_right hpos.ne', WithTop.coe_lt_coe, lt_div_iff₀ hpos]
  · rw [ite_eq_left (by rw [hr, sub_self]), hr, sub_self, mul_zero]
    simp only [WithTop.coe_lt_top, true_iff]
    linarith

lemma phase_le_coe_iff (h : x < y) (θ : K) :
    c.phase x y ≤ (θ : WithTop K) ↔ c.deg y - c.deg x ≤ θ * (c.rk y - c.rk x) := by
  rw [← not_lt, c.coe_lt_phase_iff h, not_lt]

lemma phase_lt_coe_iff (h : x < y) (θ : K) :
    c.phase x y < (θ : WithTop K) ↔ c.deg y - c.deg x < θ * (c.rk y - c.rk x) := by
  rw [← not_le, c.coe_le_phase_iff h, not_le]

/-- **Phase comparison is the cross product**, vertical steps included. -/
lemma phase_le_phase_iff {x' y' : L} (h : x < y) (h' : x' < y') :
    c.phase x y ≤ c.phase x' y' ↔
      (c.deg y - c.deg x) * (c.rk y' - c.rk x') ≤ (c.deg y' - c.deg x') * (c.rk y - c.rk x) := by
  unfold phase
  rcases c.lex_lt h with hr | ⟨hr, hd⟩ <;> rcases c.lex_lt h' with hr' | ⟨hr', hd'⟩
  · have hpos : 0 < c.rk y - c.rk x := sub_pos.mpr hr
    have hpos' : 0 < c.rk y' - c.rk x' := sub_pos.mpr hr'
    rw [ite_eq_right hpos.ne', ite_eq_right hpos'.ne', WithTop.coe_le_coe,
      div_le_div_iff₀ hpos hpos']
  · have hpos : 0 < c.rk y - c.rk x := sub_pos.mpr hr
    rw [ite_eq_right hpos.ne', ite_eq_left (by rw [hr', sub_self]), hr', sub_self, mul_zero]
    simp only [le_top, true_iff]
    exact mul_nonneg (by linarith) hpos.le
  · have hpos' : 0 < c.rk y' - c.rk x' := sub_pos.mpr hr'
    rw [ite_eq_left (by rw [hr, sub_self]), ite_eq_right hpos'.ne', hr, sub_self, mul_zero]
    simp only [top_le_iff, WithTop.coe_ne_top, false_iff, not_le]
    exact mul_pos (by linarith) hpos'
  · rw [ite_eq_left (by rw [hr, sub_self]), ite_eq_left (by rw [hr', sub_self]), hr, hr', sub_self,
      sub_self, mul_zero, mul_zero]
    simp

lemma phase_lt_phase_iff {x' y' : L} (h : x < y) (h' : x' < y') :
    c.phase x y < c.phase x' y' ↔
      (c.deg y - c.deg x) * (c.rk y' - c.rk x') < (c.deg y' - c.deg x') * (c.rk y - c.rk x) := by
  rw [← not_le, c.phase_le_phase_iff h' h, not_le]

/-- The phase form of semistability. -/
lemma isSemistable_iff_phase (h : x < y) :
    c.IsSemistable x y ↔ ∀ z, x < z → z ≤ y → c.phase x z ≤ c.phase x y := by
  constructor
  · intro hs z hxz hzy
    exact (c.phase_le_phase_iff hxz h).mpr (hs.2 z hxz.le hzy)
  · intro H
    refine ⟨h, fun z hxz hzy ↦ ?_⟩
    rcases hxz.lt_or_eq with hxz | rfl
    · exact (c.phase_le_phase_iff hxz h).mp (H z hxz hzy)
    · simp

omit [IsStrictOrderedRing K] in
/-- Vertical intervals are semistable. -/
lemma isSemistable_of_rk_eq (h : x < y) (hr : c.rk x = c.rk y) : c.IsSemistable x y := by
  refine ⟨h, fun z hxz hzy ↦ ?_⟩
  have h1 := c.rk_mono hxz
  have h2 := c.rk_mono hzy
  have : c.rk z = c.rk x := le_antisymm (hr ▸ h2) h1
  rw [this, hr]
  simp

/-! Four inequalities of real numbers: `(a, b)` is the charge of `[x, y]` and `(a', b')` that of
`[x, z]`. -/

omit [Lattice L] in
private lemma aux_bot {a b a' b' θ : K} (ha' : 0 ≤ a') (hlex : 0 < a ∨ (a = 0 ∧ 0 < b))
    (hss : b' * a ≤ b * a') (hθ : b ≤ θ * a) : b' ≤ θ * a' := by
  rcases hlex with ha | ⟨ha, hb⟩
  · nlinarith
  · subst ha; linarith

omit [Lattice L] in
private lemma aux_bot_strict {a b a' b' θ : K} (haa : a' ≤ a) (hb : a = 0 → 0 < b)
    (hlex' : 0 < a' ∨ (a' = 0 ∧ 0 < b')) (hss : b' * a ≤ b * a') (hθ : b < θ * a) :
    b' < θ * a' := by
  rcases hlex' with ha' | ⟨ha', hb'⟩
  · nlinarith
  · subst ha'
    rcases eq_or_lt_of_le haa with ha | ha
    · have := hb ha.symm
      rw [← ha] at hθ
      linarith
    · nlinarith

omit [Lattice L] in
private lemma aux_top {a b a' b' θ : K} (ha' : 0 ≤ a') (haa : a' ≤ a) (hdeg : a = a' → b' ≤ b)
    (hss : b' * a ≤ b * a') (hθ : θ * a ≤ b) : b' - θ * a' ≤ b - θ * a := by
  rcases eq_or_lt_of_le (ha'.trans haa) with ha | ha
  · have : a' = 0 := le_antisymm (ha ▸ haa) ha'
    have := hdeg (by rw [← ha, this])
    subst ha
    simp_all
  · have p : 0 ≤ (b - θ * a) * (a - a') := mul_nonneg (by linarith) (by linarith)
    nlinarith

omit [Lattice L] in
private lemma aux_top_strict {a b a' b' θ : K} (ha' : 0 ≤ a')
    (hlex : a' < a ∨ (a' = a ∧ b' < b)) (hss : b' * a ≤ b * a') (hθ : θ * a < b) :
    b' - θ * a' < b - θ * a := by
  rcases hlex with h | ⟨h, hb⟩
  · have p : 0 < (b - θ * a) * (a - a') := mul_pos (by linarith) (by linarith)
    nlinarith
  · subst h; linarith

variable {c}

/-- On a semistable `[x, y]` of phase at most `θ`, the bottom `x` maximizes `w_θ`. -/
lemma IsSemistable.weight_le_bot {θ : K} (h : c.IsSemistable x y)
    (hθ : c.phase x y ≤ (θ : WithTop K)) (hxz : x ≤ z) (hzy : z ≤ y) :
    c.weight θ z ≤ c.weight θ x := by
  have := aux_bot (sub_nonneg.mpr (c.rk_mono hxz))
    (by rcases c.lex_lt h.1 with h' | h'
        · exact Or.inl (sub_pos.mpr h')
        · exact Or.inr ⟨by rw [h'.1, sub_self], sub_pos.mpr h'.2⟩)
    (h.2 z hxz hzy) ((c.phase_le_coe_iff h.1 θ).mp hθ)
  simp only [weight]
  linarith

/-- On a semistable `[x, y]` of phase less than `θ`, the bottom `x` is the only maximizer
of `w_θ`. -/
lemma IsSemistable.eq_bot_of_weight_eq {θ : K} (h : c.IsSemistable x y)
    (hθ : c.phase x y < (θ : WithTop K)) (hxz : x ≤ z) (hzy : z ≤ y)
    (heq : c.weight θ z = c.weight θ x) : z = x := by
  by_contra hne
  have hlt : x < z := lt_of_le_of_ne hxz (Ne.symm hne)
  have := aux_bot_strict (sub_le_sub_right (c.rk_mono hzy) _)
    (fun ha ↦ by
      rcases c.lex_lt h.1 with h' | h'
      · exact absurd ha (sub_pos.mpr h').ne'
      · exact sub_pos.mpr h'.2)
    (by rcases c.lex_lt hlt with h' | h'
        · exact Or.inl (sub_pos.mpr h')
        · exact Or.inr ⟨by rw [h'.1, sub_self], sub_pos.mpr h'.2⟩)
    (h.2 z hxz hzy) ((c.phase_lt_coe_iff h.1 θ).mp hθ)
  simp only [weight] at heq
  linarith

/-- On a semistable `[x, y]` of phase at least `θ`, the top `y` maximizes `w_θ`. -/
lemma IsSemistable.weight_le_top {θ : K} (h : c.IsSemistable x y)
    (hθ : (θ : WithTop K) ≤ c.phase x y) (hxz : x ≤ z) (hzy : z ≤ y) :
    c.weight θ z ≤ c.weight θ y := by
  have := aux_top (sub_nonneg.mpr (c.rk_mono hxz)) (sub_le_sub_right (c.rk_mono hzy) _)
    (fun e ↦ by
      have : c.rk y = c.rk z := by linarith
      linarith [c.deg_le_of_le_of_rk_eq hzy this.symm])
    (h.2 z hxz hzy) ((c.coe_le_phase_iff h.1 θ).mp hθ)
  simp only [weight]
  linarith

/-- On a semistable `[x, y]` of phase greater than `θ`, the top `y` is the only maximizer
of `w_θ`. -/
lemma IsSemistable.eq_top_of_weight_eq {θ : K} (h : c.IsSemistable x y)
    (hθ : (θ : WithTop K) < c.phase x y) (hxz : x ≤ z) (hzy : z ≤ y)
    (heq : c.weight θ z = c.weight θ y) : z = y := by
  by_contra hne
  have hlt : z < y := lt_of_le_of_ne hzy hne
  have := aux_top_strict (sub_nonneg.mpr (c.rk_mono hxz))
    (by rcases c.lex_lt hlt with h' | h'
        · exact Or.inl (sub_lt_sub_right h' _)
        · exact Or.inr ⟨by rw [h'.1], sub_lt_sub_right h'.2 _⟩)
    (h.2 z hxz hzy) ((c.coe_lt_phase_iff h.1 θ).mp hθ)
  simp only [weight] at heq
  linarith

/-- **The seesaw.** For `x < y < z`, if `[x, z]` has a smaller phase than `[x, y]`, so has
`[y, z]`. -/
lemma phase_lt_of_seesaw (hxy : x < y) (hyz : y < z) (h : c.phase x z < c.phase x y) :
    c.phase y z < c.phase x y := by
  rw [c.phase_lt_phase_iff (hxy.trans hyz) hxy] at h
  rw [c.phase_lt_phase_iff hyz hxy]
  nlinarith

end OrderedField

/-! ### Harder–Narasimhan chains -/

variable [BoundedOrder L]

/-- An HN chain of `[a, ⊤]`: a chain `a = chain 0 < ⋯ < chain n = ⊤` whose factors are
semistable with strictly decreasing phases. -/
structure HNChain (a : L) where
  /-- The number of factors. -/
  n : ℕ
  /-- The chain of prefixes. -/
  chain : Fin (n + 1) → L
  strictMono : StrictMono chain
  chain_zero : chain 0 = a
  chain_last : chain (Fin.last n) = ⊤
  semistable : ∀ i : Fin n, c.IsSemistable (chain i.castSucc) (chain i.succ)
  phase_strictAnti : StrictAnti fun i : Fin n ↦ c.phase (chain i.castSucc) (chain i.succ)

/-- A Harder–Narasimhan filtration: an HN chain of `[⊥, ⊤]`. -/
abbrev HNFiltration := c.HNChain ⊥

variable {c}

namespace HNChain

variable {a : L} (F : c.HNChain a)

/-- The phase of the `i`th factor `[chain i, chain (i + 1)]`. -/
noncomputable def factorPhase (i : Fin F.n) : WithTop K :=
  c.phase (F.chain i.castSucc) (F.chain i.succ)

/-- The chain extended to `ℕ`, constant `⊤` after `n`. -/
def seq (j : ℕ) : L := F.chain ⟨min j F.n, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma seq_of_le {j : ℕ} (hj : j ≤ F.n) : F.seq j = F.chain ⟨j, Nat.lt_succ_of_le hj⟩ := by
  simp only [seq, min_eq_left hj]

lemma seq_fin (k : Fin (F.n + 1)) : F.seq k = F.chain k := by
  rw [F.seq_of_le (Nat.le_of_lt_succ k.isLt)]

lemma seq_zero : F.seq 0 = a := by
  rw [F.seq_of_le (Nat.zero_le _)]
  exact F.chain_zero

lemma seq_n : F.seq F.n = ⊤ := by
  rw [F.seq_of_le le_rfl]
  exact F.chain_last

lemma seq_mono : Monotone F.seq := fun _ _ h ↦
  F.strictMono.monotone (Fin.mk_le_mk.mpr (min_le_min_right _ h))

lemma seq_isSemistable {j : ℕ} (hj : j < F.n) : c.IsSemistable (F.seq j) (F.seq (j + 1)) := by
  rw [F.seq_of_le hj.le, F.seq_of_le hj]
  exact F.semistable ⟨j, hj⟩

lemma phase_seq {j : ℕ} (hj : j < F.n) :
    c.phase (F.seq j) (F.seq (j + 1)) = F.factorPhase ⟨j, hj⟩ := by
  rw [F.seq_of_le hj.le, F.seq_of_le hj]
  rfl

section OrderedField

variable [IsStrictOrderedRing K] {θ : K}

/-- **The prefixes maximize the weights.** If the factors below `chain k` have phases at least
`θ` and those above have phases at most `θ`, then `chain k` maximizes `w_θ` over `L`. -/
theorem weight_le (F : c.HNFiltration) (k : Fin (F.n + 1))
    (h₁ : ∀ i : Fin F.n, i.succ ≤ k → (θ : WithTop K) ≤ F.factorPhase i)
    (h₂ : ∀ i : Fin F.n, k ≤ i.castSucc → F.factorPhase i ≤ (θ : WithTop K)) (x : L) :
    c.weight θ x ≤ c.weight θ (F.chain k) := by
  rw [← F.seq_fin k]
  refine val_le_of_chain (c.weight_sup_add_inf θ) F.seq_mono F.seq_zero F.seq_n
    (Nat.le_of_lt_succ k.isLt) (fun j hj z h1 h2 ↦ ?_) (fun j hj hjn z h1 h2 ↦ ?_) x
  · have hjn : j < F.n := by omega
    exact (F.seq_isSemistable hjn).weight_le_top
      (by rw [F.phase_seq hjn]; exact h₁ ⟨j, hjn⟩ (by rw [Fin.le_def]; simp; omega)) h1 h2
  · exact (F.seq_isSemistable hjn).weight_le_bot
      (by rw [F.phase_seq hjn]; exact h₂ ⟨j, hjn⟩ (by rw [Fin.le_def]; simp; omega)) h1 h2

/-- **The prefixes are the only maximizers.** If the factors below `chain k` have phases greater
than `θ` and those above have phases less than `θ`, then `chain k` is the only maximizer
of `w_θ`. -/
theorem eq_of_weight_eq (F : c.HNFiltration) (k : Fin (F.n + 1))
    (h₁ : ∀ i : Fin F.n, i.succ ≤ k → (θ : WithTop K) < F.factorPhase i)
    (h₂ : ∀ i : Fin F.n, k ≤ i.castSucc → F.factorPhase i < (θ : WithTop K)) {x : L}
    (hx : c.weight θ x = c.weight θ (F.chain k)) : x = F.chain k := by
  rw [← F.seq_fin k] at hx ⊢
  have hkn := Nat.le_of_lt_succ k.isLt
  have H₁ : ∀ j (hj : j < F.n), j < (k : ℕ) →
      (θ : WithTop K) < c.phase (F.seq j) (F.seq (j + 1)) :=
    fun j hj hjk ↦ by rw [F.phase_seq hj]; exact h₁ ⟨j, hj⟩ (by rw [Fin.le_def]; simp; omega)
  have H₂ : ∀ j (hj : j < F.n), (k : ℕ) ≤ j →
      c.phase (F.seq j) (F.seq (j + 1)) < (θ : WithTop K) :=
    fun j hj hjk ↦ by rw [F.phase_seq hj]; exact h₂ ⟨j, hj⟩ (by rw [Fin.le_def]; simp; omega)
  exact eq_of_val_eq_of_chain (c.weight_sup_add_inf θ) F.seq_mono F.seq_zero F.seq_n hkn
    (fun j hj z h1 h2 ↦ (F.seq_isSemistable (by omega)).weight_le_top
      (H₁ j (by omega) hj).le h1 h2)
    (fun j hj z h1 h2 h3 ↦ (F.seq_isSemistable (by omega)).eq_top_of_weight_eq
      (H₁ j (by omega) hj) h1 h2 h3)
    (fun j hj hjn z h1 h2 ↦ (F.seq_isSemistable hjn).weight_le_bot (H₂ j hjn hj).le h1 h2)
    (fun j hj hjn z h1 h2 h3 ↦
      (F.seq_isSemistable hjn).eq_bot_of_weight_eq (H₂ j hjn hj) h1 h2 h3)
    hx

omit [IsStrictOrderedRing K] in
/-- Every `θ : K` lies between the phases around some prefix. -/
lemma exists_index (θ : K) : ∃ k : Fin (F.n + 1),
    (∀ i : Fin F.n, i.succ ≤ k → (θ : WithTop K) ≤ F.factorPhase i) ∧
      ∀ i : Fin F.n, k ≤ i.castSucc → F.factorPhase i ≤ (θ : WithTop K) := by
  classical
  have hP : ∃ j, j = F.n ∨ ∃ hj : j < F.n, F.factorPhase ⟨j, hj⟩ ≤ (θ : WithTop K) :=
    ⟨F.n, Or.inl rfl⟩
  have hkn : Nat.find hP ≤ F.n := Nat.find_min' hP (Or.inl rfl)
  refine ⟨⟨Nat.find hP, Nat.lt_succ_of_le hkn⟩, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · have hlt : (i : ℕ) < Nat.find hP := by simpa [Fin.le_def] using hi
    have := Nat.find_min hP hlt
    simp only [not_or, not_exists, not_le] at this
    exact (this.2 i.isLt).le
  · have hle : Nat.find hP ≤ (i : ℕ) := by simpa [Fin.le_def] using hi
    rcases Nat.find_spec hP with h | ⟨hj, hθ⟩
    · omega
    · exact (F.phase_strictAnti.antitone (Fin.mk_le_mk.mpr hle)).trans hθ

/-- Every nonzero prefix `chain (j + 1)` lies strictly between the phases around it for some
finite `θ`: the phase above it is finite even when the one below is `⊤`. -/
lemma exists_between_succ (j : Fin F.n) : ∃ θ : K,
    (θ : WithTop K) < F.factorPhase j ∧
      ∀ hj : (j : ℕ) + 1 < F.n, F.factorPhase ⟨(j : ℕ) + 1, hj⟩ < (θ : WithTop K) := by
  by_cases hj : (j : ℕ) + 1 < F.n
  · have hlt : F.factorPhase ⟨(j : ℕ) + 1, hj⟩ < F.factorPhase j :=
      F.phase_strictAnti (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _))
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
    rcases eq_or_ne (F.factorPhase j) ⊤ with htop | hne
    · exact ⟨m + 1, by rw [htop]; exact WithTop.coe_lt_top _, fun _ ↦ by
        rw [← hm, WithTop.coe_lt_coe]; exact lt_add_one m⟩
    · obtain ⟨m', hm'⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hm, ← hm', WithTop.coe_lt_coe] at hlt
      obtain ⟨θ, h1, h2⟩ := exists_between hlt
      exact ⟨θ, by rw [← hm', WithTop.coe_lt_coe]; exact h2, fun _ ↦ by
        rw [← hm, WithTop.coe_lt_coe]; exact h1⟩
  · rcases eq_or_ne (F.factorPhase j) ⊤ with htop | hne
    · exact ⟨0, by rw [htop]; exact WithTop.coe_lt_top _, fun h ↦ absurd h hj⟩
    · obtain ⟨m', hm'⟩ := WithTop.ne_top_iff_exists.mp hne
      exact ⟨m' - 1, by rw [← hm', WithTop.coe_lt_coe]; exact sub_one_lt m',
        fun h ↦ absurd h hj⟩

/-- **The prefixes are intrinsic.** An element is a prefix of an HN filtration if and only if it
is `⊥` or the unique maximizer of some weight `w_θ`, `θ : K`. The disjunct `⊥` is needed: when
the first factor is vertical, `⊥` maximizes no weight. -/
theorem mem_range_chain_iff (F : c.HNFiltration) (x : L) : x ∈ Set.range F.chain ↔
    x = ⊥ ∨ ∃ θ : K, ∀ y, c.weight θ y ≤ c.weight θ x ∧ (c.weight θ y = c.weight θ x → y = x) := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
    · exact Or.inl F.chain_zero
    · right
      obtain ⟨θ, hθ₁, hθ₂⟩ := F.exists_between_succ j
      have h₁ : ∀ i : Fin F.n, i.succ ≤ j.succ → (θ : WithTop K) < F.factorPhase i :=
        fun i hi ↦ hθ₁.trans_le (F.phase_strictAnti.antitone (Fin.succ_le_succ_iff.mp hi))
      have h₂ : ∀ i : Fin F.n, j.succ ≤ i.castSucc → F.factorPhase i < (θ : WithTop K) := by
        intro i hi
        have hji : (j : ℕ) + 1 ≤ i := by simpa [Fin.le_def] using hi
        have hj : (j : ℕ) + 1 < F.n := lt_of_le_of_lt hji i.isLt
        exact (F.phase_strictAnti.antitone (Fin.mk_le_mk.mpr hji)).trans_lt (hθ₂ hj)
      exact ⟨θ, fun y ↦ ⟨F.weight_le j.succ (fun i hi ↦ (h₁ i hi).le)
        (fun i hi ↦ (h₂ i hi).le) y, F.eq_of_weight_eq j.succ h₁ h₂⟩⟩
  · rintro (rfl | ⟨θ, hx⟩)
    · exact ⟨0, F.chain_zero⟩
    · obtain ⟨k, h₁, h₂⟩ := F.exists_index θ
      exact ⟨k, ((hx (F.chain k)).2 (le_antisymm (hx _).1 (F.weight_le k h₁ h₂ x)))⟩

/-- **Uniqueness.** A charge function has at most one HN filtration. -/
instance instSubsingleton : Subsingleton c.HNFiltration := by
  refine ⟨fun F G ↦ ?_⟩
  have hrange : Set.range F.chain = Set.range G.chain :=
    Set.ext fun x ↦ by rw [F.mem_range_chain_iff, G.mem_range_chain_iff]
  have hn : F.n = G.n := by
    have hF := Nat.card_range_of_injective F.strictMono.injective
    have hG := Nat.card_range_of_injective G.strictMono.injective
    rw [hrange, hG, Nat.card_fin, Nat.card_fin] at hF
    omega
  cases F with
  | mk n chain hmono _ _ _ _ =>
    cases G with
    | mk m chain' hmono' _ _ _ _ =>
      dsimp only at hn hrange
      subst hn
      have := (StrictMono.range_inj_of_wellFoundedLT hmono hmono').mp hrange
      subst this
      rfl

/-- **The first factor is vertical if and only if there is torsion**: some element above `⊥`
has the rank of `⊥`. -/
theorem factorPhase_zero_eq_top_iff (F : c.HNFiltration) (h0 : 0 < F.n) :
    F.factorPhase ⟨0, h0⟩ = ⊤ ↔ ∃ z, ⊥ < z ∧ c.rk z = c.rk ⊥ := by
  have hc : (⟨0, h0⟩ : Fin F.n).castSucc = 0 := rfl
  constructor
  · intro h
    have hlt := F.strictMono (⟨0, h0⟩ : Fin F.n).castSucc_lt_succ
    refine ⟨F.chain (⟨0, h0⟩ : Fin F.n).succ, ?_, ?_⟩
    · rwa [hc, F.chain_zero] at hlt
    · have := (c.phase_eq_top_iff).mp h
      rw [hc, F.chain_zero] at this
      exact this.symm
  · rintro ⟨z, hz, hr⟩
    by_contra hne
    obtain ⟨θ, hθ⟩ := WithTop.ne_top_iff_exists.mp hne
    have := F.weight_le 0 (fun i hi ↦ absurd hi (by simp))
      (fun i _ ↦ (F.phase_strictAnti.antitone
        (show (⟨0, h0⟩ : Fin F.n) ≤ i from Fin.le_def.mpr (Nat.zero_le _))).trans
          (le_of_eq hθ.symm)) z
    rw [F.chain_zero] at this
    simp only [weight, hr] at this
    rcases c.lex_lt hz with hd | hd
    · exact hd.ne' hr
    · linarith [hd.2]

/-- **Maps preserving the charge fix every prefix**, with no order condition: `⊥` is fixed
because `(rk, deg)` is injective on comparable pairs, and every other prefix is the unique
maximizer of a weight. -/
theorem apply_chain_eq (F : c.HNFiltration) {φ : L → L} (hrk : ∀ x, c.rk (φ x) = c.rk x)
    (hdeg : ∀ x, c.deg (φ x) = c.deg x) (k : Fin (F.n + 1)) : φ (F.chain k) = F.chain k := by
  rcases (F.mem_range_chain_iff (F.chain k)).mp ⟨k, rfl⟩ with h | ⟨θ, hθ⟩
  · rw [h]
    exact (c.eq_of_le_of_eq bot_le (hrk ⊥).symm (hdeg ⊥).symm).symm
  · exact (hθ _).2 (by simp only [weight, hrk, hdeg])

end OrderedField

/-! ### Building HN chains -/

/-- The HN chain of `[⊤, ⊤]`, with no factors. -/
def top : c.HNChain ⊤ where
  n := 0
  chain _ := ⊤
  strictMono i j h := by
    have := i.isLt; have := j.isLt; rw [Fin.lt_def] at h; omega
  chain_zero := rfl
  chain_last := rfl
  semistable i := i.elim0
  phase_strictAnti i := i.elim0

/-- Prepend a semistable `[a, t]` of phase larger than the first factor of an HN chain of
`[t, ⊤]`. -/
def cons {a t : L} (h : c.IsSemistable a t) (G : c.HNChain t)
    (hph : ∀ h0 : 0 < G.n, G.factorPhase ⟨0, h0⟩ < c.phase a t) : c.HNChain a where
  n := G.n + 1
  chain := Fin.cons a G.chain
  strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i ↦ ?_
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [G.chain_zero] using h.1
    · simpa [← Fin.succ_castSucc] using G.strictMono j.castSucc_lt_succ
  chain_zero := Fin.cons_zero _ _
  chain_last := by rw [← Fin.succ_last, Fin.cons_succ, G.chain_last]
  semistable i := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [G.chain_zero] using h
    · simpa [← Fin.succ_castSucc] using G.semistable j
  phase_strictAnti := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd hij (lt_irrefl _)
      | succ j =>
        have h0 : 0 < G.n := lt_of_le_of_lt (Nat.zero_le _) j.isLt
        have := (G.phase_strictAnti.antitone
          (show (⟨0, h0⟩ : Fin G.n) ≤ j from Fin.le_def.mpr (Nat.zero_le _))).trans_lt (hph h0)
        simpa [← Fin.succ_castSucc, G.chain_zero, factorPhase] using this
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j =>
        have := G.phase_strictAnti (Fin.succ_lt_succ_iff.mp hij)
        simpa [← Fin.succ_castSucc] using this

/-- **HN chains only depend on the order of phases.** An HN chain for `c` is one for every charge
function `c'` on `L` whose interval phases are ordered like those of `c`. -/
def ofPhaseOrder [IsStrictOrderedRing K] {K' : Type*} [Field K'] [LinearOrder K']
    [IsStrictOrderedRing K'] {c' : ChargeFunction L K'}
    (h : ∀ x y x' y' : L, x < y → x' < y' →
      (c.phase x y ≤ c.phase x' y' ↔ c'.phase x y ≤ c'.phase x' y'))
    (F : c.HNChain a) : c'.HNChain a where
  n := F.n
  chain := F.chain
  strictMono := F.strictMono
  chain_zero := F.chain_zero
  chain_last := F.chain_last
  semistable i := by
    have hlt := F.strictMono i.castSucc_lt_succ
    rw [c'.isSemistable_iff_phase hlt]
    intro z hz₁ hz₂
    exact (h _ _ _ _ hz₁ hlt).mp ((c.isSemistable_iff_phase hlt).mp (F.semistable i) z hz₁ hz₂)
  phase_strictAnti i j hij := by
    have := F.phase_strictAnti hij
    rw [← not_le] at this ⊢
    rwa [← h _ _ _ _ (F.strictMono (Fin.castSucc_lt_succ (i := i)))
      (F.strictMono (Fin.castSucc_lt_succ (i := j)))]

@[simp] lemma ofPhaseOrder_chain [IsStrictOrderedRing K] {K' : Type*} [Field K']
    [LinearOrder K'] [IsStrictOrderedRing K'] {c' : ChargeFunction L K'}
    (h : ∀ x y x' y' : L, x < y → x' < y' →
      (c.phase x y ≤ c.phase x' y' ↔ c'.phase x y ≤ c'.phase x' y'))
    (F : c.HNChain a) : (F.ofPhaseOrder h).chain = F.chain := rfl

end HNChain

/-! ### Existence -/

section Existence

variable (c) [IsStrictOrderedRing K]

/-- The maximal phase is attained on every interval `[a, ⊤]` with `a < ⊤`: some `z₀ > a` has
`phase a z ≤ phase a z₀` for every `z > a`. -/
def MaxPhaseAttained : Prop :=
  ∀ a : L, a < ⊤ → ∃ z₀, a < z₀ ∧ ∀ z, a < z → c.phase a z ≤ c.phase a z₀

/-- **The maximal destabilizer.** With the ascending chain condition and an attained maximal
phase, every `[a, ⊤]` with `a < ⊤` has a greatest `t > a` of maximal phase from `a`. The elements
of maximal phase are closed under `⊔`, and a maximal one exists by the ascending chain
condition. -/
theorem exists_maxDestabilizer [WellFoundedGT L] (hatt : c.MaxPhaseAttained) {a : L}
    (ha : a < ⊤) : ∃ t, a < t ∧ (∀ z, a < z → c.phase a z ≤ c.phase a t) ∧
      ∀ z, a < z → c.phase a z = c.phase a t → z ≤ t := by
  obtain ⟨z₀, hz₀, hmax'⟩ := hatt a ha
  let M : Set L := {z | a < z ∧ c.phase a z = c.phase a z₀}
  have hsup : ∀ z₁ ∈ M, ∀ z₂ ∈ M, z₁ ⊔ z₂ ∈ M := by
    rintro z₁ ⟨h₁, e₁⟩ z₂ ⟨h₂, e₂⟩
    have h₃ : a < z₁ ⊔ z₂ := h₁.trans_le le_sup_left
    have hinf : a ≤ z₁ ⊓ z₂ := le_inf h₁.le h₂.le
    refine ⟨h₃, le_antisymm (hmax' _ h₃) ?_⟩
    rcases eq_or_ne (c.phase a z₀) ⊤ with htop | hne
    · rw [htop] at e₁ e₂ ⊢
      rw [top_le_iff, c.phase_eq_top_iff]
      have r₁ := (c.phase_eq_top_iff).mp e₁
      have r₂ := (c.phase_eq_top_iff).mp e₂
      have := c.rk_sup_add_inf z₁ z₂
      have := c.rk_mono hinf
      have := c.rk_mono h₃.le
      linarith
    · obtain ⟨θ, hθ⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hθ] at e₁ e₂ hmax' ⊢
      rw [c.coe_le_phase_iff h₃]
      have w₁ := (c.coe_le_phase_iff h₁ θ).mp e₁.ge
      have w₂ := (c.coe_le_phase_iff h₂ θ).mp e₂.ge
      have w₃ : c.deg (z₁ ⊓ z₂) - θ * c.rk (z₁ ⊓ z₂) ≤ c.deg a - θ * c.rk a := by
        rcases hinf.lt_or_eq with hlt | heq
        · have := (c.phase_le_coe_iff hlt θ).mp (hmax' _ hlt)
          linarith
        · rw [← heq]
      have hw := c.weight_sup_add_inf θ z₁ z₂
      simp only [weight] at hw
      linarith
  obtain ⟨t, htM, htmax⟩ := (wellFounded_gt (α := L)).has_min M ⟨z₀, hz₀, rfl⟩
  refine ⟨t, htM.1, fun z hz ↦ htM.2 ▸ hmax' z hz, fun z hz hzt ↦ ?_⟩
  have hzM : z ∈ M := ⟨hz, hzt.trans htM.2⟩
  have hsupM := hsup t htM z hzM
  have : t = t ⊔ z := by
    by_contra hne
    exact htmax _ hsupM (lt_of_le_of_ne le_sup_left hne)
  exact this ▸ le_sup_right

/-- **Existence of HN chains** from the ascending chain condition and an attained maximal phase:
every `[a, ⊤]` has an HN chain. -/
theorem nonempty_hnChain [WellFoundedGT L] (hatt : c.MaxPhaseAttained) (a : L) :
    Nonempty (c.HNChain a) := by
  induction a using WellFoundedGT.induction with
  | _ a ih =>
    rcases eq_or_ne a ⊤ with rfl | ha
    · exact ⟨HNChain.top⟩
    obtain ⟨t, hat, hmax, hgreat⟩ := c.exists_maxDestabilizer hatt (lt_top_iff_ne_top.mpr ha)
    obtain ⟨G⟩ := ih t hat
    have hss : c.IsSemistable a t :=
      (c.isSemistable_iff_phase hat).mpr fun z hz _ ↦ hmax z hz
    refine ⟨HNChain.cons hss G fun h0 ↦ ?_⟩
    have hlt := G.strictMono (⟨0, h0⟩ : Fin G.n).castSucc_lt_succ
    rw [show (⟨0, h0⟩ : Fin G.n).castSucc = 0 from rfl, G.chain_zero] at hlt
    have hne : c.phase a (G.chain (⟨0, h0⟩ : Fin G.n).succ) ≠ c.phase a t := fun e ↦
      not_le_of_gt hlt (hgreat _ (hat.trans hlt) e)
    have := c.phase_lt_of_seesaw hat hlt (lt_of_le_of_ne (hmax _ (hat.trans hlt)) hne)
    simpa [HNChain.factorPhase, G.chain_zero] using this

/-- **Existence and uniqueness of the HN filtration** from the ascending chain condition and an
attained maximal phase. Uniqueness is `HNChain.instSubsingleton`. -/
theorem nonempty_hnFiltration [WellFoundedGT L] (hatt : c.MaxPhaseAttained) :
    Nonempty c.HNFiltration :=
  c.nonempty_hnChain hatt ⊥

/-! ### Existence for a charge with finitely many values -/

omit [BoundedOrder L] [IsStrictOrderedRing K] in
/-- Finitely many charge values bound the length of every chain: a strictly monotone
`Fin m → L` has `m` at most the number of values of `(rk, deg)`. -/
theorem card_le_of_finite_range (hfin : (Set.range fun x ↦ (c.rk x, c.deg x)).Finite) {m : ℕ}
    (f : Fin m → L) (hf : StrictMono f) : m ≤ hfin.toFinset.card := by
  have hinj : Function.Injective fun i ↦ (c.rk (f i), c.deg (f i)) := by
    intro i j hij
    by_contra hne
    have key : ∀ {i j : Fin m}, i < j → (c.rk (f i), c.deg (f i)) ≠ (c.rk (f j), c.deg (f j)) :=
      fun h e ↦ (c.strictMono_toLex (hf h)).ne (congrArg toLex e)
    rcases lt_or_gt_of_ne hne with h | h
    · exact key h hij
    · exact key h hij.symm
  have := Finset.card_le_card_of_injOn (fun i ↦ (c.rk (f i), c.deg (f i)))
    (s := (Finset.univ : Finset (Fin m))) (t := hfin.toFinset)
    (fun i _ ↦ by simp; exact ⟨f i, rfl, rfl⟩) hinj.injOn
  simpa using this

omit [BoundedOrder L] [IsStrictOrderedRing K] in
/-- Finitely many charge values give the ascending chain condition. -/
theorem wellFoundedGT_of_finite_range (hfin : (Set.range fun x ↦ (c.rk x, c.deg x)).Finite) :
    WellFoundedGT L := by
  let S : Set (Lex (K × K)) := Set.range fun x ↦ toLex (c.rk x, c.deg x)
  have hS : S.Finite := by
    have : S = toLex '' Set.range fun x ↦ (c.rk x, c.deg x) := Set.range_comp _ _
    rw [this]
    exact hfin.image _
  have : Finite S := hS.to_subtype
  let g : L → S := fun x ↦ ⟨toLex (c.rk x, c.deg x), x, rfl⟩
  have hg : StrictMono g := fun x y h ↦ by
    show toLex (c.rk x, c.deg x) < toLex (c.rk y, c.deg y)
    exact c.strictMono_toLex h
  exact hg.wellFoundedGT

omit [IsStrictOrderedRing K] in
/-- Finitely many charge values give an attained maximal phase. -/
theorem maxPhaseAttained_of_finite_range
    (hfin : (Set.range fun x ↦ (c.rk x, c.deg x)).Finite) : c.MaxPhaseAttained := by
  intro a ha
  let P : Set (K × K) := (fun x ↦ (c.rk x, c.deg x)) '' {z | a < z}
  have hP : P.Finite := hfin.subset (Set.image_subset_range _ _)
  let g : K × K → WithTop K := fun p ↦
    if p.1 - c.rk a = 0 then ⊤ else (((p.2 - c.deg a) / (p.1 - c.rk a) : K) : WithTop K)
  obtain ⟨_, ⟨z₀, hz₀, rfl⟩, hmax⟩ := Set.exists_max_image P g hP ⟨_, ⟨⊤, ha, rfl⟩⟩
  exact ⟨z₀, hz₀, fun z hz ↦ hmax _ ⟨z, hz, rfl⟩⟩

/-- **Existence of HN chains for finitely many charge values.** By `card_le_of_finite_range` the
hypothesis bounds the length of chains in `L`; `nonempty_hnChain` covers lattices of infinite
length. -/
theorem nonempty_hnChain_of_finite_range
    (hfin : (Set.range fun x ↦ (c.rk x, c.deg x)).Finite) (a : L) : Nonempty (c.HNChain a) :=
  have := c.wellFoundedGT_of_finite_range hfin
  c.nonempty_hnChain (c.maxPhaseAttained_of_finite_range hfin) a

/-- **Existence of the HN filtration for finitely many charge values**, a statement about
lattices of finite length (`card_le_of_finite_range`). -/
theorem nonempty_hnFiltration_of_finite_range
    (hfin : (Set.range fun x ↦ (c.rk x, c.deg x)).Finite) : Nonempty c.HNFiltration :=
  c.nonempty_hnChain_of_finite_range hfin ⊥

end Existence

end ChargeFunction

/-! ### Slope functions -/

/-- A slope function on a lattice: a strictly monotone rank and a degree, both valuations. This
is a charge function with no vertical steps (`SlopeFunction.toChargeFunction`). -/
structure SlopeFunction where
  /-- The rank, a strictly monotone valuation. -/
  rk : L → K
  /-- The degree, a valuation. -/
  deg : L → K
  rk_strictMono : StrictMono rk
  rk_sup_add_inf (x y : L) : rk (x ⊔ y) + rk (x ⊓ y) = rk x + rk y
  deg_sup_add_inf (x y : L) : deg (x ⊔ y) + deg (x ⊓ y) = deg x + deg y

namespace SlopeFunction

variable {L K} (s : SlopeFunction L K)

/-- A slope function is a charge function with no vertical steps. -/
def toChargeFunction : ChargeFunction L K where
  rk := s.rk
  deg := s.deg
  lex_lt h := Or.inl (s.rk_strictMono h)
  rk_sup_add_inf := s.rk_sup_add_inf
  deg_sup_add_inf := s.deg_sup_add_inf

@[simp] lemma toChargeFunction_rk : s.toChargeFunction.rk = s.rk := rfl

@[simp] lemma toChargeFunction_deg : s.toChargeFunction.deg = s.deg := rfl

/-- The weight of slope `θ`, `w_θ x = deg x - θ rk x`. -/
def weight (θ : K) (x : L) : K := s.deg x - θ * s.rk x

@[simp] lemma toChargeFunction_weight : s.toChargeFunction.weight = s.weight := rfl

/-- The slope `(deg y - deg x) / (rk y - rk x)` of the interval from `x` to `y`. -/
def slope (x y : L) : K := (s.deg y - s.deg x) / (s.rk y - s.rk x)

/-- The opposite slope function, with degree `-deg`: the slope order is reversed. -/
def neg : SlopeFunction L K where
  rk := s.rk
  deg x := -s.deg x
  rk_strictMono := s.rk_strictMono
  rk_sup_add_inf := s.rk_sup_add_inf
  deg_sup_add_inf x y := by linear_combination -s.deg_sup_add_inf x y

@[simp] lemma neg_rk : s.neg.rk = s.rk := rfl

@[simp] lemma neg_deg (x : L) : s.neg.deg x = -s.deg x := rfl

lemma neg_weight (θ : K) (x : L) : s.neg.weight θ x = -s.weight (-θ) x := by
  simp only [weight, neg_rk, neg_deg]
  ring

lemma weight_sup_add_inf (θ : K) (x y : L) :
    s.weight θ (x ⊔ y) + s.weight θ (x ⊓ y) = s.weight θ x + s.weight θ y :=
  s.toChargeFunction.weight_sup_add_inf θ x y

/-- The weight of the slope of `[x, y]` takes the same value at `x` and `y`. -/
lemma weight_slope_eq {x y : L} (h : x < y) :
    s.weight (s.slope x y) y = s.weight (s.slope x y) x := by
  have : s.rk y - s.rk x ≠ 0 := sub_ne_zero.mpr (s.rk_strictMono h).ne'
  simp only [weight, slope]
  field_simp
  ring

/-- `[x, y]` is semistable: `x < y`, and every `z` with `x ≤ z ≤ y` has `w_μ z ≤ w_μ x` for the
slope `μ` of `[x, y]`; that is, `slope x z ≤ μ` when `x < z` (`isSemistable_iff`). -/
def IsSemistable (x y : L) : Prop :=
  x < y ∧ ∀ z, x ≤ z → z ≤ y → s.weight (s.slope x y) z ≤ s.weight (s.slope x y) x

/-- `[x, y]` is stable: `x < y`, and every `z` with `x < z < y` has `w_μ z < w_μ x`, that is
`slope x z < slope x y`. -/
def IsStable (x y : L) : Prop :=
  x < y ∧ ∀ z, x < z → z < y → s.weight (s.slope x y) z < s.weight (s.slope x y) x

variable {s} in
lemma IsStable.isSemistable {x y : L} (h : s.IsStable x y) : s.IsSemistable x y := by
  refine ⟨h.1, fun z hxz hzy ↦ ?_⟩
  rcases hxz.eq_or_lt with rfl | hxz
  · exact le_rfl
  rcases hzy.eq_or_lt with rfl | hzy
  · exact (s.weight_slope_eq h.1).le
  · exact (h.2 z hxz hzy).le

/-- An interval with nothing strictly inside is stable. -/
lemma isStable_of_forall {x y : L} (h : x < y) (H : ∀ z, x < z → z < y → False) :
    s.IsStable x y :=
  ⟨h, fun z hxz hzy ↦ (H z hxz hzy).elim⟩

section OrderedField

variable [IsStrictOrderedRing K]

/-- The phase of an interval of a slope function is its slope. -/
lemma toChargeFunction_phase {x y : L} (h : x < y) :
    s.toChargeFunction.phase x y = (s.slope x y : WithTop K) := by
  rw [ChargeFunction.phase, toChargeFunction_rk, toChargeFunction_deg,
    ite_eq_right (sub_pos.mpr (s.rk_strictMono h)).ne']
  rfl

/-- `w_θ z ≤ w_θ x` for `x < z` means `slope x z ≤ θ`. -/
lemma weight_le_iff_slope_le {x z : L} (h : x < z) (θ : K) :
    s.weight θ z ≤ s.weight θ x ↔ s.slope x z ≤ θ := by
  have hpos : 0 < s.rk z - s.rk x := sub_pos.mpr (s.rk_strictMono h)
  rw [slope, div_le_iff₀ hpos, weight, weight]
  constructor <;> intro h' <;> linarith

/-- The slope form of semistability. -/
lemma isSemistable_iff {x y : L} (h : x < y) :
    s.IsSemistable x y ↔ ∀ z, x < z → z ≤ y → s.slope x z ≤ s.slope x y := by
  refine ⟨fun hs z hxz hzy ↦ (s.weight_le_iff_slope_le hxz _).mp (hs.2 z hxz.le hzy),
    fun H ↦ ⟨h, fun z hxz hzy ↦ ?_⟩⟩
  rcases hxz.eq_or_lt with rfl | hxz
  · exact le_rfl
  · exact (s.weight_le_iff_slope_le hxz _).mpr (H z hxz hzy)

/-- Division-free form of the weight inequality: for `x < y` with slope `μ`,
`w_μ z ≤ w_μ x` means `(deg z - deg x)(rk y - rk x) ≤ (deg y - deg x)(rk z - rk x)`. -/
lemma weight_slope_le_iff {x y : L} (h : x < y) (z : L) :
    s.weight (s.slope x y) z ≤ s.weight (s.slope x y) x ↔
      (s.deg z - s.deg x) * (s.rk y - s.rk x) ≤ (s.deg y - s.deg x) * (s.rk z - s.rk x) := by
  have hpos : 0 < s.rk y - s.rk x := sub_pos.mpr (s.rk_strictMono h)
  have key : (s.weight (s.slope x y) x - s.weight (s.slope x y) z) * (s.rk y - s.rk x) =
      (s.deg y - s.deg x) * (s.rk z - s.rk x) - (s.deg z - s.deg x) * (s.rk y - s.rk x) := by
    simp only [weight, slope]
    field_simp
    ring
  rw [← sub_nonneg, ← mul_nonneg_iff_of_pos_right hpos, key, sub_nonneg]

/-- The strict form of `weight_slope_le_iff`. -/
lemma weight_slope_lt_iff {x y : L} (h : x < y) (z : L) :
    s.weight (s.slope x y) z < s.weight (s.slope x y) x ↔
      (s.deg z - s.deg x) * (s.rk y - s.rk x) < (s.deg y - s.deg x) * (s.rk z - s.rk x) := by
  have hpos : 0 < s.rk y - s.rk x := sub_pos.mpr (s.rk_strictMono h)
  have key : (s.weight (s.slope x y) x - s.weight (s.slope x y) z) * (s.rk y - s.rk x) =
      (s.deg y - s.deg x) * (s.rk z - s.rk x) - (s.deg z - s.deg x) * (s.rk y - s.rk x) := by
    simp only [weight, slope]
    field_simp
    ring
  rw [← sub_pos, ← mul_pos_iff_of_pos_right hpos, key, sub_pos]

/-- Semistability of a slope function is semistability of its charge function. -/
lemma toChargeFunction_isSemistable_iff {x y : L} :
    s.toChargeFunction.IsSemistable x y ↔ s.IsSemistable x y := by
  refine ⟨fun h ↦ ⟨h.1, fun z h1 h2 ↦ (s.weight_slope_le_iff h.1 z).mpr (h.2 z h1 h2)⟩,
    fun h ↦ ⟨h.1, fun z h1 h2 ↦ (s.weight_slope_le_iff h.1 z).mp (h.2 z h1 h2)⟩⟩

/-! ### Weights on a semistable interval -/

variable {s} {x y z : L} {θ : K}

/-- On a semistable `[x, y]` of slope at most `θ`, the bottom `x` maximizes `w_θ`. -/
lemma IsSemistable.weight_le_bot (h : s.IsSemistable x y) (hθ : s.slope x y ≤ θ) (hxz : x ≤ z)
    (hzy : z ≤ y) : s.weight θ z ≤ s.weight θ x :=
  (s.toChargeFunction_isSemistable_iff.mpr h).weight_le_bot
    (by rw [s.toChargeFunction_phase h.1]; exact_mod_cast hθ) hxz hzy

/-- On a semistable `[x, y]` of slope less than `θ`, the bottom `x` is the only maximizer
of `w_θ`. -/
lemma IsSemistable.eq_bot_of_weight_eq (h : s.IsSemistable x y) (hθ : s.slope x y < θ)
    (hxz : x ≤ z) (hzy : z ≤ y) (heq : s.weight θ z = s.weight θ x) : z = x :=
  (s.toChargeFunction_isSemistable_iff.mpr h).eq_bot_of_weight_eq
    (by rw [s.toChargeFunction_phase h.1]; exact_mod_cast hθ) hxz hzy heq

/-- On a semistable `[x, y]` of slope at least `θ`, the top `y` maximizes `w_θ`. -/
lemma IsSemistable.weight_le_top (h : s.IsSemistable x y) (hθ : θ ≤ s.slope x y) (hxz : x ≤ z)
    (hzy : z ≤ y) : s.weight θ z ≤ s.weight θ y :=
  (s.toChargeFunction_isSemistable_iff.mpr h).weight_le_top
    (by rw [s.toChargeFunction_phase h.1]; exact_mod_cast hθ) hxz hzy

/-- On a semistable `[x, y]` of slope greater than `θ`, the top `y` is the only maximizer
of `w_θ`. -/
lemma IsSemistable.eq_top_of_weight_eq (h : s.IsSemistable x y) (hθ : θ < s.slope x y)
    (hxz : x ≤ z) (hzy : z ≤ y) (heq : s.weight θ z = s.weight θ y) : z = y :=
  (s.toChargeFunction_isSemistable_iff.mpr h).eq_top_of_weight_eq
    (by rw [s.toChargeFunction_phase h.1]; exact_mod_cast hθ) hxz hzy heq

/-! ### One step along a chain -/

variable {c d : L}

/-- If `c ≤ d` and `c` maximizes `w_θ` on `[c, d]`, then `w_θ (y ⊓ d) ≤ w_θ (y ⊓ c)`. -/
lemma weight_inf_le (hcd : c ≤ d) (H : ∀ z, c ≤ z → z ≤ d → s.weight θ z ≤ s.weight θ c)
    (y : L) : s.weight θ (y ⊓ d) ≤ s.weight θ (y ⊓ c) :=
  val_inf_le (s.weight_sup_add_inf θ) hcd H y

/-- If `c ≤ d` and `c` is the only maximizer of `w_θ` on `[c, d]`, then
`w_θ (y ⊓ d) = w_θ (y ⊓ c)` forces `y ⊓ d = y ⊓ c`. -/
lemma inf_eq_of_weight_eq (hcd : c ≤ d)
    (H : ∀ z, c ≤ z → z ≤ d → s.weight θ z = s.weight θ c → z = c) {y : L}
    (heq : s.weight θ (y ⊓ d) = s.weight θ (y ⊓ c)) : y ⊓ d = y ⊓ c :=
  inf_eq_of_val_eq (s.weight_sup_add_inf θ) hcd H heq

/-- If `c ≤ d` and `d` maximizes `w_θ` on `[c, d]`, then `w_θ (y ⊔ c) ≤ w_θ (y ⊔ d)`. -/
lemma weight_sup_le (hcd : c ≤ d) (H : ∀ z, c ≤ z → z ≤ d → s.weight θ z ≤ s.weight θ d)
    (y : L) : s.weight θ (y ⊔ c) ≤ s.weight θ (y ⊔ d) :=
  val_sup_le (s.weight_sup_add_inf θ) hcd H y

/-- If `c ≤ d` and `d` is the only maximizer of `w_θ` on `[c, d]`, then
`w_θ (y ⊔ c) = w_θ (y ⊔ d)` forces `y ⊔ c = y ⊔ d`. -/
lemma sup_eq_of_weight_eq (hcd : c ≤ d)
    (H : ∀ z, c ≤ z → z ≤ d → s.weight θ z = s.weight θ d → z = d) {y : L}
    (heq : s.weight θ (y ⊔ c) = s.weight θ (y ⊔ d)) : y ⊔ c = y ⊔ d :=
  sup_eq_of_val_eq (s.weight_sup_add_inf θ) hcd H heq

end OrderedField

/-! ### Harder–Narasimhan filtrations -/

variable [BoundedOrder L]

/-- A Harder–Narasimhan filtration of the slope function `s`: a chain
`⊥ = chain 0 < ⋯ < chain n = ⊤` whose factors are semistable with strictly decreasing slopes.
It is an HN filtration of `s.toChargeFunction` (`HNFiltration.toCharge`, `HNFiltration.ofCharge`)
with the factor phases in `K`. -/
structure HNFiltration where
  /-- The number of factors. -/
  n : ℕ
  /-- The chain of prefixes. -/
  chain : Fin (n + 1) → L
  strictMono : StrictMono chain
  chain_zero : chain 0 = ⊥
  chain_last : chain (Fin.last n) = ⊤
  semistable : ∀ i : Fin n, s.IsSemistable (chain i.castSucc) (chain i.succ)
  slope_strictAnti : StrictAnti fun i : Fin n ↦ s.slope (chain i.castSucc) (chain i.succ)

variable {s} in
/-- A semistable lattice is its own HN filtration, `⊥ < ⊤`. -/
def HNFiltration.ofSemistable (h : s.IsSemistable ⊥ ⊤) : s.HNFiltration where
  n := 1
  chain := ![⊥, ⊤]
  strictMono := Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
    fin_cases i
    exact h.1
  chain_zero := rfl
  chain_last := rfl
  semistable i := by
    fin_cases i
    exact h
  slope_strictAnti := Fin.strictAnti_iff_succ_lt.mpr fun i ↦ i.elim0

variable {s} in
/-- The two-step HN filtration `⊥ < x < ⊤`, from semistable factors of decreasing slopes. -/
def HNFiltration.two {x : L} (h₁ : s.IsSemistable ⊥ x) (h₂ : s.IsSemistable x ⊤)
    (h : s.slope x ⊤ < s.slope ⊥ x) : s.HNFiltration where
  n := 2
  chain := ![⊥, x, ⊤]
  strictMono := Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
    fin_cases i
    exacts [h₁.1, h₂.1]
  chain_zero := rfl
  chain_last := rfl
  semistable i := by
    fin_cases i
    exacts [h₁, h₂]
  slope_strictAnti := Fin.strictAnti_iff_succ_lt.mpr fun i ↦ by
    fin_cases i
    exact h

namespace HNFiltration

variable {s} (F : s.HNFiltration)

/-- The slope of the `i`th factor `[chain i, chain (i + 1)]`. -/
def factorSlope (i : Fin F.n) : K := s.slope (F.chain i.castSucc) (F.chain i.succ)

/-- The weight of the slope of a factor takes the same value at both of its ends. -/
lemma weight_factorSlope_succ (i : Fin F.n) :
    s.weight (F.factorSlope i) (F.chain i.succ) =
      s.weight (F.factorSlope i) (F.chain i.castSucc) :=
  s.weight_slope_eq (F.strictMono i.castSucc_lt_succ)

/-- The chain extended to `ℕ`, constant `⊤` after `n`. -/
def c (j : ℕ) : L := F.chain ⟨min j F.n, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma c_of_le {j : ℕ} (hj : j ≤ F.n) : F.c j = F.chain ⟨j, Nat.lt_succ_of_le hj⟩ := by
  simp only [c, min_eq_left hj]

lemma c_fin (k : Fin (F.n + 1)) : F.c k = F.chain k := by
  rw [F.c_of_le (Nat.le_of_lt_succ k.isLt)]

@[simp] lemma c_zero : F.c 0 = ⊥ := by
  rw [F.c_of_le (Nat.zero_le _)]
  exact F.chain_zero

lemma c_n : F.c F.n = ⊤ := by
  rw [F.c_of_le le_rfl]
  exact F.chain_last

lemma c_mono : Monotone F.c := fun _ _ h ↦
  F.strictMono.monotone (Fin.mk_le_mk.mpr (min_le_min_right _ h))

lemma c_succ_of_le {j : ℕ} (hj : F.n ≤ j) : F.c (j + 1) = F.c j := by
  simp only [c, min_eq_right hj, min_eq_right (hj.trans (Nat.le_succ j))]

lemma c_isSemistable {j : ℕ} (hj : j < F.n) : s.IsSemistable (F.c j) (F.c (j + 1)) := by
  rw [F.c_of_le hj.le, F.c_of_le hj]
  exact F.semistable ⟨j, hj⟩

lemma slope_c {j : ℕ} (hj : j < F.n) :
    s.slope (F.c j) (F.c (j + 1)) = F.factorSlope ⟨j, hj⟩ := by
  rw [F.c_of_le hj.le, F.c_of_le hj]
  rfl

section OrderedField

variable [IsStrictOrderedRing K] {θ : K}

/-- An HN filtration of a slope function is one of its charge function. -/
def toCharge : s.toChargeFunction.HNFiltration where
  n := F.n
  chain := F.chain
  strictMono := F.strictMono
  chain_zero := F.chain_zero
  chain_last := F.chain_last
  semistable i := s.toChargeFunction_isSemistable_iff.mpr (F.semistable i)
  phase_strictAnti i j hij := by
    simp only [s.toChargeFunction_phase (F.strictMono (Fin.castSucc_lt_succ (i := i))),
      s.toChargeFunction_phase (F.strictMono (Fin.castSucc_lt_succ (i := j))),
      WithTop.coe_lt_coe]
    exact F.slope_strictAnti hij

@[simp] lemma toCharge_n : F.toCharge.n = F.n := rfl

@[simp] lemma toCharge_chain : F.toCharge.chain = F.chain := rfl

lemma toCharge_factorPhase (i : Fin F.toCharge.n) :
    F.toCharge.factorPhase i = (F.factorSlope i : WithTop K) :=
  s.toChargeFunction_phase (F.strictMono i.castSucc_lt_succ)

/-- An HN filtration of the charge function of a slope function is one of the slope function. -/
def ofCharge (G : s.toChargeFunction.HNFiltration) : s.HNFiltration where
  n := G.n
  chain := G.chain
  strictMono := G.strictMono
  chain_zero := G.chain_zero
  chain_last := G.chain_last
  semistable i := s.toChargeFunction_isSemistable_iff.mp (G.semistable i)
  slope_strictAnti i j hij := by
    have := G.phase_strictAnti hij
    simp only [s.toChargeFunction_phase (G.strictMono (Fin.castSucc_lt_succ (i := i))),
      s.toChargeFunction_phase (G.strictMono (Fin.castSucc_lt_succ (i := j))),
      WithTop.coe_lt_coe] at this
    exact this

/-- HN filtrations of a slope function and of its charge function are the same. -/
def equivCharge : s.HNFiltration ≃ s.toChargeFunction.HNFiltration where
  toFun F := F.toCharge
  invFun G := ofCharge G
  left_inv _ := rfl
  right_inv _ := rfl

/-- A factor of slope at most `θ` has its bottom as a maximizer of `w_θ`. -/
lemma weight_le_c_bot {j : ℕ} (hj : j < F.n) (hθ : F.factorSlope ⟨j, hj⟩ ≤ θ) {z : L}
    (h1 : F.c j ≤ z) (h2 : z ≤ F.c (j + 1)) : s.weight θ z ≤ s.weight θ (F.c j) :=
  (F.c_isSemistable hj).weight_le_bot (by rw [F.slope_c hj]; exact hθ) h1 h2

/-- A factor of slope less than `θ` has its bottom as the only maximizer of `w_θ`. -/
lemma eq_c_bot {j : ℕ} (hj : j < F.n) (hθ : F.factorSlope ⟨j, hj⟩ < θ) {z : L}
    (h1 : F.c j ≤ z) (h2 : z ≤ F.c (j + 1)) (heq : s.weight θ z = s.weight θ (F.c j)) :
    z = F.c j :=
  (F.c_isSemistable hj).eq_bot_of_weight_eq (by rw [F.slope_c hj]; exact hθ) h1 h2 heq

/-- A factor of slope at least `θ` has its top as a maximizer of `w_θ`. -/
lemma weight_le_c_top {j : ℕ} (hj : j < F.n) (hθ : θ ≤ F.factorSlope ⟨j, hj⟩) {z : L}
    (h1 : F.c j ≤ z) (h2 : z ≤ F.c (j + 1)) : s.weight θ z ≤ s.weight θ (F.c (j + 1)) :=
  (F.c_isSemistable hj).weight_le_top (by rw [F.slope_c hj]; exact hθ) h1 h2

/-- A factor of slope greater than `θ` has its top as the only maximizer of `w_θ`. -/
lemma eq_c_top {j : ℕ} (hj : j < F.n) (hθ : θ < F.factorSlope ⟨j, hj⟩) {z : L}
    (h1 : F.c j ≤ z) (h2 : z ≤ F.c (j + 1)) (heq : s.weight θ z = s.weight θ (F.c (j + 1))) :
    z = F.c (j + 1) :=
  (F.c_isSemistable hj).eq_top_of_weight_eq (by rw [F.slope_c hj]; exact hθ) h1 h2 heq

/-- Going up from `c a` through factors of slope at most `θ`:
`w_θ (y ⊓ c (a + m)) ≤ w_θ (y ⊓ c a)`. A case of `val_inf_le_of_chain`. -/
lemma weight_inf_c_le {a : ℕ} (hθ : ∀ j (hj : j < F.n), a ≤ j → F.factorSlope ⟨j, hj⟩ ≤ θ)
    (y : L) (m : ℕ) : s.weight θ (y ⊓ F.c (a + m)) ≤ s.weight θ (y ⊓ F.c a) := by
  refine val_inf_le_of_chain (s.weight_sup_add_inf θ) F.c_mono (fun j ha z h1 h2 ↦ ?_) y m
  by_cases hj : j < F.n
  · exact F.weight_le_c_bot hj (hθ j hj ha) h1 h2
  · rw [le_antisymm (F.c_succ_of_le (not_lt.mp hj) ▸ h2) h1]

/-- Going up through factors of slope less than `θ`, equality of weights forces
`y ⊓ c (a + m) = y ⊓ c a`. A case of `inf_eq_of_val_eq_of_chain`. -/
lemma inf_c_eq {a : ℕ} (hθ : ∀ j (hj : j < F.n), a ≤ j → F.factorSlope ⟨j, hj⟩ < θ)
    (y : L) (m : ℕ) (heq : s.weight θ (y ⊓ F.c (a + m)) = s.weight θ (y ⊓ F.c a)) :
    y ⊓ F.c (a + m) = y ⊓ F.c a := by
  refine inf_eq_of_val_eq_of_chain (s.weight_sup_add_inf θ) F.c_mono (fun j ha z h1 h2 ↦ ?_)
    (fun j ha z h1 h2 h3 ↦ ?_) y m heq
  · by_cases hj : j < F.n
    · exact F.weight_le_c_bot hj (hθ j hj ha).le h1 h2
    · rw [le_antisymm (F.c_succ_of_le (not_lt.mp hj) ▸ h2) h1]
  · by_cases hj : j < F.n
    · exact F.eq_c_bot hj (hθ j hj ha) h1 h2 h3
    · exact le_antisymm (F.c_succ_of_le (not_lt.mp hj) ▸ h2) h1

/-- Going down to `c j` from `c a = c (j + d)` through factors of slope at least `θ`:
`w_θ (y ⊔ c j) ≤ w_θ (y ⊔ c a)`. A case of `val_sup_le_of_chain`. -/
lemma weight_sup_c_le {a : ℕ} (hθ : ∀ j (hj : j < F.n), j + 1 ≤ a → θ ≤ F.factorSlope ⟨j, hj⟩)
    (ha : a ≤ F.n) (y : L) (d j : ℕ) (h : j + d = a) :
    s.weight θ (y ⊔ F.c j) ≤ s.weight θ (y ⊔ F.c a) :=
  val_sup_le_of_chain (s.weight_sup_add_inf θ) F.c_mono
    (fun j hj z h1 h2 ↦ F.weight_le_c_top (by omega) (hθ j (by omega) hj) h1 h2) y j (by omega)

/-- Going down through factors of slope greater than `θ`, equality of weights forces
`y ⊔ c j = y ⊔ c a`. A case of `sup_eq_of_val_eq_of_chain`. -/
lemma sup_c_eq {a : ℕ} (hθ : ∀ j (hj : j < F.n), j + 1 ≤ a → θ < F.factorSlope ⟨j, hj⟩)
    (ha : a ≤ F.n) (y : L) (d j : ℕ) (h : j + d = a)
    (heq : s.weight θ (y ⊔ F.c j) = s.weight θ (y ⊔ F.c a)) : y ⊔ F.c j = y ⊔ F.c a :=
  sup_eq_of_val_eq_of_chain (s.weight_sup_add_inf θ) F.c_mono
    (fun j hj z h1 h2 ↦ F.weight_le_c_top (by omega) (hθ j (by omega) hj).le h1 h2)
    (fun j hj z h1 h2 h3 ↦ F.eq_c_top (by omega) (hθ j (by omega) hj) h1 h2 h3) y j (by omega)
    heq

/-- **The prefixes maximize the weights.** If the factors below `chain k` have slopes at least
`θ` and those above have slopes at most `θ`, then `chain k` maximizes `w_θ` over `L`. -/
theorem weight_le (k : Fin (F.n + 1)) (h₁ : ∀ i : Fin F.n, i.succ ≤ k → θ ≤ F.factorSlope i)
    (h₂ : ∀ i : Fin F.n, k ≤ i.castSucc → F.factorSlope i ≤ θ) (x : L) :
    s.weight θ x ≤ s.weight θ (F.chain k) :=
  F.toCharge.weight_le k
    (fun i hi ↦ by rw [F.toCharge_factorPhase]; exact_mod_cast h₁ i hi)
    (fun i hi ↦ by rw [F.toCharge_factorPhase]; exact_mod_cast h₂ i hi) x

/-- **The prefixes are the only maximizers.** If the factors below `chain k` have slopes greater
than `θ` and those above have slopes less than `θ`, then `chain k` is the only maximizer
of `w_θ`. -/
theorem eq_of_weight_eq (k : Fin (F.n + 1))
    (h₁ : ∀ i : Fin F.n, i.succ ≤ k → θ < F.factorSlope i)
    (h₂ : ∀ i : Fin F.n, k ≤ i.castSucc → F.factorSlope i < θ) {x : L}
    (hx : s.weight θ x = s.weight θ (F.chain k)) : x = F.chain k :=
  F.toCharge.eq_of_weight_eq k
    (fun i hi ↦ by rw [F.toCharge_factorPhase]; exact_mod_cast h₁ i hi)
    (fun i hi ↦ by rw [F.toCharge_factorPhase]; exact_mod_cast h₂ i hi) hx

omit [IsStrictOrderedRing K] in
/-- Every `θ` lies between the slopes around some prefix. -/
lemma exists_index (θ : K) : ∃ k : Fin (F.n + 1),
    (∀ i : Fin F.n, i.succ ≤ k → θ ≤ F.factorSlope i) ∧
      ∀ i : Fin F.n, k ≤ i.castSucc → F.factorSlope i ≤ θ := by
  classical
  have hP : ∃ j, j = F.n ∨ ∃ hj : j < F.n, F.factorSlope ⟨j, hj⟩ ≤ θ := ⟨F.n, Or.inl rfl⟩
  have hkn : Nat.find hP ≤ F.n := Nat.find_min' hP (Or.inl rfl)
  refine ⟨⟨Nat.find hP, Nat.lt_succ_of_le hkn⟩, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · have hlt : (i : ℕ) < Nat.find hP := by simpa [Fin.le_def] using hi
    have := Nat.find_min hP hlt
    simp only [not_or, not_exists, not_le] at this
    exact (this.2 i.isLt).le
  · have hle : Nat.find hP ≤ (i : ℕ) := by simpa [Fin.le_def] using hi
    rcases Nat.find_spec hP with h | ⟨hj, hθ⟩
    · omega
    · exact (F.slope_strictAnti.antitone (Fin.mk_le_mk.mpr hle)).trans hθ

omit [Lattice L] [BoundedOrder L] in
private lemma exists_between_finset {A B : Finset K} (h : ∀ a ∈ A, ∀ b ∈ B, b < a) :
    ∃ θ : K, (∀ a ∈ A, θ < a) ∧ ∀ b ∈ B, b < θ := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rcases B.eq_empty_or_nonempty with rfl | hB
    · exact ⟨0, by simp, by simp⟩
    · exact ⟨B.max' hB + 1, by simp, fun b hb ↦ (B.le_max' b hb).trans_lt (lt_add_one _)⟩
  · rcases B.eq_empty_or_nonempty with rfl | hB
    · exact ⟨A.min' hA - 1, fun a ha ↦ (sub_one_lt _).trans_le (A.min'_le a ha), by simp⟩
    · obtain ⟨θ, h1, h2⟩ := exists_between (h _ (A.min'_mem hA) _ (B.max'_mem hB))
      exact ⟨θ, fun a ha ↦ h2.trans_le (A.min'_le a ha), fun b hb ↦ (B.le_max' b hb).trans_lt h1⟩

/-- Every prefix lies strictly between the slopes around it for some `θ`. -/
lemma exists_slope_between (k : Fin (F.n + 1)) : ∃ θ : K,
    (∀ i : Fin F.n, i.succ ≤ k → θ < F.factorSlope i) ∧
      ∀ i : Fin F.n, k ≤ i.castSucc → F.factorSlope i < θ := by
  classical
  obtain ⟨θ, h1, h2⟩ := exists_between_finset
    (A := (Finset.univ.filter fun i : Fin F.n ↦ i.succ ≤ k).image F.factorSlope)
    (B := (Finset.univ.filter fun i : Fin F.n ↦ k ≤ i.castSucc).image F.factorSlope) (by
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro _ ⟨i, hi, rfl⟩ _ ⟨i', hi', rfl⟩
      refine F.slope_strictAnti ?_
      rw [Fin.lt_def]
      rw [Fin.le_def] at hi hi'
      simp only [Fin.val_succ, Fin.val_castSucc] at hi hi'
      omega)
  exact ⟨θ, fun i hi ↦ h1 _ (Finset.mem_image_of_mem _ (by simpa using hi)),
    fun i hi ↦ h2 _ (Finset.mem_image_of_mem _ (by simpa using hi))⟩

/-- **The prefixes are intrinsic.** An element is a prefix of an HN filtration if and only if it
is the unique maximizer of some weight `w_θ`. With no vertical steps, `⊥` needs no separate
case (compare `ChargeFunction.HNChain.mem_range_chain_iff`). -/
theorem mem_range_chain_iff (x : L) : x ∈ Set.range F.chain ↔
    ∃ θ : K, ∀ y, s.weight θ y ≤ s.weight θ x ∧ (s.weight θ y = s.weight θ x → y = x) := by
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨θ, h₁, h₂⟩ := F.exists_slope_between k
    exact ⟨θ, fun y ↦ ⟨F.weight_le k (fun i hi ↦ (h₁ i hi).le) (fun i hi ↦ (h₂ i hi).le) y,
      F.eq_of_weight_eq k h₁ h₂⟩⟩
  · rintro ⟨θ, hx⟩
    obtain ⟨k, h₁, h₂⟩ := F.exists_index θ
    exact ⟨k, ((hx (F.chain k)).2 (le_antisymm (hx _).1 (F.weight_le k h₁ h₂ x)))⟩

/-- **Uniqueness.** A slope function has at most one HN filtration: the case of
`ChargeFunction.HNChain.instSubsingleton`. -/
instance instSubsingleton : Subsingleton s.HNFiltration :=
  equivCharge.subsingleton

/-- **HN prefixes are fixed by symmetries.** A map `φ : L → L` preserving rank and degree fixes
every prefix of an HN filtration. -/
theorem apply_chain_eq {φ : L → L} (hrk : ∀ x, s.rk (φ x) = s.rk x)
    (hdeg : ∀ x, s.deg (φ x) = s.deg x) (k : Fin (F.n + 1)) : φ (F.chain k) = F.chain k :=
  F.toCharge.apply_chain_eq hrk hdeg k

end OrderedField

end HNFiltration

/-! ### Existence -/

section Existence

variable [IsStrictOrderedRing K]

/-- **Existence of the HN filtration of a slope function** from the ascending chain condition and
a maximal slope attained on every `[a, ⊤]`. -/
theorem nonempty_hnFiltration [WellFoundedGT L]
    (hatt : ∀ a : L, a < ⊤ → ∃ z₀, a < z₀ ∧ ∀ z, a < z → s.slope a z ≤ s.slope a z₀) :
    Nonempty s.HNFiltration := by
  refine (s.toChargeFunction.nonempty_hnFiltration fun a ha ↦ ?_).map HNFiltration.ofCharge
  obtain ⟨z₀, hz₀, h⟩ := hatt a ha
  refine ⟨z₀, hz₀, fun z hz ↦ ?_⟩
  rw [s.toChargeFunction_phase hz, s.toChargeFunction_phase hz₀]
  exact_mod_cast h z hz

/-- **Existence of the HN filtration of a slope function with finitely many values**, a statement
about lattices of finite length. -/
theorem nonempty_hnFiltration_of_finite_range
    (hfin : (Set.range fun x ↦ (s.rk x, s.deg x)).Finite) : Nonempty s.HNFiltration :=
  (s.toChargeFunction.nonempty_hnFiltration_of_finite_range hfin).map HNFiltration.ofCharge

end Existence

variable {s} in
/-- The transport of an HN filtration along an order isomorphism that carries `s` to `s'`. -/
def HNFiltration.map {L' : Type*} [Lattice L'] [BoundedOrder L'] {s' : SlopeFunction L' K}
    (φ : L ≃o L') (hrk : ∀ x, s'.rk (φ x) = s.rk x) (hdeg : ∀ x, s'.deg (φ x) = s.deg x)
    (F : s.HNFiltration) : s'.HNFiltration where
  n := F.n
  chain := φ ∘ F.chain
  strictMono := φ.strictMono.comp F.strictMono
  chain_zero := by simp [F.chain_zero]
  chain_last := by simp [F.chain_last]
  semistable i := by
    have hslope : ∀ x y, s'.slope (φ x) (φ y) = s.slope x y := fun x y ↦ by
      simp only [slope, hrk, hdeg]
    have hweight : ∀ θ x, s'.weight θ (φ x) = s.weight θ x := fun θ x ↦ by
      simp only [weight, hrk, hdeg]
    refine ⟨φ.strictMono (F.semistable i).1, fun z h₁ h₂ ↦ ?_⟩
    simp only [Function.comp_apply, hslope] at h₁ h₂ ⊢
    rw [← φ.apply_symm_apply z, hweight, hweight]
    exact (F.semistable i).2 _ (by rwa [← φ.le_iff_le, φ.apply_symm_apply])
      (by rwa [← φ.le_iff_le, φ.apply_symm_apply])
  slope_strictAnti i j hij := by
    have hslope : ∀ x y, s'.slope (φ x) (φ y) = s.slope x y := fun x y ↦ by
      simp only [slope, hrk, hdeg]
    simp only [Function.comp_apply, hslope]
    exact F.slope_strictAnti hij

variable {s} in
@[simp] lemma HNFiltration.map_chain {L' : Type*} [Lattice L'] [BoundedOrder L']
    {s' : SlopeFunction L' K} (φ : L ≃o L') (hrk : ∀ x, s'.rk (φ x) = s.rk x)
    (hdeg : ∀ x, s'.deg (φ x) = s.deg x) (F : s.HNFiltration) (k : Fin (F.n + 1)) :
    (F.map φ hrk hdeg).chain k = φ (F.chain k) := rfl

variable {s} in
/-- **HN filtrations only depend on the slope order.** An HN filtration of `s` is one of every
slope function `t` on `L` whose interval slopes are ordered like those of `s`. -/
def HNFiltration.ofSlopeOrder [IsStrictOrderedRing K] {K' : Type*} [Field K'] [LinearOrder K']
    [IsStrictOrderedRing K'] {t : SlopeFunction L K'}
    (h : ∀ x y x' y' : L, x < y → x' < y' →
      (s.slope x y ≤ s.slope x' y' ↔ t.slope x y ≤ t.slope x' y'))
    (F : s.HNFiltration) : t.HNFiltration where
  n := F.n
  chain := F.chain
  strictMono := F.strictMono
  chain_zero := F.chain_zero
  chain_last := F.chain_last
  semistable i := by
    have hlt := F.strictMono i.castSucc_lt_succ
    rw [t.isSemistable_iff hlt]
    intro z hz₁ hz₂
    exact (h _ _ _ _ hz₁ hlt).mp ((s.isSemistable_iff hlt).mp (F.semistable i) z hz₁ hz₂)
  slope_strictAnti i j hij := by
    have := F.slope_strictAnti hij
    rw [← not_le] at this ⊢
    rwa [← h _ _ _ _ (F.strictMono (Fin.castSucc_lt_succ (i := i)))
      (F.strictMono (Fin.castSucc_lt_succ (i := j)))]

variable {s} in
@[simp] lemma HNFiltration.ofSlopeOrder_chain [IsStrictOrderedRing K] {K' : Type*} [Field K']
    [LinearOrder K'] [IsStrictOrderedRing K'] {t : SlopeFunction L K'}
    (h : ∀ x y x' y' : L, x < y → x' < y' →
      (s.slope x y ≤ s.slope x' y' ↔ t.slope x y ≤ t.slope x' y'))
    (F : s.HNFiltration) : (F.ofSlopeOrder h).chain = F.chain := rfl

end SlopeFunction

end Order
