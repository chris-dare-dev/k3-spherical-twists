/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Order.HarderNarasimhan

/-!
# The first prefix of an HN filtration is the maximal destabilizer

Let `c` be a charge function on a bounded lattice `L`. An element `t` is a **maximal destabilizer**
of `[a, ⊤]` (`Order.ChargeFunction.IsMaxDestabilizer`) if `a < t`, no `z > a` has a larger phase
from `a`, and every `z > a` of the same phase lies below `t`. It is unique
(`IsMaxDestabilizer.unique`), and it exists under the ascending chain condition and an attained
maximal phase (`ChargeFunction.exists_maxDestabilizer`).

## Main results

* `Order.ChargeFunction.HNChain.isMaxDestabilizer_chain_one`: **the first nonzero prefix of an HN
  filtration is the maximal destabilizer of `[⊥, ⊤]`.** Its phase bound is the weight inequality of
  the prefixes (`HNChain.weight_le`). That it is greatest is Topkis's theorem
  (`greatest_maximizer_antitone`): the prefix is the greatest maximizer of a weight `w_θ'` with
  `θ'` just below its phase, and an element of the same phase maximizes `w_θ` for the phase `θ`
  itself, `θ' < θ`.
* `Order.ChargeFunction.HNChain.chain_one_eq_of_isMaxDestabilizer`: so the first prefix is the
  maximal destabilizer, whatever the rest of the filtration is.
* `Order.ChargeFunction.IsMaxDestabilizer.isGreatest_weight`: a maximal destabilizer of `[⊥, ⊤]` of
  finite phase `θ` is the greatest maximizer of the weight `w_θ`, and by Topkis's theorem it lies
  above every maximizer of `w_θ'` for `θ' ≥ θ` (`IsMaxDestabilizer.le_of_weight_le`).

This is the form in which the greedy rule at intersecting walls uses the charge-function frame
(`CategoryTheory/Triangulated/StabilityCondition/IntersectingWalls.lean`).
-/

namespace Order.ChargeFunction

variable {L K : Type*} [Lattice L] [Field K] [LinearOrder K] (c : ChargeFunction L K)

/-- `t` is the **maximal destabilizer** of `[a, ⊤]`: `a < t`, no `z > a` has a larger phase from
`a` than `t`, and every `z > a` of the same phase lies below `t`. -/
def IsMaxDestabilizer (a t : L) : Prop :=
  a < t ∧ (∀ z, a < z → c.phase a z ≤ c.phase a t) ∧
    ∀ z, a < z → c.phase a z = c.phase a t → z ≤ t

variable {c}

/-- **The maximal destabilizer is unique.** -/
theorem IsMaxDestabilizer.unique {a t t' : L} (h : c.IsMaxDestabilizer a t)
    (h' : c.IsMaxDestabilizer a t') : t = t' :=
  le_antisymm (h'.2.2 t h.1 (le_antisymm (h'.2.1 t h.1) (h.2.1 t' h'.1)))
    (h.2.2 t' h'.1 (le_antisymm (h.2.1 t' h'.1) (h'.2.1 t h.1)))

variable [IsStrictOrderedRing K]

/-- An interval `[x, y]` of finite phase `θ` has `w_θ x = w_θ y`. -/
lemma weight_eq_of_phase_eq {x y : L} (h : x < y) {θ : K} (hθ : c.phase x y = θ) :
    c.weight θ y = c.weight θ x := by
  have h₁ := (c.coe_le_phase_iff h θ).mp hθ.ge
  have h₂ := (c.phase_le_coe_iff h θ).mp hθ.le
  simp only [weight]
  linarith

variable [BoundedOrder L]

variable (c) in
/-- **Existence of the maximal destabilizer** from the ascending chain condition and an attained
maximal phase: `exists_maxDestabilizer` in the form of `IsMaxDestabilizer`. -/
theorem exists_isMaxDestabilizer [WellFoundedGT L] (hatt : c.MaxPhaseAttained) {a : L}
    (ha : a < ⊤) : ∃ t, c.IsMaxDestabilizer a t :=
  c.exists_maxDestabilizer hatt ha

/-- **A maximal destabilizer of `[⊥, ⊤]` of finite phase `θ` is the greatest maximizer of the
weight `w_θ`.** -/
theorem IsMaxDestabilizer.isGreatest_weight {t : L} (ht : c.IsMaxDestabilizer ⊥ t) {θ : K}
    (hθ : c.phase ⊥ t = θ) : IsGreatest {x | ∀ y, c.weight θ y ≤ c.weight θ x} t := by
  have hwt := weight_eq_of_phase_eq ht.1 hθ
  -- every `y` has `w_θ y ≤ w_θ ⊥ = w_θ t`
  have hle : ∀ y, c.weight θ y ≤ c.weight θ ⊥ := fun y => by
    rcases (bot_le : ⊥ ≤ y).lt_or_eq with hy | hy
    · have := (c.phase_le_coe_iff hy θ).mp (hθ ▸ ht.2.1 y hy)
      simp only [weight]
      linarith
    · rw [← hy]
  refine ⟨fun y => hwt ▸ hle y, fun x hx => ?_⟩
  have hx' : c.weight θ x = c.weight θ ⊥ := le_antisymm (hle x) (hwt ▸ hx t)
  rcases (bot_le : ⊥ ≤ x).lt_or_eq with hbx | hbx
  · refine ht.2.2 x hbx (le_antisymm (ht.2.1 x hbx) ?_)
    rw [hθ, c.coe_le_phase_iff hbx]
    simp only [weight] at hx'
    linarith
  · rw [← hbx]
    exact ht.1.le

/-- **Topkis's theorem for the maximal destabilizer.** A maximal destabilizer `t` of `[⊥, ⊤]` of
finite phase `θ` lies above every maximizer of the weight `w_θ'` for every `θ' ≥ θ`. -/
theorem IsMaxDestabilizer.le_of_weight_le {t : L} (ht : c.IsMaxDestabilizer ⊥ t) {θ θ' : K}
    (hθ : c.phase ⊥ t = θ) (hθθ' : θ ≤ θ') {x : L} (hx : ∀ y, c.weight θ' y ≤ c.weight θ' x) :
    x ≤ t :=
  greatest_maximizer_antitone c.rk_mono c.rk_sup_add_inf c.deg_sup_add_inf hθθ'
    (ht.isGreatest_weight hθ) hx

namespace HNChain

/-- **The first nonzero prefix of an HN filtration is the maximal destabilizer** of `[⊥, ⊤]`. The
phase bound is the weight inequality of the prefix at its own phase; that every element of the same
phase lies below the prefix is Topkis's theorem (`greatest_maximizer_antitone`), applied to the
weight `w_θ'` of which the prefix is the unique maximizer, `θ'` just below its phase. -/
theorem isMaxDestabilizer_chain_one (F : c.HNFiltration) (h0 : 0 < F.n) :
    c.IsMaxDestabilizer ⊥ (F.chain ⟨1, by omega⟩) := by
  set t := F.chain ⟨1, by omega⟩ with ht
  set i₀ : Fin F.n := ⟨0, h0⟩ with hi₀
  have hc0 : F.chain i₀.castSucc = ⊥ := F.chain_zero
  have hc1 : F.chain i₀.succ = t := rfl
  have hbt : ⊥ < t := by
    have := F.strictMono i₀.castSucc_lt_succ
    rwa [hc0, hc1] at this
  have hph : F.factorPhase i₀ = c.phase ⊥ t := by
    simp only [factorPhase, hc0, hc1]
  -- the factors above `t` have phases below that of `[⊥, t]`
  have hbelow : ∀ i : Fin F.n, (⟨1, by omega⟩ : Fin (F.n + 1)) ≤ i.castSucc →
      F.factorPhase i < c.phase ⊥ t := fun i hi => by
    rw [← hph]
    have hi' : 1 ≤ (i : ℕ) := by simpa [Fin.le_def] using hi
    exact F.phase_strictAnti (Fin.mk_lt_mk.mpr (by omega))
  have hupto : ∀ i : Fin F.n, i.succ ≤ (⟨1, by omega⟩ : Fin (F.n + 1)) → i = i₀ := fun i hi =>
    Fin.ext (by simpa [Fin.le_def] using hi)
  -- the phase bound
  have hbound : ∀ z, ⊥ < z → c.phase ⊥ z ≤ c.phase ⊥ t := by
    intro z hz
    rcases eq_or_ne (c.phase ⊥ t) ⊤ with htop | hne
    · rw [htop]
      exact le_top
    obtain ⟨θ, hθ⟩ := WithTop.ne_top_iff_exists.mp hne
    have hmax := F.weight_le (θ := θ) ⟨1, by omega⟩
      (fun i hi => by rw [hupto i hi, hph, ← hθ]) (fun i hi => by rw [hθ]; exact (hbelow i hi).le)
      z
    have hwt := weight_eq_of_phase_eq hbt hθ.symm
    rw [← hθ, c.phase_le_coe_iff hz]
    rw [← ht, hwt] at hmax
    simp only [weight] at hmax
    linarith
  refine ⟨hbt, hbound, fun z hz heq => ?_⟩
  -- `t` is the unique maximizer of `w_θ'` for a `θ'` just below the phase of `[⊥, t]`
  obtain ⟨θ', hθ'₁, hθ'₂⟩ := F.exists_between_succ i₀
  have h₁ : ∀ i : Fin F.n, i.succ ≤ (⟨1, by omega⟩ : Fin (F.n + 1)) →
      (θ' : WithTop K) < F.factorPhase i := fun i hi => by rw [hupto i hi]; exact hθ'₁
  have h₂ : ∀ i : Fin F.n, (⟨1, by omega⟩ : Fin (F.n + 1)) ≤ i.castSucc →
      F.factorPhase i < (θ' : WithTop K) := fun i hi => by
    have hi' : 1 ≤ (i : ℕ) := by simpa [Fin.le_def] using hi
    have hn : (i₀ : ℕ) + 1 < F.n := by simp only [hi₀]; omega
    exact (F.phase_strictAnti.antitone (Fin.mk_le_mk.mpr hi')).trans_lt (hθ'₂ hn)
  have hmax' : ∀ y, c.weight θ' y ≤ c.weight θ' t :=
    F.weight_le ⟨1, by omega⟩ (fun i hi => (h₁ i hi).le) (fun i hi => (h₂ i hi).le)
  have hgreat : IsGreatest {x | ∀ y, c.weight θ' y ≤ c.weight θ' x} t :=
    ⟨hmax', fun x hx => (F.eq_of_weight_eq ⟨1, by omega⟩ h₁ h₂
      (le_antisymm (hmax' x) (hx t))).le⟩
  rcases eq_or_ne (c.phase ⊥ t) ⊤ with htop | hne
  · -- a vertical first factor: `z ⊔ t` has the rank of `t` and a degree at least that of `t`
    have hrz : c.rk ⊥ = c.rk z := (c.phase_eq_top_iff).mp (heq.trans htop)
    have hrt : c.rk ⊥ = c.rk t := (c.phase_eq_top_iff).mp htop
    have hsup := c.rk_sup_add_inf z t
    have hinf := c.rk_mono (bot_le : ⊥ ≤ z ⊓ t)
    have hsup' := c.rk_mono (bot_le : ⊥ ≤ z ⊔ t)
    have hrk : c.rk t = c.rk (z ⊔ t) := by linarith
    have hdeg := c.deg_le_of_le_of_rk_eq (le_sup_right : t ≤ z ⊔ t) hrk
    have hw : c.weight θ' (z ⊔ t) = c.weight θ' t := by
      refine le_antisymm (hmax' _) ?_
      simp only [weight]
      rw [← hrk]
      linarith
    exact le_sup_left.trans (F.eq_of_weight_eq ⟨1, by omega⟩ h₁ h₂ hw).le
  · -- a finite phase `θ > θ'`: `z` maximizes `w_θ`, so Topkis puts it below `t`
    obtain ⟨θ, hθ⟩ := WithTop.ne_top_iff_exists.mp hne
    have hwz := weight_eq_of_phase_eq hz (heq.trans hθ.symm)
    have hzmax : ∀ y, c.weight θ y ≤ c.weight θ z := fun y => by
      rcases (bot_le : ⊥ ≤ y).lt_or_eq with hy | hy
      · have := (c.phase_le_coe_iff hy θ).mp (hθ ▸ hbound y hy)
        rw [hwz]
        simp only [weight]
        linarith
      · rw [← hy, hwz]
    have hθθ' : θ' ≤ θ := by
      have := hθ'₁
      rw [hph, ← hθ, WithTop.coe_lt_coe] at this
      exact this.le
    exact greatest_maximizer_antitone c.rk_mono c.rk_sup_add_inf c.deg_sup_add_inf hθθ' hgreat
      hzmax

/-- **The first prefix of an HN filtration is the maximal destabilizer**, whatever the rest of the
filtration is. -/
theorem chain_one_eq_of_isMaxDestabilizer (F : c.HNFiltration) (h0 : 0 < F.n) {t : L}
    (ht : c.IsMaxDestabilizer ⊥ t) : F.chain ⟨1, by omega⟩ = t :=
  (F.isMaxDestabilizer_chain_one h0).unique ht

omit [IsStrictOrderedRing K] in
/-- An HN filtration of a lattice with a maximal destabilizer of `[⊥, ⊤]` has a factor: `⊥ ≠ ⊤`. -/
theorem pos_n_of_isMaxDestabilizer (F : c.HNFiltration) {t : L} (ht : c.IsMaxDestabilizer ⊥ t) :
    0 < F.n := by
  by_contra h
  have hn : F.n = 0 := by omega
  have hlast : F.chain 0 = F.chain (Fin.last F.n) := congrArg F.chain (Fin.ext (by simp [hn]))
  rw [F.chain_zero, F.chain_last] at hlast
  exact absurd (hlast ▸ ht.1) (not_lt_of_ge le_top)

end HNChain

end Order.ChargeFunction
