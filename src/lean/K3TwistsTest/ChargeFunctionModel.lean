/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Order.HarderNarasimhan
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.WithBot

/-!
# Models of charge functions

Three charge functions on linear orders, each a valuation trivially. They test the statements of
`K3Twists.Order.HarderNarasimhan` at their edges.

* `c3` on `{0 < 1 < 2}`, charges `(0, 0), (0, 1), (1, 1)`: the first factor is vertical, every
  weight is larger at `1` than at `⊥`, and `⊥` is a prefix that maximizes no weight. So the
  disjunct `x = ⊥` of `ChargeFunction.HNChain.mem_range_chain_iff` is needed.
* `cN` on `WithBot ℕᵒᵈ`, `⊥ < ⋯ < x₂ < x₁ < x₀ = ⊤` with `rk = 0` at `⊥` and `1` elsewhere and
  `deg xₙ = -n`: the shape of the chain `O(D) ⊃ I_{Z₁}(D) ⊃ I_{Z₂}(D) ⊃ ⋯` in a Noetherian heart.
  It has the ascending chain condition and infinitely many charge values, so the finite-range
  existence theorem does not apply to it; the main existence theorem does (`cN_hnFiltration`).
* `cE` on `ℕ∞` with `rk n = 1 - 1/(n + 1)`, `rk ⊤ = 1`, `deg = 0`: no ascending chain condition,
  and still an HN filtration `⊥ < ⊤`. The hypotheses of the existence theorem are sufficient, not
  necessary.
-/

namespace Order.ChargeFunctionModel

open Order Order.ChargeFunction

/-- Any function on a linear order is a valuation. -/
lemma val_of_linear {L K : Type*} [LinearOrder L] [AddCommMonoid K] (f : L → K) (x y : L) :
    f (x ⊔ y) + f (x ⊓ y) = f x + f y := by
  rcases le_total x y with h | h
  · rw [sup_eq_right.mpr h, inf_eq_left.mpr h, add_comm]
  · rw [sup_eq_left.mpr h, inf_eq_right.mpr h]

/-! ### A vertical first factor -/

/-- The rank of `c3`. -/
def rk3 : Fin 3 → ℚ := fun x ↦ if x = 2 then 1 else 0

/-- The degree of `c3`. -/
def deg3 : Fin 3 → ℚ := fun x ↦ if x = 0 then 0 else 1

/-- Charges `(0, 0), (0, 1), (1, 1)` on `0 < 1 < 2`: a vertical step, then a step of phase `0`. -/
def c3 : ChargeFunction (Fin 3) ℚ where
  rk := rk3
  deg := deg3
  lex_lt := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [rk3, deg3]
  rk_sup_add_inf := val_of_linear rk3
  deg_sup_add_inf := val_of_linear deg3

/-- For every `θ`, the element `1`, of the same rank as `⊥`, has a larger weight than `⊥`. -/
theorem c3_weight_bot_lt (θ : ℚ) : c3.weight θ ⊥ < c3.weight θ 1 := by
  show deg3 ⊥ - θ * rk3 ⊥ < deg3 1 - θ * rk3 1
  rw [show (⊥ : Fin 3) = 0 from rfl]
  simp [deg3, rk3]

/-- `⊥` maximizes no weight. -/
theorem c3_bot_not_max : ¬∃ θ : ℚ, ∀ y, c3.weight θ y ≤ c3.weight θ ⊥ ∧
    (c3.weight θ y = c3.weight θ ⊥ → y = ⊥) := by
  rintro ⟨θ, h⟩
  exact absurd (h 1).1 (not_le.mpr (c3_weight_bot_lt θ))

/-- The HN filtration of `c3` exists and has `⊥` as a prefix that maximizes no weight: the
statement of `mem_range_chain_iff` without the disjunct `x = ⊥` fails for it. -/
theorem c3_disjunct_needed : ∃ F : c3.HNFiltration, ⊥ ∈ Set.range F.chain ∧
    ¬∃ θ : ℚ, ∀ y, c3.weight θ y ≤ c3.weight θ ⊥ ∧ (c3.weight θ y = c3.weight θ ⊥ → y = ⊥) := by
  obtain ⟨F⟩ := c3.nonempty_hnFiltration_of_finite_range (Set.finite_range _)
  exact ⟨F, ⟨0, F.chain_zero⟩, c3_bot_not_max⟩

/-- The first factor of the HN filtration of `c3` is vertical. -/
example (F : c3.HNFiltration) (h0 : 0 < F.n) : F.factorPhase ⟨0, h0⟩ = ⊤ :=
  (F.factorPhase_zero_eq_top_iff h0).mpr
    ⟨1, by decide, by simp [c3, rk3, show (⊥ : Fin 3) = 0 from rfl]⟩

/-! ### The ascending chain condition with infinitely many charge values -/

/-- `⊥ < ⋯ < x₂ < x₁ < x₀ = ⊤`. -/
abbrev LN := WithBot ℕᵒᵈ

/-- The rank of `cN`: `0` at `⊥`, `1` elsewhere. -/
noncomputable def rkN : LN → ℚ := fun x ↦ WithBot.recBotCoe 0 (fun _ ↦ 1) x

/-- The degree of `cN`: `0` at `⊥`, `-n` at `xₙ`. -/
noncomputable def degN : LN → ℚ :=
  fun x ↦ WithBot.recBotCoe 0 (fun n ↦ -((OrderDual.ofDual n : ℕ) : ℚ)) x

/-- The charge of `Sub(O(D)) ⊃ I_Z(D) ⊃ ⋯`: constant rank above `⊥`, unbounded degree. -/
noncomputable def cN : ChargeFunction LN ℚ where
  rk := rkN
  deg := degN
  lex_lt := by
    intro x y h
    induction x using WithBot.recBotCoe with
    | bot =>
      induction y using WithBot.recBotCoe with
      | bot => exact absurd h (lt_irrefl _)
      | coe b => left; simp [rkN]
    | coe a =>
      induction y using WithBot.recBotCoe with
      | bot => exact absurd h (not_lt_bot)
      | coe b =>
        right
        have hab : a < b := WithBot.coe_lt_coe.mp h
        have : (OrderDual.ofDual b : ℕ) < OrderDual.ofDual a := hab
        refine ⟨by simp [rkN], ?_⟩
        simp only [degN, WithBot.recBotCoe_coe]
        have : ((OrderDual.ofDual b : ℕ) : ℚ) < (OrderDual.ofDual a : ℕ) := by exact_mod_cast this
        linarith
  rk_sup_add_inf := val_of_linear rkN
  deg_sup_add_inf := val_of_linear degN

example : WellFoundedGT LN := inferInstance

theorem cN_rk_discrete (x : LN) : cN.rk x = 0 ∨ cN.rk x = 1 := by
  induction x using WithBot.recBotCoe with
  | bot => left; simp [cN, rkN]
  | coe a => right; simp [cN, rkN]

/-- The charge of `cN` takes infinitely many values. -/
theorem cN_range_infinite : ¬(Set.range fun x ↦ (cN.rk x, cN.deg x)).Finite := by
  intro hfin
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ ((1 : ℚ), -(n : ℚ)))
    (fun a b hab ↦ by simpa using hab) (fun n ↦ ?_) hfin
  exact ⟨((OrderDual.toDual n : ℕᵒᵈ) : LN), by simp [cN, rkN, degN]⟩

/-- Finitely many charge values would bound the length of chains. -/
example (hfin : (Set.range fun x ↦ (cN.rk x, cN.deg x)).Finite) {m : ℕ} (f : Fin m → LN)
    (hf : StrictMono f) : m ≤ hfin.toFinset.card :=
  cN.card_le_of_finite_range hfin f hf

lemma degN_nonpos (x : LN) : degN x ≤ 0 := by
  induction x using WithBot.recBotCoe with
  | bot => simp [degN]
  | coe a => simp [degN]

/-- The maximal phase of `cN` is attained at `⊤` on every interval. -/
theorem cN_maxPhaseAttained : cN.MaxPhaseAttained := by
  intro a ha
  refine ⟨⊤, ha, fun z hz ↦ ?_⟩
  induction a using WithBot.recBotCoe with
  | bot =>
    rw [cN.phase_le_phase_iff hz ha]
    change (degN z - degN ⊥) * (rkN ⊤ - rkN ⊥) ≤ (degN ⊤ - degN ⊥) * (rkN z - rkN ⊥)
    have h1 : degN ⊤ = 0 := rfl
    have h2 : degN ⊥ = 0 := rfl
    have h3 : rkN ⊤ = 1 := rfl
    have h4 : rkN ⊥ = 0 := rfl
    rw [h1, h2, h3, h4]
    have := degN_nonpos z
    linarith
  | coe m =>
    have : cN.phase (m : LN) ⊤ = ⊤ := cN.phase_eq_top_iff.mpr rfl
    rw [this]
    exact le_top

/-- **The main existence theorem covers `cN`**, which the finite-range version cannot reach
(`cN_range_infinite`). -/
theorem cN_hnFiltration : Nonempty cN.HNFiltration :=
  cN.nonempty_hnFiltration cN_maxPhaseAttained

/-- The HN filtration of `cN` is `⊥ < ⊤`, one semistable factor of phase `0`. -/
noncomputable def cN_hn : cN.HNFiltration where
  n := 1
  chain := ![⊥, ⊤]
  strictMono := Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
    fin_cases i
    exact WithBot.bot_lt_coe _
  chain_zero := rfl
  chain_last := rfl
  semistable i := by
    fin_cases i
    refine ⟨WithBot.bot_lt_coe _, fun z _ _ ↦ ?_⟩
    change (degN z - degN ⊥) * (rkN ⊤ - rkN ⊥) ≤ (degN ⊤ - degN ⊥) * (rkN z - rkN ⊥)
    have h1 : degN ⊤ = 0 := rfl
    have h2 : degN ⊥ = 0 := rfl
    have h3 : rkN ⊤ = 1 := rfl
    have h4 : rkN ⊥ = 0 := rfl
    rw [h1, h2, h3, h4]
    have := degN_nonpos z
    linarith
  phase_strictAnti i j h := absurd h (by rw [Subsingleton.elim i j]; exact lt_irrefl _)

/-- The filtration from the existence theorem is `cN_hn`. -/
example : Classical.choice cN_hnFiltration = cN_hn := Subsingleton.elim _ _

/-! ### No ascending chain condition -/

/-- The rank of `cE`: `1 - 1/(n + 1)` at `n`, `1` at `⊤`. -/
noncomputable def rkE : ℕ∞ → ℚ := fun x ↦ ENat.recTopCoe 1 (fun n ↦ 1 - 1 / ((n : ℚ) + 1)) x

/-- A slope function on `ℕ∞` with degree `0`. -/
noncomputable def cE : ChargeFunction ℕ∞ ℚ where
  rk := rkE
  deg := fun _ ↦ 0
  lex_lt := by
    intro x y h
    left
    induction x using ENat.recTopCoe with
    | top => exact absurd h (not_top_lt)
    | coe a =>
      induction y using ENat.recTopCoe with
      | top =>
        simp only [rkE, ENat.recTopCoe_natCast, ENat.recTopCoe_top]
        have : (0 : ℚ) < 1 / ((a : ℚ) + 1) := by positivity
        linarith
      | coe b =>
        simp only [rkE, ENat.recTopCoe_natCast]
        have hab : a < b := by exact_mod_cast h
        have : 1 / ((b : ℚ) + 1) < 1 / ((a : ℚ) + 1) := by
          apply one_div_lt_one_div_of_lt (by positivity)
          have : (a : ℚ) < b := by exact_mod_cast hab
          linarith
        linarith
  rk_sup_add_inf := val_of_linear rkE
  deg_sup_add_inf := val_of_linear (fun _ : ℕ∞ ↦ (0 : ℚ))

theorem not_wellFoundedGT_enat : ¬WellFoundedGT ℕ∞ := by
  intro h
  obtain ⟨m, ⟨n, rfl⟩, hmin⟩ := (wellFounded_gt (α := ℕ∞)).has_min
    (Set.range fun n : ℕ ↦ (n : ℕ∞)) ⟨0, 0, rfl⟩
  exact hmin _ ⟨n + 1, rfl⟩
    (by show (n : ℕ∞) < ((n + 1 : ℕ) : ℕ∞); exact_mod_cast Nat.lt_succ_self n)

/-- `⊥ < ⊤` is an HN filtration of `cE`, with no ascending chain condition. -/
noncomputable def cE_hn : cE.HNFiltration where
  n := 1
  chain := ![⊥, ⊤]
  strictMono := Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
    fin_cases i
    exact bot_lt_top
  chain_zero := rfl
  chain_last := rfl
  semistable i := by
    fin_cases i
    refine ⟨bot_lt_top, fun z _ _ ↦ ?_⟩
    simp [cE]
  phase_strictAnti i j h := absurd h (by rw [Subsingleton.elim i j]; exact lt_irrefl _)

end Order.ChargeFunctionModel
