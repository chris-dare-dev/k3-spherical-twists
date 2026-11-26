/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Complex.PhaseGap
import Mathlib.Analysis.Complex.ExponentialBounds
import K3Twists.CategoryTheory.Abelian.Subobject.Valuation
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.StabilitySpace
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.ExtensionClosure
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Heart
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.ShortStep

/-!
# Intersecting ordinary walls

Let `σ` be a stability condition at which several ordinary walls of marginal stability meet, and
`E` an object with `σ`-HN factors `B_i ∈ P_σ(φ_i)`. The lemma on intersecting ordinary walls says
that in a small neighbourhood of `σ` the HN tower of `E` at every nearby `τ` is computed inside the
abelian categories `P_σ(φ_i)`, one subobject calculation in each (Bridgeland, arXiv:math/0212237,
§8, for the deformation estimates). This file proves its two steps for one factor `B ∈ P_σ(φ)`.

## (a) The lattice gap

* `PreStabilityCondition.WithClassMap.IsPhaseGap σ φ R ε`: every nonzero `σ`-semistable object of
  phase within `2ε` of `φ` whose charge has modulus less than `R` has phase exactly `φ`. It holds
  for some `ε ∈ (0, 1/8)` as soon as the charges of the nonzero `σ`-semistable objects with
  `‖Z‖ < R` are finitely many (`exists_isPhaseGap`), in particular under the support property of
  `σ` with a norm that has finitely many classes in every ball (`finite_charges_of_hasSupport`).
  On the Mukai lattice these are the classes of square at least `-2` and bounded charge
  (`Mukai.exists_latticeGap`, `LinearAlgebra/Lattice/Mukai/PhaseGap.lean`).
* `semistable_of_isPhaseGap`: under a phase gap, a nonzero object of mass less than `R` whose
  intrinsic `σ`-phases are within `2ε` of `φ` lies in `P_σ(φ)`.
* `exists_hnFiltration_semistable_of_isPhaseGap`: **the τ-HN factors stay in `P_σ(φ)`.** Let `τ`
  be one short step from `σ` (slicings `ε`-close, masses within `e^ε`, `ε ≤ 1/8`), let
  `B ∈ P_σ(φ)` with `|Z_σ(B)| ≤ M`, and let `σ` have a phase gap at `φ` below `2M`. Then `B` has a
  `τ`-HN filtration all of whose factors lie in `P_σ(φ)`: their `σ`-mass is at most
  `e^{2ε} |Z_σ(B)| < 2M` and their `σ`-phases are within `2ε` of `φ`.
  `StabilitySpaceHypotheses.exists_hnFiltration_semistable_of_isPhaseGap` is the same for two points
  of a stability space at distance less than `ε`.

## (b) The τ-HN statement near σ

* `greedy_rule`: **the first `τ`-HN subobject is the greatest maximizer of the `τ`-phase.** Let
  `U → B → Q` be the first step of the `τ`-HN filtration of `B ∈ P_σ(φ)` (`U` semistable of the
  top phase `ψ₁`, `Q` of phases below `ψ₁`), with `U, Q ∈ P_σ(φ)`. For every subobject `V → B` in
  the abelian category `P_σ(φ)` (a distinguished triangle `V → B → Q'` with `V, Q' ∈ P_σ(φ)`), the
  rotated charge `w = e^{-iπφ} Z_τ` has `Im w(V) Re w(U) ≤ Im w(U) Re w(V)`: the phase of
  `Z_τ(V)` is at most `ψ₁`. In case of equality `V → B` factors through `U → B`.
  `greedy_rule_of_isPhaseGap` discharges `U, Q ∈ P_σ(φ)` from the phase gap.
* `rotatedChargeFunction`: **HN filtrations of the subobjects of `B` in `P_σ(φ)`.** In the heart
  `P_σ((φ - 1, φ])`, where `P_σ(φ)` is a Serre class (`isSerreClass_heartTop`), every subobject of
  `B` lies in `P_σ(φ)`, and `(rk, deg) = (Re w, Im w)` is a charge function on them with positive
  rank on every nonzero subquotient (`rotatedChargeFunction_rk_lt`): no vertical edge. Its HN
  filtration exists from the ascending chain condition and an attained maximal phase
  (`nonempty_hnFiltration_rotatedChargeFunction`, from `Order.ChargeFunction.nonempty_hnChain`),
  not from finiteness of the range of the charge.

The homotopy pullbacks that assemble the factors over the different `B_i` into the `τ`-HN tower of
`E` are the cut criterion for cones (`Slicing/ConeHN.lean`, `Slicing/ConeHNStrict.lean`); the
assembly itself is not done here.

## Tags

stability condition, wall crossing, Harder–Narasimhan filtration, phase gap, mass
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Real

universe u v u'

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace PreStabilityCondition.WithClassMap

variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-! ### (a) The phase gap -/

/-- The **phase gap** of `σ` at `φ` below `R`, of width `2ε`: every nonzero `σ`-semistable object
of phase within `2ε` of `φ` whose charge has modulus less than `R` has phase exactly `φ`. -/
def IsPhaseGap (σ : WithClassMap C v) (φ R ε : ℝ) : Prop :=
  ∀ ⦃ψ : ℝ⦄ ⦃G : C⦄, σ.slicing.P ψ G → ¬IsZero G → ‖σ.charge G‖ < R → |ψ - φ| < 2 * ε → ψ = φ

/-- **A phase gap from finitely many charges.** If the charges of the nonzero `σ`-semistable
objects with `‖Z‖ < R` lie in a finite set, then for finitely many phases `Φ` there is
`ε ∈ (0, 1/8)` with a phase gap at every `φ ∈ Φ`, and distinct phases of `Φ` are more than `2ε`
apart. -/
theorem exists_isPhaseGap (σ : WithClassMap C v) {R : ℝ} {S : Set ℂ} (hS : S.Finite)
    (hcls : ∀ ⦃ψ : ℝ⦄ ⦃G : C⦄, σ.slicing.P ψ G → ¬IsZero G → ‖σ.charge G‖ < R →
      σ.charge G ∈ S) (Φ : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 8 ∧ (∀ φ ∈ Φ, σ.IsPhaseGap φ R ε) ∧
      ∀ φ ∈ Φ, ∀ φ' ∈ Φ, φ ≠ φ' → 2 * ε < |φ - φ'| := by
  obtain ⟨ε, hε, hε8, hgap, hsep⟩ := Complex.exists_phaseGap S hS Φ
  refine ⟨ε, hε, hε8, fun φ hφ ψ G hP hG hR hlt => ?_, hsep⟩
  obtain ⟨m, hm, hZ⟩ := σ.compat ψ G hP hG
  exact hgap _ (hcls hP hG hR) φ hφ m ψ hm hZ hlt

/-- **Finitely many charges from the support property.** If `σ` has the support property for a
function `N` on classes with finitely many classes in every sublevel set, the charges of the
nonzero `σ`-semistable objects with `‖Z‖ < R` are finitely many. -/
theorem finite_charges_of_hasSupport (σ : WithClassMap C v) {N : Λ → ℝ} {K : ℝ}
    (hK : σ.HasSupport N K) (hN : ∀ r : ℝ, {x | N x ≤ r}.Finite) (R : ℝ) :
    ∃ S : Set ℂ, S.Finite ∧ ∀ ⦃ψ : ℝ⦄ ⦃G : C⦄, σ.slicing.P ψ G → ¬IsZero G →
      ‖σ.charge G‖ < R → σ.charge G ∈ S := by
  refine ⟨σ.Z '' {x | N x ≤ max K 0 * R}, (hN _).image _, fun ψ G hP _ hR => ?_⟩
  refine ⟨classOf C v G, ?_, rfl⟩
  calc N (classOf C v G) ≤ K * ‖σ.charge G‖ := hK ψ G hP
    _ ≤ max K 0 * ‖σ.charge G‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max K 0 * R := mul_le_mul_of_nonneg_left hR.le (le_max_right _ _)

/-- The norm of the charge of one HN factor is at most the mass. -/
theorem norm_charge_factor_le_mass (σ : WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) (j : Fin F.n) : ‖σ.charge (F.factor j)‖ ≤ σ.mass E := by
  rw [σ.mass_eq_sum F]
  exact Finset.single_le_sum (f := fun i => ‖σ.charge (F.factor i)‖)
    (fun i _ => norm_nonneg _) (Finset.mem_univ j)

/-- **Near `φ` means in `P(φ)`, under a phase gap.** A nonzero object of mass less than `R` whose
intrinsic `σ`-phases are within `2ε` of `φ` is `σ`-semistable of phase `φ`: its first and last HN
factors have charge of modulus less than `R`. -/
theorem semistable_of_isPhaseGap (σ : WithClassMap C v) {φ R ε : ℝ}
    (hgap : σ.IsPhaseGap φ R ε) {X : C} (hX : ¬IsZero X) (hm : σ.mass X < R)
    (hplus : |σ.slicing.phiPlus C X hX - φ| < 2 * ε)
    (hminus : |σ.slicing.phiMinus C X hX - φ| < 2 * ε) : σ.slicing.P φ X := by
  obtain ⟨F, hn, hfirst, hlast, hp, hm', -⟩ := σ.slicing.exists_hn_phase_bounds hX
  have h₁ : σ.slicing.phiPlus C X hX = φ := by
    rw [← hp]
    exact hgap (F.semistable _) hfirst ((σ.norm_charge_factor_le_mass F _).trans_lt hm)
      (by rw [hp]; exact hplus)
  have h₂ : σ.slicing.phiMinus C X hX = φ := by
    rw [← hm']
    exact hgap (F.semistable _) hlast ((σ.norm_charge_factor_le_mass F _).trans_lt hm)
      (by rw [hm']; exact hminus)
  exact σ.slicing.semistable_of_phiPlus_le_of_le_phiMinus hX h₁.le h₂.ge

/-- `e^{2ε} < 2` for `ε ≤ 1/8`. -/
theorem exp_two_mul_lt_two {ε : ℝ} (hε : ε ≤ 1 / 8) : Real.exp (2 * ε) < 2 := by
  have h4 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he := Real.exp_one_lt_d9
  have hq : Real.exp (1 / 4) < 2 := by
    by_contra h
    push Not at h
    have : (2 : ℝ) ^ 4 ≤ Real.exp (1 / 4) ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
    rw [h4] at this
    norm_num at this
    linarith
  exact (Real.exp_le_exp.mpr (by linarith)).trans_lt hq

section Factors

variable (σ τ : WithClassMap C v) {ε φ M : ℝ}

/-- One short step from `σ` to `τ`: the slicings are `ε`-close and the masses within `e^ε`.
Nonzero `τ`-semistable objects of phase within `ε` of `φ` have `σ`-phases within `2ε` of `φ`. -/
theorem abs_phi_sub_lt_of_phaseClose (hclose : σ.slicing.PhaseClose τ.slicing ε) {ψ : ℝ}
    {G : C} (hG : τ.slicing.P ψ G) (hG0 : ¬IsZero G) (hψ : |ψ - φ| < ε) :
    |σ.slicing.phiPlus C G hG0 - φ| < 2 * ε ∧ |σ.slicing.phiMinus C G hG0 - φ| < 2 * ε := by
  obtain ⟨hp, hm⟩ := τ.slicing.phiPlus_eq_phiMinus_of_semistable hG0 hG
  obtain ⟨h₁, h₂⟩ := hclose G hG0
  rw [hp] at h₁
  rw [hm] at h₂
  constructor
  · calc |σ.slicing.phiPlus C G hG0 - φ|
        ≤ |σ.slicing.phiPlus C G hG0 - ψ| + |ψ - φ| := abs_sub_le _ _ _
      _ < ε + ε := add_lt_add (by rw [abs_sub_comm]; exact h₁) hψ
      _ = 2 * ε := by ring
  · calc |σ.slicing.phiMinus C G hG0 - φ|
        ≤ |σ.slicing.phiMinus C G hG0 - ψ| + |ψ - φ| := abs_sub_le _ _ _
      _ < ε + ε := add_lt_add (by rw [abs_sub_comm]; exact h₂) hψ
      _ = 2 * ε := by ring

/-- In one short step, an object `X` with `m_τ(X) ≤ m_τ(B)` has `m_σ(X) < 2 |Z_σ(B)|`, for
`B ∈ P_σ(φ)` nonzero and `ε ≤ 1/8`. -/
theorem mass_lt_of_mass_le (hε : ε ≤ 1 / 8)
    (hστ : ∀ E, σ.mass E ≤ Real.exp ε * τ.mass E) (hτσ : ∀ E, τ.mass E ≤ Real.exp ε * σ.mass E)
    {B : C} (hB : σ.slicing.P φ B) (hB0 : ¬IsZero B) {X : C} (hX : τ.mass X ≤ τ.mass B) :
    σ.mass X < 2 * ‖σ.charge B‖ := by
  have hpos := σ.norm_charge_pos_of_semistable hB hB0
  have hmB := σ.mass_eq_norm_charge_of_semistable hB
  have he : 0 < Real.exp ε := Real.exp_pos ε
  calc σ.mass X ≤ Real.exp ε * τ.mass X := hστ X
    _ ≤ Real.exp ε * τ.mass B := mul_le_mul_of_nonneg_left hX he.le
    _ ≤ Real.exp ε * (Real.exp ε * σ.mass B) := mul_le_mul_of_nonneg_left (hτσ B) he.le
    _ = Real.exp (2 * ε) * ‖σ.charge B‖ := by
      rw [hmB, ← mul_assoc, ← Real.exp_add, two_mul]
    _ < 2 * ‖σ.charge B‖ := mul_lt_mul_of_pos_right (exp_two_mul_lt_two hε) hpos

/-- **The τ-HN factors of `B ∈ P_σ(φ)` stay in `P_σ(φ)`.** Let `τ` be one short step from `σ`
(`ε`-close slicings, masses within `e^ε`, `ε ≤ 1/8`), let `B ∈ P_σ(φ)` with `|Z_σ(B)| ≤ M`, and
let `σ` have a phase gap at `φ` below `2M`. Then some `τ`-HN filtration of `B` has all its
factors in `P_σ(φ)`. -/
theorem exists_hnFiltration_semistable_of_isPhaseGap (hε : ε ≤ 1 / 8)
    (hclose : σ.slicing.PhaseClose τ.slicing ε)
    (hστ : ∀ E, σ.mass E ≤ Real.exp ε * τ.mass E) (hτσ : ∀ E, τ.mass E ≤ Real.exp ε * σ.mass E)
    (hgap : σ.IsPhaseGap φ (2 * M) ε) {B : C} (hB : σ.slicing.P φ B) (hBM : ‖σ.charge B‖ ≤ M) :
    ∃ F : HNFiltration C τ.slicing.P B, ∀ j, σ.slicing.P φ (F.factor j) := by
  by_cases hB0 : IsZero B
  · exact ⟨HNFiltration.zero C B hB0, fun j => j.elim0⟩
  obtain ⟨F, hn, -, -, -, -, hb⟩ := τ.slicing.exists_hn_phase_bounds hB0
  refine ⟨F, fun j => ?_⟩
  by_cases hG0 : IsZero (F.factor j)
  · exact σ.slicing.zero_mem_of_isZero C φ _ hG0
  -- the `τ`-phase of the factor is within `ε` of `φ`
  obtain ⟨hpσ, hmσ⟩ := σ.slicing.phiPlus_eq_phiMinus_of_semistable hB0 hB
  obtain ⟨h₁, h₂⟩ := hclose B hB0
  rw [hpσ] at h₁
  rw [hmσ] at h₂
  have hψ : |F.φ j - φ| < ε := by
    obtain ⟨hlo, hhi⟩ := hb j
    rw [abs_lt] at h₁ h₂ ⊢
    constructor <;> linarith
  obtain ⟨hp, hm⟩ := σ.abs_phi_sub_lt_of_phaseClose τ hclose (F.semistable j) hG0 hψ
  -- its `σ`-mass is less than `2M`
  have hmass : τ.mass (F.factor j) ≤ τ.mass B := by
    rw [τ.mass_eq_norm_charge_of_semistable (F.semistable j)]
    exact τ.norm_charge_factor_le_mass F j
  have hlt := σ.mass_lt_of_mass_le τ hε hστ hτσ hB hB0 hmass
  exact σ.semistable_of_isPhaseGap hgap hG0 (hlt.trans_le (by linarith)) hp hm

end Factors

/-! ### (b) The greedy rule -/

section Greedy

variable [IsTriangulated C] (σ τ : WithClassMap C v) {ε φ : ℝ}

omit [IsTriangulated C] in
/-- `Re(e^{-iπφ} Z) = Im(e^{-iπ(φ - 1/2)} Z)`: a semistable object of phase `ψ` with charge
`m e^{iπψ}` has `imPhase (φ - 1/2) = m cos π(ψ - φ)`. -/
theorem imPhase_sub_half_of_charge_eq {φ : ℝ} {E : C} {m ψ : ℝ}
    (h : τ.charge E = (m : ℂ) * Complex.exp ((Real.pi * ψ : ℝ) * Complex.I)) :
    τ.imPhase (φ - 1 / 2) E = m * Real.cos (Real.pi * (ψ - φ)) := by
  rw [τ.imPhase_of_charge_eq _ h, show Real.pi * (ψ - (φ - 1 / 2)) =
    Real.pi * (ψ - φ) + Real.pi / 2 by ring, Real.sin_add_pi_div_two]

/-- **The greedy rule: the first `τ`-HN subobject is the greatest maximizer of the `τ`-phase.**
Let `σ` and `τ` have `ε`-close slicings with `ε ≤ 1/4`, and let `U → B → Q` be the first step of
the `τ`-HN filtration of `B ∈ P_σ(φ)`: `U` nonzero semistable of phase `ψ₁`, `Q` of phases below
`ψ₁`, with `U ∈ P_σ(φ)`. For every subobject `V → B` in `P_σ(φ)` (a distinguished triangle
`V → B → Q'` with `V, Q' ∈ P_σ(φ)`), the rotated charge `w = e^{-iπφ} Z_τ` satisfies
`Im w(V) Re w(U) ≤ Im w(U) Re w(V)`, and in case of equality `V → B` factors through `U → B`. -/
theorem greedy_rule (hε : ε ≤ 1 / 4) (hclose : σ.slicing.PhaseClose τ.slicing ε) {ψ₁ : ℝ}
    {B U Q : C} {i : U ⟶ B} {p : B ⟶ Q} {δ : Q ⟶ U⟦(1 : ℤ)⟧}
    (hT : Triangle.mk i p δ ∈ distTriang C) (hUτ : τ.slicing.P ψ₁ U) (hU0 : ¬IsZero U)
    (hQτ : τ.slicing.ltProp C ψ₁ Q) (hUσ : σ.slicing.P φ U) {V Q' : C} {j : V ⟶ B}
    {q : B ⟶ Q'} {δ' : Q' ⟶ V⟦(1 : ℤ)⟧} (hT' : Triangle.mk j q δ' ∈ distTriang C)
    (hVσ : σ.slicing.P φ V) (hQ'σ : σ.slicing.P φ Q') :
    τ.imPhase φ V * τ.imPhase (φ - 1 / 2) U ≤ τ.imPhase φ U * τ.imPhase (φ - 1 / 2) V ∧
      (τ.imPhase φ V * τ.imPhase (φ - 1 / 2) U = τ.imPhase φ U * τ.imPhase (φ - 1 / 2) V →
        ∃ f : V ⟶ U, f ≫ i = j) := by
  -- `ψ₁` is within `ε` of `φ`
  have hψ₁ : |ψ₁ - φ| < ε := by
    have h := (hclose U hU0).1
    rwa [(τ.slicing.phiPlus_eq_phiMinus_of_semistable hU0 hUτ).1,
      (σ.slicing.phiPlus_eq_phiMinus_of_semistable hU0 hUσ).1] at h
  obtain ⟨hψ₁l, hψ₁r⟩ := abs_lt.mp hψ₁
  -- the charge of `U`
  obtain ⟨mU, hmU, hZU⟩ := τ.compat ψ₁ U hUτ hU0
  have hdegU := τ.imPhase_of_charge_eq φ hZU
  have hrkU := τ.imPhase_sub_half_of_charge_eq (φ := φ) hZU
  -- `B`, hence `V`, has `τ`-phases at most `ψ₁`
  have hBle : τ.slicing.leProp C ψ₁ B := τ.slicing.leProp_ext₂ hT
    (τ.slicing.leProp_of_semistable C hUτ le_rfl) (τ.slicing.leProp_of_ltProp C _ hQτ)
  have hQ'1 : τ.slicing.leProp C ψ₁ (Q'⟦(-1 : ℤ)⟧) := by
    have h1 : σ.slicing.P (φ + ((-1 : ℤ) : ℝ)) (Q'⟦(-1 : ℤ)⟧) :=
      (σ.slicing.shift_int C φ Q' (-1)).mp hQ'σ
    have h2 := hclose.ltProp_of_leProp (σ.slicing.leProp_of_semistable C h1 le_rfl)
    exact τ.slicing.leProp_mono C (by push_cast; linarith) _
      (τ.slicing.leProp_of_ltProp C _ h2)
  have hVle : τ.slicing.leProp C ψ₁ V := by
    refine τ.slicing.leProp_iff_hom_eq_zero.2 fun X hX g => ?_
    have hg : g ≫ j = 0 := τ.slicing.hom_eq_zero_of_gtProp_leProp hX hBle _
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ (Triangle.mk j q δ').invRotate
      (inv_rot_of_distTriang _ hT') g hg
    rw [hy, τ.slicing.hom_eq_zero_of_gtProp_leProp hX hQ'1 y]
    exact zero_comp
  -- the case `V = 0`
  by_cases hV0 : IsZero V
  · refine ⟨by simp [τ.imPhase_isZero _ hV0], fun _ => ⟨0, hV0.eq_of_src _ _⟩⟩
  -- the `τ`-phases of `V` lie in `(φ - ε, ψ₁]`
  have hVgt : τ.slicing.gtProp C (φ - ε) V :=
    hclose.gtProp_of_geProp (σ.slicing.geProp_of_semistable C hVσ)
  obtain ⟨F, hn, -, hlast, -, hm, hb⟩ := τ.slicing.exists_hn_phase_bounds hV0
  have hphase : ∀ k, φ - ε < F.φ k ∧ F.φ k ≤ ψ₁ := fun k =>
    ⟨(τ.slicing.lt_phiMinus_of_gtProp hV0 hVgt).trans_le (hb k).1,
      (hb k).2.trans (τ.slicing.phiPlus_le_of_leProp hV0 hVle)⟩
  -- one term per HN factor
  set t : Fin F.n → ℝ := fun k => τ.imPhase φ (F.factor k) * τ.imPhase (φ - 1 / 2) U -
    τ.imPhase φ U * τ.imPhase (φ - 1 / 2) (F.factor k) with ht
  have hterm : ∀ k, (¬IsZero (F.factor k) → ∃ m : ℝ, 0 < m ∧
      t k = m * mU * Real.sin (Real.pi * (F.φ k - ψ₁))) ∧
      (IsZero (F.factor k) → t k = 0) := fun k => by
    refine ⟨fun hk => ?_, fun hk => by simp [ht, τ.imPhase_isZero _ hk]⟩
    obtain ⟨m, hm0, hZ⟩ := τ.compat (F.φ k) _ (F.semistable k) hk
    refine ⟨m, hm0, ?_⟩
    rw [ht]
    simp only
    rw [τ.imPhase_of_charge_eq φ hZ, τ.imPhase_sub_half_of_charge_eq (φ := φ) hZ, hdegU, hrkU,
      show Real.pi * (F.φ k - ψ₁) = Real.pi * (F.φ k - φ) - Real.pi * (ψ₁ - φ) by ring,
      Real.sin_sub]
    ring
  have hnonpos : ∀ k, t k ≤ 0 := fun k => by
    by_cases hk : IsZero (F.factor k)
    · rw [(hterm k).2 hk]
    obtain ⟨m, hm0, hk'⟩ := (hterm k).1 hk
    rw [hk']
    have hs : Real.sin (Real.pi * (F.φ k - ψ₁)) ≤ 0 := by
      apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
      · nlinarith [Real.pi_pos, (hphase k).2]
      · nlinarith [Real.pi_pos, (hphase k).1]
    have := mul_pos hm0 hmU
    nlinarith
  have hsum : ∑ k, t k = τ.imPhase φ V * τ.imPhase (φ - 1 / 2) U -
      τ.imPhase φ U * τ.imPhase (φ - 1 / 2) V := by
    rw [τ.imPhase_eq_sum φ F, τ.imPhase_eq_sum (φ - 1 / 2) F, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
  refine ⟨by linarith [Finset.sum_nonpos fun k (_ : k ∈ Finset.univ) => hnonpos k], fun heq => ?_⟩
  -- equality: the last `τ`-HN factor of `V` has phase `ψ₁`, so `V` has phases at least `ψ₁`
  have hzero : ∀ k, t k = 0 :=
    fun k => (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hnonpos k).mp
      (by rw [hsum]; linarith) k (Finset.mem_univ k)
  obtain ⟨m, hm0, hk'⟩ := (hterm _).1 hlast
  have hsin : Real.sin (Real.pi * (F.φ ⟨F.n - 1, by omega⟩ - ψ₁)) = 0 := by
    have := hzero ⟨F.n - 1, by omega⟩
    rw [hk'] at this
    have := mul_pos hm0 hmU
    rcases mul_eq_zero.mp (by linarith : m * mU * Real.sin _ = 0) with h | h
    · linarith
    · exact h
  have hl := hphase ⟨F.n - 1, by omega⟩
  have h0 := (Real.sin_eq_zero_iff_of_lt_of_lt (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])).mp hsin
  have hlastφ : F.φ ⟨F.n - 1, by omega⟩ = ψ₁ := by
    have := (mul_eq_zero.mp h0).resolve_left Real.pi_ne_zero
    linarith
  have hVge : τ.slicing.geProp C ψ₁ V :=
    τ.slicing.geProp_of_le_phiMinus hV0 (by rw [← hm, hlastφ])
  obtain ⟨f, hf⟩ := Triangle.coyoneda_exact₂ _ hT j
    (τ.slicing.hom_eq_zero_of_geProp_ltProp hVge hQτ _)
  exact ⟨f, hf.symm⟩

omit [IsTriangulated C] in
/-- The intrinsic phases of a nonzero object with `τ`-phases in `(φ - ε, φ + ε)` move by less than
`2ε` away from `φ` in one short step. -/
theorem abs_phi_sub_lt_of_mem_interval (hclose : σ.slicing.PhaseClose τ.slicing ε) {X : C}
    (hX0 : ¬IsZero X) (h₁ : τ.slicing.gtProp C (φ - ε) X) (h₂ : τ.slicing.ltProp C (φ + ε) X) :
    |σ.slicing.phiPlus C X hX0 - φ| < 2 * ε ∧ |σ.slicing.phiMinus C X hX0 - φ| < 2 * ε := by
  obtain ⟨hp, hm⟩ := hclose X hX0
  have a₁ := τ.slicing.lt_phiMinus_of_gtProp hX0 h₁
  have a₂ := τ.slicing.phiPlus_lt_of_ltProp hX0 h₂
  have a₃ := τ.slicing.phiMinus_le_phiPlus C X hX0
  rw [abs_lt] at hp hm ⊢
  rw [abs_lt]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **The greedy rule under a phase gap.** In one short step from `σ` (`ε ≤ 1/8`) with a phase gap
of `σ` at `φ` below `2M`, the first step `U → B → Q` of the `τ`-HN filtration of `B ∈ P_σ(φ)`,
`|Z_σ(B)| ≤ M`, lies in `P_σ(φ)`, and `U` is the greatest maximizer of the `τ`-phase among the
subobjects of `B` in `P_σ(φ)`. -/
theorem greedy_rule_of_isPhaseGap {M : ℝ} (hε : ε ≤ 1 / 8)
    (hclose : σ.slicing.PhaseClose τ.slicing ε)
    (hστ : ∀ E, σ.mass E ≤ Real.exp ε * τ.mass E) (hτσ : ∀ E, τ.mass E ≤ Real.exp ε * σ.mass E)
    (hgap : σ.IsPhaseGap φ (2 * M) ε) {B : C} (hB : σ.slicing.P φ B) (hBM : ‖σ.charge B‖ ≤ M)
    {ψ₁ : ℝ} {U Q : C} {i : U ⟶ B} {p : B ⟶ Q} {δ : Q ⟶ U⟦(1 : ℤ)⟧}
    (hT : Triangle.mk i p δ ∈ distTriang C) (hUτ : τ.slicing.P ψ₁ U) (hU0 : ¬IsZero U)
    (hQτ : τ.slicing.ltProp C ψ₁ Q) :
    σ.slicing.P φ U ∧ σ.slicing.P φ Q ∧
      ∀ ⦃V Q' : C⦄ {j : V ⟶ B} {q : B ⟶ Q'} {δ' : Q' ⟶ V⟦(1 : ℤ)⟧},
        Triangle.mk j q δ' ∈ distTriang C → σ.slicing.P φ V → σ.slicing.P φ Q' →
        τ.imPhase φ V * τ.imPhase (φ - 1 / 2) U ≤ τ.imPhase φ U * τ.imPhase (φ - 1 / 2) V ∧
          (τ.imPhase φ V * τ.imPhase (φ - 1 / 2) U =
              τ.imPhase φ U * τ.imPhase (φ - 1 / 2) V → ∃ f : V ⟶ U, f ≫ i = j) := by
  -- `B` has phases at most `ψ₁`, and `ψ₁` is its top phase
  have hBle : τ.slicing.leProp C ψ₁ B := τ.slicing.leProp_ext₂ hT
    (τ.slicing.leProp_of_semistable C hUτ le_rfl) (τ.slicing.leProp_of_ltProp C _ hQτ)
  have hUplus := (τ.slicing.phiPlus_eq_phiMinus_of_semistable hU0 hUτ).1
  have hBnlt : ¬τ.slicing.ltProp C ψ₁ B := fun hBlt => by
    have hUlt : τ.slicing.ltProp C ψ₁ U := τ.slicing.ltProp_ext₂ (inv_rot_of_distTriang _ hT)
      (τ.slicing.ltProp_shift_neg_one hQτ) hBlt
    have := τ.slicing.phiPlus_lt_of_ltProp hU0 hUlt
    rw [hUplus] at this
    exact lt_irrefl _ this
  have hB0 : ¬IsZero B := fun h => hBnlt (τ.slicing.ltProp_of_isZero C h ψ₁)
  have htop : τ.slicing.phiPlus C B hB0 = ψ₁ := by
    refine le_antisymm (τ.slicing.phiPlus_le_of_leProp hB0 hBle) ?_
    by_contra hlt
    push Not at hlt
    exact hBnlt (τ.slicing.ltProp_of_phiPlus_lt hB0 hlt)
  -- so `ψ₁` is within `ε` of `φ`
  have hψ₁ : |ψ₁ - φ| < ε := by
    have h := (hclose B hB0).1
    rwa [htop, (σ.slicing.phiPlus_eq_phiMinus_of_semistable hB0 hB).1] at h
  obtain ⟨hψl, hψr⟩ := abs_lt.mp hψ₁
  -- the mass splits along the cut
  obtain ⟨t, ht, hQt⟩ : ∃ t, t < ψ₁ ∧ τ.slicing.leProp C t Q := by
    by_cases hQ0 : IsZero Q
    · exact ⟨ψ₁ - 1, by linarith, τ.slicing.leProp_of_isZero C hQ0 _⟩
    · exact ⟨τ.slicing.phiPlus C Q hQ0, τ.slicing.phiPlus_lt_of_ltProp hQ0 hQτ,
        τ.slicing.leProp_of_phiPlus_le hQ0 le_rfl⟩
  have hsplit := τ.mass_eq_add_of_triangle hT (τ.slicing.gtProp_of_semistable C hUτ ht) hQt
  have hmU : τ.mass U ≤ τ.mass B := by linarith [τ.mass_nonneg Q]
  have hmQ : τ.mass Q ≤ τ.mass B := by linarith [τ.mass_nonneg U]
  -- `U` lies in `P_σ(φ)`
  have hUσ : σ.slicing.P φ U := by
    obtain ⟨hp, hm⟩ := σ.abs_phi_sub_lt_of_phaseClose τ hclose hUτ hU0 hψ₁
    exact σ.semistable_of_isPhaseGap hgap hU0
      ((σ.mass_lt_of_mass_le τ hε hστ hτσ hB hB0 hmU).trans_le (by linarith)) hp hm
  -- `Q` lies in `P_σ(φ)`
  have hQσ : σ.slicing.P φ Q := by
    by_cases hQ0 : IsZero Q
    · exact σ.slicing.zero_mem_of_isZero C φ _ hQ0
    have hBgt : τ.slicing.gtProp C (φ - ε) B :=
      hclose.gtProp_of_geProp (σ.slicing.geProp_of_semistable C hB)
    have hU1 : τ.slicing.gtProp C (φ - ε) (U⟦(1 : ℤ)⟧) :=
      τ.slicing.gtProp_shift_one (τ.slicing.gtProp_of_semistable C hUτ (by linarith))
    have hQgt : τ.slicing.gtProp C (φ - ε) Q :=
      τ.slicing.gtProp_ext₂ (rot_of_distTriang _ hT) hBgt hU1
    have hQlt : τ.slicing.ltProp C (φ + ε) Q :=
      τ.slicing.ltProp_mono C (by linarith : ψ₁ ≤ φ + ε) _ hQτ
    obtain ⟨hp, hm⟩ := σ.abs_phi_sub_lt_of_mem_interval τ hclose hQ0 hQgt hQlt
    exact σ.semistable_of_isPhaseGap hgap hQ0
      ((σ.mass_lt_of_mass_le τ hε hστ hτσ hB hB0 hmQ).trans_le (by linarith)) hp hm
  exact ⟨hUσ, hQσ, fun V Q' j q δ' hT' hV hQ' =>
    σ.greedy_rule τ (by linarith) hclose hT hUτ hU0 hQτ hUσ hT' hV hQ'⟩

end Greedy

/-! ### (b) The rotated charge on the subobjects of `B` in `P_σ(φ)` -/

section Subobjects

variable [IsTriangulated C] (σ τ : WithClassMap C v) {ε φ : ℝ}

/-- `B ∈ P_σ(φ)` as an object of the heart `P_σ((φ - 1, φ])`. -/
def heartObj {B : C} (hB : σ.slicing.P φ B) : σ.slicing.HeartCat C (φ - 1) :=
  ⟨B, σ.slicing.heartProp_of_semistable C hB (by linarith) (by linarith)⟩

omit [IsTriangulated C] in
/-- `P_σ(φ)` as the top class of the heart `P_σ((φ - 1, φ])`. -/
lemma heartTop_iff {X : σ.slicing.HeartCat C (φ - 1)} :
    σ.slicing.heartTop C (φ - 1) X ↔ σ.slicing.P φ X.obj := by
  change σ.slicing.P (φ - 1 + 1) X.obj ↔ _
  rw [sub_add_cancel]

/-- **Every subquotient of `B` in the heart lies in `P_σ(φ)`**: `P_σ(φ)` is a Serre class of the
heart `P_σ((φ - 1, φ])` (`isSerreClass_heartTop`). -/
theorem semistable_cokernel_ofLE {B : C} (hB : σ.slicing.P φ B)
    {A A' : Subobject (σ.heartObj hB)} (h : A ≤ A') :
    σ.slicing.P φ (cokernel (Subobject.ofLE A A' h)).obj := by
  have := σ.isSerreClass_heartTop (φ - 1)
  have hB' : σ.slicing.heartTop C (φ - 1) (σ.heartObj hB) := (σ.heartTop_iff).mpr hB
  have hA' := (σ.slicing.heartTop C (φ - 1)).prop_of_mono A'.arrow hB'
  exact (σ.heartTop_iff).mp ((σ.slicing.heartTop C (φ - 1)).prop_of_epi (cokernel.π _) hA')

/-- `Im(e^{-iπθ} Z_τ)` is additive on the short exact sequences of the heart. -/
theorem imPhase_shortExact (θ : ℝ) {a : ℝ} {S : ShortComplex (σ.slicing.HeartCat C a)}
    (hS : S.ShortExact) : τ.imPhase θ S.X₂.obj = τ.imPhase θ S.X₁.obj + τ.imPhase θ S.X₃.obj := by
  have h := Slicing.HeartCat.K₀_of_shortExact C hS
  simp only [imPhase, charge_def, classOf, h, map_add, mul_add, Complex.add_im]

omit [IsTriangulated C] in
/-- **Positive rank in one short step.** A nonzero object of `P_σ(φ)` has `Re(e^{-iπφ} Z_τ) > 0`
when the slicings are `ε`-close with `ε ≤ 1/2`: its `τ`-phases lie in `(φ - 1/2, φ + 1/2)`. -/
theorem imPhase_sub_half_pos (hε : ε ≤ 1 / 2) (hclose : σ.slicing.PhaseClose τ.slicing ε)
    {X : C} (hX : σ.slicing.P φ X) (hX0 : ¬IsZero X) : 0 < τ.imPhase (φ - 1 / 2) X := by
  have h₁ : τ.slicing.gtProp C (φ - ε) X :=
    hclose.gtProp_of_geProp (σ.slicing.geProp_of_semistable C hX)
  have h₂ : τ.slicing.ltProp C (φ + ε) X :=
    hclose.ltProp_of_leProp (σ.slicing.leProp_of_semistable C hX le_rfl)
  exact τ.imPhase_pos hX0 (τ.slicing.gtProp_anti C (by linarith) _ h₁)
    (τ.slicing.ltProp_mono C (by linarith) _ h₂)

/-- **The rotated charge function** on the subobjects of `B ∈ P_σ(φ)` in the heart
`P_σ((φ - 1, φ])`: `rk = Re(e^{-iπφ} Z_τ)` and `deg = Im(e^{-iπφ} Z_τ)`, for `ε`-close slicings with
`ε ≤ 1/2`. Every subquotient lies in `P_σ(φ)`, where the rank is positive, so the rank strictly
increases along every strict inclusion: there is no vertical edge. -/
def rotatedChargeFunction (hε : ε ≤ 1 / 2) (hclose : σ.slicing.PhaseClose τ.slicing ε) {B : C}
    (hB : σ.slicing.P φ B) : Order.ChargeFunction (Subobject (σ.heartObj hB)) ℝ where
  rk A := τ.imPhase (φ - 1 / 2) (A : σ.slicing.HeartCat C (φ - 1)).obj
  deg A := τ.imPhase φ (A : σ.slicing.HeartCat C (φ - 1)).obj
  lex_lt {A A'} h := by
    left
    have h1 := Subobject.additive_cokernel_ofLE
      (Z := fun X : σ.slicing.HeartCat C (φ - 1) => τ.imPhase (φ - 1 / 2) X.obj)
      (fun _ hS => σ.imPhase_shortExact τ _ hS) h.le
    have hQ : ¬IsZero (cokernel (Subobject.ofLE A A' h.le)).obj := fun hz =>
      h.ne (Subobject.eq_of_le_of_isZero_cokernel h.le (Slicing.HeartCat.isZero_of_obj_isZero C hz))
    have := σ.imPhase_sub_half_pos τ hε hclose (σ.semistable_cokernel_ofLE hB h.le) hQ
    linarith
  rk_sup_add_inf := Subobject.additive_sup_add_inf
    (Z := fun X : σ.slicing.HeartCat C (φ - 1) => τ.imPhase (φ - 1 / 2) X.obj)
    (fun _ hS => σ.imPhase_shortExact τ _ hS)
  deg_sup_add_inf := Subobject.additive_sup_add_inf
    (Z := fun X : σ.slicing.HeartCat C (φ - 1) => τ.imPhase φ X.obj)
    (fun _ hS => σ.imPhase_shortExact τ _ hS)

/-- **No vertical edge**: the rank of the rotated charge function strictly increases along every
strict inclusion of subobjects of `B`. -/
theorem rotatedChargeFunction_rk_lt (hε : ε ≤ 1 / 2) (hclose : σ.slicing.PhaseClose τ.slicing ε)
    {B : C} (hB : σ.slicing.P φ B) {A A' : Subobject (σ.heartObj hB)} (h : A < A') :
    (σ.rotatedChargeFunction τ hε hclose hB).rk A <
      (σ.rotatedChargeFunction τ hε hclose hB).rk A' := by
  rcases (σ.rotatedChargeFunction τ hε hclose hB).lex_lt h with h' | ⟨h', -⟩
  · exact h'
  · have h1 := Subobject.additive_cokernel_ofLE
      (Z := fun X : σ.slicing.HeartCat C (φ - 1) => τ.imPhase (φ - 1 / 2) X.obj)
      (fun _ hS => σ.imPhase_shortExact τ _ hS) h.le
    have hQ : ¬IsZero (cokernel (Subobject.ofLE A A' h.le)).obj := fun hz =>
      h.ne (Subobject.eq_of_le_of_isZero_cokernel h.le (Slicing.HeartCat.isZero_of_obj_isZero C hz))
    have := σ.imPhase_sub_half_pos τ hε hclose (σ.semistable_cokernel_ofLE hB h.le) hQ
    change τ.imPhase (φ - 1 / 2) (A : σ.slicing.HeartCat C (φ - 1)).obj =
      τ.imPhase (φ - 1 / 2) (A' : σ.slicing.HeartCat C (φ - 1)).obj at h'
    linarith

/-- **The HN filtration of the subobjects of `B` for the rotated charge exists** from the ascending
chain condition on the subobjects of `B` in the heart and an attained maximal phase
(`Order.ChargeFunction.nonempty_hnFiltration`); it is unique. Finiteness of the range of the charge
is not assumed. -/
theorem nonempty_hnFiltration_rotatedChargeFunction (hε : ε ≤ 1 / 2)
    (hclose : σ.slicing.PhaseClose τ.slicing ε) {B : C} (hB : σ.slicing.P φ B)
    [IsNoetherianObject (σ.heartObj hB)]
    (hatt : (σ.rotatedChargeFunction τ hε hclose hB).MaxPhaseAttained) :
    Nonempty (σ.rotatedChargeFunction τ hε hclose hB).HNFiltration :=
  (σ.rotatedChargeFunction τ hε hclose hB).nonempty_hnFiltration hatt

end Subobjects

end PreStabilityCondition.WithClassMap

/-! ### In a space of stability conditions -/

namespace StabilitySpaceHypotheses

variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ} {Stab : Type*} [PseudoMetricSpace Stab]
  {Γ : Type*} [Group Γ] [MulAction Γ Stab] (I : StabilitySpaceHypotheses C v Stab Γ)

/-- **The τ-HN factors stay in `P_σ(φ)`, in a space of stability conditions.** For `d(σ, τ) < ε`
with `ε ≤ 1/8` and a phase gap of `σ` at `φ` below `2M`, every `B ∈ P_σ(φ)` with `|Z_σ(B)| ≤ M`
has a `τ`-HN filtration with all factors in `P_σ(φ)`. -/
theorem exists_hnFiltration_semistable_of_isPhaseGap {σ τ : Stab} {ε φ M : ℝ} (hε : ε ≤ 1 / 8)
    (hd : dist σ τ < ε) (hgap : (I.cond σ).IsPhaseGap φ (2 * M) ε) {B : C}
    (hB : (I.cond σ).slicing.P φ B) (hBM : ‖(I.cond σ).charge B‖ ≤ M) :
    ∃ F : HNFiltration C (I.cond τ).slicing.P B, ∀ j, (I.cond σ).slicing.P φ (F.factor j) := by
  have hle : Real.exp (dist σ τ) ≤ Real.exp ε := Real.exp_le_exp.mpr hd.le
  exact (I.cond σ).exists_hnFiltration_semistable_of_isPhaseGap (I.cond τ) hε
    (I.phaseClose_of_dist_lt hd)
    (fun E => (I.mass_le_exp_dist σ τ E).trans (mul_le_mul_of_nonneg_right hle
      ((I.cond τ).mass_nonneg E)))
    (fun E => (I.mass_le_exp_dist τ σ E).trans (by
      rw [dist_comm] at hle
      exact mul_le_mul_of_nonneg_right hle ((I.cond σ).mass_nonneg E)))
    hgap hB hBM

end StabilitySpaceHypotheses

end CategoryTheory.Triangulated
