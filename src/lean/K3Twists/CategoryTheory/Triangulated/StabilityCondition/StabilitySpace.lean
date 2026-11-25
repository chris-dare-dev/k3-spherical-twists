/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.SpecificLimits.GrowthRate
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Mass
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Slicing.HarderNarasimhan
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The stability-space interface

`StabilitySpaceHypotheses` packages a space of stability conditions as the later results use it:
an abstract metric space `Stab` whose points are prestability conditions on `C` with a class map
`v : K₀ C → Λ`, together with the facts about Bridgeland's space that the library does not prove.

* **Covering.** The map `σ ↦ Z_σ` to central charges is a covering map onto its image
  (Bridgeland, arXiv:math/0212237, Theorem 1.2; for a K3 surface the image of the distinguished
  component is the period domain `P₀⁺(X)`, Bridgeland, arXiv:math/0307164, Theorem 1.1).
* **Metric bound.** The intrinsic phases and the masses move by at most the distance:
  `|φ^±_σ(E) - φ^±_τ(E)| ≤ d(σ, τ)` and `m_σ(E) ≤ e^{d(σ, τ)} m_τ(E)` (these are the terms of
  Bridgeland's metric, arXiv:math/0212237, §8).
* **Support.** Each `σ` has a support constant `K`: `‖v(E)‖ ≤ K |Z_σ(E)|` for semistable `E`, for a
  norm `‖·‖` on `Λ` that vanishes only at `0` (Kontsevich–Soibelman, arXiv:0811.2435, §1.2).
* **Action.** A group `Γ` acts on `Stab` through exact autoequivalences of `C`: `g σ` has the
  slicing `Φ_g · P_σ` and charge `Z_{gσ}(Φ_g E) = Z_σ(E)`.
* **Ikeda subadditivity.** `m_σ(B) ≤ m_σ(A) + m_σ(C)` on every distinguished triangle (Ikeda,
  arXiv:1612.00995, Proposition 3.3).

The rest of the mass layer is proved for every prestability condition in
`StabilityCondition/Mass.lean`: invariance under isomorphisms and shifts, the split identity,
`m ≥ |Z|` and the `2m(D)` lemma. From the fields this file proves the invariance `m_{gσ}(Φ_g E) =
m_σ(E)` (`mass_smul`), the **path layer** (`exists_subdivision_phaseClose`: a continuous path
`[0, 1] → Stab` subdivides into steps whose slicings are `ε`-close, which is what the short-step
stability test needs) and the independence of exponential mass growth from the stability condition
(`tendsto_log_mass_div_iff`).

## Real objects

Mathlib has no triangulated category carrying a slicing: neither the derived category of a K3
surface with Bridgeland's stability conditions nor `D^b(Vect)` with its standard slicing. So no
field here has an instance from geometry, and none from other objects of the library either: every
field asks for a stability condition first. The missing input is the 2-Calabi–Yau category
`D^b(X)` of a K3 surface with its space `Stab†(X)`. The test `K3TwistsTest/StabilitySpaceModel.lean`
checks that the fields can hold together, relative to one prestability condition with injective
central charge and Ikeda subadditivity (the one-point space).

## Main definitions

* `StabilitySpaceHypotheses C v Stab Γ`: the stability-space interface.
* `PreStabilityCondition.WithClassMap.HasSupport σ ‖·‖ K`: the support property with constant
  `K`.

## Main results

* `StabilitySpaceHypotheses.mass_smul`: `m_{gσ}(Φ_g E) = m_σ(E)`.
* `StabilitySpaceHypotheses.phaseClose_of_dist_lt`: conditions at distance `< ε` have `ε`-close
  slicings.
* `StabilitySpaceHypotheses.exists_subdivision_phaseClose`: the path layer.
* `StabilitySpaceHypotheses.tendsto_log_mass_div_iff`: `log m_σ(E_n)/n` and `log m_τ(E_n)/n` have
  the same limits, for any objects `E_n`.
* `StabilitySpaceHypotheses.abs_sub_mass_cone_le`: the `2m(D)` lemma at every point.

## Tags

stability condition, space of stability conditions, mass, covering map
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Filter Topology
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

universe u v u'

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

namespace PreStabilityCondition.WithClassMap

/-- The **support property** with constant `K` for a function `N` on classes (a norm on `Λ ⊗ ℝ`):
`N(v(E)) ≤ K |Z(E)|` for every semistable `E`. -/
def HasSupport (σ : WithClassMap C v) (N : Λ → ℝ) (K : ℝ) : Prop :=
  ∀ (φ : ℝ) (E : C), σ.slicing.P φ E → N (classOf C v E) ≤ K * ‖σ.charge E‖

/-- The mass computed from an HN filtration for a slicing equal to that of `σ`. -/
theorem mass_eq_sum_of_slicing_eq (σ : WithClassMap C v) {s : Slicing C} (hs : σ.slicing = s)
    {E : C} (F : HNFiltration C s.P E) : σ.mass E = ∑ i, ‖σ.charge (F.factor i)‖ := by
  subst hs
  exact σ.mass_eq_sum F

end PreStabilityCondition.WithClassMap

variable (C v) in
/-- **A space of stability conditions.** `Stab` is a metric space of prestability
conditions on `C` with class map `v`, and `Γ` a group acting on it through exact
autoequivalences. The fields are the facts about Bridgeland's space used downstream; see the
module docstring for their sources. -/
structure StabilitySpaceHypotheses (Stab : Type*) [PseudoMetricSpace Stab] (Γ : Type*) [Group Γ]
    [MulAction Γ Stab] where
  /-- The prestability condition at a point of the space. -/
  cond : Stab → PreStabilityCondition.WithClassMap C v
  /-- The map to central charges is a covering map onto its image (Bridgeland,
  arXiv:math/0212237, Theorem 1.2; arXiv:math/0307164, Theorem 1.1 for the period domain of a K3
  surface). -/
  isCoveringMap_charge : IsCoveringMap (Set.rangeFactorization fun σ : Stab => ⇑(cond σ).Z)
  /-- The highest phase moves by at most the distance (Bridgeland, arXiv:math/0212237, §8). -/
  abs_phiPlus_sub_le : ∀ (σ τ : Stab) (E : C) (hE : ¬IsZero E),
    |(cond σ).slicing.phiPlus C E hE - (cond τ).slicing.phiPlus C E hE| ≤ dist σ τ
  /-- The lowest phase moves by at most the distance (Bridgeland, arXiv:math/0212237, §8). -/
  abs_phiMinus_sub_le : ∀ (σ τ : Stab) (E : C) (hE : ¬IsZero E),
    |(cond σ).slicing.phiMinus C E hE - (cond τ).slicing.phiMinus C E hE| ≤ dist σ τ
  /-- The mass changes by at most `e^{d(σ, τ)}` (Bridgeland, arXiv:math/0212237, §8;
  Ikeda, arXiv:1612.00995, Proposition 3.3 and §3). -/
  mass_le_exp_dist : ∀ (σ τ : Stab) (E : C),
    (cond σ).mass E ≤ Real.exp (dist σ τ) * (cond τ).mass E
  /-- A norm on the class lattice, used for the support property. -/
  classNorm : Λ → ℝ
  classNorm_pos : ∀ x : Λ, x ≠ 0 → 0 < classNorm x
  /-- The support property (Kontsevich–Soibelman, arXiv:0811.2435, §1.2). -/
  support : ∀ σ : Stab, ∃ K : ℝ, 0 < K ∧ (cond σ).HasSupport classNorm K
  /-- The exact autoequivalence through which `g` acts. -/
  tri : Γ → TriEquiv C
  /-- `g σ` has the slicing `Φ_g · P_σ`. -/
  slicing_smul : ∀ (g : Γ) (σ : Stab), (cond (g • σ)).slicing = (tri g).act (cond σ).slicing
  /-- `Z_{gσ}(Φ_g E) = Z_σ(E)`. -/
  charge_smul : ∀ (g : Γ) (σ : Stab) (E : C),
    (cond (g • σ)).charge ((tri g).e.functor.obj E) = (cond σ).charge E
  /-- Ikeda subadditivity (arXiv:1612.00995, Proposition 3.3). -/
  mass_subadditive : ∀ σ : Stab, (cond σ).MassSubadditive

namespace StabilitySpaceHypotheses

variable {Stab : Type*} [PseudoMetricSpace Stab] {Γ : Type*} [Group Γ] [MulAction Γ Stab]
  (I : StabilitySpaceHypotheses C v Stab Γ)

/-- **Equivariance of the mass**: `m_{gσ}(Φ_g E) = m_σ(E)`. -/
theorem mass_smul (g : Γ) (σ : Stab) (E : C) :
    (I.cond (g • σ)).mass ((I.tri g).e.functor.obj E) = (I.cond σ).mass E := by
  obtain ⟨F⟩ := (I.cond σ).slicing.hn_exists E
  rw [(I.cond (g • σ)).mass_eq_sum_of_slicing_eq (I.slicing_smul g σ) ((I.tri g).mapHN F),
    (I.cond σ).mass_eq_sum F]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TriEquiv.mapHN_factor, I.charge_smul]

/-- The mass is positive on nonzero objects at every point. -/
theorem mass_pos (σ : Stab) {E : C} (hE : ¬IsZero E) : 0 < (I.cond σ).mass E :=
  (I.cond σ).mass_pos hE

/-- `|log m_σ(E) - log m_τ(E)| ≤ d(σ, τ)` for nonzero `E`. -/
theorem abs_log_mass_sub_le (σ τ : Stab) {E : C} (hE : ¬IsZero E) :
    |Real.log ((I.cond σ).mass E) - Real.log ((I.cond τ).mass E)| ≤ dist σ τ := by
  have h₁ := I.mass_le_exp_dist σ τ E
  have h₂ := I.mass_le_exp_dist τ σ E
  have hσ := I.mass_pos σ hE
  have hτ := I.mass_pos τ hE
  have l₁ := Real.log_le_log hσ h₁
  have l₂ := Real.log_le_log hτ h₂
  rw [Real.log_mul (Real.exp_pos _).ne' hτ.ne', Real.log_exp] at l₁
  rw [Real.log_mul (Real.exp_pos _).ne' hσ.ne', Real.log_exp, dist_comm] at l₂
  rw [abs_le]
  constructor <;> linarith

/-- **σ-independence of mass growth.** For any objects `E_n`, nonzero, `log m_σ(E_n)/n → η` if and
only if `log m_τ(E_n)/n → η`: the two differ by at most `d(σ, τ)/n`. -/
theorem tendsto_log_mass_div_iff (σ τ : Stab) (E : ℕ → C) (hE : ∀ n, ¬IsZero (E n)) (η : ℝ) :
    Tendsto (fun n : ℕ => Real.log ((I.cond σ).mass (E n)) / n) atTop (𝓝 η) ↔
      Tendsto (fun n : ℕ => Real.log ((I.cond τ).mass (E n)) / n) atTop (𝓝 η) := by
  have he : Tendsto (fun n : ℕ => dist σ τ / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  constructor
  · intro h
    exact Real.tendsto_log_div_of_bound (fun n => by
      rw [dist_comm]; exact I.abs_log_mass_sub_le τ σ (hE n)) he h
  · intro h
    exact Real.tendsto_log_div_of_bound (fun n => I.abs_log_mass_sub_le σ τ (hE n)) he h

/-- Conditions at distance less than `ε` have `ε`-close slicings. -/
theorem phaseClose_of_dist_lt {σ τ : Stab} {ε : ℝ} (h : dist σ τ < ε) :
    (I.cond σ).slicing.PhaseClose (I.cond τ).slicing ε := fun E hE =>
  ⟨by rw [abs_sub_comm]; exact (I.abs_phiPlus_sub_le σ τ E hE).trans_lt h,
    by rw [abs_sub_comm]; exact (I.abs_phiMinus_sub_le σ τ E hE).trans_lt h⟩

/-- **The path layer.** A path `γ : [0, 1] → Stab`, continuous on `[0, 1]`, subdivides into `N`
steps `γ(k/N) → γ((k+1)/N)` whose slicings are `ε`-close, for any `ε > 0`: Heine–Cantor and the
metric bound. With `ε ≤ 1/4` this is the input of the short-step stability test along the path. -/
theorem exists_subdivision_phaseClose (γ : ℝ → Stab) (hγ : ContinuousOn γ (Set.Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ k < N,
      (I.cond (γ (k / N))).slicing.PhaseClose (I.cond (γ ((k + 1) / N))).slicing ε := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hγ
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hδu⟩ := hu ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  refine ⟨N, by exact_mod_cast hNpos, fun k hk => I.phaseClose_of_dist_lt ?_⟩
  have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  refine hδu _ ⟨by positivity, ?_⟩ _ ⟨by positivity, ?_⟩ ?_
  · rw [div_le_one hNpos]; linarith
  · rw [div_le_one hNpos]; linarith
  · rw [Real.dist_eq, show (k : ℝ) / N - (k + 1) / N = -(1 / N) by ring, abs_neg,
      abs_of_pos (by positivity)]
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ] at hN
    linarith

/-- **The `2m(D)` lemma** at every point of the space. -/
theorem abs_sub_mass_cone_le [IsTriangulated C] (σ : Stab) {A B D K K' : C} {f f' : A ⟶ B}
    (a : A ⟶ D) (b : D ⟶ B) (hf : f' = f + a ≫ b) {g : B ⟶ K} {h : K ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) {g' : B ⟶ K'} {h' : K' ⟶ A⟦(1 : ℤ)⟧}
    (hT' : Triangle.mk f' g' h' ∈ distTriang C) :
    |(I.cond σ).mass K - (I.cond σ).mass K'| ≤ 2 * (I.cond σ).mass D :=
  (I.cond σ).abs_sub_mass_cone_le (I.mass_subadditive σ) a b hf hT hT'

end StabilitySpaceHypotheses

end CategoryTheory.Triangulated
