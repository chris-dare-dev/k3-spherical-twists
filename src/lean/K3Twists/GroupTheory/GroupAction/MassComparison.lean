/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.GroupAction.TwistSystem

/-!
# Mass comparison: the mass form of the twist-system exponent theorem

`HomTwistSystem₀` proves the exponent theorem for the counts `h(S_i, W S_j)` between centres. Its
mass form, for the masses `m_σ(W S_j)` under a stability condition, needs a comparison between
masses and counts. This file states that comparison as a list of inputs,
`MassComparisonHypotheses`, and proves from it:

* the **lower comparison** `h(G, V) ≤ L_σ m_σ(V)` for the split generator `G = ⊕ S_k`
  (`hom_G_le_mul_mass`): from the twist triangle of each summand `S_k`, Ikeda subadditivity
  (arXiv:1612.00995, Proposition 3.3), equivariance and the distance bound,
  `h(S_k, V) m_σ(S_k) ≤ m_σ(V) + m_σ(T_{S_k} V) ≤ (1 + e^{δ(T_{S_k}^{-1} σ, σ)}) m_σ(V)`;
* the **comparison** `h(U, V) ≤ c_U(σ) m_σ(V)` for every object `U` (`hom_le_mul_mass`): the
  diagonal estimate `h(U, V) ≤ K h(U, G) h(G, V)` places `U` in the thick subcategory of `G`, and
  the lower comparison finishes;
* the **upper comparison** `m_σ(U) ≤ (m_σ(G)/C₁) h(G, U)` is the input `dhkk_comparison`:
  Ikeda (arXiv:1612.00995, Proposition 3.4) bounds the mass by `m_σ(G)` times the complexity
  `δ(G, U)`, and Dimitrov–Haiden–Katzarkov–Kontsevich (arXiv:1307.8418, eq. (9)) bound the
  complexity by `h(G, U)/C₁` with `C₁` independent of `σ`;
* the **uniform estimate** `e^{-δ(σ,τ)} h(G, V)/L_τ ≤ m_σ(V) ≤ e^{δ(σ,τ)} (m_τ(G)/C₁) h(G, V)`
  for every nonnegative symmetric bound `δ` with `m_σ ≤ e^{δ(σ, τ)} m_τ` (`uniform_estimate`);
* **categorical entropy** `h_cat(Φ) = lim log h(G, Φⁿ G)/n` exists by the diagonal estimate and
  Fekete's lemma (`tendsto_hcat`); by DHKK (arXiv:1307.8418, Theorem 2.6, whose input is their
  eq. (9)) it is the categorical entropy at `t = 0`;
* the **mass domination system** (`toDomination`): the masses `m_σ(-)`, one test for each `σ`,
  pulled back along a letter by `σ ↦ T_a^{-1} σ`, satisfy the domination recursion of
  `DominationSystem`;
* **the twist-system exponent theorem in mass form** (`tendsto_log_massMax`): for a twist
  system whose letters are twists (or inverse twists) along spherical centres and whose count is
  `h`, the masses `M_q(σ) = max m_σ(W S_j)` over `|W| ≤ q` have exponent `lim log M_N/N = η`, the
  exponent of the centre counts, at every `σ`. The two directions are `P_q ≤ A_σ M_q` from the
  comparison and `M_q ≤ m_σ(⊕ S_i)(1 + q P_q)` from the mass form of the one-letter bound;
* **σ-independence** of exponential mass growth along any sequence of objects
  (`MassDistanceBound.tendsto_log_mass_div_iff`).

## Main definitions

* `MassDistanceBound Stab Obj`: masses at the points of `Stab`, with a nonnegative symmetric `δ`
  and `m_σ ≤ e^{δ(σ, τ)} m_τ`. Bridgeland's metric is one `δ` (arXiv:math/0212237, §8).
* `MassComparisonHypotheses Obj Γ Stab κ`: the comparison inputs.
* `MassComparisonHypotheses.IsTwistSystem H`: the twist system `H` has spherical centres, its
  letters are the twists along them or their inverses, and its count is `h`.
* `MassComparisonHypotheses.massMax H σ q`: `M_q(σ)`.

## Implementation notes

As in `TwistSystem.lean`, objects are a type `Obj` with an action of a group `Γ` of
autoequivalences, standing for isomorphism classes of objects of a triangulated category; masses
and counts are functions on it. The twist along a spherical object is `twist E : Γ`, with the
conjugation formula `T_{gE} = g T_E g⁻¹` (Seidel–Thomas, arXiv:math/0001043, Lemma 2.11) and
`T_E V = V` when `h(E, V) = 0`. No field of this file has a geometric instance in the library: the
missing input is the 2-Calabi–Yau category `D^b(X)` of a K3 surface, with its twist functors and
stability conditions.

## Tags

mass, stability condition, spherical twist, categorical entropy, growth
-/

open Filter Topology Real Finset

/-! ### A distance bound on masses -/

/-- **Masses at the points of a space, with a distance bound.** `δ` is nonnegative and symmetric,
with `m_σ(U) ≤ e^{δ(σ, τ)} m_τ(U)`. Bridgeland's metric is one such bound
(arXiv:math/0212237, §8). -/
structure MassDistanceBound (Stab Obj : Type*) where
  /-- The mass `m_σ(U)`. -/
  mass : Stab → Obj → ℝ
  mass_nonneg : ∀ σ U, 0 ≤ mass σ U
  /-- The distance bound. -/
  δ : Stab → Stab → ℝ
  δ_nonneg : ∀ σ τ, 0 ≤ δ σ τ
  δ_symm : ∀ σ τ, δ σ τ = δ τ σ
  /-- `m_σ ≤ e^{δ(σ, τ)} m_τ`. -/
  mass_le_exp_δ : ∀ σ τ U, mass σ U ≤ exp (δ σ τ) * mass τ U

/-- Two positive sequences within a constant factor `e^D` of each other have the same exponential
rate. -/
theorem Real.tendsto_log_div_of_le_exp_mul {a b : ℕ → ℝ} {D : ℝ} (ha : ∀ n, 0 < a n)
    (hb : ∀ n, 0 < b n) (hab : ∀ n, a n ≤ exp D * b n) (hba : ∀ n, b n ≤ exp D * a n) {η : ℝ}
    (h : Tendsto (fun n : ℕ => log (a n) / n) atTop (𝓝 η)) :
    Tendsto (fun n : ℕ => log (b n) / n) atTop (𝓝 η) := by
  refine Real.tendsto_log_div_of_bound (e := fun _ => D) (fun n => ?_)
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop) h
  have l₁ := log_le_log (ha n) (hab n)
  have l₂ := log_le_log (hb n) (hba n)
  rw [log_mul (exp_pos _).ne' (hb n).ne', log_exp] at l₁
  rw [log_mul (exp_pos _).ne' (ha n).ne', log_exp] at l₂
  rw [abs_le]
  constructor <;> linarith

namespace MassDistanceBound

variable {Stab Obj : Type*} (B : MassDistanceBound Stab Obj)

theorem mass_pos_of_pos {σ τ : Stab} {U : Obj} (h : 0 < B.mass σ U) : 0 < B.mass τ U := by
  have := B.mass_le_exp_δ σ τ U
  by_contra hle
  have h0 : B.mass τ U = 0 := le_antisymm (not_lt.mp hle) (B.mass_nonneg τ U)
  rw [h0, mul_zero] at this
  linarith

/-- **σ-independence of mass growth.** For objects `E_n` of positive mass, `log m_σ(E_n)/n` and
`log m_τ(E_n)/n` have the same limits. -/
theorem tendsto_log_mass_div_iff (σ τ : Stab) (E : ℕ → Obj) (hE : ∀ n, 0 < B.mass σ (E n))
    (η : ℝ) :
    Tendsto (fun n : ℕ => log (B.mass σ (E n)) / n) atTop (𝓝 η) ↔
      Tendsto (fun n : ℕ => log (B.mass τ (E n)) / n) atTop (𝓝 η) := by
  have hE' : ∀ n, 0 < B.mass τ (E n) := fun n => B.mass_pos_of_pos (hE n)
  have h₁ : ∀ n, B.mass σ (E n) ≤ exp (B.δ σ τ) * B.mass τ (E n) := fun n => B.mass_le_exp_δ _ _ _
  have h₂ : ∀ n, B.mass τ (E n) ≤ exp (B.δ σ τ) * B.mass σ (E n) := fun n => by
    rw [B.δ_symm]; exact B.mass_le_exp_δ _ _ _
  exact ⟨Real.tendsto_log_div_of_le_exp_mul hE hE' h₁ h₂,
    Real.tendsto_log_div_of_le_exp_mul hE' hE h₂ h₁⟩

end MassDistanceBound

/-! ### The comparison inputs -/

/-- **The mass comparison inputs.** `Obj` stands for the isomorphism classes of objects of a
2-Calabi–Yau triangulated category (on a K3 surface, `D^b(X)`), `Γ` for a group of exact
autoequivalences acting on them and on the points `Stab` of a space of stability conditions, and
`G = ⊕_k S_k` for a split generator with spherical summands. `h(U, V)` is the total dimension of
`Ext^*(U, V)`. -/
structure MassComparisonHypotheses (Obj Γ Stab κ : Type*) [Group Γ] [MulAction Γ Obj]
    [MulAction Γ Stab] [Fintype κ] extends MassDistanceBound Stab Obj where
  /-- `h(U, V) = Σ_j dim Hom(U, V[j])`. -/
  hom : Obj → Obj → ℝ
  hom_nonneg : ∀ U V, 0 ≤ hom U V
  /-- Serre duality in a 2-Calabi–Yau category: `Hom(U, V[j]) ≅ Hom(V, U[2 - j])^*`. -/
  hom_comm : ∀ U V, hom U V = hom V U
  /-- An autoequivalence preserves graded Hom spaces. -/
  hom_smul : ∀ (g : Γ) (U V : Obj), hom (g • U) (g • V) = hom U V
  /-- The action on stability conditions: `m_{gσ}(gU) = m_σ(U)`. -/
  mass_smul : ∀ (g : Γ) σ U, mass (g • σ) (g • U) = mass σ U
  /-- The split generator `G = ⊕_k S_k`. -/
  G : Obj
  /-- The summands of the split generator. -/
  S : κ → Obj
  /-- Total Hom is additive on `G = ⊕_k S_k`. -/
  hom_G : ∀ V, hom G V = ∑ k, hom (S k) V
  /-- The constant of the diagonal estimate. -/
  K : ℝ
  K_pos : 0 < K
  /-- The diagonal estimate `h(U, V) ≤ K h(U, G) h(G, V)`, from Orlov's generation theorem
  (arXiv:0804.1163, Theorem 4) for the diagonal of `X × X`. -/
  hom_diag : ∀ U V, hom U V ≤ K * hom U G * hom G V
  /-- `W G ≠ 0`, so its total Hom from `G` is at least one. -/
  one_le_hom_G : ∀ W : Γ, 1 ≤ hom G (W • G)
  /-- Spherical objects. -/
  Spherical : Obj → Prop
  spherical_S : ∀ k, Spherical (S k)
  /-- Autoequivalences preserve sphericity. -/
  spherical_smul : ∀ (g : Γ) U, Spherical U → Spherical (g • U)
  /-- The class of the spherical twist `T_E`. -/
  twist : Obj → Γ
  /-- `T_{gE} = g T_E g⁻¹` (Seidel–Thomas, arXiv:math/0001043, Lemma 2.11). -/
  twist_conj : ∀ (g : Γ) E, Spherical E → twist (g • E) = g * twist E * g⁻¹
  /-- `T_E V = V` when `Ext^*(E, V) = 0`: the twist triangle `Ext^*(E, V) ⊗ E → V → T_E V`. -/
  twist_smul_of_hom_eq_zero : ∀ E V, Spherical E → hom E V = 0 → twist E • V = V
  /-- (U_m): `m_σ(T_E V) ≤ m_σ(V) + h(E, V) m_σ(E)`, from the twist triangle and Ikeda
  subadditivity (arXiv:1612.00995, Proposition 3.3). -/
  mass_twist_le : ∀ σ E V, Spherical E → mass σ (twist E • V) ≤ mass σ V + hom E V * mass σ E
  /-- (U_m) for the inverse twist: `m_σ(T_E⁻¹ V) ≤ m_σ(V) + h(V, E) m_σ(E)`, from the triangle
  `T_E⁻¹ V → V → Ext^*(V, E)^* ⊗ E`. -/
  mass_twist_inv_le : ∀ σ E V, Spherical E →
    mass σ ((twist E)⁻¹ • V) ≤ mass σ V + hom V E * mass σ E
  /-- (L_m): `h(E, V) m_σ(E) ≤ m_σ(V) + m_σ(T_E V)`, from the rotated twist triangle and Ikeda
  subadditivity. -/
  hom_mul_mass_le : ∀ σ E V, Spherical E → hom E V * mass σ E ≤ mass σ V + mass σ (twist E • V)
  /-- Spherical objects are nonzero, so their mass is positive. -/
  mass_pos_of_spherical : ∀ σ E, Spherical E → 0 < mass σ E
  /-- The constant of the upper comparison, independent of `σ`. -/
  C₁ : ℝ
  C₁_pos : 0 < C₁
  /-- **The upper comparison** `C₁ m_σ(U) ≤ m_σ(G) h(G, U)`: Ikeda (arXiv:1612.00995,
  Proposition 3.4) gives `m_σ(U) ≤ m_σ(G) δ(G, U)` for the complexity `δ(G, U)`, and
  Dimitrov–Haiden–Katzarkov–Kontsevich (arXiv:1307.8418, eq. (9)) give `C₁ δ(G, U) ≤ h(G, U)`. -/
  dhkk_comparison : ∀ σ U, C₁ * mass σ U ≤ mass σ G * hom G U

namespace MassComparisonHypotheses

variable {Obj Γ Stab κ : Type*} [Group Γ] [MulAction Γ Obj] [MulAction Γ Stab] [Fintype κ]
  (I : MassComparisonHypotheses Obj Γ Stab κ)

/-! ### Moving autoequivalences -/

lemma mass_smul_eq (g : Γ) (σ : Stab) (U : Obj) : I.mass σ (g • U) = I.mass (g⁻¹ • σ) U := by
  rw [← I.mass_smul g (g⁻¹ • σ) U, smul_inv_smul]

lemma hom_smul_left (g : Γ) (U V : Obj) : I.hom (g • U) V = I.hom U (g⁻¹ • V) := by
  calc I.hom (g • U) V = I.hom (g • U) (g • (g⁻¹ • V)) := by rw [smul_inv_smul]
    _ = I.hom U (g⁻¹ • V) := I.hom_smul g U _

lemma hom_G_smul (g : Γ) (V : Obj) : I.hom I.G (g • V) = I.hom (g⁻¹ • I.G) V := by
  rw [I.hom_smul_left, inv_inv]

/-- `m_σ(gU) ≤ e^{δ(g⁻¹σ, σ)} m_σ(U)`: an autoequivalence changes the mass by a bounded factor. -/
lemma mass_smul_le (g : Γ) (σ : Stab) (U : Obj) :
    I.mass σ (g • U) ≤ exp (I.δ (g⁻¹ • σ) σ) * I.mass σ U := by
  rw [I.mass_smul_eq]
  exact I.mass_le_exp_δ _ _ _

/-- **Twists at Ext-orthogonal spherical objects commute**: `T_E F = F` and the conjugation
formula give `T_F = T_{T_E F} = T_E T_F T_E⁻¹`. -/
theorem twist_commute {E F : Obj} (hE : I.Spherical E) (hF : I.Spherical F)
    (h : I.hom E F = 0) : Commute (I.twist E) (I.twist F) := by
  have h₁ := I.twist_conj (I.twist E) F hF
  rw [I.twist_smul_of_hom_eq_zero E F hE h, eq_mul_inv_iff_mul_eq] at h₁
  exact h₁.symm

/-! ### The lower comparison -/

/-- The constant `L_σ = Σ_k (1 + e^{δ(T_{S_k}^{-1} σ, σ)}) / m_σ(S_k)` of the lower comparison. -/
noncomputable def lowerConst (σ : Stab) : ℝ :=
  ∑ k, (1 + exp (I.δ ((I.twist (I.S k))⁻¹ • σ) σ)) / I.mass σ (I.S k)

lemma lowerConst_nonneg (σ : Stab) : 0 ≤ I.lowerConst σ :=
  Finset.sum_nonneg fun k _ =>
    div_nonneg (by positivity) (I.mass_pos_of_spherical σ _ (I.spherical_S k)).le

/-- **The lower comparison** `h(G, V) ≤ L_σ m_σ(V)`: from the twist triangle of each summand,
`h(S_k, V) m_σ(S_k) ≤ m_σ(V) + m_σ(T_{S_k} V) ≤ (1 + e^{δ(T_{S_k}^{-1} σ, σ)}) m_σ(V)`. -/
theorem hom_G_le_mul_mass (σ : Stab) (V : Obj) : I.hom I.G V ≤ I.lowerConst σ * I.mass σ V := by
  rw [I.hom_G, lowerConst, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  have hS := I.mass_pos_of_spherical σ _ (I.spherical_S k)
  have hL := I.hom_mul_mass_le σ (I.S k) V (I.spherical_S k)
  have hT := I.mass_smul_le (I.twist (I.S k)) σ V
  rw [div_mul_eq_mul_div, le_div_iff₀ hS]
  have := I.mass_nonneg σ V
  nlinarith

include I in
/-- The split generator has a summand: `1 ≤ h(G, G) = Σ_k h(S_k, G)`. -/
lemma nonempty_summand : Nonempty κ := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := I.one_le_hom_G 1
  rw [one_smul, I.hom_G, Finset.univ_eq_empty, Finset.sum_empty] at this
  linarith

lemma lowerConst_pos [Nonempty κ] (σ : Stab) : 0 < I.lowerConst σ :=
  Finset.sum_pos (fun k _ =>
    div_pos (by positivity) (I.mass_pos_of_spherical σ _ (I.spherical_S k))) Finset.univ_nonempty

/-- `m_σ(G) > 0`: by the upper comparison, `C₁ m_σ(S_k) ≤ m_σ(G) h(G, S_k)`. -/
lemma mass_G_pos [Nonempty κ] (σ : Stab) : 0 < I.mass σ I.G := by
  obtain ⟨k⟩ := ‹Nonempty κ›
  have h := I.dhkk_comparison σ (I.S k)
  have hS := I.mass_pos_of_spherical σ _ (I.spherical_S k)
  have hG := I.mass_nonneg σ I.G
  have hh := I.hom_nonneg I.G (I.S k)
  by_contra hle
  have h0 : I.mass σ I.G = 0 := le_antisymm (not_lt.mp hle) hG
  rw [h0, zero_mul] at h
  nlinarith [I.C₁_pos]

/-- **The comparison** `h(U, V) ≤ K h(U, G) L_σ m_σ(V)` for every object `U`: the diagonal estimate
places `U` in the thick subcategory of `G`, and the lower comparison finishes. For a spherical
centre `U = S` this is the comparison `h(S, -) ≤ c_S m_σ(-)` of the mass form. -/
theorem hom_le_mul_mass (σ : Stab) (U V : Obj) :
    I.hom U V ≤ I.K * I.hom U I.G * I.lowerConst σ * I.mass σ V := by
  have h₁ := I.hom_diag U V
  have h₂ := I.hom_G_le_mul_mass σ V
  have : 0 ≤ I.K * I.hom U I.G := mul_nonneg I.K_pos.le (I.hom_nonneg _ _)
  calc I.hom U V ≤ I.K * I.hom U I.G * I.hom I.G V := h₁
    _ ≤ I.K * I.hom U I.G * (I.lowerConst σ * I.mass σ V) := by gcongr
    _ = I.K * I.hom U I.G * I.lowerConst σ * I.mass σ V := by ring

/-- **The upper comparison** `m_σ(U) ≤ (m_σ(G)/C₁) h(G, U)`. -/
theorem mass_le_mul_hom (σ : Stab) (U : Obj) :
    I.mass σ U ≤ I.mass σ I.G / I.C₁ * I.hom I.G U := by
  rw [div_mul_eq_mul_div, le_div_iff₀ I.C₁_pos, mul_comm]
  exact I.dhkk_comparison σ U

/-- **The uniform estimate** for any distance bound: for every `σ` and reference `τ`,
`e^{-δ(σ,τ)} h(G, V)/L_τ ≤ m_σ(V) ≤ e^{δ(σ,τ)} (m_τ(G)/C₁) h(G, V)`. -/
theorem uniform_estimate (σ τ : Stab) (V : Obj) :
    exp (-I.δ σ τ) * I.hom I.G V ≤ I.lowerConst τ * I.mass σ V ∧
      I.mass σ V ≤ exp (I.δ σ τ) * (I.mass τ I.G / I.C₁) * I.hom I.G V := by
  have hlo := I.hom_G_le_mul_mass τ V
  have hτσ := I.mass_le_exp_δ τ σ V
  have hστ := I.mass_le_exp_δ σ τ V
  have hup := I.mass_le_mul_hom τ V
  rw [I.δ_symm τ σ] at hτσ
  have hL := I.lowerConst_nonneg τ
  constructor
  · rw [exp_neg, inv_mul_le_iff₀ (exp_pos _)]
    calc I.hom I.G V ≤ I.lowerConst τ * I.mass τ V := hlo
      _ ≤ I.lowerConst τ * (exp (I.δ σ τ) * I.mass σ V) := by gcongr
      _ = exp (I.δ σ τ) * (I.lowerConst τ * I.mass σ V) := by ring
  · calc I.mass σ V ≤ exp (I.δ σ τ) * I.mass τ V := hστ
      _ ≤ exp (I.δ σ τ) * (I.mass τ I.G / I.C₁ * I.hom I.G V) := by gcongr
      _ = exp (I.δ σ τ) * (I.mass τ I.G / I.C₁) * I.hom I.G V := by ring

/-! ### Categorical entropy -/

/-- `H(W) = h(G, WG)`. -/
def H (W : Γ) : ℝ := I.hom I.G (W • I.G)

lemma H_pos (W : Γ) : 0 < I.H W := lt_of_lt_of_le one_pos (I.one_le_hom_G W)

/-- `H(Φ^{m+n}) ≤ K H(Φ^m) H(Φ^n)`, from the diagonal estimate. -/
theorem H_pow_add_le (Φ : Γ) (m n : ℕ) :
    I.H (Φ ^ (m + n)) ≤ I.K * I.H (Φ ^ m) * I.H (Φ ^ n) := by
  simp only [H]
  rw [pow_add, mul_smul, I.hom_G_smul]
  calc I.hom ((Φ ^ m)⁻¹ • I.G) (Φ ^ n • I.G)
      ≤ I.K * I.hom ((Φ ^ m)⁻¹ • I.G) I.G * I.hom I.G (Φ ^ n • I.G) := I.hom_diag _ _
    _ = I.K * I.hom I.G (Φ ^ m • I.G) * I.hom I.G (Φ ^ n • I.G) := by
      rw [I.hom_smul_left, inv_inv]

/-- `H(W⁻¹) = H(W)`, by Serre duality and invariance of total Hom. -/
theorem H_inv (W : Γ) : I.H W⁻¹ = I.H W := by
  simp only [H]
  rw [I.hom_G_smul, inv_inv, I.hom_comm]

/-- **Categorical entropy** `h_cat(Φ) = lim log h(G, Φⁿ G)/n` (Dimitrov–Haiden–Katzarkov–Kontsevich,
arXiv:1307.8418, Theorem 2.6, at `t = 0`; the limit exists by `tendsto_hcat`). -/
noncomputable def hcat (Φ : Γ) : ℝ :=
  limUnder atTop fun n : ℕ => log (I.H (Φ ^ n)) / n

/-- The limit defining `h_cat` exists: Fekete's lemma for `H(Φ^{m+n}) ≤ K H(Φ^m) H(Φ^n)`. -/
theorem tendsto_hcat (Φ : Γ) :
    Tendsto (fun n : ℕ => log (I.H (Φ ^ n)) / n) atTop (𝓝 (I.hcat Φ)) := by
  obtain ⟨ρ, hρ, -, -⟩ :=
    exists_rate_of_submul (H := fun n => I.H (Φ ^ n)) I.K_pos (fun n => (I.H_pos _).le)
      (I.H_pow_add_le Φ)
  have hρ1 : 1 ≤ ρ := by
    refine ge_of_tendsto hρ (Eventually.of_forall fun n => ?_)
    exact one_le_rpow (I.one_le_hom_G _) (by positivity)
  have h := tendsto_log_div_of_rpow_inv (fun n => I.H_pos (Φ ^ n)) (by linarith) hρ
  rw [hcat, h.limUnder_eq]
  exact h

/-- `h_cat(Φ⁻¹) = h_cat(Φ)`. -/
theorem hcat_inv (Φ : Γ) : I.hcat Φ⁻¹ = I.hcat Φ := by
  refine tendsto_nhds_unique (I.tendsto_hcat Φ⁻¹) ?_
  refine (I.tendsto_hcat Φ).congr fun n => ?_
  rw [inv_pow, I.H_inv]

/-! ### Twist systems with masses -/

variable {ι α : Type*}

/-- `H` is a **twist system of spherical objects for these inputs**: its centres are spherical,
its letters are the twists along their centres or their inverses, and its count is `h`. -/
structure IsTwistSystem (H : HomTwistSystem₀ Γ Obj ι α) : Prop where
  count_eq : ∀ U V, (H.h U V : ℝ) = I.hom U V
  spherical : ∀ i, I.Spherical (H.S i)
  letter : ∀ a, H.T a = I.twist (H.S (H.c a)) ∨ H.T a = (I.twist (H.S (H.c a)))⁻¹

variable {H : HomTwistSystem₀ Γ Obj ι α} {I}

/-- (U_m) for a letter: `m_σ(T_a V) ≤ m_σ(V) + h(S_{c(a)}, V) m_σ(S_{c(a)})`. -/
theorem IsTwistSystem.mass_letter_le (hH : I.IsTwistSystem H) (a : α) (σ : Stab) (V : Obj) :
    I.mass σ (H.T a • V) ≤ I.mass σ V + H.h (H.S (H.c a)) V * I.mass σ (H.S (H.c a)) := by
  rw [hH.count_eq]
  rcases hH.letter a with h | h <;> rw [h]
  · exact I.mass_twist_le σ _ V (hH.spherical _)
  · rw [I.hom_comm]
    exact I.mass_twist_inv_le σ _ V (hH.spherical _)

/-- **The mass domination system.** The masses `m_σ(-)`, one test for each `σ`, pulled back along a
letter by `σ ↦ T_a^{-1} σ`, with the coupling `h(S_{c(a)}, S_k)`. -/
def IsTwistSystem.toDomination (hH : I.IsTwistSystem H) : DominationSystem Γ Obj ι α Stab where
  S := H.S
  T := H.T
  c := H.c
  G a k := H.h (H.S (H.c a)) (H.S k)
  test σ Y := I.mass σ Y
  pull a σ := (H.T a)⁻¹ • σ
  test_pull a σ Y := by
    show I.mass ((H.T a)⁻¹ • σ) Y = I.mass σ (H.T a • Y)
    rw [I.mass_smul_eq]
  centre_le a σ k := by
    show I.mass σ (H.T a • H.S k) ≤ I.mass σ (H.S k) +
      ((H.h (H.S (H.c a)) (H.S k) : ℕ) : ℝ) * I.mass σ (H.S (H.c a))
    exact hH.mass_letter_le a σ (H.S k)

/-! ### The exponent theorem in mass form -/

section MassMax

variable [Fintype ι] [Fintype α] [Nonempty ι]

variable (I H) in
/-- `M_q(σ) = max m_σ(W S_j)` over centres `j` and words `W` of length at most `q`. -/
noncomputable def massMax (σ : Stab) (q : ℕ) : ℝ :=
  Finset.univ.sup' ⟨(Classical.arbitrary ι, ⟨0, Fin.elim0⟩), Finset.mem_univ _⟩
    fun x : ι × (Σ n : Fin (q + 1), Fin n → α) => I.mass σ (H.wordOf x.2.2 • H.S x.1)

omit [Nonempty ι] in
theorem le_massMax [Nonempty ι] (σ : Stab) {q : ℕ} (j : ι) (w : List α) (hw : w.length ≤ q) :
    I.mass σ (H.word w • H.S j) ≤ I.massMax H σ q := by
  have h := Finset.le_sup' (f := fun x : ι × (Σ n : Fin (q + 1), Fin n → α) =>
    I.mass σ (H.wordOf x.2.2 • H.S x.1))
    (Finset.mem_univ (j, ⟨⟨w.length, by omega⟩, w.get⟩))
  have e : H.wordOf w.get = H.word w := by simp [HomTwistSystem₀.wordOf, List.ofFn_get]
  simp only at h
  rw [e] at h
  exact h

theorem exists_massMax_eq (σ : Stab) (q : ℕ) :
    ∃ j, ∃ w : List α, w.length ≤ q ∧ I.massMax H σ q = I.mass σ (H.word w • H.S j) := by
  obtain ⟨⟨j, ⟨n, w⟩⟩, -, hx⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    ⟨(Classical.arbitrary ι, ⟨0, Fin.elim0⟩), Finset.mem_univ _⟩
    (fun x : ι × (Σ n : Fin (q + 1), Fin n → α) => I.mass σ (H.wordOf x.2.2 • H.S x.1))
  exact ⟨j, List.ofFn w, by simpa using Nat.lt_succ_iff.1 n.2, hx⟩

theorem IsTwistSystem.massMax_pos (hH : I.IsTwistSystem H) (σ : Stab) (q : ℕ) :
    0 < I.massMax H σ q := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  have := I.le_massMax (H := H) σ (q := q) j [] (Nat.zero_le _)
  rw [HomTwistSystem₀.word_nil, one_smul] at this
  exact (I.mass_pos_of_spherical σ _ (hH.spherical j)).trans_le this

/-- `m_σ(⊕ S_i) = Σ_i m_σ(S_i)`, the mass of the sum of the centres. -/
noncomputable def centreMass (σ : Stab) : ℝ := ∑ i, I.mass σ (H.S i)

omit [Fintype α] [Nonempty ι] in
/-- **The mass form of the iterated one-letter bound**:
`m_σ(W S_j) ≤ m_σ(⊕ S_i)(1 + |W| P_q)` for `|W| ≤ q`. -/
theorem IsTwistSystem.mass_word_le [Fintype α] (hH : I.IsTwistSystem H) (σ : Stab) {q : ℕ}
    (j : ι) : ∀ w : List α, w.length ≤ q →
      I.mass σ (H.word w • H.S j) ≤ I.centreMass (H := H) σ * (1 + w.length * H.maxCount q)
  | [], _ => by
      simp only [HomTwistSystem₀.word_nil, one_smul, List.length_nil, CharP.cast_eq_zero,
        zero_mul, add_zero, mul_one]
      exact Finset.single_le_sum (f := fun i => I.mass σ (H.S i))
        (fun i _ => I.mass_nonneg σ _) (Finset.mem_univ j)
  | a :: w, hw => by
      simp only [List.length_cons] at hw
      have ih := hH.mass_word_le σ (q := q) j w (by omega)
      have h1 := hH.mass_letter_le a σ (H.word w • H.S j)
      have h2 : (H.h (H.S (H.c a)) (H.word w • H.S j) : ℝ) ≤ H.maxCount q := by
        exact_mod_cast H.le_maxCount (q := q) (H.c a) j w (by omega)
      have h3 : I.mass σ (H.S (H.c a)) ≤ I.centreMass (H := H) σ :=
        Finset.single_le_sum (f := fun i => I.mass σ (H.S i))
          (fun i _ => I.mass_nonneg σ _) (Finset.mem_univ _)
      have hM := I.mass_nonneg σ (H.S (H.c a))
      have hP : (0 : ℝ) ≤ H.maxCount q := Nat.cast_nonneg _
      rw [HomTwistSystem₀.word_cons, mul_smul]
      calc I.mass σ (H.T a • H.word w • H.S j)
          ≤ I.mass σ (H.word w • H.S j) +
              H.h (H.S (H.c a)) (H.word w • H.S j) * I.mass σ (H.S (H.c a)) := h1
        _ ≤ I.centreMass (H := H) σ * (1 + w.length * H.maxCount q) +
              H.maxCount q * I.centreMass (H := H) σ := by gcongr
        _ = I.centreMass (H := H) σ * (1 + ((a :: w).length : ℕ) * H.maxCount q) := by
            rw [List.length_cons]; push_cast; ring

/-- `M_q(σ) ≤ m_σ(⊕ S_i)(1 + q P_q)`. -/
theorem IsTwistSystem.massMax_le (hH : I.IsTwistSystem H) (σ : Stab) (q : ℕ) :
    I.massMax H σ q ≤ I.centreMass (H := H) σ * (1 + q * H.maxCount q) := by
  obtain ⟨j, w, hw, he⟩ := I.exists_massMax_eq (H := H) σ q
  rw [he]
  refine (hH.mass_word_le σ j w hw).trans ?_
  have hM : 0 ≤ I.centreMass (H := H) σ :=
    Finset.sum_nonneg fun i _ => I.mass_nonneg σ _
  have hw' : (w.length : ℝ) ≤ q := by exact_mod_cast hw
  gcongr

/-- The constant `A_σ = K (Σ_i h(S_i, G)) L_σ` of `P_q ≤ A_σ M_q(σ)`. -/
noncomputable def countConst (σ : Stab) : ℝ :=
  I.K * (∑ i, I.hom (H.S i) I.G) * I.lowerConst σ

/-- `P_q ≤ A_σ M_q(σ)`: the centre counts are bounded by the masses, through the comparison. -/
theorem IsTwistSystem.maxCount_le (hH : I.IsTwistSystem H) (σ : Stab) (q : ℕ) :
    (H.maxCount q : ℝ) ≤ I.countConst (H := H) σ * I.massMax H σ q := by
  obtain ⟨i, j, w, hw, he⟩ := H.exists_maxCount_eq q
  rw [he, hH.count_eq]
  have h₁ := I.hom_le_mul_mass σ (H.S i) (H.word w • H.S j)
  have h₂ := I.le_massMax (H := H) σ j w hw
  have h₃ : I.hom (H.S i) I.G ≤ ∑ i, I.hom (H.S i) I.G :=
    Finset.single_le_sum (f := fun i => I.hom (H.S i) I.G) (fun i _ => I.hom_nonneg _ _)
      (Finset.mem_univ i)
  have hL := I.lowerConst_nonneg σ
  have hK := I.K_pos.le
  have hm := I.mass_nonneg σ (H.word w • H.S j)
  have hsum : 0 ≤ ∑ i, I.hom (H.S i) I.G := Finset.sum_nonneg fun i _ => I.hom_nonneg _ _
  calc I.hom (H.S i) (H.word w • H.S j)
      ≤ I.K * I.hom (H.S i) I.G * I.lowerConst σ * I.mass σ (H.word w • H.S j) := h₁
    _ ≤ I.K * (∑ i, I.hom (H.S i) I.G) * I.lowerConst σ * I.mass σ (H.word w • H.S j) := by
        gcongr
    _ ≤ I.K * (∑ i, I.hom (H.S i) I.G) * I.lowerConst σ * I.massMax H σ q := by
        gcongr
    _ = I.countConst (H := H) σ * I.massMax H σ q := rfl

/-- **The twist-system exponent theorem in mass form.** For a twist system of spherical objects
with the lower one-letter bound, sphericity and directed connectivity, the masses
`M_N(σ) = max m_σ(W S_j)` over `|W| ≤ N` satisfy `log M_N(σ)/N → η`, the exponent of the centre
counts, at every `σ`. In particular the mass exponent does not depend on `σ`, and the
certificates of `HomTwistSystem₀.homExponent_lower` and `homExponent_upper` bound it. -/
theorem IsTwistSystem.tendsto_log_massMax (hH : I.IsTwistSystem H) (hL : H.LowerBound)
    (hsph : H.IsSpherical) {d : ℕ} (hconn : H.DirectedConnected d) (σ : Stab) :
    Tendsto (fun N : ℕ => log (I.massMax H σ N) / N) atTop (𝓝 H.homExponent) := by
  have hη := H.tendsto_homExponent hL hsph hconn
  have hP2 : ∀ N, (2 : ℝ) ≤ H.maxCount N := fun N => by exact_mod_cast H.two_le_maxCount hsph N
  set A := I.countConst (H := H) σ
  set M₀ := I.centreMass (H := H) σ
  have hMpos : 0 < M₀ := Finset.sum_pos (fun i _ => I.mass_pos_of_spherical σ _ (hH.spherical i))
    Finset.univ_nonempty
  have hmax_nonneg : ∀ N, 0 ≤ I.massMax H σ N := fun N => by
    obtain ⟨j, w, -, he⟩ := I.exists_massMax_eq (H := H) σ N
    rw [he]; exact I.mass_nonneg _ _
  have hAM : ∀ N, 0 < A * I.massMax H σ N := fun N =>
    lt_of_lt_of_le (by linarith [hP2 N]) (hH.maxCount_le σ N)
  have hApos : 0 < A := by
    by_contra h
    have h' : A ≤ 0 := not_lt.mp h
    have := hAM 0
    nlinarith [hmax_nonneg 0]
  have hmax_pos : ∀ N, 0 < I.massMax H σ N := fun N => pos_of_mul_pos_right (hAM N) hApos.le
  -- the lower sequence `log(P_N / A)/N`
  have hlow : Tendsto (fun N : ℕ => log (H.maxCount N / A) / N) atTop (𝓝 H.homExponent) := by
    have hc : Tendsto (fun N : ℕ => log A / N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have := hη.sub hc
    rw [sub_zero] at this
    refine this.congr fun N => ?_
    rw [log_div (by linarith [hP2 N]) hApos.ne', sub_div]
  -- the upper sequence `log(M₀ (1 + N P_N))/N`
  have hup : Tendsto (fun N : ℕ => log (M₀ * (1 + N * H.maxCount N)) / N) atTop
      (𝓝 H.homExponent) := by
    have hc : Tendsto (fun N : ℕ => log M₀ / N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hlogn : Tendsto (fun N : ℕ => log ((N : ℝ) + 1) / N) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => log ((N : ℝ) + 1) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
        have := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
          (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
        refine this.congr fun n => ?_
        simp
      have h2 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / N) atTop (𝓝 1) := by
        have : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
        rw [add_zero] at this
        refine this.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with n hn
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp
      have := h1.mul h2
      rw [zero_mul] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    -- `log(1 + N P_N)` lies between `log P_N` and `log(N + 1) + log P_N`
    have hmid : Tendsto (fun N : ℕ => log (1 + N * H.maxCount N) / N) atTop
        (𝓝 H.homExponent) := by
      have hhi : Tendsto (fun N : ℕ => log ((N : ℝ) + 1) / N + log (H.maxCount N) / N) atTop
          (𝓝 (0 + H.homExponent)) := hlogn.add hη
      rw [zero_add] at hhi
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hη hhi (fun N => ?_) (fun N => ?_)
      · rcases Nat.eq_zero_or_pos N with h0 | hpos
        · subst h0; simp
        · refine div_le_div_of_nonneg_right (log_le_log (by linarith [hP2 N]) ?_)
            (Nat.cast_nonneg _)
          have : (1 : ℝ) ≤ N := by exact_mod_cast hpos
          nlinarith [hP2 N]
      · rw [← add_div]
        refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
        rw [← log_mul (by positivity) (by linarith [hP2 N])]
        refine log_le_log (by positivity) ?_
        nlinarith [hP2 N]
    have := hc.add hmid
    rw [zero_add] at this
    refine this.congr fun N => ?_
    rw [log_mul hMpos.ne' (by positivity), add_div]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun N => ?_) (fun N => ?_)
  · refine div_le_div_of_nonneg_right (log_le_log (div_pos (by linarith [hP2 N]) hApos) ?_)
      (Nat.cast_nonneg _)
    rw [div_le_iff₀ hApos, mul_comm]
    exact hH.maxCount_le σ N
  · exact div_le_div_of_nonneg_right (log_le_log (hmax_pos N) (hH.massMax_le σ N))
      (Nat.cast_nonneg _)

end MassMax

end MassComparisonHypotheses
