/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Real.Sqrt
import K3Twists.CategoryTheory.MassProfile.FibreFunctor

/-!
# Class infima of profiles

Let `μ` be a profile on a type `Obj` of objects, `𝒮` a set of objects (the spherical objects of a
triangulated category) and `v : Obj → Λ` a class map (the Mukai vector). The **class infimum** of
`μ` at a class `γ` is

  `d_μ(γ) = inf {μ(S) : S ∈ 𝒮, v(S) = γ}`,

the infimum in `ℝ≥0`, which is `0` when no object of `𝒮` has class `γ`. Every lemma that needs an
object of the class assumes that this fibre is nonempty. On a K3 surface every root class has a
spherical representative, semistable for any given stability condition in the distinguished
component (Kikuta–Koseki–Ouchi, arXiv:2504.12253, Lemma 3.4), so on roots the fibres are nonempty.

For the mass of a stability condition σ the class infimum is `|Z_σ|` on roots (the same paper,
Corollary 3.5); its square is then a quadratic form of rank two, which recovers the period. A
limit of normalized masses keeps every lower bound (`le_of_tendsto_of_le`), but its class infimum
need not be the square root of a quadratic form, and in general it is only upper semicontinuous in
the profile (`eventually_classInf_lt`). This file proves the order and limit properties on abstract
profiles, with no geometry.

## Main definitions

* `Profile.classFibre 𝒮 v γ`: the objects of `𝒮` of class `γ`.
* `Profile.classInf 𝒮 v μ γ`: the class infimum `d_μ(γ)`.

## Main results

* `Profile.classInf_mono`, `Profile.classInf_smul`, `Profile.add_classInf_le`,
  `Profile.sum_classInf_le`: `μ ↦ d_μ` is monotone, positively homogeneous and superadditive.
* `Profile.classInf_smul_group`: `d_{g • μ}(γ) = d_μ(g⁻¹ • γ)` when `g` permutes `𝒮` compatibly
  with `v`; `Profile.classInf_congr`: `d_μ` only sees the values on `𝒮`;
  `Profile.classInf_normalize`: normalizing by an object divides by its value.
* `Profile.le_classInf_of_forall_le`, `Profile.sum_mul_le_classInf`: lower bounds on `𝒮`, read
  through the class, bound the class infimum, also for positive combinations of profiles;
  `Profile.div_le_classInf_normalize_add`: the bound on segments `[μ₀ + r μ₁]`.
* `Profile.le_of_tendsto_of_le`, `Profile.le_classInf_of_tendsto`,
  `Profile.le_sq_classInf_of_tendsto`: lower bounds pass to pointwise limits of profiles and of
  the bounds; in particular `|Z_n ∘ v| ≤ μ_n` with `μ_n → μ` gives `q ≤ d_μ²` for every pointwise
  limit `q` of the period forms `|Z_n|²`, whether or not the charges `Z_n` converge.
* `Profile.eventually_classInf_lt`: upper semicontinuity under pointwise convergence along any
  filter, stated without a `limsup`.
* `Profile.classInf_eq_zero_of_tendsto_smul`: if `μ(g_n • S) → 0` along elements acting trivially
  on classes (products of squared twists), then `d_μ(v(S)) = 0`.
* `Profile.exists_classInf_eq`, `Profile.exists_classInf_eq_natCast`: for a profile with values in
  `ℕ` the infimum is attained and is a natural number.
* `FibreFunctorProfile.exists_classInf_eq`: the class infimum of a fibre-functor profile is
  attained, at least `|⟨w_F, γ⟩|` and congruent to `⟨w_F, γ⟩` modulo two. For the rank functional
  (`w_F = v(𝒪_x)`) this bounds `d_R(γ)` below by the absolute rank; for the total `Ext` count
  `h(A, -)` of a spherical object (`w_F = v(A)`) by `|⟨v(A), γ⟩|`. Equality is not claimed.
-/

open Filter Topology Set
open scoped NNReal

namespace Profile

variable {Obj Λ : Type*}

/-- The objects of `𝒮` of class `γ`. -/
def classFibre (𝒮 : Set Obj) (v : Obj → Λ) (γ : Λ) : Set Obj := {S | S ∈ 𝒮 ∧ v S = γ}

@[simp]
lemma mem_classFibre {𝒮 : Set Obj} {v : Obj → Λ} {γ : Λ} {S : Obj} :
    S ∈ classFibre 𝒮 v γ ↔ S ∈ 𝒮 ∧ v S = γ :=
  Iff.rfl

/-- The **class infimum** `d_μ(γ) = inf {μ(S) : S ∈ 𝒮, v(S) = γ}` of a profile, in `ℝ≥0`; it is `0`
when no object of `𝒮` has class `γ`. -/
noncomputable def classInf (𝒮 : Set Obj) (v : Obj → Λ) (μ : Profile Obj) (γ : Λ) : ℝ≥0 :=
  ⨅ S : classFibre 𝒮 v γ, μ S

variable {𝒮 : Set Obj} {v : Obj → Λ} {μ ν : Profile Obj} {γ : Λ}

lemma classInf_le_of_mem {S : Obj} (hS : S ∈ classFibre 𝒮 v γ) : classInf 𝒮 v μ γ ≤ μ S :=
  ciInf_le (OrderBot.bddBelow _) (⟨S, hS⟩ : classFibre 𝒮 v γ)

/-- The class infimum at the class of an object of `𝒮` is at most the value there. -/
lemma classInf_le {S : Obj} (hS : S ∈ 𝒮) : classInf 𝒮 v μ (v S) ≤ μ S :=
  classInf_le_of_mem ⟨hS, rfl⟩

/-- On a class with no object of `𝒮` the class infimum is `0`. -/
lemma classInf_eq_zero_of_eq_empty (h : classFibre 𝒮 v γ = ∅) : classInf 𝒮 v μ γ = 0 := by
  have : IsEmpty (classFibre 𝒮 v γ) := by rw [h]; exact Set.isEmpty_coe_sort.2 rfl
  exact NNReal.iInf_empty _

lemma le_classInf {c : ℝ≥0} (hne : (classFibre 𝒮 v γ).Nonempty)
    (h : ∀ S ∈ classFibre 𝒮 v γ, c ≤ μ S) : c ≤ classInf 𝒮 v μ γ := by
  haveI := hne.to_subtype
  exact le_ciInf fun S ↦ h S S.2

lemma exists_lt_of_classInf_lt {c : ℝ≥0} (hne : (classFibre 𝒮 v γ).Nonempty)
    (h : classInf 𝒮 v μ γ < c) : ∃ S ∈ classFibre 𝒮 v γ, μ S < c := by
  haveI := hne.to_subtype
  obtain ⟨S, hS⟩ := exists_lt_of_ciInf_lt h
  exact ⟨S, S.2, hS⟩

/-- The class infimum as a real infimum. -/
lemma coe_classInf : (classInf 𝒮 v μ γ : ℝ) = ⨅ S : classFibre 𝒮 v γ, (μ S : ℝ) :=
  NNReal.coe_iInf _

/-- A real lower bound on the fibre is a lower bound of the class infimum. -/
lemma le_coe_classInf {c : ℝ} (hne : (classFibre 𝒮 v γ).Nonempty)
    (h : ∀ S ∈ classFibre 𝒮 v γ, c ≤ μ S) : c ≤ classInf 𝒮 v μ γ := by
  haveI := hne.to_subtype
  rw [coe_classInf]
  exact le_ciInf fun S ↦ h S S.2

/-- Evaluation of a finite sum of profiles. -/
@[simp]
lemma sum_apply {ι : Type*} (s : Finset ι) (μs : ι → Profile Obj) (E : Obj) :
    (∑ i ∈ s, μs i) E = ∑ i ∈ s, μs i E := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

/-! ### Order properties -/

/-- `μ ↦ d_μ` is monotone. -/
theorem classInf_mono (h : μ ≤ ν) : classInf 𝒮 v μ γ ≤ classInf 𝒮 v ν γ :=
  ciInf_mono (OrderBot.bddBelow _) fun S ↦ h S

/-- The class infimum only sees the values on `𝒮`. -/
theorem classInf_congr (h : ∀ S ∈ 𝒮, μ S = ν S) : classInf 𝒮 v μ γ = classInf 𝒮 v ν γ :=
  iInf_congr fun S ↦ h S S.2.1

/-- `μ ↦ d_μ` is positively homogeneous: `d_{cμ} = c d_μ`. -/
theorem classInf_smul (c : ℝ≥0) : classInf 𝒮 v (c • μ) γ = c * classInf 𝒮 v μ γ := by
  simp only [classInf, nnreal_smul_apply]
  rw [NNReal.mul_iInf]

/-- The class infimum of a profile normalized by an object `G` is `d_μ / μ(G)`. With
`sum_mul_le_classInf` this gives the lower bound
`d_{[μ_* + r h_A]}(γ) ≥ (|Z_*(γ)| + r |⟨v(A), γ⟩|) / (μ_*(G) + r h_A(G))` on segments, and its
analogue on joins with several centres. -/
theorem classInf_normalize (G : Obj) :
    classInf 𝒮 v (normalize μ G) γ = (μ G)⁻¹ * classInf 𝒮 v μ γ :=
  classInf_smul _

/-- `μ ↦ d_μ` is superadditive: `d_μ + d_ν ≤ d_{μ + ν}`. -/
theorem add_classInf_le : classInf 𝒮 v μ γ + classInf 𝒮 v ν γ ≤ classInf 𝒮 v (μ + ν) γ := by
  rcases (classFibre 𝒮 v γ).eq_empty_or_nonempty with h | h
  · simp [classInf_eq_zero_of_eq_empty h]
  · exact le_classInf h fun S hS ↦ add_le_add (classInf_le_of_mem hS) (classInf_le_of_mem hS)

/-- Superadditivity for finite sums: `∑ d_{μ_i} ≤ d_{∑ μ_i}`. -/
theorem sum_classInf_le {ι : Type*} (s : Finset ι) (μs : ι → Profile Obj) :
    ∑ i ∈ s, classInf 𝒮 v (μs i) γ ≤ classInf 𝒮 v (∑ i ∈ s, μs i) γ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact zero_le
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (add_le_add le_rfl ih).trans add_classInf_le

/-! ### Equivariance -/

section Equivariance

variable {Γ : Type*} [Group Γ] [MulAction Γ Obj] [MulAction Γ Λ]

/-- **Equivariance.** If `Γ` preserves `𝒮` and `v(g • S) = g • v(S)`, then
`d_{g • μ}(γ) = d_μ(g⁻¹ • γ)`: the class infimum of a translated profile is the translated class
infimum. -/
theorem classInf_smul_group (h𝒮 : ∀ (g : Γ), ∀ S ∈ 𝒮, g • S ∈ 𝒮)
    (hv : ∀ (g : Γ) S, v (g • S) = g • v S) (g : Γ) (μ : Profile Obj) (γ : Λ) :
    classInf 𝒮 v (g • μ) γ = classInf 𝒮 v μ (g⁻¹ • γ) := by
  let e : classFibre 𝒮 v γ ≃ classFibre 𝒮 v (g⁻¹ • γ) :=
    { toFun := fun S ↦ ⟨g⁻¹ • S.1, h𝒮 _ _ S.2.1, by rw [hv, S.2.2]⟩
      invFun := fun S ↦ ⟨g • S.1, h𝒮 _ _ S.2.1, by rw [hv, S.2.2, smul_inv_smul]⟩
      left_inv := fun S ↦ Subtype.ext (smul_inv_smul g S.1)
      right_inv := fun S ↦ Subtype.ext (inv_smul_smul g S.1) }
  exact e.iInf_congr fun S ↦ rfl

end Equivariance

/-! ### Lower bounds and limits -/

/-- **Lower bounds through the class.** If `f(v(S)) ≤ μ(S)` for every `S ∈ 𝒮`, then
`f(γ) ≤ d_μ(γ)` on every class with an object of `𝒮`. For `f = |Z|` and the mass of a stability
condition with charge `Z` this is the lower half of `d_{m_σ} = |Z_σ|`. -/
theorem le_classInf_of_forall_le {f : Λ → ℝ} (h : ∀ S ∈ 𝒮, f (v S) ≤ μ S)
    (hne : (classFibre 𝒮 v γ).Nonempty) : f γ ≤ classInf 𝒮 v μ γ :=
  le_coe_classInf hne fun S hS ↦ hS.2 ▸ h S hS.1

/-- **Lower bounds for positive combinations.** If `f_i(v(S)) ≤ μ_i(S)` on the fibre of `γ` for each
`i`, then `∑ c_i f_i(γ) ≤ d_{∑ c_i μ_i}(γ)`. With `μ_0` a limiting mass, `f_0 = |Z|`, and
`μ_i = h(A_i, -)` the total `Ext` counts of spherical objects, `f_i = |⟨v(A_i), -⟩|` off the classes
`±v(A_i)`, this is the lower bound on segments and joins of the mass boundary. -/
theorem sum_mul_le_classInf {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0) (μs : ι → Profile Obj)
    (f : ι → Λ → ℝ) (h : ∀ i ∈ s, ∀ S ∈ classFibre 𝒮 v γ, f i (v S) ≤ μs i S)
    (hne : (classFibre 𝒮 v γ).Nonempty) :
    ∑ i ∈ s, (c i : ℝ) * f i γ ≤ classInf 𝒮 v (∑ i ∈ s, c i • μs i) γ := by
  refine le_coe_classInf hne fun S hS ↦ ?_
  rw [sum_apply, NNReal.coe_sum]
  simp only [nnreal_smul_apply, NNReal.coe_mul]
  refine Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left ?_ (c i).2
  rw [← hS.2]
  exact h i hi S hS

/-- **The segment bound.** If `f₀(v(S)) ≤ μ₀(S)` and `f₁(v(S)) ≤ μ₁(S)` on the fibre of `γ`, then
the profile `μ₀ + r μ₁` normalized by an object `G` has
`d(γ) ≥ (f₀(γ) + r f₁(γ)) / (μ₀(G) + r μ₁(G))`. For `μ₀` a limiting mass with `f₀ = |Z_*|` and
`μ₁ = h(A, -)` the total `Ext` count of a spherical object, with `f₁ = |⟨v(A), -⟩|` on classes other
than `±v(A)`, this bounds the class infima along the segment `[μ₀ + r h_A]` below. -/
theorem div_le_classInf_normalize_add (G : Obj) (μ₀ μ₁ : Profile Obj) (r : ℝ≥0) {f₀ f₁ : Λ → ℝ}
    (h₀ : ∀ S ∈ classFibre 𝒮 v γ, f₀ (v S) ≤ μ₀ S) (h₁ : ∀ S ∈ classFibre 𝒮 v γ, f₁ (v S) ≤ μ₁ S)
    (hne : (classFibre 𝒮 v γ).Nonempty) :
    (f₀ γ + r * f₁ γ) / (μ₀ G + r * μ₁ G) ≤ classInf 𝒮 v (normalize (μ₀ + r • μ₁) G) γ := by
  refine le_coe_classInf hne fun S hS ↦ ?_
  have hnum : f₀ γ + r * f₁ γ ≤ μ₀ S + r * μ₁ S := by
    rw [← hS.2]
    exact add_le_add (h₀ S hS) (mul_le_mul_of_nonneg_left (h₁ S hS) r.2)
  simp only [normalize_apply, add_apply, nnreal_smul_apply, NNReal.coe_mul, NNReal.coe_inv,
    NNReal.coe_add]
  rw [inv_mul_eq_div]
  exact div_le_div_of_nonneg_right hnum (by positivity)

/-- **Lower bounds pass to limits.** Let `μ_a → μ` pointwise and `f_a → f` pointwise along a
nontrivial filter. If eventually `f_a(v(S)) ≤ μ_a(S)` on `𝒮`, then `f(v(S)) ≤ μ(S)` on `𝒮`. The
bounds `f_a` need not come from converging charges. -/
theorem le_of_tendsto_of_le {α : Type*} {l : Filter α} [l.NeBot] {μs : α → Profile Obj}
    {fs : α → Λ → ℝ} {f : Λ → ℝ} (hμ : Tendsto μs l (𝓝 μ))
    (hf : ∀ γ, Tendsto (fun a ↦ fs a γ) l (𝓝 (f γ)))
    (hle : ∀ᶠ a in l, ∀ S ∈ 𝒮, fs a (v S) ≤ μs a S) : ∀ S ∈ 𝒮, f (v S) ≤ μ S := by
  intro S hS
  have hμS : Tendsto (fun a ↦ (μs a S : ℝ)) l (𝓝 (μ S : ℝ)) :=
    (NNReal.tendsto_coe.2 (tendsto_nhds_iff.1 hμ S))
  exact le_of_tendsto_of_tendsto (hf (v S)) hμS (hle.mono fun a ha ↦ ha S hS)

/-- The class infimum of a limit is bounded below by the limit of the bounds. -/
theorem le_classInf_of_tendsto {α : Type*} {l : Filter α} [l.NeBot] {μs : α → Profile Obj}
    {fs : α → Λ → ℝ} {f : Λ → ℝ} (hμ : Tendsto μs l (𝓝 μ))
    (hf : ∀ γ, Tendsto (fun a ↦ fs a γ) l (𝓝 (f γ)))
    (hle : ∀ᶠ a in l, ∀ S ∈ 𝒮, fs a (v S) ≤ μs a S) (hne : (classFibre 𝒮 v γ).Nonempty) :
    f γ ≤ classInf 𝒮 v μ γ :=
  le_classInf_of_forall_le (le_of_tendsto_of_le hμ hf hle) hne

/-- **Limit period forms.** If `|Z_a(v(S))| ≤ μ_a(S)` on `𝒮` eventually, `μ_a → μ` pointwise and the
period forms converge, `|Z_a(γ)|² → q(γ)` for every class, then `q(γ) ≤ d_μ(γ)²` on every class with
an object of `𝒮`. The charges `Z_a` need not converge, nor be additive. -/
theorem le_sq_classInf_of_tendsto {α : Type*} {l : Filter α} [l.NeBot] {μs : α → Profile Obj}
    {Z : α → Λ → ℂ} {q : Λ → ℝ} (hμ : Tendsto μs l (𝓝 μ))
    (hq : ∀ γ, Tendsto (fun a ↦ ‖Z a γ‖ ^ 2) l (𝓝 (q γ)))
    (hle : ∀ᶠ a in l, ∀ S ∈ 𝒮, ‖Z a (v S)‖ ≤ μs a S) (hne : (classFibre 𝒮 v γ).Nonempty) :
    q γ ≤ (classInf 𝒮 v μ γ : ℝ) ^ 2 := by
  have hsqrt : ∀ γ, Tendsto (fun a ↦ ‖Z a γ‖) l (𝓝 (Real.sqrt (q γ))) := fun γ ↦ by
    have := (Real.continuous_sqrt.tendsto _).comp (hq γ)
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  have hq0 : 0 ≤ q γ :=
    ge_of_tendsto (hq γ) (Eventually.of_forall fun a ↦ sq_nonneg _)
  have h := le_classInf_of_tendsto hμ hsqrt hle hne
  calc q γ = Real.sqrt (q γ) ^ 2 := (Real.sq_sqrt hq0).symm
    _ ≤ (classInf 𝒮 v μ γ : ℝ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

/-- **Upper semicontinuity.** If `μ_a → μ` pointwise along any filter, then for every `ε > 0`,
eventually `d_{μ_a}(γ) < d_μ(γ) + ε`, on every class with an object of `𝒮`. -/
theorem eventually_classInf_lt {α : Type*} {l : Filter α} {μs : α → Profile Obj}
    (hμ : Tendsto μs l (𝓝 μ)) (hne : (classFibre 𝒮 v γ).Nonempty) {ε : ℝ≥0} (hε : 0 < ε) :
    ∀ᶠ a in l, classInf 𝒮 v (μs a) γ < classInf 𝒮 v μ γ + ε := by
  obtain ⟨S, hS, hlt⟩ := exists_lt_of_classInf_lt hne (lt_add_of_pos_right _ hε)
  have h : ∀ᶠ a in l, μs a S < classInf 𝒮 v μ γ + ε :=
    (tendsto_nhds_iff.1 hμ S).eventually (eventually_lt_nhds hlt)
  exact h.mono fun a ha ↦ (classInf_le_of_mem hS).trans_lt ha

/-! ### Vanishing class infima -/

/-- If objects `S_n` of `𝒮` of class `γ` have `μ(S_n) → 0`, then `d_μ(γ) = 0`. -/
theorem classInf_eq_zero_of_tendsto {S : ℕ → Obj} (hS : ∀ n, S n ∈ classFibre 𝒮 v γ)
    (h : Tendsto (fun n ↦ μ (S n)) atTop (𝓝 0)) : classInf 𝒮 v μ γ = 0 :=
  le_antisymm (ge_of_tendsto' h fun n ↦ classInf_le_of_mem (hS n)) zero_le

/-- **Numerically trivial words.** Let `Γ` act on `Obj` preserving `𝒮`, and let `g_n` act trivially
on classes (`v(g_n • E) = v(E)`, as products of squared spherical twists do). If `S ∈ 𝒮` and
`μ(g_n • S) → 0`, then `d_μ(v(S)) = 0`. This is how boundary profiles that are limits along words
of numerically trivial blocks get vanishing class infima on every root. -/
theorem classInf_eq_zero_of_tendsto_smul {Γ : Type*} [Group Γ] [MulAction Γ Obj]
    (h𝒮 : ∀ (g : Γ), ∀ S ∈ 𝒮, g • S ∈ 𝒮) {g : ℕ → Γ} (hg : ∀ n E, v (g n • E) = v E)
    {S : Obj} (hS : S ∈ 𝒮) (h : Tendsto (fun n ↦ μ (g n • S)) atTop (𝓝 0)) :
    classInf 𝒮 v μ (v S) = 0 :=
  classInf_eq_zero_of_tendsto (fun n ↦ ⟨h𝒮 _ _ hS, hg n S⟩) h

/-! ### Profiles with values in `ℕ` -/

/-- For a profile with values in `ℕ`, the class infimum of a class with an object of `𝒮` is
attained. -/
theorem exists_classInf_eq (hμ : ∀ E, ∃ n : ℕ, μ E = n) (hne : (classFibre 𝒮 v γ).Nonempty) :
    ∃ S ∈ classFibre 𝒮 v γ, μ S = classInf 𝒮 v μ γ := by
  classical
  have hex : ∃ n : ℕ, ∃ S ∈ classFibre 𝒮 v γ, μ S = n := by
    obtain ⟨S, hS⟩ := hne
    obtain ⟨n, hn⟩ := hμ S
    exact ⟨n, S, hS, hn⟩
  obtain ⟨S₀, hS₀, hS₀n⟩ := Nat.find_spec hex
  refine ⟨S₀, hS₀, le_antisymm ?_ (classInf_le_of_mem hS₀)⟩
  rw [hS₀n]
  refine le_classInf hne fun S hS ↦ ?_
  obtain ⟨n, hn⟩ := hμ S
  rw [hn]
  exact_mod_cast Nat.find_min' hex ⟨S, hS, hn⟩

/-- For a profile with values in `ℕ`, the class infimum is a natural number, attained on the
fibre. -/
theorem exists_classInf_eq_natCast (hμ : ∀ E, ∃ n : ℕ, μ E = n)
    (hne : (classFibre 𝒮 v γ).Nonempty) :
    ∃ n : ℕ, classInf 𝒮 v μ γ = n ∧ ∃ S ∈ classFibre 𝒮 v γ, μ S = n := by
  obtain ⟨S, hS, hSeq⟩ := exists_classInf_eq hμ hne
  obtain ⟨n, hn⟩ := hμ S
  exact ⟨n, hSeq ▸ hn, S, hS, hn⟩

end Profile

namespace FibreFunctorProfile

open Profile

variable {Obj Λ : Type*} [AddCommGroup Λ] {B : LinearMap.BilinForm ℤ Λ}
  (F : FibreFunctorProfile Obj Λ B)

/-- **Fibre-functor parity for class infima.** On a class `γ` with an object of `𝒮`, the class
infimum of a fibre-functor profile `μ_F` over `𝒮` is attained at an object `S` of class `γ`; it
is at least `|⟨w_F, γ⟩|` and congruent to `⟨w_F, γ⟩` modulo two. -/
theorem exists_classInf_eq (𝒮 : Set Obj) {γ : Λ} (hne : (classFibre 𝒮 F.cls γ).Nonempty) :
    ∃ S ∈ classFibre 𝒮 F.cls γ, classInf 𝒮 F.cls F.toProfile γ = F.mass S ∧
      |B F.w γ| ≤ F.mass S ∧ B F.w γ ≡ F.mass S [ZMOD 2] := by
  obtain ⟨S, hS, hSeq⟩ :=
    Profile.exists_classInf_eq (μ := F.toProfile) (fun E ↦ ⟨F.mass E, rfl⟩) hne
  refine ⟨S, hS, hSeq.symm, ?_, ?_⟩
  · rw [← hS.2]
    exact F.abs_le_mass S
  · rw [← hS.2]
    exact F.modEq_mass S

/-- On a class `γ` with an object of `𝒮`, the class infimum of a fibre-functor profile is at
least `|⟨w_F, γ⟩|`. -/
theorem abs_le_classInf (𝒮 : Set Obj) {γ : Λ} (hne : (classFibre 𝒮 F.cls γ).Nonempty) :
    (|B F.w γ| : ℝ) ≤ classInf 𝒮 F.cls F.toProfile γ := by
  obtain ⟨S, -, hSeq, habs, -⟩ := F.exists_classInf_eq 𝒮 hne
  rw [hSeq, NNReal.coe_natCast]
  exact_mod_cast habs

end FibreFunctorProfile
