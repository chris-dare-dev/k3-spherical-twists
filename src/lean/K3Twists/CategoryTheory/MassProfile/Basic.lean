/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import K3Twists.Analysis.Convex.HilbertMetric

/-!
# Profiles: nonnegative functionals on objects

A **profile** on a type `Obj` of objects is a nonnegative functional `μ : Obj → ℝ≥0`: the mass
`m_σ` of a stability condition, a total `Ext` count `h(A, -)` or `h(-, A)`, the rank functional.
A group `Γ` acting on `Obj` (autoequivalences acting on objects) acts on profiles by
`(g • μ)(E) = μ(g⁻¹ • E)`. This file builds that action, limits of normalized profiles and two
pseudometrics, with no geometry.

`Profile Obj` is a type synonym for `Obj → ℝ≥0`, not reducible, so that its action is
Mathlib's `arrowAction` (a `def`, not a global instance on function types, where the pointwise
action `(g • f)(E) = g • f(E)` would clash). `Profile` adds no geometric field.

## Main definitions

* `Profile Obj`, with the action `Profile.instMulAction` given by `arrowAction`, the
  pointwise order, addition and `ℝ≥0`-scaling, and the product topology;
* `Profile.homProfile h A = h(A, -)` and `Profile.homToProfile h A = h(-, A)` for a count
  `h : Src → Obj → ℝ≥0`;
* `Profile.normalize μ G = μ(G)⁻¹ • μ`, the profile normalized by an object;
* `Profile.thompsonEDist S μ ν = sup_{E ∈ S} |log μ(E) - log ν(E)|`, the Thompson pseudometric
  over a set `S` of objects on which the profiles are positive (such as an orbit of a point or
  the spherical objects), and `Profile.halfHilbertEDist S μ ν`, half the oscillation
  `(sup_S - inf_S) log (ν/μ)`. Both come from `Analysis/Convex/HilbertMetric.lean`; they are plain
  functions, with no `MetricSpace` instance.

## Main results

* `Profile.homProfile_smul`: for a `Γ`-invariant count, `g • h(A, -) = h(g • A, -)`;
  `Profile.homToProfile_smul`: `g • h(-, A) = h(-, g • A)`.
* `Profile.tendsto_smul_iff`, `Profile.tendsto_normalized_smul`: `g` carries limits of
  normalized profiles to `g • (limit)`, along any filter and for any normalizer; with
  `m_{g σ} = g • m_σ` this is the abstract form of the equivariance of masses
  (`Profile.tendsto_normalized_of_equivariant`). `Profile.mapClusterPt_smul_iff` is the same for
  cluster points, `Profile.normalize_smul` for normalization by an object and its translate.
* `Profile.thompsonEDist_smul`, `Profile.halfHilbertEDist_smul`: `Γ` acts isometrically,
  `d(g • S; g • μ, g • ν) = d(S; μ, ν)`, so over a `Γ`-invariant set `S` both pseudometrics are
  `Γ`-invariant (`Profile.thompsonEDist_smul_of_invariant`,
  `Profile.halfHilbertEDist_smul_of_invariant`).
* `Profile.halfHilbertEDist_le_thompsonEDist`: `d_S ≤ d_T`;
  `Profile.halfHilbertEDist_nnreal_smul_left`: `d_S` is a pseudometric on rays.

## The instance from real objects

`RepresentationTheory/Quiver/Kronecker/HomProfile.lean` builds `homProfile` from the dimensions
of the morphism spaces of representations of the doubled Kronecker quiver, with the group of
permutations of the arrows acting by relabelling; the relabelled profile of a representation is
in general a different profile.
-/

open Filter Topology Set
open scoped NNReal ENNReal Pointwise

/-- A **profile** on `Obj`: a nonnegative functional `Obj → ℝ≥0`. A type synonym, not
reducible, so that a group acting on `Obj` acts on profiles by `(g • μ)(E) = μ(g⁻¹ • E)`. -/
def Profile (Obj : Type*) : Type _ := Obj → ℝ≥0

namespace Profile

variable {Obj : Type*}

instance : FunLike (Profile Obj) Obj ℝ≥0 where
  coe μ := μ
  coe_injective _ _ h := h

/-- The profile with values `f`. -/
def ofFun (f : Obj → ℝ≥0) : Profile Obj := f

@[simp]
lemma ofFun_apply (f : Obj → ℝ≥0) (E : Obj) : ofFun f E = f E := rfl

@[ext]
lemma ext {μ ν : Profile Obj} (h : ∀ E, μ E = ν E) : μ = ν := DFunLike.ext _ _ h

instance : AddCommMonoid (Profile Obj) := inferInstanceAs (AddCommMonoid (Obj → ℝ≥0))

instance : Module ℝ≥0 (Profile Obj) := inferInstanceAs (Module ℝ≥0 (Obj → ℝ≥0))

instance : PartialOrder (Profile Obj) := inferInstanceAs (PartialOrder (Obj → ℝ≥0))

instance : TopologicalSpace (Profile Obj) := inferInstanceAs (TopologicalSpace (Obj → ℝ≥0))

instance : Inhabited (Profile Obj) := ⟨0⟩

@[simp]
lemma zero_apply (E : Obj) : (0 : Profile Obj) E = 0 := rfl

@[simp]
lemma add_apply (μ ν : Profile Obj) (E : Obj) : (μ + ν) E = μ E + ν E := rfl

@[simp]
lemma nnreal_smul_apply (c : ℝ≥0) (μ : Profile Obj) (E : Obj) : (c • μ) E = c * μ E := rfl

lemma le_def {μ ν : Profile Obj} : μ ≤ ν ↔ ∀ E, μ E ≤ ν E := Iff.rfl

/-- Profiles are functions, with the product topology. -/
def homeomorphFun : Profile Obj ≃ₜ (Obj → ℝ≥0) := Homeomorph.refl _

@[simp]
lemma homeomorphFun_apply (μ : Profile Obj) : homeomorphFun μ = ⇑μ := rfl

lemma continuous_apply (E : Obj) : Continuous fun μ : Profile Obj ↦ μ E :=
  _root_.continuous_apply (A := fun _ : Obj ↦ ℝ≥0) E

/-- A family of profiles converges iff it converges at every object. -/
lemma tendsto_nhds_iff {α : Type*} {l : Filter α} {μ : α → Profile Obj} {ν : Profile Obj} :
    Tendsto μ l (𝓝 ν) ↔ ∀ E, Tendsto (fun a ↦ μ a E) l (𝓝 (ν E)) :=
  tendsto_pi_nhds

lemma continuous_iff {X : Type*} [TopologicalSpace X] {f : X → Profile Obj} :
    Continuous f ↔ ∀ E, Continuous fun x ↦ f x E :=
  continuous_pi_iff

instance : ContinuousSMul ℝ≥0 (Profile Obj) :=
  inferInstanceAs (ContinuousSMul ℝ≥0 (Obj → ℝ≥0))

instance : ContinuousAdd (Profile Obj) := inferInstanceAs (ContinuousAdd (Obj → ℝ≥0))

/-! ### The arrow action -/

section Action

variable {Γ : Type*} [Group Γ] [MulAction Γ Obj]

/-- `Γ` acts on profiles by `(g • μ)(E) = μ(g⁻¹ • E)`: Mathlib's `arrowAction`. -/
instance instMulAction : MulAction Γ (Profile Obj) := arrowAction

@[simp]
lemma smul_apply (g : Γ) (μ : Profile Obj) (E : Obj) : (g • μ) E = μ (g⁻¹ • E) := rfl

lemma smul_apply_smul (g : Γ) (μ : Profile Obj) (E : Obj) : (g • μ) (g • E) = μ E := by
  simp

instance : DistribMulAction Γ (Profile Obj) where
  toMulAction := instMulAction
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

instance : SMulCommClass Γ ℝ≥0 (Profile Obj) where
  smul_comm _ _ _ := rfl

instance : SMulCommClass ℝ≥0 Γ (Profile Obj) where
  smul_comm _ _ _ := rfl

lemma smul_mono (g : Γ) {μ ν : Profile Obj} (h : μ ≤ ν) : g • μ ≤ g • ν :=
  fun E ↦ h (g⁻¹ • E)

instance : ContinuousConstSMul Γ (Profile Obj) where
  continuous_const_smul g := continuous_iff.2 fun E ↦ continuous_apply (g⁻¹ • E)

/-! ### Profiles of counts -/

variable {Src : Type*}

/-- The profile `h(A, -)` of `A` for a count `h : Src → Obj → ℝ≥0`, such as a total `Ext`
count. -/
def homProfile (h : Src → Obj → ℝ≥0) (A : Src) : Profile Obj := ofFun (h A)

/-- The profile `h(-, A)` of `A` for a count `h : Obj → Src → ℝ≥0`, such as `h(-, 𝒪_x)`. -/
def homToProfile (h : Obj → Src → ℝ≥0) (A : Src) : Profile Obj := ofFun fun E ↦ h E A

@[simp]
lemma homProfile_apply (h : Src → Obj → ℝ≥0) (A : Src) (E : Obj) : homProfile h A E = h A E :=
  rfl

@[simp]
lemma homToProfile_apply (h : Obj → Src → ℝ≥0) (A : Src) (E : Obj) :
    homToProfile h A E = h E A :=
  rfl

variable [MulAction Γ Src]

/-- For a `Γ`-invariant count, `g • h(A, -) = h(g • A, -)`. -/
theorem homProfile_smul (h : Src → Obj → ℝ≥0) (hh : ∀ (g : Γ) A E, h (g • A) (g • E) = h A E)
    (g : Γ) (A : Src) : g • homProfile h A = homProfile h (g • A) := by
  ext E
  rw [smul_apply, homProfile_apply, homProfile_apply, ← hh g A (g⁻¹ • E), smul_inv_smul]

/-- For a `Γ`-invariant count, `g • h(-, A) = h(-, g • A)`. -/
theorem homToProfile_smul (h : Obj → Src → ℝ≥0) (hh : ∀ (g : Γ) E A, h (g • E) (g • A) = h E A)
    (g : Γ) (A : Src) : g • homToProfile h A = homToProfile h (g • A) := by
  ext E
  rw [smul_apply, homToProfile_apply, homToProfile_apply, ← hh g (g⁻¹ • E) A, smul_inv_smul]

/-! ### Limits of normalized profiles -/

variable {α : Type*} {l : Filter α}

/-- `g` is a homeomorphism of profiles: a family converges to `ν` iff its translates by `g`
converge to `g • ν`. -/
theorem tendsto_smul_iff (g : Γ) {μ : α → Profile Obj} {ν : Profile Obj} :
    Tendsto (fun a ↦ g • μ a) l (𝓝 (g • ν)) ↔ Tendsto μ l (𝓝 ν) :=
  tendsto_const_smul_iff g

/-- **Limits of normalized profiles are equivariant**, for any filter and any normalizer
`N : α → ℝ≥0`: if `N(a)⁻¹ • μ_a → ν`, then `N(a)⁻¹ • (g • μ_a) → g • ν`, and conversely. -/
theorem tendsto_normalized_smul (g : Γ) {μ : α → Profile Obj} {N : α → ℝ≥0} {ν : Profile Obj} :
    Tendsto (fun a ↦ (N a)⁻¹ • (g • μ a)) l (𝓝 (g • ν)) ↔
      Tendsto (fun a ↦ (N a)⁻¹ • μ a) l (𝓝 ν) := by
  simp_rw [← tendsto_smul_iff g (μ := fun a ↦ (N a)⁻¹ • μ a), smul_comm g]

/-- The abstract form of `m_{g σ} = g • m_σ`: for an equivariant map `m` from a type of states
(stability conditions) to profiles, if the normalized profiles `N(a)⁻¹ • m(σ_a)` converge to
`ν`, then `N(a)⁻¹ • m(g • σ_a)` converge to `g • ν`, for any filter and normalizer. -/
theorem tendsto_normalized_of_equivariant {State : Type*} [MulAction Γ State]
    {m : State → Profile Obj} (hm : ∀ (g : Γ) σ, m (g • σ) = g • m σ) (g : Γ)
    {σ : α → State} {N : α → ℝ≥0}
    {ν : Profile Obj} (h : Tendsto (fun a ↦ (N a)⁻¹ • m (σ a)) l (𝓝 ν)) :
    Tendsto (fun a ↦ (N a)⁻¹ • m (g • σ a)) l (𝓝 (g • ν)) := by
  simp_rw [hm]
  exact (tendsto_normalized_smul g).2 h

/-- Cluster points of normalized profiles are equivariant, for any filter and normalizer. -/
theorem mapClusterPt_smul_iff (g : Γ) {μ : α → Profile Obj} {N : α → ℝ≥0} {ν : Profile Obj} :
    MapClusterPt (g • ν) l (fun a ↦ (N a)⁻¹ • (g • μ a)) ↔
      MapClusterPt ν l (fun a ↦ (N a)⁻¹ • μ a) := by
  have key : ∀ (g : Γ) (μ : α → Profile Obj) (ν : Profile Obj),
      MapClusterPt ν l (fun a ↦ (N a)⁻¹ • μ a) →
        MapClusterPt (g • ν) l (fun a ↦ (N a)⁻¹ • (g • μ a)) := fun g μ ν h ↦ by
    have := h.continuousAt_comp (f := fun μ : Profile Obj ↦ g • μ)
      (continuous_const_smul g).continuousAt
    simpa [Function.comp_def, smul_comm g] using this
  refine ⟨fun h ↦ ?_, key g μ ν⟩
  simpa using key g⁻¹ (fun a ↦ g • μ a) _ h

/-- The profile normalized by an object, `μ(G)⁻¹ • μ` (the zero profile if `μ(G) = 0`). -/
noncomputable def normalize (μ : Profile Obj) (G : Obj) : Profile Obj := (μ G)⁻¹ • μ

@[simp]
lemma normalize_apply (μ : Profile Obj) (G E : Obj) : normalize μ G E = (μ G)⁻¹ * μ E := rfl

/-- Normalizing the translate by the translate of the object is the translate of the
normalized profile. -/
lemma normalize_smul (g : Γ) (μ : Profile Obj) (G : Obj) :
    normalize (g • μ) (g • G) = g • normalize μ G := by
  ext E
  simp

lemma normalize_self {μ : Profile Obj} {G : Obj} (h : μ G ≠ 0) : normalize μ G G = 1 := by
  simp [h]

end Action

/-! ### The Thompson and half-Hilbert pseudometrics -/

section Metric

/-- The **Thompson pseudometric** of two profiles over a set `S` of objects,
`sup_{E ∈ S} |log μ(E) - log ν(E)|`, in `[0, ∞]`. It is meant for profiles positive on `S`,
such as an orbit of a point or the set of spherical objects. -/
noncomputable def thompsonEDist (S : Set Obj) (μ ν : Profile Obj) : ℝ≥0∞ :=
  _root_.thompsonEDist S (fun E ↦ (μ E : ℝ)) (fun E ↦ (ν E : ℝ))

/-- The **half-Hilbert (oscillation) pseudometric** of two profiles over a set `S` of objects,
`½ (sup_S - inf_S) log (ν/μ)`, in `[0, ∞]`. It depends only on the rays of the profiles
(`halfHilbertEDist_nnreal_smul_left`). -/
noncomputable def halfHilbertEDist (S : Set Obj) (μ ν : Profile Obj) : ℝ≥0∞ :=
  hilbertEDist S (fun E ↦ (μ E : ℝ)) (fun E ↦ (ν E : ℝ)) / 2

variable {S : Set Obj} {μ ν ρ : Profile Obj}

@[simp]
lemma thompsonEDist_self : thompsonEDist S μ μ = 0 := _root_.thompsonEDist_self

lemma thompsonEDist_comm : thompsonEDist S μ ν = thompsonEDist S ν μ := _root_.thompsonEDist_comm

lemma thompsonEDist_triangle : thompsonEDist S μ ρ ≤ thompsonEDist S μ ν + thompsonEDist S ν ρ :=
  _root_.thompsonEDist_triangle

lemma thompsonEDist_eq_zero_iff (hμ : ∀ E ∈ S, 0 < μ E) (hν : ∀ E ∈ S, 0 < ν E) :
    thompsonEDist S μ ν = 0 ↔ EqOn μ ν S := by
  rw [thompsonEDist, _root_.thompsonEDist_eq_zero_iff (fun E hE ↦ by simpa using hμ E hE)
    (fun E hE ↦ by simpa using hν E hE)]
  exact ⟨fun h E hE ↦ NNReal.coe_injective (h hE), fun h E hE ↦ congrArg _ (h hE)⟩

@[simp]
lemma halfHilbertEDist_self : halfHilbertEDist S μ μ = 0 := by
  simp [halfHilbertEDist]

lemma halfHilbertEDist_comm : halfHilbertEDist S μ ν = halfHilbertEDist S ν μ := by
  rw [halfHilbertEDist, hilbertEDist_comm, halfHilbertEDist]

lemma halfHilbertEDist_triangle :
    halfHilbertEDist S μ ρ ≤ halfHilbertEDist S μ ν + halfHilbertEDist S ν ρ := by
  simp only [halfHilbertEDist, ← ENNReal.add_div]
  exact ENNReal.div_le_div_right hilbertEDist_triangle 2

/-- `d_S ≤ d_T`. -/
theorem halfHilbertEDist_le_thompsonEDist : halfHilbertEDist S μ ν ≤ thompsonEDist S μ ν := by
  rw [halfHilbertEDist, ENNReal.div_le_iff (by norm_num) (by norm_num), mul_comm]
  exact hilbertEDist_le_two_mul_thompsonEDist

/-- `d_S` depends only on rays: rescaling a profile positive on `S` does not change it. -/
lemma halfHilbertEDist_nnreal_smul_left {c : ℝ≥0} (hc : 0 < c) (hμ : ∀ E ∈ S, 0 < μ E) :
    halfHilbertEDist S (c • μ) ν = halfHilbertEDist S μ ν := by
  have := hilbertEDist_smul_left (s := S) (x := fun E ↦ (μ E : ℝ)) (y := fun E ↦ (ν E : ℝ))
    (c := c) (by exact_mod_cast hc) fun E hE ↦ by simpa using (hμ E hE).ne'
  have hfun : (fun E ↦ ((c • μ) E : ℝ)) = (c : ℝ) • fun E ↦ (μ E : ℝ) := by
    funext E
    simp
  simp only [halfHilbertEDist, hfun, this]

/-- For profiles positive on `S`, `d_S` vanishes exactly on proportional profiles. -/
lemma halfHilbertEDist_eq_zero_iff (hμ : ∀ E ∈ S, 0 < μ E) (hν : ∀ E ∈ S, 0 < ν E) :
    halfHilbertEDist S μ ν = 0 ↔ ∃ c : ℝ, 0 < c ∧ ∀ E ∈ S, (μ E : ℝ) = c * ν E := by
  rw [halfHilbertEDist, ENNReal.div_eq_zero_iff, or_iff_left (by simp),
    hilbertEDist_eq_zero_iff (fun E hE ↦ by simpa using hμ E hE)
      (fun E hE ↦ by simpa using hν E hE)]
  rfl

variable {Γ : Type*} [Group Γ] [MulAction Γ Obj]

/-- **`Γ` acts isometrically for the Thompson pseudometric**: `d_T(g • S; g • μ, g • ν) =
d_T(S; μ, ν)`. -/
theorem thompsonEDist_smul (g : Γ) (S : Set Obj) (μ ν : Profile Obj) :
    thompsonEDist (g • S) (g • μ) (g • ν) = thompsonEDist S μ ν := by
  have := _root_.thompsonEDist_comp (x := fun E ↦ (μ E : ℝ)) (y := fun E ↦ (ν E : ℝ))
    (fun E : Obj ↦ g⁻¹ • E) (g • S)
  rw [Set.image_smul, inv_smul_smul] at this
  exact this

/-- **`Γ` acts isometrically for the half-Hilbert pseudometric**. -/
theorem halfHilbertEDist_smul (g : Γ) (S : Set Obj) (μ ν : Profile Obj) :
    halfHilbertEDist (g • S) (g • μ) (g • ν) = halfHilbertEDist S μ ν := by
  have := _root_.hilbertEDist_comp (x := fun E ↦ (μ E : ℝ)) (y := fun E ↦ (ν E : ℝ))
    (fun E : Obj ↦ g⁻¹ • E) (g • S)
  rw [Set.image_smul, inv_smul_smul] at this
  exact congrArg (· / 2) this

lemma smul_set_eq_of_invariant (hS : ∀ (g : Γ), ∀ E ∈ S, g • E ∈ S) (g : Γ) : g • S = S := by
  refine Subset.antisymm (Set.smul_set_subset_iff.2 fun E hE ↦ hS g E hE) fun E hE ↦ ?_
  exact ⟨g⁻¹ • E, hS g⁻¹ E hE, smul_inv_smul g E⟩

/-- Over a `Γ`-invariant set of objects the Thompson pseudometric is `Γ`-invariant. -/
theorem thompsonEDist_smul_of_invariant (hS : ∀ (g : Γ), ∀ E ∈ S, g • E ∈ S) (g : Γ)
    (μ ν : Profile Obj) : thompsonEDist S (g • μ) (g • ν) = thompsonEDist S μ ν := by
  conv_lhs => rw [← smul_set_eq_of_invariant hS g]
  exact thompsonEDist_smul g S μ ν

/-- Over a `Γ`-invariant set of objects the half-Hilbert pseudometric is `Γ`-invariant. -/
theorem halfHilbertEDist_smul_of_invariant (hS : ∀ (g : Γ), ∀ E ∈ S, g • E ∈ S) (g : Γ)
    (μ ν : Profile Obj) : halfHilbertEDist S (g • μ) (g • ν) = halfHilbertEDist S μ ν := by
  conv_lhs => rw [← smul_set_eq_of_invariant hS g]
  exact halfHilbertEDist_smul g S μ ν

end Metric

end Profile
