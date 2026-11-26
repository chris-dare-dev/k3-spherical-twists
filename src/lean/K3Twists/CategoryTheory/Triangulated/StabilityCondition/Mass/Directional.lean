/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import K3Twists.Analysis.Complex.Crofton
import K3Twists.CategoryTheory.MassProfile.ClassInfimum
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.StabilitySpace

/-!
# Masses for a seminorm: the mass, directional profiles and their class infima

For a prestability condition `σ = (P, Z)` and a seminorm `p` on `ℂ` (as a real vector space), the
**mass for `p`** of an object `E` with HN factors `A_i` is

  `M_{σ,p}(E) = Σ_i p(Z(A_i))`,

independent of the HN filtration (`massBy_eq_sum`). For `p = ‖·‖` it is the mass
(`massBy_normSeminorm`). For `p_θ(z) = |Re(e^{-iθ} z)|` it is the **directional profile**
`ν_{σ,θ}(E) = Σ_i |Re(e^{-iθ} Z(A_i))|` (`directional`); for a positive semidefinite form `Q` on
`ℝ²`, `p(z) = (zᵀ Q z)^{1/2}` gives the mass after acting on the charge by `Q^{1/2}`. All share:

* `p(Z(E)) ≤ M_{σ,p}(E)`, with equality on semistable objects (`seminorm_charge_le_massBy`,
  `massBy_of_semistable`);
* invariance under isomorphisms and shifts, and under autoequivalences acting on a space of
  stability conditions (`StabilitySpaceHypotheses.massBy_smul`);
* the **class infimum** `inf {M_{σ,p}(S) : S ∈ 𝒮, v(S) = γ} = p(Z(γ))`, attained, whenever the class
  `γ` has a representative in `𝒮` semistable for `σ` (`classInf_massByProfile`). On a K3 surface,
  with `𝒮` the spherical objects, every root class has one for every stability condition in the
  distinguished component (Kikuta–Koseki–Ouchi, arXiv:2504.12253, Lemma 3.4, whose proof uses
  Bayer–Macrì, J. Amer. Math. Soc. 27 (2014), Corollary 6.9, in every Picard rank). For the mass
  this is the same paper's Corollary 3.5: `d_{m_σ} = |Z_σ|` on roots (`classInf_massProfile`). For
  a directional profile the class infimum is `|Re(e^{-iθ} Z(γ))|` (`classInf_directionalProfile`),
  the absolute value of one real linear form: its square has rank one, while for the mass it is the
  rank-two form `|Z|²`.

For the directional profiles in particular:

* `directional_le_mass`: `ν_{σ,θ} ≤ m_σ`;
* `mass_eq_integral_directional`: **the barycentre identity**
  `m_σ(E) = (1/4) ∫₀^{2π} ν_{σ,θ}(E) dθ`, from the Crofton formula `Complex.sum_norm_eq_integral`;
* `directional_eq_re_of_cos_nonneg`, `directional_add_of_triangle`: on objects all of whose HN
  phases `ψ` have `cos(πψ - θ) ≥ 0` (a sector of width one where `Re(e^{-iθ} Z)` has one sign),
  `ν_{σ,θ}(E) = Re(e^{-iθ} Z(E))`, so `ν_{σ,θ}` is additive on distinguished triangles inside the
  sector.

## Real objects

Mathlib has no triangulated category carrying a slicing, so there is no instance from geometry:
the missing input is the derived category of a K3 surface with its stability conditions. The
statements hold for every prestability condition, so the semistable-representative condition is a
hypothesis (`HasSemistableRepresentatives`), not a structure.

## Main definitions

* `PreStabilityCondition.WithClassMap.massBy σ p`: the mass for a seminorm `p`.
* `directionalSeminorm θ`, `PreStabilityCondition.WithClassMap.directional σ θ`: the directional
  profile.
* `PreStabilityCondition.WithClassMap.massByProfile`, `massProfile`, `directionalProfile`: the same
  as profiles `C → ℝ≥0`.
* `PreStabilityCondition.WithClassMap.HasSemistableRepresentatives σ 𝒮 R`: every class in `R` has a
  representative in `𝒮` that is semistable for `σ`.

## References

* T. Bridgeland, *Stability conditions on triangulated categories*, arXiv:math/0212237, §8.
* K. Kikuta, N. Koseki, G. Ouchi, arXiv:2504.12253, Lemma 3.4 and Corollary 3.5.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Filter Topology Set
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
open scoped NNReal Real

universe u v u'

/-- The directional seminorm `z ↦ |Re(e^{-iθ} z)|` on `ℂ`. -/
def directionalSeminorm (θ : ℝ) : Seminorm ℝ ℂ :=
  (normSeminorm ℝ ℝ).comp (Complex.reLm.comp (LinearMap.mulLeft ℝ (Complex.exp (-(θ * Complex.I)))))

@[simp]
lemma directionalSeminorm_apply (θ : ℝ) (z : ℂ) :
    directionalSeminorm θ z = |(Complex.exp (-(θ * Complex.I)) * z).re| := by
  simp [directionalSeminorm, Real.norm_eq_abs]

/-- A seminorm of a finite sum is at most the sum of the seminorms. -/
lemma Seminorm.apply_sum_le {E : Type*} [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E)
    {ι : Type*} (s : Finset ι) (z : ι → E) : p (∑ i ∈ s, z i) ≤ ∑ i ∈ s, p (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

namespace PreStabilityCondition.WithClassMap

variable (σ : WithClassMap C v) (p : Seminorm ℝ ℂ)

/-! ### The mass for a seminorm -/

/-- The **mass for a seminorm** `p` on `ℂ`: `M_{σ,p}(E) = Σ_i p(Z(A_i))` over the HN factors `A_i`
of `E`. Any HN filtration gives the same value (`massBy_eq_sum`). -/
def massBy (E : C) : ℝ :=
  ∑ i, p (σ.charge ((σ.slicing.hn_exists E).some.factor i))

/-- The mass for `p` is the sum over **any** HN filtration. -/
theorem massBy_eq_sum {E : C} (F : HNFiltration C σ.slicing.P E) :
    σ.massBy p E = ∑ i, p (σ.charge (F.factor i)) :=
  HNFiltration.sum_factor_eq σ.slicing (fun _ X => p (σ.charge X))
    (fun _ _ _ e => by simp only [charge_def, classOf_iso C v e])
    (fun _ _ hX => by simp [charge_isZero σ hX]) _ F

/-- The mass for `p` computed from an HN filtration for a slicing equal to that of `σ`. -/
theorem massBy_eq_sum_of_slicing_eq {s : Slicing C} (hs : σ.slicing = s) {E : C}
    (F : HNFiltration C s.P E) : σ.massBy p E = ∑ i, p (σ.charge (F.factor i)) := by
  subst hs
  exact σ.massBy_eq_sum p F

theorem massBy_nonneg (E : C) : 0 ≤ σ.massBy p E :=
  Finset.sum_nonneg fun _ _ => apply_nonneg _ _

/-- Isomorphic objects have the same mass for `p`. -/
theorem massBy_iso {E E' : C} (e : E ≅ E') : σ.massBy p E = σ.massBy p E' := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [σ.massBy_eq_sum p F, σ.massBy_eq_sum p (F.ofIso C e)]
  rfl

/-- Shifts preserve the mass for `p`. -/
theorem massBy_shift (E : C) (a : ℤ) : σ.massBy p (E⟦a⟧) = σ.massBy p E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [σ.massBy_eq_sum p (F.shift C σ.slicing a), σ.massBy_eq_sum p F]
  refine Finset.sum_congr rfl fun i _ => ?_
  change p (σ.Z (classOf C v ((F.factor i)⟦a⟧))) = p (σ.Z (classOf C v (F.factor i)))
  rw [classOf, classOf, K₀.of_shift_int, map_zsmul, map_zsmul]
  rcases Nat.even_or_odd (Int.natAbs a) with h | h
  · rw [h.neg_one_pow, one_zsmul]
  · rw [h.neg_one_pow, neg_one_zsmul, map_neg_eq_map]

/-- A semistable object has mass `p(Z(E))` for `p`. -/
theorem massBy_of_semistable {φ : ℝ} {E : C} (hP : σ.slicing.P φ E) :
    σ.massBy p E = p (σ.charge E) := by
  rw [σ.massBy_eq_sum p (HNFiltration.single C E φ hP)]
  change ∑ _ : Fin 1, _ = _
  rw [Fin.sum_univ_one]
  rfl

/-- `p(Z(E)) ≤ M_{σ,p}(E)`: the seminorm is subadditive on the charges of the HN factors. -/
theorem seminorm_charge_le_massBy (E : C) : p (σ.charge E) ≤ σ.massBy p E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [σ.massBy_eq_sum p F, σ.charge_postnikovTower_eq_sum F.toPostnikovTower]
  exact p.apply_sum_le _ _

/-- For the norm the mass for a seminorm is the mass. -/
theorem massBy_normSeminorm (E : C) : σ.massBy (normSeminorm ℝ ℂ) E = σ.mass E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [σ.massBy_eq_sum _ F, σ.mass_eq_sum F]
  rfl

/-- A seminorm bounded by `c ‖·‖` gives a mass bounded by `c m_σ`. -/
theorem massBy_le_mul_mass {c : ℝ} (hp : ∀ z, p z ≤ c * ‖z‖) (E : C) :
    σ.massBy p E ≤ c * σ.mass E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [σ.massBy_eq_sum p F, σ.mass_eq_sum F, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hp _

/-! ### Profiles and class infima -/

/-- The mass for `p` as a profile. -/
def massByProfile : Profile C := Profile.ofFun fun E ↦ ⟨σ.massBy p E, σ.massBy_nonneg p E⟩

@[simp]
lemma coe_massByProfile_apply (E : C) : (σ.massByProfile p E : ℝ) = σ.massBy p E := rfl

/-- The mass as a profile. -/
def massProfile : Profile C := Profile.ofFun fun E ↦ ⟨σ.mass E, σ.mass_nonneg E⟩

@[simp]
lemma coe_massProfile_apply (E : C) : (σ.massProfile E : ℝ) = σ.mass E := rfl

lemma massByProfile_normSeminorm : σ.massByProfile (normSeminorm ℝ ℂ) = σ.massProfile :=
  Profile.ext fun E ↦ NNReal.coe_injective (σ.massBy_normSeminorm E)

/-- Every class of `R` has a representative in `𝒮` that is semistable for `σ`. On a K3 surface, for
`𝒮` the spherical objects and `R` the classes of square `-2`, this holds at every stability
condition of the distinguished component (Kikuta–Koseki–Ouchi, arXiv:2504.12253, Lemma 3.4). -/
def HasSemistableRepresentatives (𝒮 : Set C) (R : Set Λ) : Prop :=
  ∀ γ ∈ R, ∃ S ∈ 𝒮, classOf C v S = γ ∧ ∃ φ, σ.slicing.P φ S

/-- **The class infimum of a mass for a seminorm.** If the class `γ` has a representative in `𝒮`
that is semistable for `σ`, the infimum of `M_{σ,p}` over the objects of `𝒮` of class `γ` is
`p(Z(γ))`. -/
theorem classInf_massByProfile {𝒮 : Set C} {γ : Λ}
    (h : ∃ S ∈ 𝒮, classOf C v S = γ ∧ ∃ φ, σ.slicing.P φ S) :
    (Profile.classInf 𝒮 (classOf C v) (σ.massByProfile p) γ : ℝ) = p (σ.Z γ) := by
  obtain ⟨S, hS𝒮, hSγ, φ, hφ⟩ := h
  have hmem : S ∈ Profile.classFibre 𝒮 (classOf C v) γ := ⟨hS𝒮, hSγ⟩
  refine le_antisymm ?_ ?_
  · have := Profile.classInf_le_of_mem (μ := σ.massByProfile p) hmem
    refine (NNReal.coe_le_coe.2 this).trans ?_
    rw [coe_massByProfile_apply, σ.massBy_of_semistable p hφ, charge_def, hSγ]
  · exact Profile.le_classInf_of_forall_le (f := fun γ ↦ p (σ.Z γ))
      (fun S _ ↦ σ.seminorm_charge_le_massBy p S) ⟨S, hmem⟩

/-- The class infimum of `M_{σ,p}` is attained on a semistable representative. -/
theorem exists_classInf_massByProfile_eq {𝒮 : Set C} {γ : Λ}
    (h : ∃ S ∈ 𝒮, classOf C v S = γ ∧ ∃ φ, σ.slicing.P φ S) :
    ∃ S ∈ Profile.classFibre 𝒮 (classOf C v) γ,
      σ.massByProfile p S = Profile.classInf 𝒮 (classOf C v) (σ.massByProfile p) γ := by
  obtain ⟨S, hS𝒮, hSγ, φ, hφ⟩ := h
  refine ⟨S, ⟨hS𝒮, hSγ⟩, NNReal.coe_injective ?_⟩
  rw [σ.classInf_massByProfile p ⟨S, hS𝒮, hSγ, φ, hφ⟩, coe_massByProfile_apply,
    σ.massBy_of_semistable p hφ, charge_def, hSγ]

/-- **The class infimum of the mass is the modulus of the charge** (Kikuta–Koseki–Ouchi,
arXiv:2504.12253, Corollary 3.5): on every class with a semistable representative in `𝒮`,
`d_{m_σ}(γ) = |Z_σ(γ)|`, attained. -/
theorem classInf_massProfile {𝒮 : Set C} {γ : Λ}
    (h : ∃ S ∈ 𝒮, classOf C v S = γ ∧ ∃ φ, σ.slicing.P φ S) :
    (Profile.classInf 𝒮 (classOf C v) σ.massProfile γ : ℝ) = ‖σ.Z γ‖ := by
  rw [← massByProfile_normSeminorm, σ.classInf_massByProfile _ h]
  rfl

/-! ### Directional profiles -/

/-- The **directional profile** `ν_{σ,θ}(E) = Σ_i |Re(e^{-iθ} Z(A_i))|` over the HN factors. -/
def directional (θ : ℝ) (E : C) : ℝ := σ.massBy (directionalSeminorm θ) E

/-- The directional profile as a profile. -/
def directionalProfile (θ : ℝ) : Profile C := σ.massByProfile (directionalSeminorm θ)

theorem directional_eq_sum (θ : ℝ) {E : C} (F : HNFiltration C σ.slicing.P E) :
    σ.directional θ E = ∑ i, |(Complex.exp (-(θ * Complex.I)) * σ.charge (F.factor i)).re| := by
  rw [directional, σ.massBy_eq_sum _ F]
  simp

/-- `ν_{σ,θ} ≤ m_σ`. -/
theorem directional_le_mass (θ : ℝ) (E : C) : σ.directional θ E ≤ σ.mass E := by
  have := σ.massBy_le_mul_mass (directionalSeminorm θ) (c := 1)
    (fun z ↦ by rw [one_mul, directionalSeminorm_apply]; exact Complex.abs_re_exp_neg_mul_le z θ) E
  rwa [one_mul] at this

/-- **The barycentre identity**: `m_σ(E) = (1/4) ∫₀^{2π} ν_{σ,θ}(E) dθ`. -/
theorem mass_eq_integral_directional (E : C) :
    σ.mass E = (1 / 4) * ∫ θ in (0)..(2 * π), σ.directional θ E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [σ.mass_eq_sum F]
  simp_rw [σ.directional_eq_sum _ F]
  exact Complex.sum_norm_eq_integral Finset.univ _

/-- **One-sign sectors.** If every HN phase `ψ` of `E` has `cos(πψ - θ) ≥ 0`, then
`ν_{σ,θ}(E) = Re(e^{-iθ} Z(E))`. -/
theorem directional_eq_re_of_cos_nonneg (θ : ℝ) {E : C} (F : HNFiltration C σ.slicing.P E)
    (hF : ∀ i, 0 ≤ Real.cos (π * F.φ i - θ)) :
    σ.directional θ E = (Complex.exp (-(θ * Complex.I)) * σ.charge E).re := by
  rw [σ.directional_eq_sum θ F, σ.charge_postnikovTower_eq_sum F.toPostnikovTower, Finset.mul_sum,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ abs_of_nonneg ?_
  by_cases hz : IsZero (F.factor i)
  · simp [charge_isZero σ hz]
  obtain ⟨m, hm, hZ⟩ := σ.compat (F.φ i) _ (F.semistable i) hz
  change 0 ≤ (Complex.exp (-(θ * Complex.I)) * σ.charge (F.factor i)).re
  rw [hZ, ← mul_assoc, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add,
    show -(θ * Complex.I) + (π * F.φ i : ℝ) * Complex.I = ((π * F.φ i - θ : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  exact mul_nonneg hm.le (hF i)

/-- **Additivity on one-sign sectors.** On a distinguished triangle `E → F → G` whose three objects
have all their HN phases in a sector where `cos(πψ - θ) ≥ 0`,
`ν_{σ,θ}(F) = ν_{σ,θ}(E) + ν_{σ,θ}(G)`. -/
theorem directional_add_of_triangle (θ : ℝ) {E F G : C} {f : E ⟶ F} {g : F ⟶ G}
    {h : G ⟶ E⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (FE : HNFiltration C σ.slicing.P E) (FF : HNFiltration C σ.slicing.P F)
    (FG : HNFiltration C σ.slicing.P G) (hE : ∀ i, 0 ≤ Real.cos (π * FE.φ i - θ))
    (hF : ∀ i, 0 ≤ Real.cos (π * FF.φ i - θ)) (hG : ∀ i, 0 ≤ Real.cos (π * FG.φ i - θ)) :
    σ.directional θ F = σ.directional θ E + σ.directional θ G := by
  rw [σ.directional_eq_re_of_cos_nonneg θ FE hE, σ.directional_eq_re_of_cos_nonneg θ FF hF,
    σ.directional_eq_re_of_cos_nonneg θ FG hG, ← Complex.add_re, ← mul_add]
  have hK := classOf_triangle C v _ hT
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃] at hK
  rw [charge_def, charge_def, charge_def, hK, map_add]

/-- **The class infimum of a directional profile** is `|Re(e^{-iθ} Z(γ))|` on every class with a
semistable representative in `𝒮`: the absolute value of one real linear form of `γ`. -/
theorem classInf_directionalProfile (θ : ℝ) {𝒮 : Set C} {γ : Λ}
    (h : ∃ S ∈ 𝒮, classOf C v S = γ ∧ ∃ φ, σ.slicing.P φ S) :
    (Profile.classInf 𝒮 (classOf C v) (σ.directionalProfile θ) γ : ℝ) =
      |(Complex.exp (-(θ * Complex.I)) * σ.Z γ).re| := by
  rw [directionalProfile, σ.classInf_massByProfile _ h, directionalSeminorm_apply]

end PreStabilityCondition.WithClassMap

/-! ### Equivariance on a space of stability conditions -/

namespace StabilitySpaceHypotheses

variable {Stab : Type*} [PseudoMetricSpace Stab] {Γ : Type*} [Group Γ] [MulAction Γ Stab]
  (I : StabilitySpaceHypotheses C v Stab Γ)

/-- **Equivariance of the masses for a seminorm**: `M_{gσ,p}(Φ_g E) = M_{σ,p}(E)`; in particular
for the directional profiles. -/
theorem massBy_smul (p : Seminorm ℝ ℂ) (g : Γ) (σ : Stab) (E : C) :
    (I.cond (g • σ)).massBy p ((I.tri g).e.functor.obj E) = (I.cond σ).massBy p E := by
  obtain ⟨F⟩ := (I.cond σ).slicing.hn_exists E
  rw [(I.cond (g • σ)).massBy_eq_sum_of_slicing_eq p (I.slicing_smul g σ) ((I.tri g).mapHN F),
    (I.cond σ).massBy_eq_sum p F]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TriEquiv.mapHN_factor, I.charge_smul]

/-- Equivariance of the directional profiles: `ν_{gσ,θ}(Φ_g E) = ν_{σ,θ}(E)`. -/
theorem directional_smul (θ : ℝ) (g : Γ) (σ : Stab) (E : C) :
    (I.cond (g • σ)).directional θ ((I.tri g).e.functor.obj E) = (I.cond σ).directional θ E :=
  I.massBy_smul _ g σ E

end StabilitySpaceHypotheses

end CategoryTheory.Triangulated
