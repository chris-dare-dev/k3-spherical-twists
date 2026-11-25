/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.Braid
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.SupportProperty
import K3Twists.LinearAlgebra.Lattice.Arrangement
import K3Twists.LinearAlgebra.RootSystem.Spherical

/-!
# The kernel root system on the Mukai lattice of the elliptic K3 surface

The Mukai lattice `MukaiLattice ℤ NS` of the elliptic K3 surface with a section, `NS = ℤC ⊕ ℤF`,
carries the objects of `LinearAlgebra/RootSystem/Spherical.lean`, `LinearAlgebra/Lattice/
Arrangement.lean` and the punctured support bound of `LinearAlgebra/Lattice/Mukai/Support.lean`:

* **The spherical pairing** of the whole lattice, with infinitely many roots, is reduced
  (`sphericalPairing_isReduced_mukaiLattice`, `infinite_sphericalRoots`).
* **Signature `(2, 2)`**: the real Mukai form has `sigPos = 2` (`sigPos_mukaiForm`), from the
  positive plane of `(1, 0, -1)` and `(0, H, 0)` and the negative plane of `(0, C, 0)` and
  `(1, 0, 1)`.
* **An `A₁` stratum.** The normalized charge with `x = 3`, `β = -C/2`, `H = C + 2F`, `a = 1`
  (`stratumCharge`) vanishes on `v(𝒪_C) = (0, C, 1)`, the root `A` of the curve wall. Its kernel
  is negative definite (squares `-2c₁² - 5r²`), and its roots are exactly `±v(𝒪_C)`
  (`kernelRoots_stratumCharge`): the kernel root system is `A₁`
  (`kernelRootPairing_stratumCharge`). On a ball around it the punctured support bound holds for
  every other class of square at least `-2`, and the only roots whose charge vanishes there are
  `±v(𝒪_C)` (`exists_punctured_supportBound_stratumCharge`, `exists_ball_roots_stratumCharge`).
* **Two roots that never meet, two that do.** The roots `A = 𝒪_C` and `B = 𝒪_C(-1)[1]` of the
  curve wall pair to `2`: their sum is the isotropic class of a point, and no positive period
  vanishes on both (`not_exists_posPlane_wallA_wallB`). The roots `v(𝒪_X[1])` and `v(𝒪_C)`
  pair to `1`, an `A₂` configuration, and some positive period vanishes on both
  (`exists_posPlane_a2`).

These are lattice statements: that the charges are those of stability conditions is not
formalized.
-/

namespace AlgebraicGeometry.K3.EllipticWithSection

open Mukai RootPairing

/-! ### The spherical pairing of the Mukai lattice -/

lemma mukaiForm_intersection_comm (x y : MukaiLattice ℤ NS) :
    mukaiForm intersection x y = mukaiForm intersection y x :=
  mukaiForm_comm _ intersection_comm x y

lemma intersection_separating (x : NS) (hx : ∀ y, intersection x y = 0) : x = 0 := by
  have h1 := hx (1, 0)
  have h2 := hx (0, 1)
  simp only [intersection_apply] at h1 h2
  obtain ⟨a, b⟩ := x
  simp only at h1 h2
  ext <;> simp <;> omega

lemma injective_mukaiForm_intersection : Function.Injective (mukaiForm intersection) := by
  intro v w h
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_pairing_eq_zero intersection_separating fun y => ?_
  have := LinearMap.congr_fun h y
  rw [mukaiForm_apply, mukaiForm_apply] at this
  rw [pairing_sub_left, this, sub_self]

/-- **The spherical pairing of the Mukai lattice is reduced**, with no definiteness. -/
theorem sphericalPairing_isReduced_mukaiLattice :
    (sphericalPairing mukaiForm_intersection_comm injective_mukaiForm_intersection).IsReduced :=
  sphericalPairing_isReduced _ _

/-- The Mukai lattice has infinitely many roots: the line bundles `𝒪_X(nF)`. -/
theorem infinite_sphericalRoots : (sphericalRoots (mukaiForm intersection)).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => lineBundle (0, n))
    (fun m n h => by simpa [lineBundle] using h) fun n => ?_
  exact isSpherical_lineBundle _

/-! ### Signature `(2, 2)` -/

lemma intersectionReal_separating (x : ℝ × ℝ) (hx : ∀ y, intersectionReal x y = 0) : x = 0 := by
  have h1 := hx (1, 0)
  have h2 := hx (0, 1)
  simp only [intersectionReal_apply] at h1 h2
  obtain ⟨a, b⟩ := x
  simp only at h1 h2
  ext <;> simp <;> linarith

lemma mukaiForm_real_comm (x y : MukaiLattice ℝ (ℝ × ℝ)) :
    mukaiForm intersectionReal x y = mukaiForm intersectionReal y x :=
  mukaiForm_comm _ intersectionReal_comm x y

lemma mukaiForm_real_separating (w : MukaiLattice ℝ (ℝ × ℝ))
    (hw : ∀ y, mukaiForm intersectionReal w y = 0) : w = 0 :=
  eq_zero_of_forall_pairing_eq_zero intersectionReal_separating hw

/-- **The real Mukai form of the elliptic K3 has signature `(2, 2)`.** -/
theorem sigPos_mukaiForm : sigPos (mukaiForm intersectionReal).toQuadraticMap = 2 := by
  apply le_antisymm
  · -- a negative-definite plane: `(0, C, 0)` and `(1, 0, 1)`
    set a : MukaiLattice ℝ (ℝ × ℝ) := (0, (1, 0), 0)
    set b : MukaiLattice ℝ (ℝ × ℝ) := (1, (0, 0), 1)
    have hli : LinearIndependent ℝ ![a, b] := by
      refine LinearIndependent.pair_iff.mpr fun s t h => ?_
      have h1 := congrArg (fun v => v.2.1.1) h
      have h2 := congrArg (fun v => v.1) h
      simp [a, b] at h1 h2
      exact ⟨h1, h2⟩
    have hneg : ∀ x ∈ Submodule.span ℝ (Set.range ![a, b]),
        (mukaiForm intersectionReal).toQuadraticMap x ≤ 0 := by
      intro x hx
      obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        LinearMap.BilinMap.toQuadraticMap_apply, mukaiForm_apply, a, b]
      simp only [Mukai.pairing, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, intersectionReal_apply]
      nlinarith [sq_nonneg (g 0), sq_nonneg (g 1)]
    have := QuadraticForm.sigPos_add_finrank_le_of_nonpos hneg
    rw [finrank_span_eq_card hli, Fintype.card_fin] at this
    have hdim : Module.finrank ℝ (MukaiLattice ℝ (ℝ × ℝ)) = 4 := by
      simp [Module.finrank_prod]
    omega
  · -- a positive-definite plane: `(1, 0, -1)` and `(0, H, 0)`
    have := le_sigPos_of_forall_pos (mukaiForm intersectionReal)
      ![((1 : ℝ), ((0 : ℝ), (0 : ℝ)), (-1 : ℝ)), ((0 : ℝ), ((1 : ℝ), (2 : ℝ)), (0 : ℝ))]
      fun g hg => by
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mukaiForm_apply,
          Mukai.pairing, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, intersectionReal_apply]
        have : g 0 ≠ 0 ∨ g 1 ≠ 0 := by
          by_contra h
          push Not at h
          apply hg
          funext i
          fin_cases i <;> simp [h.1, h.2]
        rcases this with h | h
        · have : 0 < g 0 ^ 2 := by positivity
          nlinarith [sq_nonneg (g 1)]
        · have : 0 < g 1 ^ 2 := by positivity
          nlinarith [sq_nonneg (g 0)]
    exact this

/-! ### Two roots of the curve wall, and an `A₂` pair -/

lemma realModel_wallA : realModel toRealNS wallA = (0, (1, 0), 1) := by
  simp [wallA, curveSheaf, curve, realModel]

lemma realModel_wallB : realModel toRealNS wallB = (0, (-1, 0), 0) := by
  simp [wallB, curveSheaf, curve, realModel]

lemma realModel_structureSheaf_shift : realModel toRealNS (-lineBundle 0) = (-1, (0, 0), -1) := by
  simp [lineBundle, realModel]

/-- **The roots of the curve wall never meet in `P⁺`.** `v(𝒪_C)` and `v(𝒪_C(-1)[1])` pair to
`2`, and no positive period of the real Mukai lattice is orthogonal to both. -/
theorem not_exists_posPlane_wallA_wallB :
    ¬∃ Ω₁ Ω₂, IsPosPlane (mukaiForm intersectionReal) Ω₁ Ω₂ ∧
      mukaiForm intersectionReal Ω₁ (realModel toRealNS wallA) = 0 ∧
      mukaiForm intersectionReal Ω₂ (realModel toRealNS wallA) = 0 ∧
      mukaiForm intersectionReal Ω₁ (realModel toRealNS wallB) = 0 ∧
      mukaiForm intersectionReal Ω₂ (realModel toRealNS wallB) = 0 := by
  rw [exists_posPlane_orthogonal_pair_iff _ mukaiForm_real_comm mukaiForm_real_separating
    sigPos_mukaiForm]
  · rw [realModel_wallA, realModel_wallB]
    norm_num [Mukai.pairing]
  · rw [realModel_wallA]; norm_num [Mukai.pairing]
  · rw [realModel_wallB]; norm_num [Mukai.pairing]
  · rw [realModel_wallA, realModel_wallB]
    refine LinearIndependent.pair_iff.mpr fun s t h => ?_
    have h1 := congrArg (fun v => v.2.1.1) h
    have h2 := congrArg (fun v => v.2.2) h
    simp at h1 h2
    exact ⟨h2, by linarith⟩

/-- **An `A₂` pair meets in `P⁺`.** `v(𝒪_X[1])` and `v(𝒪_C)` pair to `1`, and some positive period
of the real Mukai lattice is orthogonal to both. -/
theorem exists_posPlane_a2 :
    ∃ Ω₁ Ω₂, IsPosPlane (mukaiForm intersectionReal) Ω₁ Ω₂ ∧
      mukaiForm intersectionReal Ω₁ (realModel toRealNS (-lineBundle 0)) = 0 ∧
      mukaiForm intersectionReal Ω₂ (realModel toRealNS (-lineBundle 0)) = 0 ∧
      mukaiForm intersectionReal Ω₁ (realModel toRealNS wallA) = 0 ∧
      mukaiForm intersectionReal Ω₂ (realModel toRealNS wallA) = 0 := by
  rw [exists_posPlane_orthogonal_pair_iff _ mukaiForm_real_comm mukaiForm_real_separating
    sigPos_mukaiForm]
  · rw [realModel_structureSheaf_shift, realModel_wallA]
    norm_num [Mukai.pairing]
  · rw [realModel_structureSheaf_shift]; norm_num [Mukai.pairing]
  · rw [realModel_wallA]; norm_num [Mukai.pairing]
  · rw [realModel_structureSheaf_shift, realModel_wallA]
    refine LinearIndependent.pair_iff.mpr fun s t h => ?_
    have h1 := congrArg (fun v => v.1) h
    have h2 := congrArg (fun v => v.2.1.1) h
    simp at h1 h2
    exact ⟨h1, h2⟩

/-! ### An `A₁` stratum -/

/-- The normalized charge with `x = 3`, `β = -C/2`, `H = C + 2F`, `a = 1`. -/
noncomputable abbrev stratumCharge : MukaiLattice ℝ (ℝ × ℝ) →ₗ[ℝ] ℂ :=
  normalizedCharge intersectionReal 3 (-1 / 2, 0) polarizationReal 1

/-- The stratum charge on integral classes. -/
noncomputable def stratumChargeInt : MukaiLattice ℤ NS →+ ℂ :=
  stratumCharge.toAddMonoidHom.comp (realModel toRealNS)

/-- On the kernel of the stratum charge a real class has `c₂ = r`, `s = 5r/2 + c₁` and square
`-2c₁² - 5r²`. -/
lemma ker_stratumCharge {v : MukaiLattice ℝ (ℝ × ℝ)} (hv : stratumCharge v = 0) :
    v.2.1.2 = v.1 ∧ 2 * v.2.2 = 5 * v.1 + 2 * v.2.1.1 ∧
      selfPairing intersectionReal v = -2 * v.2.1.1 ^ 2 - 5 * v.1 ^ 2 := by
  have hre := congrArg Complex.re hv
  have him := congrArg Complex.im hv
  rw [re_normalizedCharge, Complex.zero_re] at hre
  rw [im_normalizedCharge, Complex.zero_im] at him
  obtain ⟨r, ⟨c₁, c₂⟩, s⟩ := v
  simp only [intersectionReal_apply] at hre him
  have h2 : c₂ = r := by linarith
  have hs : 2 * s = 5 * r + 2 * c₁ := by rw [h2] at hre; linarith
  refine ⟨h2, hs, ?_⟩
  simp only [selfPairing_mk, intersectionReal_apply]
  rw [h2]
  linear_combination (-r) * hs

/-- The kernel of the stratum charge is negative definite on real classes. -/
theorem negDef_ker_stratumCharge (v : MukaiLattice ℝ (ℝ × ℝ)) (hv : stratumCharge v = 0)
    (hv0 : v ≠ 0) : mukaiForm intersectionReal v v < 0 := by
  obtain ⟨h2, hs, hsq⟩ := ker_stratumCharge hv
  change selfPairing intersectionReal v < 0
  rw [hsq]
  obtain ⟨r, ⟨c₁, c₂⟩, s⟩ := v
  simp only at h2 hs ⊢
  by_cases hr : r = 0
  · have hc₁ : c₁ ≠ 0 := by
      intro hc₁
      apply hv0
      have : s = 0 := by rw [hr, hc₁] at hs; linarith
      simp [hr, hc₁, h2, this]
    have : 0 < c₁ ^ 2 := by positivity
    nlinarith
  · have : 0 < r ^ 2 := by positivity
    nlinarith [sq_nonneg c₁]

/-- On integral classes the stratum charge vanishes exactly on `(2k, (c₁, 2k), 5k + c₁)`, of
square `-2c₁² - 20k²`. -/
lemma ker_stratumChargeInt {v : MukaiLattice ℤ NS} (hv : stratumChargeInt v = 0) :
    v.2.1.2 = v.1 ∧ 2 * v.2.2 = 5 * v.1 + 2 * v.2.1.1 ∧
      selfPairing intersection v = -2 * v.2.1.1 ^ 2 - 5 * v.1 ^ 2 := by
  obtain ⟨h2, hs, hsq⟩ := ker_stratumCharge (v := realModel toRealNS v) hv
  rw [selfPairing_realModel intersectionReal_toRealNS] at hsq
  obtain ⟨r, ⟨c₁, c₂⟩, s⟩ := v
  simp only [realModel_apply, toRealNS_apply] at h2 hs hsq
  refine ⟨by exact_mod_cast h2, by exact_mod_cast hs, by exact_mod_cast hsq⟩

/-- The form is negative on the nonzero lattice points of the kernel. -/
theorem negDef_ker_stratumChargeInt (v : MukaiLattice ℤ NS) (hv : stratumChargeInt v = 0)
    (hv0 : v ≠ 0) : mukaiForm intersection v v < 0 := by
  have h := negDef_ker_stratumCharge (realModel toRealNS v) hv fun h => hv0 (by
    obtain ⟨r, ⟨c₁, c₂⟩, s⟩ := v
    simp only [realModel_apply, toRealNS_apply, Prod.mk_eq_zero, Int.cast_eq_zero] at h
    simp [h])
  change selfPairing intersectionReal _ < 0 at h
  rw [selfPairing_realModel intersectionReal_toRealNS] at h
  exact_mod_cast h

/-- **The roots of the stratum are `±v(𝒪_C)`**: the kernel root system is `A₁`. -/
theorem kernelRoots_stratumCharge :
    kernelRoots (mukaiForm intersection) stratumChargeInt = {wallA, -wallA} := by
  ext v
  constructor
  · rintro ⟨hv, hZ⟩
    obtain ⟨h2, hs, hsq⟩ := ker_stratumChargeInt hZ
    have hv' : selfPairing intersection v = -2 := hv
    rw [hv'] at hsq
    obtain ⟨r, ⟨c₁, c₂⟩, s⟩ := v
    simp only at h2 hs hsq
    have hr : r = 0 := by nlinarith [sq_nonneg c₁, sq_nonneg r]
    subst hr
    have hc : c₁ = 1 ∨ c₁ = -1 := by
      have : (c₁ - 1) * (c₁ + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp this with h | h
      · left; omega
      · right; omega
    have hs' : s = c₁ := by omega
    rcases hc with rfl | rfl
    · left; simp [wallA, curveSheaf, curve, h2, hs']
    · right; simp [wallA, curveSheaf, curve, h2, hs']
  · rintro (rfl | rfl)
    · refine ⟨isSpherical_wallA, ?_⟩
      simp [stratumChargeInt, realModel_wallA, Complex.ext_iff, re_normalizedCharge,
        im_normalizedCharge]
      norm_num
    · refine ⟨(isSpherical_wallA).neg, ?_⟩
      simp [stratumChargeInt, realModel_wallA, Complex.ext_iff, re_normalizedCharge,
        im_normalizedCharge]
      norm_num

/-- **The kernel root system at the stratum** is a finite, reduced, simply laced root pairing:
`A₁`. -/
theorem kernelRootPairing_stratumCharge :
    Finite (sphericalRoots (kernelForm (mukaiForm intersection) stratumChargeInt)) ∧
      (kernelRootPairing mukaiForm_intersection_comm negDef_ker_stratumChargeInt).IsReduced ∧
      ∀ i j : sphericalRoots (kernelForm (mukaiForm intersection) stratumChargeInt), i ≠ j →
        (i : kernelLattice stratumChargeInt) ≠ -(j : kernelLattice stratumChargeInt) →
        (kernelRootPairing mukaiForm_intersection_comm negDef_ker_stratumChargeInt).pairing i j ∈
          ({-1, 0, 1} : Set ℤ) :=
  kernelRootPairing_finite_isReduced_simplyLaced _ _

/-- **The punctured support bound at the stratum.** On a ball around the stratum charge, every
integral class of square at least `-2` other than `0` and `±v(𝒪_C)` has `‖v‖ ≤ K |Z(v)|`. -/
theorem exists_punctured_supportBound_stratumCharge :
    ∃ η > 0, ∃ K, ∀ Z : MukaiLattice ℝ (ℝ × ℝ) →L[ℝ] ℂ,
      ‖Z - LinearMap.toContinuousLinearMap stratumCharge‖ < η →
      ∀ v : MukaiLattice ℤ NS, -2 ≤ selfPairing intersection v → v ≠ 0 → v ≠ wallA →
        v ≠ -wallA → ‖realModel toRealNS v‖ ≤ K * ‖Z (realModel toRealNS v)‖ := by
  obtain ⟨η, hη, K, hK⟩ := exists_punctured_supportBound (mukaiForm intersectionReal)
    (LinearMap.toContinuousLinearMap stratumCharge) negDef_ker_stratumCharge
    (finite_range_realModel_norm_le finite_toRealNS_norm_le)
  refine ⟨η, hη, K, fun Z hZ v hv hv0 hA hA' => hK Z hZ _ ⟨v, rfl⟩ ?_ ?_⟩
  · change -2 ≤ selfPairing intersectionReal _
    rw [selfPairing_realModel intersectionReal_toRealNS]
    exact_mod_cast hv
  · intro hZ₀
    have hZ₀' : stratumChargeInt v = 0 := hZ₀
    have hneg := negDef_ker_stratumChargeInt v hZ₀' hv0
    have hroot : v ∈ kernelRoots (mukaiForm intersection) stratumChargeInt := by
      refine ⟨?_, hZ₀'⟩
      obtain ⟨_, _, hsq⟩ := ker_stratumChargeInt hZ₀'
      have hv' : -2 ≤ selfPairing intersection v := hv
      have hlt : selfPairing intersection v < 0 := hneg
      change selfPairing intersection v = -2
      rw [hsq] at hv' hlt ⊢
      have hr : v.1 = 0 := by nlinarith [sq_nonneg v.2.1.1, sq_nonneg v.1]
      rw [hr] at hv' hlt ⊢
      generalize v.2.1.1 ^ 2 = x at hv' hlt ⊢
      omega
    rw [kernelRoots_stratumCharge] at hroot
    rcases hroot with h | h
    · exact hA h
    · exact hA' h

/-- **The only roots vanishing near the stratum are `±v(𝒪_C)`.** -/
theorem exists_ball_roots_stratumCharge :
    ∃ η > 0, ∀ Z : MukaiLattice ℝ (ℝ × ℝ) →L[ℝ] ℂ,
      ‖Z - LinearMap.toContinuousLinearMap stratumCharge‖ < η →
      ∀ δ : MukaiLattice ℤ NS, IsSpherical intersection δ → Z (realModel toRealNS δ) = 0 →
        δ = wallA ∨ δ = -wallA := by
  obtain ⟨η, hη, K, hK⟩ := exists_punctured_supportBound_stratumCharge
  refine ⟨η, hη, fun Z hZ δ hδ hZδ => ?_⟩
  by_contra h
  push Not at h
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    simp [IsSpherical] at hδ
  have := hK Z hZ δ (by rw [show selfPairing intersection δ = -2 from hδ]) hδ0 h.1 h.2
  rw [hZδ, norm_zero, mul_zero, norm_le_zero_iff] at this
  apply hδ0
  obtain ⟨r, ⟨c₁, c₂⟩, s⟩ := δ
  simp only [realModel_apply, toRealNS_apply, Prod.mk_eq_zero, Int.cast_eq_zero] at this
  simp [this]

end AlgebraicGeometry.K3.EllipticWithSection
