/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.Visibility
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.Basic

/-!
# Visibility on the cover: the stability statement

Let `X` be a K3 surface with `Pic X = ℤH`, `H² = 2d`. The lemma "Visibility on the cover" of the
article "Harder–Narasimhan towers of spherical twist words on a Picard-rank-one K3 surface" says:

* a spherical object, up to shift, is stable exactly where the straight segment to its puncture
  meets no intervening puncture and lifts to its marking;
* a point image `G 𝒪_x` is stable exactly when `G⁻¹σ` is in the geometric chamber; equivalently,
  the ray to its cusp is unobstructed and has the prescribed marking.

Mathlib has neither derived categories of K3 surfaces nor Bridgeland stability, so this file
proves the lemma from the inputs listed in `VisibilityHypotheses`. Each field cites its source,
mostly Bayer–Bridgeland, *Derived automorphism groups of K3 surfaces of Picard rank 1*
(arXiv:1310.8266, cited as [BB]), and Bridgeland, *Stability conditions on K3 surfaces*
(arXiv:math/0307164). The lattice and geometric arguments come from
`AlgebraicGeometry.K3.PicardRankOne.Visibility` and are proved from Mathlib alone.

The objects are isomorphism classes with the shift as an action of `ℤ`; a stability condition
`σ` has a point `base σ` of the projective model (the kernel line of its central charge), and
`Z_σ` is the geometric central charge at that point followed by a real-linear automorphism of
`ℂ`. A *marked puncture* `ℓ` is a component of the preimage, in the cover, of a small punctured
disc about the puncture of a root `root ℓ` of positive rank; `Sees σ ℓ` says that the segment from
`base σ` to that puncture is clear and lifts, from `σ`, into `ℓ`; `sphere ℓ` is the sphere marked
by `ℓ`, a deck translate of the spherical bundle of class `root ℓ`.

## Main results

* `stable_of_semistable_of_segmentClear`: a semistable sphere whose puncture is seen along a clear
  segment is stable (the rigid-factor lemma and `eq_singleton_of_segmentClear`);
* `stable_sphere_of_sees`: the sphere of a marked puncture is stable wherever the puncture is
  seen with its marking, since stability can neither appear nor be lost first along the
  (connected) locus of such points;
* `segmentClear_of_stable`: where a sphere is stable, the segment to its puncture is clear (a
  first obstacle would carry a stable sphere of the same phase with negative pairing);
* `eq_of_stable_of_cl_eq`: a stable sphere is determined by its class and phase;
* `exists_sees_of_stable`, `exists_eq_vadd_sphere`, `stable_vadd_sphere_iff`,
  `stable_iff_sees_marking`, `stable_iff_segmentClear_and_sees`: **the lemma**: every sphere is a
  shifted marked sphere `n +ᵥ sphere ℓ` (with `ℓ = marking`), and it is stable at `σ` exactly
  when `σ` sees `ℓ`, that is when the segment from `base σ` to its puncture is clear and lifts to
  its marking;
* `stable_smul_point_iff`, `stable_smul_point_iff_rayClear`: a point image `G 𝒪_x` is stable at
  `σ` exactly when `G⁻¹σ` is geometric, that is when `G⁻¹σ` lies on the geometric sheet and the
  upward ray from its point is clear, by Bayer–Bridgeland's description of the geometric chamber
  and `rayClear_iff`;
* `rayClear_inv_smul_iff`: the Mukai action `G_*` carries that upward ray to the sight line from
  `base σ` to the cusp of `v(G 𝒪_x)`, since it is an isometry matching the charges of `G⁻¹σ` with
  those of `σ` (`cuspRayClear_iff_of_isometry`);
* `stable_smul_point_iff_cuspRayClear`, `stable_smul_point_iff_cuspClear`,
  `stable_smul_point_iff_rayClear_of_r_eq_zero`: **the lemma for point images**: `G 𝒪_x` is
  stable at `σ` exactly when the ray from `base σ` to its cusp is unobstructed and has the
  prescribed marking (`G⁻¹σ` on the geometric sheet); the ray is the straight segment to the cusp
  `(c/r, (c/r)²)` when `v(G 𝒪_x) = (r, c, s)` has `r ≠ 0`, and the upward ray when `r = 0`.
-/

noncomputable section

namespace AlgebraicGeometry.K3.PicardRankOne

open MukaiVector Complex

/-! ### Phases of real-proportional charges -/

/-- If `m₁ e^{iπφ₁} = c m₂ e^{iπφ₂}` with `m₁, m₂ > 0` and `c` real, the phases differ by an
integer `j`, which is even exactly when `c > 0`. -/
lemma exists_int_phase_sub {m₁ m₂ φ₁ φ₂ c : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h : (m₁ : ℂ) * exp (↑(Real.pi * φ₁) * I) = c * (m₂ * exp (↑(Real.pi * φ₂) * I))) :
    ∃ j : ℤ, φ₁ - φ₂ = j ∧ (0 < c ↔ Even j) := by
  have hpi := Real.pi_pos
  set u : ℝ := c * m₂ / m₁ with hu
  have hexp : exp (↑(Real.pi * (φ₁ - φ₂)) * I) = u := by
    have h2 : exp (↑(Real.pi * φ₂) * I) ≠ 0 := exp_ne_zero _
    have hm : (m₁ : ℂ) ≠ 0 := by exact_mod_cast hm₁.ne'
    have hsplit : exp (↑(Real.pi * φ₁) * I) =
        exp (↑(Real.pi * (φ₁ - φ₂)) * I) * exp (↑(Real.pi * φ₂) * I) := by
      rw [← exp_add]; congr 1; push_cast; ring
    rw [hsplit] at h
    have : (m₁ : ℂ) * exp (↑(Real.pi * (φ₁ - φ₂)) * I) = c * m₂ := by
      apply mul_right_cancel₀ h2; linear_combination h
    rw [hu, Complex.ofReal_div, Complex.ofReal_mul c m₂, eq_div_iff hm]
    linear_combination this
  have hnorm : |u| = 1 := by
    have := congrArg norm hexp
    rwa [norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, eq_comm] at this
  have hc : 0 < c ↔ 0 < u := by
    rw [hu]
    constructor
    · intro hc; positivity
    · intro h'
      by_contra hc
      push Not at hc
      have : c * m₂ / m₁ ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hc hm₂.le) hm₁.le
      linarith
  rcases abs_eq (zero_le_one' ℝ) |>.mp hnorm with h1 | h1
  · -- `e^{iπ(φ₁ - φ₂)} = 1`
    rw [h1, Complex.ofReal_one, ← exp_zero, exp_eq_exp_iff_exists_int] at hexp
    obtain ⟨n, hn⟩ := hexp
    have him := congrArg Complex.im hn
    simp at him
    refine ⟨2 * n, ?_, ?_⟩
    · push_cast
      have : Real.pi * (φ₁ - φ₂) = Real.pi * (2 * n) := by linarith
      exact mul_left_cancel₀ hpi.ne' this
    · rw [hc, h1]; simp
  · -- `e^{iπ(φ₁ - φ₂)} = -1`
    rw [h1, Complex.ofReal_neg, Complex.ofReal_one, ← exp_pi_mul_I,
      exp_eq_exp_iff_exists_int] at hexp
    obtain ⟨n, hn⟩ := hexp
    have him := congrArg Complex.im hn
    simp at him
    refine ⟨2 * n + 1, ?_, ?_⟩
    · push_cast
      have : Real.pi * (φ₁ - φ₂) = Real.pi * (2 * n + 1) := by linarith
      exact mul_left_cancel₀ hpi.ne' this
    · rw [hc, h1]
      simp only [Left.neg_pos_iff, Int.even_add_one, even_two, Even.mul_right, not_true_eq_false,
        iff_false, not_lt]
      norm_num

/-! ### The inputs -/

/-- The inputs of the lemma "Visibility on the cover".

`Obj` stands for the isomorphism classes of objects of `D^b(X)`, with the shift `[n]` written
`n +ᵥ E`; `Stab` for the distinguished component `Stab†(X)` with its topology; `Mark` for the
marked punctures, the components of the preimages in the cover of small punctured discs about
the punctures; `Γ` for a group of autoequivalences acting on objects and on `Stab`. -/
structure VisibilityHypotheses (Obj Stab Mark Γ : Type*) [AddAction ℤ Obj] [TopologicalSpace Stab]
    [Group Γ] [MulAction Γ Obj] [MulAction Γ Stab] where
  /-- `H² = 2d`. -/
  d : ℤ
  d_pos : 0 < d
  /-- The Mukai vector `v(E) = (r, c, s)`. -/
  cl : Obj → MukaiVector ℤ
  /-- `v(E[1]) = -v(E)`. -/
  cl_vadd_one : ∀ E, cl ((1 : ℤ) +ᵥ E) = -cl E
  /-- Spherical objects. -/
  Spherical : Obj → Prop
  /-- A shift of a spherical object is spherical. -/
  spherical_vadd : ∀ (n : ℤ) E, Spherical E → Spherical (n +ᵥ E)
  /-- A spherical object has `v(E)² = -χ(E, E) = -2` (Riemann–Roch). -/
  isRoot_cl : ∀ E, Spherical E → IsRoot d (cl E)
  /-- The point `(b, t)` of the projective model under `σ`: the kernel line of `Z_σ` on real
  classes. -/
  base : Stab → ℝ × ℝ
  base_mem : ∀ σ, (base σ).1 ^ 2 < (base σ).2
  /-- The central charge `Z_σ`. -/
  charge : Stab → MukaiVector ℤ → ℂ
  /-- The real-linear change of normalization taking the geometric charge at `base σ` to `Z_σ`. -/
  normalization : Stab → ℂ ≃ₗ[ℝ] ℂ
  /-- `Z_σ = A_σ ∘ Z_{base σ}`. Bridgeland's covering map `Stab†(X) → 𝒫⁺₀(X)`
  (arXiv:math/0307164, Theorem 1.1) gives `Z_σ = ⟨Ω_σ, -⟩`, and modulo `GL⁺₂(ℝ)` the vector
  `Ω_σ` is `exp(zH)` for a point `z` of the punctured half-plane ([BB], equations (2) and (3)). -/
  charge_eq : ∀ σ v, charge σ v = normalization σ (modelCharge d (base σ) v.toReal)
  /-- No stability condition lies over a puncture: `Z_σ(δ) ≠ 0` for every root, since `Ω_σ` lies
  in `𝒫⁺₀(X)` (arXiv:math/0307164, Theorem 1.1). -/
  charge_ne_zero : ∀ σ δ, IsRoot d δ → charge σ δ ≠ 0
  /-- `σ`-semistable objects. -/
  Semistable : Stab → Obj → Prop
  /-- `σ`-stable objects. -/
  Stable : Stab → Obj → Prop
  semistable_of_stable : ∀ σ E, Stable σ E → Semistable σ E
  /-- Shifts preserve stability. -/
  stable_vadd : ∀ σ (n : ℤ) E, Stable σ E → Stable σ (n +ᵥ E)
  /-- The phase `φ_σ(E)` of a semistable object. -/
  phase : Stab → Obj → ℝ
  /-- `φ(E[n]) = φ(E) + n`. -/
  phase_vadd : ∀ σ (n : ℤ) E, phase σ (n +ᵥ E) = phase σ E + n
  /-- A semistable object of phase `φ` has `Z_σ(E) ∈ ℝ_{>0} e^{iπφ}` (the compatibility of a
  slicing with its central charge). -/
  charge_cl : ∀ σ E, Semistable σ E →
    ∃ m : ℝ, 0 < m ∧ charge σ (cl E) = m * exp (↑(Real.pi * phase σ E) * I)
  /-- The stable factors of a semistable object, with multiplicity: the Jordan–Hölder factors in
  the finite length category `𝒫(φ)` ([BB], §2, wall-crossing). -/
  factors : Stab → Obj → List Obj
  factors_stable : ∀ σ E, Semistable σ E → ∀ F ∈ factors σ E, Stable σ F ∧ phase σ F = phase σ E
  factors_sum : ∀ σ E, Semistable σ E → ((factors σ E).map cl).sum = cl E
  /-- A semistable object with a single stable factor is stable. -/
  stable_of_length_factors : ∀ σ E, Semistable σ E → (factors σ E).length = 1 → Stable σ E
  /-- **The rigid-factor lemma** ([BB], Lemma 2.6 (a)): the stable factors of a rigid object are
  rigid, and a rigid stable object on a K3 surface is spherical. -/
  spherical_of_mem_factors : ∀ σ E, Spherical E → Semistable σ E → ∀ F ∈ factors σ E,
    Spherical F
  /-- Non-isomorphic stable objects of one phase have no morphisms in either direction, so by
  Serre duality and Riemann–Roch `⟨v(E), v(F)⟩ = -χ(E, F) = ext¹(E, F) ≥ 0` (the proof of
  [BB], Lemma 3.1). -/
  pairing_nonneg : ∀ σ E F, Stable σ E → Stable σ F → phase σ E = phase σ F → E ≠ F →
    0 ≤ pairing d (cl E) (cl F)
  /-- Stability is open ([BB], Proposition 2.10). -/
  isOpen_stable : ∀ E, IsOpen {σ | Stable σ E}
  /-- Semistability is closed: the phases `φ^±_σ(E)` are continuous in `σ`, being `1`-Lipschitz
  for Bridgeland's metric (arXiv:math/0212237, §8). -/
  isClosed_semistable : ∀ E, IsClosed {σ | Semistable σ E}
  /-- The root of positive rank whose puncture a marked puncture lies over. -/
  root : Mark → MukaiVector ℤ
  isRoot_root : ∀ ℓ, IsRoot d (root ℓ)
  root_r_pos : ∀ ℓ, 0 < (root ℓ).r
  /-- `σ` sees the marked puncture `ℓ`: the straight segment from `base σ` to the puncture of
  `root ℓ` is clear and its lift from `σ` ends in `ℓ`. -/
  Sees : Stab → Mark → Prop
  segmentClear_of_sees : ∀ σ ℓ, Sees σ ℓ → SegmentClear d (base σ) (root ℓ)
  /-- A clear segment lifts from `σ` and ends in some marked puncture over its end: path lifting
  in the cover `Stab†(X)/GL̃⁺₂(ℝ)` of the punctured half-plane (arXiv:math/0307164,
  Theorem 1.1; [BB], Theorem 1.3). -/
  exists_sees : ∀ σ δ, IsRoot d δ → 0 < δ.r → SegmentClear d (base σ) δ →
    ∃ ℓ, root ℓ = δ ∧ Sees σ ℓ
  /-- The points that see a marked puncture form a connected set: two of them are joined by
  following their lifted sight segments into the lifted punctured disc and connecting them there
  (the proof of the lemma "Visibility on the cover"). -/
  isPreconnected_sees : ∀ ℓ, IsPreconnected {σ | Sees σ ℓ}
  /-- The sphere marked by `ℓ`: the deck translate of the spherical bundle `S_δ` of class
  `δ = root ℓ` ([BB], Proposition 2.3, Theorem 1.4). -/
  sphere : Mark → Obj
  spherical_sphere : ∀ ℓ, Spherical (sphere ℓ)
  cl_sphere : ∀ ℓ, cl (sphere ℓ) = root ℓ
  /-- The sphere of `ℓ` is stable near its marked puncture ([BB], Lemma 5.3 and its
  footnote, translated by the deck group). -/
  exists_stable_sphere : ∀ ℓ, ∃ σ, Sees σ ℓ ∧ Stable σ (sphere ℓ)
  /-- Distinct marked punctures carry spheres that differ even up to shift: a deck element fixing
  a sphere up to shift centralizes the loop `T²` around its puncture, so lies in the cyclic group
  it generates, the stabilizer of the marked puncture ([BB], Proposition 2.3 and Theorem 1.4). -/
  sphere_injective : ∀ ℓ ℓ' (n : ℤ), n +ᵥ sphere ℓ = sphere ℓ' → ℓ = ℓ'
  /-- Every spherical object is stable somewhere ([BB], Corollary 6.9). -/
  exists_stable : ∀ E, Spherical E → ∃ σ, Stable σ E
  /-- Autoequivalences act compatibly on objects and stability conditions:
  `g (Z, 𝒫) = (Z ∘ g_*⁻¹, g 𝒫)` ([BB], §2). -/
  stable_smul : ∀ (g : Γ) σ E, Stable (g • σ) (g • E) ↔ Stable σ E
  /-- The action `g_*` of an autoequivalence on the Mukai lattice. -/
  act : Γ → MukaiVector ℤ → MukaiVector ℤ
  /-- `g_*` is an isometry: the cohomological action of a Fourier–Mukai equivalence preserves the
  integral structure and the Mukai pairing ([BB], §1). -/
  pairing_act : ∀ g v w, pairing d (act g v) (act g w) = pairing d v w
  act_one : ∀ v, act 1 v = v
  act_mul : ∀ g h v, act (g * h) v = act g (act h v)
  /-- `v(gE) = g_* v(E)`. -/
  cl_smul : ∀ g E, cl (g • E) = act g (cl E)
  /-- `Z_{gσ}(g_* v) = Z_σ(v)` ([BB], §2). -/
  charge_smul : ∀ g σ v, charge (g • σ) (act g v) = charge σ v
  /-- A skyscraper sheaf `𝒪_x`. -/
  point : Obj
  /-- `v(𝒪_x) = (0, 0, 1)`. -/
  cl_point : cl point = MukaiVector.point
  /-- The geometric chamber `U(X)`: the stability conditions in which all skyscraper sheaves are
  stable of one phase. -/
  Geometric : Stab → Prop
  /-- One skyscraper sheaf is stable exactly in the geometric chamber ([BB], Lemma 6.7). -/
  stable_point_iff : ∀ σ, Stable σ point ↔ Geometric σ
  /-- The geometric sheet: the lift of the slit region `V(X)` that contains `U(X)`. -/
  OnGeometricSheet : Stab → Prop
  /-- The geometric chamber is the part of the geometric sheet over
  `V(X) = {z : Z_z(δ) ∉ ℝ_{≤0} for every root δ of positive rank}` ([BB], Theorem 2.2). -/
  geometric_iff : ∀ σ, Geometric σ ↔ OnGeometricSheet σ ∧ ∀ δ : MukaiVector ℤ, IsRoot d δ →
    0 < δ.r → ∀ x : ℝ, x ≤ 0 → modelCharge d (base σ) δ.toReal ≠ x

namespace VisibilityHypotheses

variable {Obj Stab Mark Γ : Type*} [AddAction ℤ Obj] [TopologicalSpace Stab] [Group Γ]
  [MulAction Γ Obj] [MulAction Γ Stab] (I : VisibilityHypotheses Obj Stab Mark Γ)

/-! ### Shifts and classes -/

private lemma neg_neg_mukai (v : MukaiVector ℤ) : - -v = v := by ext <;> simp

lemma cl_vadd_add_one (n : ℤ) (E : Obj) : I.cl ((n + 1) +ᵥ E) = -I.cl (n +ᵥ E) := by
  rw [add_comm, add_vadd, I.cl_vadd_one]

lemma cl_vadd_two_mul (k : ℤ) (E : Obj) : I.cl ((2 * k) +ᵥ E) = I.cl E := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show 2 * ((k : ℤ) + 1) = (2 * k + 1) + 1 by ring, I.cl_vadd_add_one, I.cl_vadd_add_one,
      neg_neg_mukai, ih]
  | pred k ih =>
    have h := I.cl_vadd_add_one (2 * (-(k : ℤ) - 1) + 1) E
    rw [show 2 * (-(k : ℤ) - 1) + 1 + 1 = 2 * -(k : ℤ) by ring, ih, I.cl_vadd_add_one,
      neg_neg_mukai] at h
    exact h.symm

/-- `v(E[n]) = ±v(E)`, with the sign `+` exactly for even `n`. -/
lemma cl_vadd (n : ℤ) (E : Obj) : I.cl (n +ᵥ E) = if Even n then I.cl E else -I.cl E := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · simp only [even_two_mul, ↓reduceIte, I.cl_vadd_two_mul]
  · simp only [Int.not_even_two_mul_add_one, ↓reduceIte, I.cl_vadd_add_one, I.cl_vadd_two_mul]

/-- Roots have nonzero rank. -/
lemma r_ne_zero_of_isRoot {δ : MukaiVector ℤ} (hδ : IsRoot I.d δ) : δ.r ≠ 0 := by
  intro h
  rw [isRoot_iff] at hδ
  rw [h, zero_mul] at hδ
  nlinarith [I.d_pos, sq_nonneg δ.c]

lemma isRoot_neg {δ : MukaiVector ℤ} (hδ : IsRoot I.d δ) : IsRoot I.d (-δ) := by
  unfold IsRoot at hδ ⊢
  rw [pairing_neg_left, pairing_neg_right, neg_neg, hδ]

/-- The class of `E` normalized to positive rank: `v(E)` or `-v(E)`. -/
def posClass (E : Obj) : MukaiVector ℤ := if 0 < (I.cl E).r then I.cl E else -I.cl E

lemma posClass_r_pos {E : Obj} (hE : I.Spherical E) : 0 < (I.posClass E).r := by
  have := I.r_ne_zero_of_isRoot (I.isRoot_cl E hE)
  unfold posClass
  split_ifs with h
  · exact h
  · simp only [neg_r]; omega

lemma isRoot_posClass {E : Obj} (hE : I.Spherical E) : IsRoot I.d (I.posClass E) := by
  unfold posClass
  split_ifs
  · exact I.isRoot_cl E hE
  · exact I.isRoot_neg (I.isRoot_cl E hE)

/-! ### Charges -/

lemma charge_add (σ : Stab) (v w : MukaiVector ℤ) :
    I.charge σ (v + w) = I.charge σ v + I.charge σ w := by
  rw [I.charge_eq, I.charge_eq, I.charge_eq, ← map_add]
  congr 1
  have : (v + w).toReal = v.toReal + w.toReal := by ext <;> simp
  rw [this, modelCharge_add]

lemma charge_neg (σ : Stab) (v : MukaiVector ℤ) : I.charge σ (-v) = -I.charge σ v := by
  rw [I.charge_eq, I.charge_eq, ← map_neg]
  congr 1
  have : (-v).toReal = -v.toReal := by ext <;> simp
  rw [this, modelCharge_neg]

/-- Real-proportional central charges are real-proportional geometric charges. -/
lemma modelCharge_eq_of_charge_eq {σ : Stab} {v w : MukaiVector ℤ} {c : ℝ}
    (h : I.charge σ v = c * I.charge σ w) :
    modelCharge I.d (I.base σ) v.toReal = c * modelCharge I.d (I.base σ) w.toReal := by
  rw [I.charge_eq, I.charge_eq, ← Complex.real_smul, ← map_smul] at h
  rw [← Complex.real_smul]
  exact (I.normalization σ).injective h

lemma charge_eq_of_modelCharge_eq {σ : Stab} {v w : MukaiVector ℤ} {c : ℝ}
    (h : modelCharge I.d (I.base σ) v.toReal = c * modelCharge I.d (I.base σ) w.toReal) :
    I.charge σ v = c * I.charge σ w := by
  rw [I.charge_eq, I.charge_eq, h, ← Complex.real_smul, map_smul, Complex.real_smul]

/-- The point of a stability condition is not the puncture of a root. -/
lemma base_ne_puncture (σ : Stab) {δ : MukaiVector ℤ} (hδ : IsRoot I.d δ) (hr : δ.r ≠ 0) :
    I.base σ ≠ puncture I.d δ := by
  intro h
  apply I.charge_ne_zero σ δ hδ
  rw [I.charge_eq, (modelCharge_eq_zero_iff_eq_puncture I.d_pos hr (I.base_mem σ)).mpr h,
    map_zero]

/-- Two semistable objects whose charges are real multiples `Z(F) = c Z(E)` have phases
differing by an integer, even exactly when `c > 0`. -/
lemma exists_phase_sub {σ : Stab} {E F : Obj} (hE : I.Semistable σ E) (hF : I.Semistable σ F)
    {c : ℝ} (h : I.charge σ (I.cl F) = c * I.charge σ (I.cl E)) :
    ∃ j : ℤ, I.phase σ F - I.phase σ E = j ∧ (0 < c ↔ Even j) := by
  obtain ⟨m₁, hm₁, h₁⟩ := I.charge_cl σ F hF
  obtain ⟨m₂, hm₂, h₂⟩ := I.charge_cl σ E hE
  rw [h₁, h₂] at h
  exact exists_int_phase_sub hm₁ hm₂ h

/-! ### Stability along clear segments -/

/-- **No first loss of stability.** A semistable sphere whose puncture is seen from `base σ`
along a clear segment is stable: its stable factors are spheres ([BB], Lemma 2.6) whose charges
are positive multiples of its own, so `eq_singleton_of_segmentClear` leaves a single factor. -/
theorem stable_of_semistable_of_segmentClear {σ : Stab} {E : Obj} (hE : I.Spherical E)
    (hss : I.Semistable σ E) (hclear : SegmentClear I.d (I.base σ) (I.posClass E)) :
    I.Stable σ E := by
  apply I.stable_of_length_factors σ E hss
  set L := I.factors σ E
  set ε : MukaiVector ℤ → MukaiVector ℤ := fun v => if 0 < (I.cl E).r then v else -v
  have hεneg : ∀ v, ε (-v) = -ε v := by intro v; simp only [ε]; split_ifs <;> rfl
  have hεadd : ∀ v w, ε (v + w) = ε v + ε w := by
    intro v w; simp only [ε]; split_ifs
    · rfl
    · ext <;> simp <;> ring
  have hεzero : ε 0 = 0 := by simp only [ε]; split_ifs <;> ext <;> simp
  have hεcl : ε (I.cl E) = I.posClass E := rfl
  -- the factors, with the sign that makes `E` of positive rank
  have hgen : ∀ L' : List Obj, (L'.map fun F => ε (I.cl F)).sum = ε ((L'.map I.cl).sum) := by
    intro L'
    induction L' with
    | nil => simp only [List.map_nil, List.sum_nil]; exact hεzero.symm
    | cons a L' ih => simp only [List.map_cons, List.sum_cons, hεadd, ih]
  have hsum : (L.map fun F => ε (I.cl F)).sum = I.posClass E := by
    rw [hgen, I.factors_sum σ E hss]
    exact hεcl
  have hroots : ∀ δ' ∈ L.map fun F => ε (I.cl F), IsRoot I.d δ' := by
    intro δ' hδ'
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hδ'
    have hsph := I.spherical_of_mem_factors σ E hE hss F hF
    simp only [ε]; split_ifs
    · exact I.isRoot_cl F hsph
    · exact I.isRoot_neg (I.isRoot_cl F hsph)
  have hcharge : ∀ δ' ∈ L.map fun F => ε (I.cl F), ∃ l : ℝ, 0 < l ∧
      modelCharge I.d (I.base σ) δ'.toReal =
        l * modelCharge I.d (I.base σ) (I.posClass E).toReal := by
    intro δ' hδ'
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hδ'
    obtain ⟨hstF, hph⟩ := I.factors_stable σ E hss F hF
    obtain ⟨m₁, hm₁, h₁⟩ := I.charge_cl σ F (I.semistable_of_stable σ F hstF)
    obtain ⟨m₂, hm₂, h₂⟩ := I.charge_cl σ E hss
    refine ⟨m₁ / m₂, div_pos hm₁ hm₂, I.modelCharge_eq_of_charge_eq ?_⟩
    have key : I.charge σ (I.cl F) = (m₁ / m₂ : ℝ) * I.charge σ (I.cl E) := by
      have hm₂' : (m₂ : ℂ) ≠ 0 := by exact_mod_cast hm₂.ne'
      rw [h₁, h₂, hph]; push_cast; field_simp
    simp only [ε, posClass]; split_ifs
    · exact key
    · rw [I.charge_neg, I.charge_neg, key]; ring
  have h1 := eq_singleton_of_segmentClear I.d_pos (I.base_mem σ) (I.isRoot_posClass hE)
    (I.posClass_r_pos hE) (I.base_ne_puncture σ (I.isRoot_posClass hE) (I.posClass_r_pos hE).ne')
    hclear hroots hsum hcharge
  have := congrArg List.length h1
  simpa using this

/-- **Stable wherever the marked puncture is seen.** The sphere of a marked puncture `ℓ` is
stable at every `σ` that sees `ℓ`. It is stable near the puncture ([BB], Lemma 5.3); stability is
open; and at a limit point that still sees `ℓ` the sphere is semistable, hence stable by
`stable_of_semistable_of_segmentClear`. The locus of points seeing `ℓ` being connected, the
sphere is stable on all of it. -/
theorem stable_sphere_of_sees {σ : Stab} {ℓ : Mark} (h : I.Sees σ ℓ) :
    I.Stable σ (I.sphere ℓ) := by
  have hsub : {σ | I.Sees σ ℓ} ⊆ {σ | I.Stable σ (I.sphere ℓ)} := by
    refine (I.isPreconnected_sees ℓ).subset_of_closure_inter_subset
      (I.isOpen_stable (I.sphere ℓ)) ?_ ?_
    · obtain ⟨σ₀, h₀, hs₀⟩ := I.exists_stable_sphere ℓ
      exact ⟨σ₀, h₀, hs₀⟩
    · rintro σ' ⟨hcl, hsees⟩
      have hss : I.Semistable σ' (I.sphere ℓ) :=
        closure_minimal (fun τ hτ => I.semistable_of_stable τ _ hτ)
          (I.isClosed_semistable (I.sphere ℓ)) hcl
      apply I.stable_of_semistable_of_segmentClear (I.spherical_sphere ℓ) hss
      have hpos : I.posClass (I.sphere ℓ) = I.root ℓ := by
        simp [posClass, I.cl_sphere, I.root_r_pos ℓ]
      rw [hpos]
      exact I.segmentClear_of_sees σ' ℓ hsees
  exact hsub h

/-- **A stable sphere sees its puncture.** Where a spherical object is stable, the segment from
`base σ` to its puncture is clear. Otherwise take the first obstacle: it is seen along a clear
segment, so its marked sphere is stable at `σ`; its charge is a positive multiple of that of the
puncture (`obstacle_charge_pos_mul`), so after a shift the two stable spheres have one phase; and
their pairing is at most `-3` (`MukaiVector.pairing_le_neg_three`), against
`pairing_nonneg`. -/
theorem segmentClear_of_stable {σ : Stab} {E : Obj} (hE : I.Spherical E) (hst : I.Stable σ E) :
    SegmentClear I.d (I.base σ) (I.posClass E) := by
  by_contra hcon
  obtain ⟨δ', hδ', hr', hne, hmem, hclear'⟩ := exists_first_obstacle I.d_pos (I.base_mem σ)
    (I.isRoot_posClass hE) (I.posClass_r_pos hE) hcon
  obtain ⟨ℓ', hℓ', hsees⟩ := I.exists_sees σ δ' hδ' hr' hclear'
  have hst' := I.stable_sphere_of_sees hsees
  -- `Z(δ') = μ Z(δ)` with `μ > 0`, where `δ = ±v(E)`
  obtain ⟨μ, hμ, hZ⟩ := obstacle_charge_pos_mul I.d_pos (I.base_mem σ) (I.posClass_r_pos hE) hr'
    hmem (I.base_ne_puncture σ hδ' hr'.ne')
  have hZ' := I.charge_eq_of_modelCharge_eq hZ
  set ε : ℝ := if 0 < (I.cl E).r then 1 else -1
  have hεcl : I.charge σ (I.posClass E) = ε * I.charge σ (I.cl E) := by
    simp only [posClass, ε]; split_ifs
    · simp
    · rw [I.charge_neg]; push_cast; ring
  rw [← hℓ', ← I.cl_sphere ℓ', hεcl, ← mul_assoc] at hZ'
  -- align the phases by a shift of the obstacle sphere
  obtain ⟨j, hj, hpar⟩ := I.exists_phase_sub (I.semistable_of_stable σ E hst)
    (I.semistable_of_stable σ _ hst') (c := μ * ε) (by rw [hZ']; push_cast; ring)
  have hjE : Even j ↔ 0 < (I.cl E).r := by
    rw [← hpar]
    simp only [ε]
    split_ifs with h
    · simp [hμ, h]
    · simp only [h, iff_false, mul_neg, mul_one, Left.neg_pos_iff, not_lt]
      exact hμ.le
  set F := (-j) +ᵥ I.sphere ℓ'
  have hstF : I.Stable σ F := I.stable_vadd σ (-j) _ hst'
  have hphF : I.phase σ E = I.phase σ F := by
    simp only [F, I.phase_vadd]; push_cast; linarith
  have hclF : I.cl F = if 0 < (I.cl E).r then δ' else -δ' := by
    simp only [F, I.cl_vadd, I.cl_sphere, hℓ', even_neg, hjE]
  have hpair : pairing I.d (I.cl E) (I.cl F) = pairing I.d (I.posClass E) δ' := by
    rw [hclF]
    simp only [posClass]
    split_ifs with h
    · rfl
    · rw [pairing_neg_right, pairing_neg_left]
  have hle := pairing_le_neg_three I.d_pos (I.isRoot_posClass hE) hδ' (I.posClass_r_pos hE) hr'
    (Ne.symm hne)
  have hEF : E ≠ F := by
    intro hEF
    have hcl : I.cl E = I.cl F := congrArg I.cl hEF
    rw [hclF] at hcl
    apply hne
    simp only [posClass]
    by_cases h : 0 < (I.cl E).r
    · simp only [h, ↓reduceIte] at hcl ⊢; exact hcl.symm
    · simp only [h, ↓reduceIte] at hcl ⊢; rw [hcl, neg_neg_mukai]
  have h0 := I.pairing_nonneg σ E F hst hstF hphF hEF
  rw [hpair] at h0
  linarith

/-- **Uniqueness.** Two stable spheres with the same class and phase are isomorphic: otherwise
`pairing_nonneg` would give `0 ≤ ⟨v, v⟩ = -2`. -/
theorem eq_of_stable_of_cl_eq {σ : Stab} {E F : Obj} (hE : I.Spherical E) (hst : I.Stable σ E)
    (hstF : I.Stable σ F) (hcl : I.cl E = I.cl F) (hph : I.phase σ E = I.phase σ F) : E = F := by
  by_contra hne
  have h := I.pairing_nonneg σ E F hst hstF hph hne
  rw [← hcl, I.isRoot_cl E hE] at h
  norm_num at h

/-- **A stable sphere is a shifted marked sphere seen from `σ`.** The segment to its puncture is
clear (`segmentClear_of_stable`), so it lifts to a marked puncture `ℓ` (`exists_sees`), whose
sphere is stable at `σ` (`stable_sphere_of_sees`); a shift gives it the class and phase of the
given sphere, and uniqueness identifies the two. -/
theorem exists_sees_of_stable {σ : Stab} {E : Obj} (hE : I.Spherical E) (hst : I.Stable σ E) :
    ∃ ℓ, ∃ n : ℤ, I.Sees σ ℓ ∧ E = n +ᵥ I.sphere ℓ := by
  obtain ⟨ℓ, hℓ, hsees⟩ := I.exists_sees σ _ (I.isRoot_posClass hE) (I.posClass_r_pos hE)
    (I.segmentClear_of_stable hE hst)
  have hst₀ := I.stable_sphere_of_sees hsees
  set ε : ℝ := if 0 < (I.cl E).r then 1 else -1
  have hZ : I.charge σ (I.cl (I.sphere ℓ)) = ε * I.charge σ (I.cl E) := by
    rw [I.cl_sphere, hℓ]
    simp only [posClass, ε]
    split_ifs
    · simp
    · rw [I.charge_neg]; push_cast; ring
  obtain ⟨j, hj, hpar⟩ := I.exists_phase_sub (I.semistable_of_stable σ E hst)
    (I.semistable_of_stable σ _ hst₀) hZ
  have hjE : Even j ↔ 0 < (I.cl E).r := by
    rw [← hpar]
    simp only [ε]
    split_ifs with h
    · simp [h]
    · simp [h]
  refine ⟨ℓ, -j, hsees, ?_⟩
  apply I.eq_of_stable_of_cl_eq hE hst (I.stable_vadd σ (-j) _ hst₀)
  · rw [I.cl_vadd, I.cl_sphere, hℓ]
    simp only [even_neg, hjE, posClass]
    split_ifs <;> simp
  · rw [I.phase_vadd]; push_cast; linarith

/-- **Visibility on the cover, for marked spheres.** The shifted sphere `n +ᵥ sphere ℓ` is stable
at `σ` exactly when `σ` sees the marked puncture `ℓ`. -/
theorem stable_vadd_sphere_iff {σ : Stab} {ℓ : Mark} (n : ℤ) :
    I.Stable σ (n +ᵥ I.sphere ℓ) ↔ I.Sees σ ℓ := by
  constructor
  · intro hst
    obtain ⟨ℓ', m, hsees, heq⟩ :=
      I.exists_sees_of_stable (I.spherical_vadd n _ (I.spherical_sphere ℓ)) hst
    have : (n - m) +ᵥ I.sphere ℓ = I.sphere ℓ' := by
      rw [sub_eq_add_neg, add_comm, add_vadd, heq, ← add_vadd, neg_add_cancel, zero_vadd]
    rwa [I.sphere_injective ℓ ℓ' (n - m) this]
  · intro h
    exact I.stable_vadd σ n _ (I.stable_sphere_of_sees h)

/-- **Every sphere is a shifted marked sphere**, since it is stable somewhere ([BB],
Corollary 6.9). -/
theorem exists_eq_vadd_sphere {E : Obj} (hE : I.Spherical E) :
    ∃ ℓ, ∃ n : ℤ, E = n +ᵥ I.sphere ℓ := by
  obtain ⟨σ, hσ⟩ := I.exists_stable E hE
  obtain ⟨ℓ, n, -, h⟩ := I.exists_sees_of_stable hE hσ
  exact ⟨ℓ, n, h⟩

/-- The marked puncture of a spherical object. -/
def marking {E : Obj} (hE : I.Spherical E) : Mark := (I.exists_eq_vadd_sphere hE).choose

lemma exists_eq_vadd_sphere_marking {E : Obj} (hE : I.Spherical E) :
    ∃ n : ℤ, E = n +ᵥ I.sphere (I.marking hE) :=
  (I.exists_eq_vadd_sphere hE).choose_spec

/-- The marking is well defined: a shifted marked sphere determines its marked puncture. -/
lemma marking_eq {E : Obj} (hE : I.Spherical E) {ℓ : Mark} {n : ℤ}
    (h : E = n +ᵥ I.sphere ℓ) : I.marking hE = ℓ := by
  obtain ⟨m, hm⟩ := I.exists_eq_vadd_sphere_marking hE
  have : (n - m) +ᵥ I.sphere ℓ = I.sphere (I.marking hE) := by
    have h' : n +ᵥ I.sphere ℓ = m +ᵥ I.sphere (I.marking hE) := h.symm.trans hm
    rw [sub_eq_add_neg, add_comm, add_vadd, h', ← add_vadd, neg_add_cancel, zero_vadd]
  exact (I.sphere_injective _ _ _ this).symm

/-- The marked puncture of a sphere lies over the puncture of its class. -/
lemma root_marking {E : Obj} (hE : I.Spherical E) : I.root (I.marking hE) = I.posClass E := by
  obtain ⟨n, hn⟩ := I.exists_eq_vadd_sphere_marking hE
  have hpos := I.root_r_pos (I.marking hE)
  have hcl : I.cl E = if Even n then I.root (I.marking hE) else -I.root (I.marking hE) := by
    conv_lhs => rw [hn]
    rw [I.cl_vadd, I.cl_sphere]
  unfold posClass
  by_cases hev : Even n
  · simp only [hev, ↓reduceIte] at hcl
    rw [hcl]
    simp only [hpos, ↓reduceIte]
  · simp only [hev, ↓reduceIte] at hcl
    rw [hcl]
    have : ¬0 < (-I.root (I.marking hE)).r := by simp only [neg_r]; omega
    simp only [this, ↓reduceIte, neg_neg_mukai]

/-- **Visibility on the cover.** A spherical object is stable at `σ` exactly when `σ` sees its
marked puncture. -/
theorem stable_iff_sees_marking {σ : Stab} {E : Obj} (hE : I.Spherical E) :
    I.Stable σ E ↔ I.Sees σ (I.marking hE) := by
  obtain ⟨n, hn⟩ := I.exists_eq_vadd_sphere_marking hE
  conv_lhs => rw [hn]
  exact I.stable_vadd_sphere_iff n

/-- **Visibility on the cover**, in the words of the article: a spherical object, up to shift, is
stable at `σ` exactly when the straight segment from `base σ` to its puncture meets no
intervening puncture and lifts to its marking. -/
theorem stable_iff_segmentClear_and_sees {σ : Stab} {E : Obj} (hE : I.Spherical E) :
    I.Stable σ E ↔ SegmentClear I.d (I.base σ) (I.posClass E) ∧ I.Sees σ (I.marking hE) := by
  rw [I.stable_iff_sees_marking hE]
  refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
  rw [← I.root_marking hE]
  exact I.segmentClear_of_sees σ _ h

/-! ### Point images -/

/-- **Point images.** A point image `G 𝒪_x` is stable at `σ` exactly when `G⁻¹σ` is in the
geometric chamber. -/
theorem stable_smul_point_iff (G : Γ) (σ : Stab) :
    I.Stable σ (G • I.point) ↔ I.Geometric (G⁻¹ • σ) := by
  rw [← I.stable_smul G⁻¹ σ (G • I.point), inv_smul_smul, I.stable_point_iff]

/-- **Point images, by the ray test.** A point image `G 𝒪_x` is stable at `σ` exactly when
`G⁻¹σ` lies on the geometric sheet and the upward ray from its point, the geodesic ray to the cusp
of `𝒪_x`, meets no puncture: Bayer–Bridgeland's slit region `V(X)` is the region where the upward
ray is clear (`rayClear_iff`). -/
theorem stable_smul_point_iff_rayClear (G : Γ) (σ : Stab) :
    I.Stable σ (G • I.point) ↔
      I.OnGeometricSheet (G⁻¹ • σ) ∧ RayClear I.d (I.base (G⁻¹ • σ)) := by
  rw [I.stable_smul_point_iff, I.geometric_iff, rayClear_iff I.d_pos (I.base_mem _)]

lemma act_inv_act (G : Γ) (v : MukaiVector ℤ) : I.act G⁻¹ (I.act G v) = v := by
  rw [← I.act_mul, inv_mul_cancel, I.act_one]

lemma act_act_inv (G : Γ) (v : MukaiVector ℤ) : I.act G (I.act G⁻¹ v) = v := by
  rw [← I.act_mul, mul_inv_cancel, I.act_one]

/-- `Z_{G⁻¹σ}(v) = Z_σ(G_* v)`. -/
lemma charge_inv_smul (G : Γ) (σ : Stab) (v : MukaiVector ℤ) :
    I.charge (G⁻¹ • σ) v = I.charge σ (I.act G v) := by
  have h := I.charge_smul G⁻¹ σ (I.act G v)
  rwa [I.act_inv_act] at h

/-- **The Mukai action carries the ray to the cusp.** The upward ray from the point of `G⁻¹σ`,
the geodesic ray to the cusp of `𝒪_x`, is clear exactly when the sight line from the point of `σ`
to the cusp of `v(G 𝒪_x) = G_*(0, 0, 1)` is clear: `G_*` is an isometry matching the charges of
`G⁻¹σ` with those of `σ` (`cuspRayClear_iff_of_isometry`). -/
theorem rayClear_inv_smul_iff (G : Γ) (σ : Stab) :
    RayClear I.d (I.base (G⁻¹ • σ)) ↔ CuspRayClear I.d (I.base σ) (I.cl (G • I.point)) := by
  rw [← cuspRayClear_point_iff I.d_pos (I.base_mem _), I.cl_smul, I.cl_point]
  refine cuspRayClear_iff_of_isometry (I.act G) (I.act G⁻¹) (I.act_act_inv G) (I.pairing_act G)
    (fun v w m => ⟨fun h => ?_, fun h => ?_⟩) _
  · have h' := I.charge_eq_of_modelCharge_eq h
    rw [I.charge_inv_smul, I.charge_inv_smul] at h'
    exact I.modelCharge_eq_of_charge_eq h'
  · have h' := I.charge_eq_of_modelCharge_eq h
    rw [← I.charge_inv_smul, ← I.charge_inv_smul] at h'
    exact I.modelCharge_eq_of_charge_eq h'

/-- **Point images, by the ray to their cusp.** `G 𝒪_x` is stable at `σ` exactly when the sight
line from the point of `σ` to the cusp of `G 𝒪_x` is unobstructed and has the prescribed marking,
that is `G⁻¹σ` lies on the geometric sheet. -/
theorem stable_smul_point_iff_cuspRayClear (G : Γ) (σ : Stab) :
    I.Stable σ (G • I.point) ↔
      I.OnGeometricSheet (G⁻¹ • σ) ∧ CuspRayClear I.d (I.base σ) (I.cl (G • I.point)) := by
  rw [I.stable_smul_point_iff_rayClear, I.rayClear_inv_smul_iff]

/-- The class of a point image is isotropic. -/
lemma isIsotropic_cl_smul_point (G : Γ) : IsIsotropic I.d (I.cl (G • I.point)) := by
  unfold IsIsotropic
  rw [I.cl_smul, I.pairing_act, I.cl_point]
  exact isIsotropic_point I.d

/-- **Point images with a cusp on the parabola.** If `v(G 𝒪_x) = (r, c, s)` has `r ≠ 0`, then
`G 𝒪_x` is stable at `σ` exactly when `G⁻¹σ` lies on the geometric sheet and the straight segment
from the point of `σ` to the cusp `(c/r, (c/r)²)` meets no puncture. -/
theorem stable_smul_point_iff_cuspClear (G : Γ) (σ : Stab) (hr : (I.cl (G • I.point)).r ≠ 0) :
    I.Stable σ (G • I.point) ↔ I.OnGeometricSheet (G⁻¹ • σ) ∧
      CuspClear I.d (I.base σ) (((I.cl (G • I.point)).c : ℝ) / (I.cl (G • I.point)).r) := by
  rw [I.stable_smul_point_iff_cuspRayClear,
    cuspRayClear_iff_cuspClear I.d_pos (I.base_mem σ) (I.isIsotropic_cl_smul_point G) hr]

/-- **Point images with the cusp at infinity.** If `v(G 𝒪_x)` has rank zero, `G 𝒪_x` is stable
at `σ` exactly when `G⁻¹σ` lies on the geometric sheet and the upward ray from the point of `σ`
meets no puncture. -/
theorem stable_smul_point_iff_rayClear_of_r_eq_zero (G : Γ) (σ : Stab)
    (hr : (I.cl (G • I.point)).r = 0) :
    I.Stable σ (G • I.point) ↔ I.OnGeometricSheet (G⁻¹ • σ) ∧ RayClear I.d (I.base σ) := by
  have hne : I.cl (G • I.point) ≠ 0 := by
    -- `⟨G_*(0, 0, 1), G_*(1, 0, 0)⟩ = ⟨(0, 0, 1), (1, 0, 0)⟩ = -1`
    intro h0
    have h1 := I.pairing_act G MukaiVector.point ⟨1, 0, 0⟩
    have h2 : I.act G MukaiVector.point = 0 := by rw [← I.cl_point, ← I.cl_smul]; exact h0
    rw [h2] at h1
    simp [pairing, MukaiVector.point] at h1
  rw [I.stable_smul_point_iff_cuspRayClear,
    cuspRayClear_iff_rayClear I.d_pos (I.base_mem σ) (I.isIsotropic_cl_smul_point G) hr hne]

end VisibilityHypotheses

end AlgebraicGeometry.K3.PicardRankOne
