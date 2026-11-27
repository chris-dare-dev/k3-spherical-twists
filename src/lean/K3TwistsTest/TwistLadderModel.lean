/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Mass.TwistLadder

/-!
# Twist ladders relative to one prestability condition

Mathlib has no twist functors, so no ladder here comes from a real twist; the prestability
condition is a variable, as in `CutLossModel`. The models and the answers known independently:

* the empty ladder family on `𝟙 E`, whose cone is zero and has mass `N k a = 0`;
* a semistable object above a cut: the mass above the cut is read off its one-factor filtration;
* the one-cell ladder of a semistable object `S`: a distinguished triangle `E → F → S → E⟦1⟧` is
  a twist ladder with `N = k = 1` and `a = |Z(S)|`. Its zero-loss case is equal-phase additivity,
  `m(F) = m(E) + m(S)`, and the twist bound holds;
* the one-cell ladder `E → 0 → E⟦1⟧` of a semistable `E` attains the twist bound, so the constant
  `2` cannot be improved;
* the opening example at `n = 2`: `m(F) = 1 + 20/9 = 29/9`;
* a negative power with one cell above the cut loses nothing, as the split identity says.

Built by `lake test`.
-/

namespace CategoryTheory.Triangulated.TwistLadderModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  {Λ : Type*} [AddCommGroup Λ] {v : K₀ C →+ Λ}

omit [IsTriangulated C] in
/-- A biproduct over `Fin 0` is zero. -/
lemma isZero_biproduct_fin_zero (L : Fin 0 → C) : IsZero (⨁ L) :=
  (IsZero.iff_id_eq_zero _).2 (by rw [← biproduct.total]; simp)

/-- An object is the biproduct of one copy of itself. -/
noncomputable def isoBiproductFinOne (S : C) : S ≅ ⨁ fun _ : Fin 1 ↦ S where
  hom := biproduct.lift fun _ ↦ 𝟙 S
  inv := biproduct.π _ 0
  hom_inv_id := by simp
  inv_hom_id := by
    ext j k
    rw [Subsingleton.elim j 0, Subsingleton.elim k 0]
    simp

/-- The empty ladder family. -/
noncomputable def emptyFamily (σ : PreStabilityCondition.WithClassMap C v) : σ.LadderFamily where
  N := 0
  k := 0
  a := 0
  a_nonneg := le_rfl
  ψ := Fin.elim0
  L := Fin.elim0
  filtration := fun c ↦ c.elim0
  length_eq := fun c ↦ c.elim0
  phase_eq := fun c ↦ c.elim0
  norm_charge_eq := fun c ↦ c.elim0

/-- The empty twist ladder on `𝟙 E`: the triangle `E → E → 0 → E⟦1⟧`. -/
noncomputable def emptyLadder (σ : PreStabilityCondition.WithClassMap C v) (E : C) :
    σ.TwistLadderHypotheses (𝟙 E) where
  toLadderFamily := emptyFamily σ
  cone := 0
  g := 0
  h := 0
  dist := contractible_distinguished E
  iso := (isZero_zero C).iso (isZero_biproduct_fin_zero _)

/-- The one-cell ladder family of a semistable object `S` of phase `ψ₀`. -/
noncomputable def oneCell (σ : PreStabilityCondition.WithClassMap C v) {S : C} {ψ₀ : ℝ}
    (hS : σ.slicing.P ψ₀ S) : σ.LadderFamily where
  N := 1
  k := 1
  a := ‖σ.charge S‖
  a_nonneg := norm_nonneg _
  ψ := fun _ ↦ ψ₀
  L := fun _ ↦ S
  filtration := fun _ ↦ HNFiltration.single C S ψ₀ hS
  length_eq := fun _ ↦ rfl
  phase_eq := fun _ j ↦ by
    change ψ₀ = ψ₀ - ((j : ℕ) : ℝ)
    rw [show (j : ℕ) = 0 from Fin.val_eq_zero (j : Fin 1)]
    simp
  norm_charge_eq := fun _ _ ↦ rfl

/-- A distinguished triangle `E → F → S → E⟦1⟧` with `S` semistable is a one-cell twist ladder. -/
noncomputable def oneCellLadder (σ : PreStabilityCondition.WithClassMap C v) {E F S : C}
    {f : E ⟶ F} {g : F ⟶ S} {h : S ⟶ E⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    {ψ₀ : ℝ} (hS : σ.slicing.P ψ₀ S) : σ.TwistLadderHypotheses f where
  toLadderFamily := oneCell σ hS
  cone := S
  g := g
  h := h
  dist := hT
  iso := isoBiproductFinOne S

/-- **The empty ladder.** Its cone is zero, of mass `N k a = 0`. -/
example (σ : PreStabilityCondition.WithClassMap C v) (E : C) :
    σ.mass (emptyLadder σ E).cone = 0 := by
  rw [(emptyLadder σ E).mass_cone]
  simp [emptyLadder, emptyFamily]

/-- **The mass above a cut of a semistable object.** For `Q` semistable of phase `ψ₀ > s`, the
truncation `Q → Q → 0` and the one-factor filtration give `m(Q) = |Z(Q)|`. -/
example (σ : PreStabilityCondition.WithClassMap C v) {Q : C} {ψ₀ s : ℝ}
    (hQ : σ.slicing.P ψ₀ Q) (hs : s < ψ₀) : σ.mass Q = ‖σ.charge Q‖ := by
  rw [σ.mass_eq_sum_ite_of_gtProp_leProp (contractible_distinguished Q)
    (σ.slicing.gtProp_of_semistable C hQ hs) (σ.slicing.leProp_of_isZero C (isZero_zero C) s)
    (HNFiltration.single C Q ψ₀ hQ)]
  change ∑ _ : Fin 1, (if s < ψ₀ then ‖σ.charge Q‖ else 0) = _
  simp [hs]

/-- **Zero loss for one cell.** If `E` has phases at least `s` and `S` is semistable of phase
`ψ₀ ≤ s`, the twist ladder gives `m(F) = m(E) + |Z(S)|`, which is equal-phase additivity. -/
example (σ : PreStabilityCondition.WithClassMap C v) {E F S : C} {f : E ⟶ F} {g : F ⟶ S}
    {h : S ⟶ E⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C) {ψ₀ s : ℝ}
    (hS : σ.slicing.P ψ₀ S) (hψ : ψ₀ ≤ s) (hE : σ.slicing.geProp C s E) :
    σ.mass F = σ.mass E + ‖σ.charge S‖ ∧ σ.mass F = σ.mass E + σ.mass S := by
  refine ⟨?_, σ.mass_eq_add_of_geProp_leProp hT hE (σ.slicing.leProp_of_semistable C hS hψ)⟩
  have := (oneCellLadder σ hT hS).zero_loss hE fun _ ↦ hψ
  simpa [oneCellLadder, oneCell] using this

/-- **The twist bound for one cell.** If `E` has phases at least `s`, the loss
`m(E) + |Z(S)| - m(F)` lies between `0` and `2|Z(S)| min{1, ⌈ψ₀ - s⌉₊}`. -/
example (σ : PreStabilityCondition.WithClassMap C v) (hσ : σ.MassSubadditive) {E F S : C}
    {f : E ⟶ F} {g : F ⟶ S} {h : S ⟶ E⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    {ψ₀ s : ℝ} (hS : σ.slicing.P ψ₀ S) (hE : σ.slicing.geProp C s E) :
    0 ≤ σ.mass E + ‖σ.charge S‖ - σ.mass F ∧
      σ.mass E + ‖σ.charge S‖ - σ.mass F ≤ 2 * ‖σ.charge S‖ * (min 1 ⌈ψ₀ - s⌉₊ : ℕ) := by
  have h : 0 ≤ σ.mass E + ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * ‖σ.charge S‖ - σ.mass F ∧
      σ.mass E + ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * ‖σ.charge S‖ - σ.mass F ≤
        2 * ‖σ.charge S‖ * ((∑ _c : Fin 1, min 1 ⌈ψ₀ - s⌉₊ : ℕ) : ℝ) :=
    (oneCellLadder σ hT hS).twist_bound hσ hE
  simpa using h

/-- **The constant `2` is attained.** For `E` semistable of phase `φ`, the triangle
`E → 0 → E⟦1⟧` is the one-cell ladder of `E⟦1⟧`, of phase `φ + 1`. At the cut `s = φ` its loss
`m(E) + |Z(E⟦1⟧)| - m(0) = 2|Z(E)|` equals the bound `2a min{1, ⌈1⌉₊} = 2|Z(E)|`. -/
example (σ : PreStabilityCondition.WithClassMap C v) {φ : ℝ} {E : C} (hE : σ.slicing.P φ E) :
    let T := oneCellLadder σ (contractible_distinguished₂ E) (σ.slicing.shift C φ E hE)
    σ.mass E + T.N * T.k * T.a - σ.mass (0 : C) =
      2 * T.a * (∑ c, min T.k ⌈T.ψ c - φ⌉₊ : ℕ) := by
  intro T
  change σ.mass E + ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * ‖σ.charge (E⟦(1 : ℤ)⟧)‖ - σ.mass (0 : C) =
    2 * ‖σ.charge (E⟦(1 : ℤ)⟧)‖ * ((∑ _c : Fin 1, min 1 ⌈φ + 1 - φ⌉₊ : ℕ) : ℝ)
  have h₁ : ‖σ.charge (E⟦(1 : ℤ)⟧)‖ = ‖σ.charge E‖ := by
    simp [PreStabilityCondition.WithClassMap.charge_def]
  rw [add_sub_cancel_left, Nat.ceil_one, min_self, h₁, σ.mass_eq_norm_charge_of_semistable hE,
    σ.mass_of_isZero (isZero_zero C)]
  simp only [Nat.cast_one, one_mul, sub_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  ring

open AlgebraicGeometry.K3 in
/-- **The opening example at `n = 2`.** A twist ladder with one ladder of two cells of mass
`|Z(𝒪_X[1])| = 10/9`, on an `E` of mass `|Z(𝒪_x)| = 1` with no cell above the cut, has
`m(F) = 1 + 20/9 = 29/9`. -/
example (σ : PreStabilityCondition.WithClassMap C v) {E F : C} {f : E ⟶ F}
    (T : σ.TwistLadderHypotheses f) (hN : T.N = 1) (hk : T.k = 2)
    (ha : T.a = ‖PicardRankOne.charge 1 PicardRankOne.ζ PicardRankOne.classS‖)
    (hEm : σ.mass E = ‖PicardRankOne.charge 1 PicardRankOne.ζ MukaiVector.point‖) {s : ℝ}
    (hE : σ.slicing.geProp C s E) (hψ : ∀ c, T.ψ c ≤ s) : σ.mass F = 29 / 9 := by
  rw [T.mass_eq_opening hN hk ha hEm hE hψ]
  norm_num

/-- **A negative power with one cell above the cut.** For a distinguished triangle
`S → F → E → S⟦1⟧` with `S` semistable of phase `ψ₀ > s` and `E` of phases at most `s`, the bound
for negative powers gives `m(F) = m(E) + |Z(S)|`, as the split identity does. -/
example (σ : PreStabilityCondition.WithClassMap C v) (hσ : σ.MassSubadditive) {S F E : C}
    {u : S ⟶ F} {f : F ⟶ E} {h : E ⟶ S⟦(1 : ℤ)⟧} (hT : Triangle.mk u f h ∈ distTriang C)
    {ψ₀ s : ℝ} (hS : σ.slicing.P ψ₀ S) (hs : s < ψ₀) (hE : σ.slicing.leProp C s E) :
    σ.mass F = σ.mass E + ‖σ.charge S‖ ∧ σ.mass F = σ.mass S + σ.mass E := by
  refine ⟨?_, σ.mass_eq_add_of_triangle hT (σ.slicing.gtProp_of_semistable C hS hs) hE⟩
  have hc : ⌈ψ₀ - s⌉₊ ≠ 0 := by
    rw [Ne, Nat.ceil_eq_zero, not_le]
    linarith
  obtain ⟨h₁, h₂⟩ := (oneCell σ hS).inverse_twist_bound hσ hT (isoBiproductFinOne S) hE
  have h₁' : 0 ≤ σ.mass E + ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * ‖σ.charge S‖ - σ.mass F := h₁
  have h₂' : σ.mass E + ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * ‖σ.charge S‖ - σ.mass F ≤
      2 * ‖σ.charge S‖ * ((∑ _c : Fin 1, (1 - min 1 ⌈ψ₀ - s⌉₊) : ℕ) : ℝ) := h₂
  rw [min_eq_left (Nat.one_le_iff_ne_zero.2 hc), Nat.sub_self] at h₂'
  norm_num at h₁' h₂'
  linarith

end CategoryTheory.Triangulated.TwistLadderModel
