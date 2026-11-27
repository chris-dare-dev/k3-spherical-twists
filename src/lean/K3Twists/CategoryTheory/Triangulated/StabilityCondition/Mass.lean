/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.ShortStep
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Insertion
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Uniqueness

/-!
# The mass of an object

For a prestability condition `σ = (P, Z)` the **mass** of an object `E` with HN factors `A_i` is
`m_σ(E) = Σ_i |Z(A_i)|` (Bridgeland, arXiv:math/0212237, §8; Ikeda, arXiv:1612.00995, §3). It is
well defined because HN filtrations are unique up to zero factors: every function of the factors
that is invariant under isomorphism and vanishes on zero objects has the same sum over any two HN
filtrations of `E` (`HNFiltration.sum_factor_eq`).

## Main definitions

* `PreStabilityCondition.WithClassMap.mass σ E`: the mass.
* `PreStabilityCondition.WithClassMap.MassSubadditive σ`: `m_σ(B) ≤ m_σ(A) + m_σ(C)` on every
  distinguished triangle `A → B → C → A[1]`. For a stability condition this is Ikeda
  (arXiv:1612.00995, Proposition 3.3); it is an input here, not a theorem.

## Main results

* `mass_eq_sum`: the mass is the sum over any HN filtration;
* `mass_iso`, `mass_shift`: invariance under isomorphism and shifts;
* `norm_charge_le_mass`: `|Z(E)| ≤ m_σ(E)`, with equality for semistable objects
  (`mass_eq_norm_charge_of_semistable`); `mass_pos`: a nonzero object has positive mass;
* `mass_eq_add_of_triangle`, `exists_mass_split`: **the split identity**
  `m(E) = m(E_{> t}) + m(E_{≤ t})` for the truncation triangle at any phase `t`;
* `abs_sub_mass_cone_le`: **the `2m(D)` lemma.** For any function `m` on objects that is invariant
  under shifts and subadditive on distinguished triangles, if `f, f' : A → B`
  differ by a map that factors through `D`, the cones satisfy `|m(cone f) - m(cone f')| ≤ 2 m(D)`
  (`PreStabilityCondition.WithClassMap.abs_sub_mass_cone_le` for the mass, under
  `MassSubadditive`).

## References

* T. Bridgeland, *Stability conditions on triangulated categories*, arXiv:math/0212237.
* A. Ikeda, *Mass growth of objects and categorical entropy*, arXiv:1612.00995, Proposition 3.3.

## Tags

stability condition, mass, Harder–Narasimhan filtration
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Sums over the factors of an HN filtration -/

section Sums

variable {M : Type*} [AddCommMonoid M]

/-- Split off the last term of a sum over `Fin n`, `n > 0`. -/
theorem _root_.Fin.sum_eq_sum_pred_add_last {n : ℕ} (hn : 0 < n) (g : Fin n → M) :
    ∑ i, g i = ∑ i : Fin (n - 1), g ⟨i, by omega⟩ + g ⟨n - 1, by omega⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Fin.sum_univ_castSucc]
  rfl

/-- A sum over `Fin n` with `n = a + b` splits into the first `a` and the last `b` terms. -/
theorem _root_.Fin.sum_eq_add_of_eq {n a b : ℕ} (h : n = a + b) (g : Fin n → M) :
    ∑ k, g k = ∑ i : Fin a, g ⟨i, by omega⟩ + ∑ j : Fin b, g ⟨a + j, by omega⟩ := by
  subst h
  rw [Fin.sum_univ_add]
  rfl

/-- Every map from the next-to-last chain object of an HN filtration to an object of phase at
most the last phase vanishes. -/
theorem HNFiltration.hom_chain_pred_eq_zero' (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (hn : 0 < F.n) {X : C} {ψ : ℝ} (hX : s.P ψ X)
    (hψ : ψ ≤ F.φ ⟨F.n - 1, by omega⟩) (f : F.chain.obj ⟨F.n - 1, by omega⟩ ⟶ X) : f = 0 :=
  s.hom_eq_zero_of_phase_gap C (F.prefix C (F.n - 1) (by omega))
    (HNFiltration.single C X ψ hX)
    (fun _ _ => hψ.trans_lt (F.hφ (Fin.mk_lt_mk.mpr (by omega)))) f

/-- Remove a zero last factor of an HN filtration with at least one factor. -/
def HNFiltration.dropLastZero {P : ℝ → ObjectProperty C} {E : C} (F : HNFiltration C P E)
    (hn : 0 < F.n) (hzero : IsZero (F.factor ⟨F.n - 1, by omega⟩)) : HNFiltration C P E :=
  haveI : IsIso (F.triangle ⟨F.n - 1, by omega⟩).mor₁ :=
    (Triangle.isZero₃_iff_isIso₁ _ (F.triangle_dist _)).mp hzero
  (F.prefix C (F.n - 1) (by omega)).ofIso C
    ((F.lastTriangleObj₁Iso hn).symm ≪≫
      asIso (F.triangle ⟨F.n - 1, Nat.sub_lt hn Nat.one_pos⟩).mor₁ ≪≫ F.lastTriangleObj₂Iso hn)

theorem HNFiltration.dropLastZero_n {P : ℝ → ObjectProperty C} {E : C} (F : HNFiltration C P E)
    (hn : 0 < F.n) (hzero : IsZero (F.factor ⟨F.n - 1, by omega⟩)) :
    (F.dropLastZero hn hzero).n = F.n - 1 := rfl

/-- Dropping a zero last factor does not change a sum vanishing on zero objects. -/
theorem HNFiltration.sum_dropLastZero {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hn : 0 < F.n) (hzero : IsZero (F.factor ⟨F.n - 1, by omega⟩))
    (f : ℝ → C → M) (hf : ∀ φ X, IsZero X → f φ X = 0) :
    ∑ i, f (F.φ i) (F.factor i) =
      ∑ i, f ((F.dropLastZero hn hzero).φ i) ((F.dropLastZero hn hzero).factor i) := by
  rw [Fin.sum_eq_sum_pred_add_last hn, hf _ _ hzero, add_zero]
  rfl

/-- **Uniqueness of HN filtrations, read through sums.** A function of the factors that is
invariant under isomorphism and vanishes on zero objects has the same sum over any two HN
filtrations of the same object. -/
theorem HNFiltration.sum_factor_eq (s : Slicing C) (f : ℝ → C → M)
    (hiso : ∀ φ {X Y : C}, (X ≅ Y) → f φ X = f φ Y) (hzero : ∀ φ X, IsZero X → f φ X = 0)
    {E : C} (F G : HNFiltration C s.P E) :
    ∑ i, f (F.φ i) (F.factor i) = ∑ j, f (G.φ j) (G.factor j) := by
  suffices key : ∀ N {E : C} (F G : HNFiltration C s.P E), F.n + G.n ≤ N →
      ∑ i, f (F.φ i) (F.factor i) = ∑ j, f (G.φ j) (G.factor j) from key _ F G le_rfl
  intro N
  induction N with
  | zero =>
    intro E F G hN
    rw [Finset.sum_eq_zero fun i _ => absurd i.isLt (by omega),
      Finset.sum_eq_zero fun i _ => absurd i.isLt (by omega)]
  | succ N ih =>
    intro E F G hN
    by_cases hF : ∃ hn : 0 < F.n, IsZero (F.factor ⟨F.n - 1, by omega⟩)
    · obtain ⟨hn, hz⟩ := hF
      rw [F.sum_dropLastZero hn hz f hzero]
      exact ih _ G (by rw [HNFiltration.dropLastZero_n]; omega)
    by_cases hG : ∃ hn : 0 < G.n, IsZero (G.factor ⟨G.n - 1, by omega⟩)
    · obtain ⟨hn, hz⟩ := hG
      rw [G.sum_dropLastZero hn hz f hzero]
      exact ih F _ (by rw [HNFiltration.dropLastZero_n]; omega)
    push Not at hF hG
    rcases Nat.eq_zero_or_pos F.n with hF0 | hFpos
    · have hE := F.isZero_of_n_eq_zero hF0
      rcases Nat.eq_zero_or_pos G.n with hG0 | hGpos
      · rw [Finset.sum_eq_zero fun i _ => absurd i.isLt (by omega),
          Finset.sum_eq_zero fun i _ => absurd i.isLt (by omega)]
      · exact absurd (G.lastFactor_isZero_of_hom_eq_zero C s hGpos
          fun g => hE.eq_of_src g 0) (hG hGpos)
    rcases Nat.eq_zero_or_pos G.n with hG0 | hGpos
    · have hE := G.isZero_of_n_eq_zero hG0
      exact absurd (F.lastFactor_isZero_of_hom_eq_zero C s hFpos
        fun g => hE.eq_of_src g 0) (hF hFpos)
    have hFl := hF hFpos
    have hGl := hG hGpos
    -- the last phases agree and the last triangles are isomorphic
    have hlast : F.φ ⟨F.n - 1, by omega⟩ = G.φ ⟨G.n - 1, by omega⟩ :=
      F.phiMinus_eq_of_lastFactors_nonzero C s G hFpos hGpos hFl hGl
    set TF := F.triangle ⟨F.n - 1, by omega⟩ with hTF
    set TG := G.triangle ⟨G.n - 1, by omega⟩ with hTG
    have hTFd : TF ∈ distTriang C := F.triangle_dist _
    have hTGd : TG ∈ distTriang C := G.triangle_dist _
    let eF₁ := F.lastTriangleObj₁Iso hFpos
    let eG₁ := G.lastTriangleObj₁Iso hGpos
    let e₂ : TF.obj₂ ≅ TG.obj₂ :=
      (F.lastTriangleObj₂Iso hFpos).trans (G.lastTriangleObj₂Iso hGpos).symm
    have hFfac : s.P (F.φ ⟨F.n - 1, by omega⟩) TF.obj₃ := F.semistable _
    have hGfac : s.P (G.φ ⟨G.n - 1, by omega⟩) TG.obj₃ := G.semistable _
    have hshift : ∀ {X : C} {ψ : ℝ}, s.P ψ X → s.P (ψ - 1) (X⟦(-1 : ℤ)⟧) := by
      intro X ψ hX
      have := (s.shift_int C ψ X (-1)).mp hX
      rwa [show ψ + ((-1 : ℤ) : ℝ) = ψ - 1 by push_cast; ring] at this
    obtain ⟨iso, -⟩ := exists_iso_of_hom_eq_zero hTFd hTGd e₂
      (fun g => by
        have := F.hom_chain_pred_eq_zero' s hFpos hGfac hlast.ge (eF₁.inv ≫ g)
        simpa using congrArg (eF₁.hom ≫ ·) this)
      (fun g => by
        have := G.hom_chain_pred_eq_zero' s hGpos hFfac hlast.le (eG₁.inv ≫ g)
        simpa using congrArg (eG₁.hom ≫ ·) this)
      (fun g => by
        have := F.hom_chain_pred_eq_zero' s hFpos (hshift hFfac) (by linarith) (eF₁.inv ≫ g)
        simpa using congrArg (eF₁.hom ≫ ·) this)
      (fun g => by
        have := G.hom_chain_pred_eq_zero' s hGpos (hshift hGfac) (by linarith) (eG₁.inv ≫ g)
        simpa using congrArg (eG₁.hom ≫ ·) this)
    -- the prefixes filter isomorphic objects
    let eA : G.chain.obj ⟨G.n - 1, by omega⟩ ≅ F.chain.obj ⟨F.n - 1, by omega⟩ :=
      eG₁.symm.trans ((Triangle.π₁.mapIso iso).symm.trans eF₁)
    let F' := F.prefix C (F.n - 1) (by omega)
    let G' := (G.prefix C (G.n - 1) (by omega)).ofIso C eA
    have hpre := ih F' G' (by change (F.n - 1) + (G.n - 1) ≤ N; omega)
    rw [Fin.sum_eq_sum_pred_add_last hFpos, Fin.sum_eq_sum_pred_add_last hGpos]
    have hl : f (F.φ ⟨F.n - 1, by omega⟩) (F.factor ⟨F.n - 1, by omega⟩) =
        f (G.φ ⟨G.n - 1, by omega⟩) (G.factor ⟨G.n - 1, by omega⟩) := by
      rw [hlast]
      exact hiso _ (Triangle.π₃.mapIso iso)
    exact congrArg₂ (· + ·) hpre hl

/-- The same statement for the HN filtrations of two isomorphic objects. -/
theorem HNFiltration.sum_factor_eq_of_iso (s : Slicing C) (f : ℝ → C → M)
    (hiso : ∀ φ {X Y : C}, (X ≅ Y) → f φ X = f φ Y) (hzero : ∀ φ X, IsZero X → f φ X = 0)
    {E E' : C} (e : E ≅ E') (F : HNFiltration C s.P E) (G : HNFiltration C s.P E') :
    ∑ i, f (F.φ i) (F.factor i) = ∑ j, f (G.φ j) (G.factor j) :=
  HNFiltration.sum_factor_eq s f hiso hzero (F.ofIso C e) G

end Sums

/-! ### The mass -/

namespace PreStabilityCondition.WithClassMap

variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ} (σ : WithClassMap C v)

/-- The **mass** `m_σ(E) = Σ_i |Z(A_i)|` over the HN factors `A_i` of `E`
(Bridgeland, arXiv:math/0212237, §8). Any HN filtration gives the same value (`mass_eq_sum`). -/
def mass (E : C) : ℝ :=
  ∑ i, ‖σ.charge ((σ.slicing.hn_exists E).some.factor i)‖

/-- The mass is the sum over **any** HN filtration. -/
theorem mass_eq_sum {E : C} (F : HNFiltration C σ.slicing.P E) :
    σ.mass E = ∑ i, ‖σ.charge (F.factor i)‖ :=
  HNFiltration.sum_factor_eq σ.slicing (fun _ X => ‖σ.charge X‖)
    (fun _ _ _ e => by simp only [charge_def, classOf_iso C v e])
    (fun _ _ hX => by simp [charge_isZero σ hX]) _ F

theorem mass_nonneg (E : C) : 0 ≤ σ.mass E :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Isomorphic objects have the same mass. -/
theorem mass_iso {E E' : C} (e : E ≅ E') : σ.mass E = σ.mass E' := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [σ.mass_eq_sum F, σ.mass_eq_sum (F.ofIso C e)]
  rfl

theorem mass_of_isZero {E : C} (hE : IsZero E) : σ.mass E = 0 := by
  rw [σ.mass_eq_sum (HNFiltration.zero C E hE)]
  rfl

/-- A semistable object has mass `|Z(E)|`. -/
theorem mass_eq_norm_charge_of_semistable {φ : ℝ} {E : C} (hP : σ.slicing.P φ E) :
    σ.mass E = ‖σ.charge E‖ := by
  rw [σ.mass_eq_sum (HNFiltration.single C E φ hP)]
  change ∑ _ : Fin 1, _ = _
  rw [Fin.sum_univ_one]
  rfl

/-- `|Z(E)| ≤ m_σ(E)`. -/
theorem norm_charge_le_mass (E : C) : ‖σ.charge E‖ ≤ σ.mass E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [σ.mass_eq_sum F, σ.charge_postnikovTower_eq_sum F.toPostnikovTower]
  exact norm_sum_le _ _

/-- A nonzero semistable factor has `|Z| > 0`. -/
theorem norm_charge_pos_of_semistable {φ : ℝ} {E : C} (hP : σ.slicing.P φ E)
    (hE : ¬IsZero E) : 0 < ‖σ.charge E‖ := by
  obtain ⟨m, hm, hZ⟩ := σ.compat φ E hP hE
  rw [hZ, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hm]
  exact hm

/-- A nonzero object has positive mass. -/
theorem mass_pos {E : C} (hE : ¬IsZero E) : 0 < σ.mass E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  obtain ⟨i, hi⟩ := F.exists_nonzero_factor C hE
  rw [σ.mass_eq_sum F]
  exact Finset.sum_pos' (fun _ _ => norm_nonneg _)
    ⟨i, Finset.mem_univ _, σ.norm_charge_pos_of_semistable (F.semistable i) hi⟩

theorem mass_eq_zero_iff (E : C) : σ.mass E = 0 ↔ IsZero E :=
  ⟨fun h => by_contra fun hE => (σ.mass_pos hE).ne' h, σ.mass_of_isZero⟩

/-- Shifts preserve the mass. -/
theorem mass_shift (E : C) (a : ℤ) : σ.mass (E⟦a⟧) = σ.mass E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [σ.mass_eq_sum (F.shift C σ.slicing a), σ.mass_eq_sum F]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ‖σ.Z (classOf C v ((F.factor i)⟦a⟧))‖ = ‖σ.Z (classOf C v (F.factor i))‖
  rw [classOf, classOf, K₀.of_shift_int, map_zsmul, map_zsmul, zsmul_eq_mul, norm_mul]
  simp

/-! ### The split identity -/

/-- **The split identity.** In a distinguished triangle `X → E → Y → X[1]` with `X` of phases
above `t` and `Y` of phases at most `t`, `m(E) = m(X) + m(Y)`. -/
theorem mass_eq_add_of_triangle [IsTriangulated C] {t : ℝ} {X E Y : C} {f : X ⟶ E}
    {g : E ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (hX : σ.slicing.gtProp C t X) (hY : σ.slicing.leProp C t Y) :
    σ.mass E = σ.mass X + σ.mass Y := by
  have hFX : ∃ FX : HNFiltration C σ.slicing.P X, ∀ i, t < FX.φ i := by
    rcases hX with hX | ⟨F, hn, hlt⟩
    · exact ⟨HNFiltration.zero C X hX, fun i => i.elim0⟩
    · exact ⟨F, fun i => hlt.trans_le (F.phase_mem_range C hn i).1⟩
  have hFY : ∃ FY : HNFiltration C σ.slicing.P Y, ∀ j, FY.φ j ≤ t := by
    rcases hY with hY | ⟨F, hn, hle⟩
    · exact ⟨HNFiltration.zero C Y hY, fun i => i.elim0⟩
    · exact ⟨F, fun j => (F.phase_mem_range C hn j).2.trans hle⟩
  obtain ⟨FX, hFX⟩ := hFX
  obtain ⟨FY, hFY⟩ := hFY
  obtain ⟨FE, hn, hfirst, hsecond⟩ :=
    HNFiltration.exists_concat FX FY hT fun i j => (hFY j).trans_lt (hFX i)
  rw [σ.mass_eq_sum FE, σ.mass_eq_sum FX, σ.mass_eq_sum FY, Fin.sum_eq_add_of_eq hn]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨-, ⟨e⟩⟩ := hfirst i
    simp only [charge_def, classOf_iso C v e]
  · refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨-, ⟨e⟩⟩ := hsecond j
    simp only [charge_def, classOf_iso C v e]

/-- Every object splits at any phase `t` into its parts above and at most `t`, and the mass
splits accordingly: `m(E) = m(E_{> t}) + m(E_{≤ t})`. -/
theorem exists_mass_split [IsTriangulated C] (t : ℝ) (E : C) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧ σ.slicing.gtProp C t X ∧ σ.slicing.leProp C t Y ∧
        σ.mass E = σ.mass X + σ.mass Y := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  obtain ⟨X, Y, GX, GY, f, g, h, hT, hGX, hGY, -, -⟩ := F.exists_split_at_cutoff C t
  have hX : σ.slicing.gtProp C t X := by
    by_cases hn : 0 < GX.n
    · exact σ.slicing.gtProp_of_hn C GX t hGX hn
    · exact Or.inl (GX.isZero_of_length_zero (by omega))
  have hY : σ.slicing.leProp C t Y := by
    by_cases hn : 0 < GY.n
    · exact σ.slicing.leProp_of_hn C GY t hGY hn
    · exact Or.inl (GY.isZero_of_length_zero (by omega))
  exact ⟨X, Y, f, g, h, hT, hX, hY, σ.mass_eq_add_of_triangle hT hX hY⟩

/-! ### Ikeda subadditivity -/

/-- **Ikeda subadditivity**: `m_σ(B) ≤ m_σ(A) + m_σ(C)` on every distinguished triangle
`A → B → C → A[1]`. For a stability condition this is Ikeda, arXiv:1612.00995, Proposition 3.3;
the library does not prove it, so it is a hypothesis wherever it is used. -/
def MassSubadditive : Prop :=
  ∀ T ∈ distTriang C, σ.mass T.obj₂ ≤ σ.mass T.obj₁ + σ.mass T.obj₃

end PreStabilityCondition.WithClassMap

/-! ### The `2m(D)` lemma -/

section TwoMass

variable [IsTriangulated C]

/-- One side of the `2m(D)` lemma: the cone of `(f, a) : A → B ⊞ D` and the cone of `f` differ in
`m` by at most `m(D)`. -/
private theorem abs_sub_cone_lift_le (m : C → ℝ)
    (hshift : ∀ (X : C) (a : ℤ), m (X⟦a⟧) = m X)
    (hsub : ∀ T ∈ distTriang C, m T.obj₂ ≤ m T.obj₁ + m T.obj₃)
    {A B D K L : C} {f : A ⟶ B} {g : B ⟶ K} {h : K ⟶ A⟦(1 : ℤ)⟧} (a : A ⟶ D)
    (hT : Triangle.mk f g h ∈ distTriang C) {g' : B ⊞ D ⟶ L} {h' : L ⟶ A⟦(1 : ℤ)⟧}
    (hT' : Triangle.mk (biprod.lift f a) g' h' ∈ distTriang C) :
    |m K - m L| ≤ m D := by
  -- the triangle `B ⊞ D → B → D[1] → (B ⊞ D)[1]`
  have hfst : Triangle.mk (biprod.fst : B ⊞ D ⟶ B) (0 : B ⟶ D⟦(1 : ℤ)⟧)
      (-(biprod.inr : D ⟶ B ⊞ D)⟦(1 : ℤ)⟧') ∈ distTriang C := by
    refine isomorphic_distinguished _
      (rot_of_distTriang _ (binaryBiproductTriangle_distinguished D B)) _ ?_
    refine Triangle.isoMk _ _ (biprod.braiding B D) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · change biprod.fst ≫ 𝟙 B = biprod.lift biprod.snd biprod.fst ≫ biprod.snd
      rw [Category.comp_id, biprod.lift_snd]
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · have e : (biprod.inr : D ⟶ B ⊞ D) ≫ biprod.lift biprod.snd biprod.fst = biprod.inl := by
        apply biprod.hom_ext <;> simp
      change (-(shiftFunctor C (1 : ℤ)).map (biprod.inr : D ⟶ B ⊞ D)) ≫
          (shiftFunctor C (1 : ℤ)).map (biprod.lift biprod.snd biprod.fst) =
        𝟙 _ ≫ (-(shiftFunctor C (1 : ℤ)).map (biprod.inl : D ⟶ D ⊞ B))
      rw [Category.id_comp, Preadditive.neg_comp, ← Functor.map_comp, e]
  have hcomp : biprod.lift f a ≫ biprod.fst = f := biprod.lift_fst _ _
  let O := Triangulated.someOctahedron hcomp hT' hfst hT
  have hO := O.mem
  have h₁ := hsub _ hO
  have h₂ := hsub _ (inv_rot_of_distTriang _ hO)
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.invRotate_obj₁,
    Triangle.invRotate_obj₂, Triangle.invRotate_obj₃] at h₁ h₂
  rw [hshift] at h₁
  have hD : m ((D⟦(1 : ℤ)⟧)⟦(-1 : ℤ)⟧) = m D := by rw [hshift, hshift]
  rw [hD] at h₂
  rw [abs_le]
  constructor <;> linarith

/-- **The `2m(D)` lemma.** Let `m` be invariant under shifts and subadditive on distinguished
triangles. If `f, f' : A → B` differ by a map `a ≫ b` through `D`, and `K`, `K'`
are cones of `f`, `f'`, then `|m(K) - m(K')| ≤ 2 m(D)`. The map `(f, a) : A → B ⊞ D` and its
composite with the automorphism `[[1, b], [0, 1]]` of `B ⊞ D`, which is `(f', a)`, have the same
cone `L`, and the octahedral axiom gives `|m(K) - m(L)| ≤ m(D)` and `|m(K') - m(L)| ≤ m(D)`. -/
theorem abs_sub_mass_cone_le (m : C → ℝ)
    (hshift : ∀ (X : C) (a : ℤ), m (X⟦a⟧) = m X)
    (hsub : ∀ T ∈ distTriang C, m T.obj₂ ≤ m T.obj₁ + m T.obj₃)
    {A B D K K' : C} {f f' : A ⟶ B} (a : A ⟶ D) (b : D ⟶ B) (hf : f' = f + a ≫ b)
    {g : B ⟶ K} {h : K ⟶ A⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    {g' : B ⟶ K'} {h' : K' ⟶ A⟦(1 : ℤ)⟧} (hT' : Triangle.mk f' g' h' ∈ distTriang C) :
    |m K - m K'| ≤ 2 * m D := by
  obtain ⟨L, gL, hL, hTL⟩ := distinguished_cocone_triangle (biprod.lift f a)
  -- the automorphism `[[1, b], [0, 1]]` of `B ⊞ D`
  let φ : B ⊞ D ≅ B ⊞ D :=
    { hom := biprod.lift (biprod.fst + biprod.snd ≫ b) biprod.snd
      inv := biprod.lift (biprod.fst - biprod.snd ≫ b) biprod.snd
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  have hφ : biprod.lift f a ≫ φ.hom = biprod.lift f' a := by
    ext <;> simp [φ, hf]
  have hTL' : Triangle.mk (biprod.lift f' a) (φ.inv ≫ gL) hL ∈ distTriang C := by
    refine isomorphic_distinguished _ hTL _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) φ.symm (Iso.refl _) ?_ ?_ ?_
    · simp [← hφ]
    · simp
    · simp
  have h₁ := abs_sub_cone_lift_le m hshift hsub a hT hTL
  have h₂ := abs_sub_cone_lift_le m hshift hsub a hT' hTL'
  rw [abs_le] at h₁ h₂ ⊢
  constructor <;> linarith

/-- **The `2m(D)` lemma for the mass**, under Ikeda subadditivity. -/
theorem PreStabilityCondition.WithClassMap.abs_sub_mass_cone_le {Λ : Type u'} [AddCommGroup Λ]
    {v : K₀ C →+ Λ} (σ : PreStabilityCondition.WithClassMap C v) (hσ : σ.MassSubadditive)
    {A B D K K' : C} {f f' : A ⟶ B} (a : A ⟶ D) (b : D ⟶ B) (hf : f' = f + a ≫ b)
    {g : B ⟶ K} {h : K ⟶ A⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    {g' : B ⟶ K'} {h' : K' ⟶ A⟦(1 : ℤ)⟧} (hT' : Triangle.mk f' g' h' ∈ distTriang C) :
    |σ.mass K - σ.mass K'| ≤ 2 * σ.mass D :=
  Triangulated.abs_sub_mass_cone_le σ.mass σ.mass_shift hσ a b hf hT hT'

end TwoMass

end CategoryTheory.Triangulated
