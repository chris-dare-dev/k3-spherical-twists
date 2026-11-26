/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Mass
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.ConeHN

/-!
# Flag reassembly and additivity of the mass

Let `U → E → Q →δ U⟦1⟧` be a distinguished triangle in a triangulated category with a
prestability condition `σ = (P, Z)`. For a phase `t`, the cut composite
`d_t : Q_{≥t} → Q → U⟦1⟧ → U_{<t}⟦1⟧` vanishes exactly when the triangle truncates compatibly at
`t` (`CategoryTheory.Triangulated.Slicing.cut_criterion`); when it vanishes at every `t`, the HN
filtrations of `U` and `Q` reassemble into one of `E`. This file proves that the mass is then
additive:

  `d_t = 0` for every `t` `⟹` `m(E) = m(U) + m(Q)`
  (`PreStabilityCondition.WithClassMap.mass_eq_add_of_forall_cutVanishes`).

The proof reads the mass from charges of truncations. For an HN filtration `F` of `X`, the charge
of the part of `X` of phases at least `t` is `∑_{φ_i ≥ t} Z(A_i)`, for any choice of the
truncation (`charge_coreflection_eq_chargeGe`): the HN filtrations of the two parts concatenate
to an HN filtration of `X`, and sums over HN factors do not depend on the filtration. A
compatible truncation triangle `U_{≥t} → E_{≥t} → Q_{≥t}` makes these partial charges additive at
every `t`. Their jump at a phase `ψ` is the total charge of the factors of phase `ψ`, a
nonnegative multiple of `exp(iπψ)`, and the mass is the sum of the norms of the jumps
(`mass_eq_sum_norm_jump`). The jumps of `E` are the sums of those of `U` and `Q`, which lie on one
ray, so their norms add.

## The converse and the defect identity

The converse, `m(E) = m(U) + m(Q) ⟹ d_t = 0` for every `t`, is the vanishing case of the mass
defect identity on the family of hearts `P((a, a + 1])`: the defect `m(U) + m(Q) - m(E)` is an
integral over `a` of the lengths `Im(e^{-iπa} Z)` of the images of the connecting maps of the
long exact sequences of heart cohomology. The library has the hearts `P((a, a + 1])` as
t-structures (`Slicing.toTStructure`) but not their cohomology functors `H⁰` as homological
functors (Beilinson–Bernstein–Deligne, *Faisceaux pervers*, 1.3.6), so neither the defect
identity nor the converse is proved here. Ikeda subadditivity (`MassSubadditive`), its inequality
case, stays a hypothesis wherever it is used.

## Main definitions

* `CategoryTheory.Triangulated.Slicing.CutVanishes`: the cut composite `d_t` vanishes.
* `PreStabilityCondition.WithClassMap.chargeGe`, `PreStabilityCondition.WithClassMap.jump`: the
  partial charge in phases at least `t` and its jump at a phase.

## Main results

* `PreStabilityCondition.WithClassMap.charge_coreflection_eq_chargeGe`: the charge of the part of
  phases at least `t`.
* `PreStabilityCondition.WithClassMap.mass_eq_sum_norm_jump`: the mass from the jumps.
* `PreStabilityCondition.WithClassMap.mass_eq_add_of_forall_cutVanishes`: flag reassembly gives
  additive mass.

## References

* T. Bridgeland, *Stability conditions on triangulated categories*, arXiv:math/0212237, §3, §8.
* A. Bapat, A. Deopurkar, A. Licata, *Spherical objects and stability conditions on 2-CY
  quiver categories*, arXiv:2011.07908, Appendix A (rectifiability of one triangle).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v u'

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The cut composite `d_t : Q_{≥t} → Q → U⟦1⟧ → U_{<t}⟦1⟧` of a map `δ : Q ⟶ U⟦1⟧` vanishes,
for some choice of the `(≥ t, < t)` truncation of `U` and of the coreflection of `Q` into
`P(≥ t)`; by `Slicing.cut_criterion` the condition does not depend on the choice. -/
def Slicing.CutVanishes (s : Slicing C) (t : ℝ) {U Q : C} (δ : Q ⟶ U⟦(1 : ℤ)⟧) : Prop :=
  ∃ (U₁ U₂ : C) (ιU : U₁ ⟶ U) (πU : U ⟶ U₂) (εU : U₂ ⟶ U₁⟦(1 : ℤ)⟧) (Q₁ : C) (ιQ : Q₁ ⟶ Q),
    Triangle.mk ιU πU εU ∈ distTriang C ∧ s.geProp C t U₁ ∧ s.ltProp C t U₂ ∧
      (s.geProp C t).IsCoreflection ιQ ∧ ιQ ≫ δ ≫ πU⟦(1 : ℤ)⟧' = 0

namespace PreStabilityCondition.WithClassMap

variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ} (σ : WithClassMap C v)

/-! ### Partial charges -/

/-- The charge of the HN factors of phase at least `t`. -/
def chargeGe {E : C} (F : HNFiltration C σ.slicing.P E) (t : ℝ) : ℂ :=
  ∑ i, if t ≤ F.φ i then σ.charge (F.factor i) else 0

/-- The partial charge does not depend on the HN filtration. -/
lemma chargeGe_eq {E : C} (F G : HNFiltration C σ.slicing.P E) (t : ℝ) :
    σ.chargeGe F t = σ.chargeGe G t :=
  HNFiltration.sum_factor_eq σ.slicing (fun φ X ↦ if t ≤ φ then σ.charge X else 0)
    (fun _ _ _ e ↦ by simp only [charge_def, classOf_iso C v e])
    (fun _ _ hX ↦ by simp [charge_isZero σ hX]) F G

/-- An object of phases at least `t` has an HN filtration with all phases at least `t`. -/
private lemma exists_hn_ge {t : ℝ} {X : C} (hX : σ.slicing.geProp C t X) :
    ∃ F : HNFiltration C σ.slicing.P X, ∀ i, t ≤ F.φ i := by
  rcases hX with hX | ⟨F, hn, hle⟩
  · exact ⟨HNFiltration.zero C X hX, fun i ↦ i.elim0⟩
  · exact ⟨F, fun i ↦ hle.trans (F.phase_mem_range C hn i).1⟩

/-- An object of phases below `t` has an HN filtration with all phases below `t`. -/
private lemma exists_hn_lt {t : ℝ} {X : C} (hX : σ.slicing.ltProp C t X) :
    ∃ F : HNFiltration C σ.slicing.P X, ∀ i, F.φ i < t := by
  rcases hX with hX | ⟨F, hn, hlt⟩
  · exact ⟨HNFiltration.zero C X hX, fun i ↦ i.elim0⟩
  · exact ⟨F, fun i ↦ (F.phase_mem_range C hn i).2.trans_lt hlt⟩

variable [IsTriangulated C]

/-- **The charge of the part of phases at least `t`.** For a distinguished triangle
`X₁ → X → X₂ → X₁⟦1⟧` with `X₁` of phases at least `t` and `X₂` of phases below `t`, and any HN
filtration `F` of `X`, `Z(X₁) = ∑_{φ_i ≥ t} Z(A_i)`. -/
theorem charge_eq_chargeGe {t : ℝ} {X₁ X X₂ : C} {f : X₁ ⟶ X} {g : X ⟶ X₂}
    {h : X₂ ⟶ X₁⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (h₁ : σ.slicing.geProp C t X₁) (h₂ : σ.slicing.ltProp C t X₂)
    (F : HNFiltration C σ.slicing.P X) : σ.charge X₁ = σ.chargeGe F t := by
  obtain ⟨F₁, hF₁⟩ := σ.exists_hn_ge h₁
  obtain ⟨F₂, hF₂⟩ := σ.exists_hn_lt h₂
  obtain ⟨FX, hn, hfirst, hsecond⟩ :=
    HNFiltration.exists_concat F₁ F₂ hT fun i j ↦ (hF₂ j).trans_le (hF₁ i)
  rw [σ.chargeGe_eq F FX, chargeGe, Fin.sum_eq_add_of_eq hn,
    σ.charge_postnikovTower_eq_sum F₁.toPostnikovTower]
  have hz : ∑ j : Fin F₂.n, (if t ≤ FX.φ ⟨F₁.n + j, by omega⟩ then
      σ.charge (FX.factor ⟨F₁.n + j, by omega⟩) else 0) = 0 :=
    Finset.sum_eq_zero fun j _ ↦ by
      rw [(hsecond j).1, ite_eq_right (not_le.mpr (hF₂ j))]
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  obtain ⟨hφ, ⟨e⟩⟩ := hfirst i
  rw [hφ, ite_eq_left (hF₁ i)]
  simp only [charge_def, classOf_iso C v e]

/-- The charge of any coreflection into `P(≥ t)` is the partial charge. -/
theorem charge_coreflection_eq_chargeGe {t : ℝ} {X₁ X : C} {ι : X₁ ⟶ X}
    (hι : (σ.slicing.geProp C t).IsCoreflection ι) (F : HNFiltration C σ.slicing.P X) :
    σ.charge X₁ = σ.chargeGe F t := by
  obtain ⟨Y₁, Y₂, f, g, h, hT, h₁, h₂⟩ := σ.slicing.exists_split_geProp_ltProp t X
  have hf := σ.slicing.isCoreflection_geProp_of_top hT h₁ h₂
  rw [← σ.charge_eq_chargeGe hT h₁ h₂ F]
  simp only [charge_def, classOf_iso C v (hι.isoOfIsCoreflection hf)]

/-! ### Jumps -/

/-- The charge of the HN factors of phase exactly `ψ`. -/
def jump {E : C} (F : HNFiltration C σ.slicing.P E) (ψ : ℝ) : ℂ :=
  ∑ i, if F.φ i = ψ then σ.charge (F.factor i) else 0

/-- Above a phase `ψ`, the finitely many phases of a finite set leave a gap. -/
private lemma exists_gap_above (S : Finset ℝ) (ψ : ℝ) :
    ∃ ε > 0, ∀ φ ∈ S, ψ < φ → ψ + ε ≤ φ := by
  classical
  by_cases hS : (S.filter (ψ < ·)).Nonempty
  · refine ⟨(S.filter (ψ < ·)).min' hS - ψ, ?_, fun φ hφ hψ ↦ ?_⟩
    · have := (Finset.mem_filter.mp ((S.filter (ψ < ·)).min'_mem hS)).2
      linarith
    · have := (S.filter (ψ < ·)).min'_le φ (Finset.mem_filter.mpr ⟨hφ, hψ⟩)
      linarith
  · refine ⟨1, one_pos, fun φ hφ hψ ↦ absurd ⟨φ, Finset.mem_filter.mpr ⟨hφ, hψ⟩⟩ hS⟩

omit [IsTriangulated C] in
/-- The jump of the partial charge at `ψ`, for a gap `ε` above `ψ` containing no phase of `F`. -/
lemma chargeGe_sub_chargeGe {E : C} (F : HNFiltration C σ.slicing.P E) {ψ ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ i, ψ < F.φ i → ψ + ε ≤ F.φ i) :
    σ.chargeGe F ψ - σ.chargeGe F (ψ + ε) = σ.jump F ψ := by
  simp only [chargeGe, jump, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases lt_trichotomy (F.φ i) ψ with h | h | h
  · rw [ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_right h.ne, sub_zero]
  · rw [ite_eq_left h.ge, ite_eq_right (by linarith), ite_eq_left h, sub_zero]
  · rw [ite_eq_left h.le, ite_eq_left (hgap i h), ite_eq_right h.ne', sub_self]

omit [IsTriangulated C] in
/-- A jump lies on the ray of its phase: it is a nonnegative multiple of `exp(iπψ)`. -/
lemma exists_jump_eq {E : C} (F : HNFiltration C σ.slicing.P E) (ψ : ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧ σ.jump F ψ = (r : ℂ) * Complex.exp ((Real.pi * ψ : ℝ) * Complex.I) := by
  have key : ∀ i, ∃ r : ℝ, 0 ≤ r ∧ (if F.φ i = ψ then σ.charge (F.factor i) else 0) =
      (r : ℂ) * Complex.exp ((Real.pi * ψ : ℝ) * Complex.I) := fun i ↦ by
    by_cases hi : F.φ i = ψ
    · rw [ite_eq_left hi]
      by_cases hz : IsZero (F.factor i)
      · exact ⟨0, le_rfl, by simp [charge_isZero σ hz]⟩
      · obtain ⟨m, hm, hZ⟩ := σ.compat _ _ (F.semistable i) hz
        exact ⟨m, hm.le, by rw [hZ, hi]⟩
    · exact ⟨0, le_rfl, by simp [hi]⟩
  choose r hr he using key
  refine ⟨∑ i, r i, Finset.sum_nonneg fun i _ ↦ hr i, ?_⟩
  rw [jump, Complex.ofReal_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ he i

omit [IsTriangulated C] in
/-- The norm of a jump is the sum of the norms of the factors of that phase: the phases of an HN
filtration are distinct. -/
lemma norm_jump {E : C} (F : HNFiltration C σ.slicing.P E) (ψ : ℝ) :
    ‖σ.jump F ψ‖ = ∑ i, if F.φ i = ψ then ‖σ.charge (F.factor i)‖ else 0 := by
  classical
  by_cases h : ∃ i, F.φ i = ψ
  · obtain ⟨i₀, hi₀⟩ := h
    have hother : ∀ j, j ≠ i₀ → F.φ j ≠ ψ := fun j hj hjψ ↦
      hj (F.hφ.injective (hjψ.trans hi₀.symm))
    rw [jump, Finset.sum_eq_single i₀ (fun j _ hj ↦ by rw [ite_eq_right (hother j hj)])
        (by simp), ite_eq_left hi₀,
      Finset.sum_eq_single i₀ (fun j _ hj ↦ by rw [ite_eq_right (hother j hj)]) (by simp),
      ite_eq_left hi₀]
  · push Not at h
    simp [jump, h]

omit [IsTriangulated C] in
/-- **The mass from the jumps.** For any finite set `S` containing the phases of an HN filtration
`F` of `E`, `m(E) = ∑_{ψ ∈ S} |jump(ψ)|`. -/
theorem mass_eq_sum_norm_jump {E : C} (F : HNFiltration C σ.slicing.P E) (S : Finset ℝ)
    (hS : ∀ i, F.φ i ∈ S) : σ.mass E = ∑ ψ ∈ S, ‖σ.jump F ψ‖ := by
  classical
  simp only [σ.norm_jump F]
  rw [Finset.sum_comm, σ.mass_eq_sum F]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_ite_eq S (F.φ i) (fun _ ↦ ‖σ.charge (F.factor i)‖), ite_eq_left (hS i)]

/-! ### Flag reassembly -/

/-- **The partial charges are additive** when the triangle truncates compatibly at `t`. -/
theorem chargeGe_add_of_cutVanishes {U E Q : C} {u : U ⟶ E} {e : E ⟶ Q}
    {δ : Q ⟶ U⟦(1 : ℤ)⟧} (hT : Triangle.mk u e δ ∈ distTriang C) {t : ℝ}
    (ht : σ.slicing.CutVanishes t δ) (FU : HNFiltration C σ.slicing.P U)
    (FE : HNFiltration C σ.slicing.P E) (FQ : HNFiltration C σ.slicing.P Q) :
    σ.chargeGe FE t = σ.chargeGe FU t + σ.chargeGe FQ t := by
  obtain ⟨U₁, U₂, ιU, πU, εU, Q₁, ιQ, hU, hU₁, hU₂, hιQ, hd⟩ := ht
  obtain ⟨E₁, E₂, ιE, πE, εE, hE, hE₁, hE₂⟩ := σ.slicing.exists_split_geProp_ltProp t E
  have hιE := σ.slicing.isCoreflection_geProp_of_top hE hE₁ hE₂
  obtain ⟨a, b, c, hA, -, -, -⟩ :=
    ((σ.slicing.cut_criterion hT hU hU₁ hU₂ hιQ hιE).out 1 3).1 hd
  have hK := classOf_triangle C v _ hA
  have hZ : σ.charge E₁ = σ.charge U₁ + σ.charge Q₁ := by
    simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃] at hK
    rw [charge_def, charge_def, charge_def, hK, map_add]
  rw [← σ.charge_eq_chargeGe hE hE₁ hE₂ FE, ← σ.charge_eq_chargeGe hU hU₁ hU₂ FU,
    ← σ.charge_coreflection_eq_chargeGe hιQ FQ, hZ]

/-- **Flag reassembly gives additive mass.** Let `U → E → Q →δ U⟦1⟧` be distinguished. If the cut
composite `d_t : Q_{≥t} → U_{<t}⟦1⟧` vanishes for every `t`, that is, if the HN filtrations of `U`
and `Q` reassemble to one of `E`, then `m(E) = m(U) + m(Q)`. -/
theorem mass_eq_add_of_forall_cutVanishes {U E Q : C} {u : U ⟶ E} {e : E ⟶ Q}
    {δ : Q ⟶ U⟦(1 : ℤ)⟧} (hT : Triangle.mk u e δ ∈ distTriang C)
    (hcut : ∀ t, σ.slicing.CutVanishes t δ) : σ.mass E = σ.mass U + σ.mass Q := by
  classical
  obtain ⟨FU⟩ := σ.slicing.hn_exists U
  obtain ⟨FE⟩ := σ.slicing.hn_exists E
  obtain ⟨FQ⟩ := σ.slicing.hn_exists Q
  let S : Finset ℝ :=
    Finset.univ.image FU.φ ∪ Finset.univ.image FE.φ ∪ Finset.univ.image FQ.φ
  have hSU : ∀ i, FU.φ i ∈ S := fun i ↦ by simp [S]
  have hSE : ∀ i, FE.φ i ∈ S := fun i ↦ by simp [S]
  have hSQ : ∀ i, FQ.φ i ∈ S := fun i ↦ by simp [S]
  have hjump : ∀ ψ, σ.jump FE ψ = σ.jump FU ψ + σ.jump FQ ψ := fun ψ ↦ by
    obtain ⟨ε, hε, hgap⟩ := exists_gap_above S ψ
    rw [← σ.chargeGe_sub_chargeGe FE hε fun i h ↦ hgap _ (hSE i) h,
      ← σ.chargeGe_sub_chargeGe FU hε fun i h ↦ hgap _ (hSU i) h,
      ← σ.chargeGe_sub_chargeGe FQ hε fun i h ↦ hgap _ (hSQ i) h,
      σ.chargeGe_add_of_cutVanishes hT (hcut ψ) FU FE FQ,
      σ.chargeGe_add_of_cutVanishes hT (hcut (ψ + ε)) FU FE FQ]
    ring
  rw [σ.mass_eq_sum_norm_jump FE S hSE, σ.mass_eq_sum_norm_jump FU S hSU,
    σ.mass_eq_sum_norm_jump FQ S hSQ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ψ _ ↦ ?_
  obtain ⟨r, hr, hrU⟩ := σ.exists_jump_eq FU ψ
  obtain ⟨r', hr', hrQ⟩ := σ.exists_jump_eq FQ ψ
  rw [hjump, hrU, hrQ, ← add_mul, ← Complex.ofReal_add, norm_mul, norm_mul, norm_mul,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr, abs_of_nonneg hr',
    abs_of_nonneg (add_nonneg hr hr')]
  ring

end PreStabilityCondition.WithClassMap

end CategoryTheory.Triangulated
