/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.CentralCharge
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Mass.CutLoss
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.DivisibilityObstruction

/-!
# Twist ladders and the mass of a twist power

Let `σ = (P, Z)` be a prestability condition on a triangulated category and `A` a spherical
object, semistable for `σ` of mass `a` and phase `φ`. For `k ≥ 1` the cone of `E → T_A^k E` is a
sum of *ladders*: for each Ext degree `p`, `dim Ext^p(A, E)` copies of the `k`-cell object whose
layers `A[1 - p - j]`, `j < k`, are semistable of mass `a` at the phases `φ + 1 - p - j`
(Bapat–Deopurkar–Licata, arXiv:2011.07908, Lemma 4.11, under two hypotheses on `E`). This file
reads the mass of the twist power off that shape with the cut-loss lemma.

`LadderFamily σ` is the shape: `N` ladders `L c`, each with an HN filtration of `k` cells of mass
`a`, the `j`-th of phase `ψ c - j`. `TwistLadderHypotheses σ f` is a distinguished triangle
`E → F → cone → E⟦1⟧` on `f` whose cone is the sum of a ladder family; its field
`TwistLadderHypotheses.iso` records the source of that shape and its hypotheses. Then:

* the cone has mass `N k a` (`TwistLadderHypotheses.mass_cone`), and for every truncation of the
  cone at a cut `s` the part above `s` has mass `a ∑_c min{k, ⌈ψ c - s⌉₊}`
  (`LadderFamily.mass_of_gtProp_leProp`): the cell `j` of the ladder `c` lies above `s` exactly
  when `j < ψ c - s` (`Nat.card_filter_range_lt_sub_eq_min_ceil`);
* **the twist bound** (`TwistLadderHypotheses.twist_bound`): under Ikeda subadditivity, if `E` has
  phases at least `s`, then `0 ≤ m(E) + N k a - m(F) ≤ 2a ∑_c min{k, ⌈ψ c - s⌉₊}`;
* **zero loss** (`TwistLadderHypotheses.zero_loss`): if moreover no ladder starts above `s`, then
  `m(F) = m(E) + N k a`, with no subadditivity. The mass `1 + 10n/9` of `Tⁿ𝒪_x` in the opening
  example (`AlgebraicGeometry.K3.PicardRankOne.opening_mass_Tpow`) is an instance
  (`TwistLadderHypotheses.mass_eq_opening`);
* negative powers, with the ladder sum as the first term of the triangle and the dual cut-loss
  lemma (`LadderFamily.inverse_twist_bound`).

The general inputs are the mass of the part above a cut, read off any HN filtration
(`PreStabilityCondition.WithClassMap.mass_eq_sum_ite_of_gtProp_leProp`,
`PreStabilityCondition.WithClassMap.mass_eq_sum_ite_of_geProp_ltProp`), and its additivity over a
finite biproduct (`PreStabilityCondition.WithClassMap.mass_eq_sum_mass_of_biproduct`).

## Real objects

Mathlib has no twist functors, and no triangulated category carrying a slicing, so
`TwistLadderHypotheses` has no instance from real objects. The missing input is the 2-Calabi–Yau
category `D^b(X)` of a K3 surface with its spherical twists and its stability conditions. The test
`K3TwistsTest/TwistLadderModel.lean` builds ladders relative to one prestability condition: the
empty ladder family and the one-cell ladder of a semistable object.

## Main definitions

* `PreStabilityCondition.WithClassMap.LadderFamily σ`: `N` ladders of `k` cells of mass `a`.
* `PreStabilityCondition.WithClassMap.TwistLadderHypotheses σ f`: a triangle on `f` whose cone is
  a sum of ladders.

## Main results

* `PreStabilityCondition.WithClassMap.mass_eq_sum_ite_of_gtProp_leProp`: the mass above a cut.
* `PreStabilityCondition.WithClassMap.LadderFamily.mass_of_gtProp_leProp`: the cells above a cut.
* `PreStabilityCondition.WithClassMap.TwistLadderHypotheses.twist_bound`: **the twist bound**.
* `PreStabilityCondition.WithClassMap.TwistLadderHypotheses.zero_loss`,
  `PreStabilityCondition.WithClassMap.TwistLadderHypotheses.mass_eq_opening`: **zero loss**, and
  the opening example as an instance.
* `PreStabilityCondition.WithClassMap.LadderFamily.inverse_twist_bound`: negative powers.

## References

* A. Bapat, A. Deopurkar, A. Licata, *Spherical objects and stability conditions on 2-CY quiver
  categories*, arXiv:2011.07908, Lemma 4.11 and Appendix A.
* A. Ikeda, *Mass growth of objects and categorical entropy*, arXiv:1612.00995, Proposition 3.3.
* P. Seidel, R. Thomas, *Braid group actions on derived categories of coherent sheaves*,
  arXiv:math/0001043, §2.

## Tags

stability condition, mass, spherical twist, ladder, cut-loss lemma
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace PreStabilityCondition.WithClassMap

variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ} (σ : WithClassMap C v)

/-! ### Ladders -/

/-- **A family of ladders** for `σ`: `N` objects `L c`, each with an HN filtration of `k`
factors (the cells), the `j`-th of phase `ψ c - j` and with charge of norm `a`. For a spherical
object `A` semistable of mass `a` and phase `φ`, the `k`-cell object with layers `A[1 - p - j]`
is a ladder with top phase `φ + 1 - p` (see `TwistLadderHypotheses.iso`). -/
structure LadderFamily where
  /-- The number of ladders. -/
  N : ℕ
  /-- The number of cells of each ladder. -/
  k : ℕ
  /-- The mass of each cell. -/
  a : ℝ
  /-- The mass of a cell is nonnegative. -/
  a_nonneg : 0 ≤ a
  /-- The top phases: the `j`-th cell of the ladder `c` has phase `ψ c - j`. For the cone of
  `E → T_A^k E`, `ψ c = φ + 1 - p_c` for the Ext degree `p_c` of the copy `c`. -/
  ψ : Fin N → ℝ
  /-- The ladders. -/
  L : Fin N → C
  /-- An HN filtration of each ladder. -/
  filtration : ∀ c, HNFiltration C σ.slicing.P (L c)
  /-- Each ladder has `k` cells. -/
  length_eq : ∀ c, (filtration c).n = k
  /-- The `j`-th cell of the ladder `c` has phase `ψ c - j`. -/
  phase_eq : ∀ c (j : Fin (filtration c).n), (filtration c).φ j = ψ c - (j : ℕ)
  /-- Each cell has charge of norm `a`, so mass `a`. -/
  norm_charge_eq : ∀ c j, ‖σ.charge ((filtration c).factor j)‖ = a

/-- **A twist ladder** for `f : E ⟶ F`: a distinguished triangle `E → F → cone → E⟦1⟧` whose cone
is the sum of a family of ladders. It is the shape of the cone of `E → T_A^k E` for a spherical
twist `T_A`; the field `iso` gives the source and its hypotheses. -/
structure TwistLadderHypotheses {E F : C} (f : E ⟶ F) extends LadderFamily σ where
  /-- The third term of a distinguished triangle on `f`. -/
  cone : C
  /-- The second map of the triangle. -/
  g : F ⟶ cone
  /-- The connecting map of the triangle. -/
  h : cone ⟶ E⟦(1 : ℤ)⟧
  /-- The triangle `E → F → cone → E⟦1⟧` is distinguished. -/
  dist : Triangle.mk f g h ∈ distTriang C
  /-- **The twist ladder**: the cone is the sum of the ladders.

  For a spherical object `A`, semistable for `σ` of mass `a` and phase `φ`, and `k ≥ 1`, the cone
  of `E → T_A^k E` is `Hom•(A, E) ⊗ A_{k-1}[1]`, where `A_{k-1}` is the `k`-cell object: for each
  Ext degree `p`, `h^p = dim Ext^p(A, E)` copies of the `k`-cell object whose layers
  `A[1 - p], A[-p], …, A[2 - p - k]` are semistable of mass `a` at the strictly decreasing phases
  `φ + 1 - p - j`, `j = 0, …, k - 1` (Bapat–Deopurkar–Licata, arXiv:2011.07908, Lemma 4.11). So
  `N = ∑_p h^p` and `ψ c = φ + 1 - p_c`. That lemma needs two hypotheses on `E`: no shift of `A`
  is a direct summand of `E`, and `E` has no endomorphisms of negative degree; the appendix of the
  same paper assumes `A` semistable.

  The sharp hypothesis for one power `k` is that `E` has no indecomposable summand `Λ_n[j]` in the
  thick subcategory of `A` with `n < k`, where `Λ_n` is the `n`-cell object. **This statement has
  no published proof and no human review.** "No shift of `A` is a direct summand" alone is too
  weak from `k = 3` on: for `E = Λ₂` and `k = 3` the cone is two copies of `Λ₂`, not of `Λ₃`.
  Mathlib has no twist functors, so no Lean test of `Λ₂` is possible. -/
  iso : cone ≅ ⨁ L

/-! ### HN filtrations within phase bounds -/

private lemma exists_hn_of_gtProp {s : ℝ} {X : C} (hX : σ.slicing.gtProp C s X) :
    ∃ F : HNFiltration C σ.slicing.P X, ∀ i, s < F.φ i := by
  rcases hX with hX | ⟨F, hn, hlt⟩
  · exact ⟨HNFiltration.zero C X hX, fun i ↦ i.elim0⟩
  · exact ⟨F, fun i ↦ hlt.trans_le (F.phase_mem_range C hn i).1⟩

private lemma exists_hn_of_leProp {s : ℝ} {Y : C} (hY : σ.slicing.leProp C s Y) :
    ∃ F : HNFiltration C σ.slicing.P Y, ∀ i, F.φ i ≤ s := by
  rcases hY with hY | ⟨F, hn, hle⟩
  · exact ⟨HNFiltration.zero C Y hY, fun i ↦ i.elim0⟩
  · exact ⟨F, fun i ↦ (F.phase_mem_range C hn i).2.trans hle⟩

private lemma exists_hn_of_geProp {s : ℝ} {X : C} (hX : σ.slicing.geProp C s X) :
    ∃ F : HNFiltration C σ.slicing.P X, ∀ i, s ≤ F.φ i := by
  rcases hX with hX | ⟨F, hn, hle⟩
  · exact ⟨HNFiltration.zero C X hX, fun i ↦ i.elim0⟩
  · exact ⟨F, fun i ↦ hle.trans (F.phase_mem_range C hn i).1⟩

private lemma exists_hn_of_ltProp {s : ℝ} {Y : C} (hY : σ.slicing.ltProp C s Y) :
    ∃ F : HNFiltration C σ.slicing.P Y, ∀ i, F.φ i < s := by
  rcases hY with hY | ⟨F, hn, hlt⟩
  · exact ⟨HNFiltration.zero C Y hY, fun i ↦ i.elim0⟩
  · exact ⟨F, fun i ↦ (F.phase_mem_range C hn i).2.trans_lt hlt⟩

namespace LadderFamily

variable {σ} (T : σ.LadderFamily)

/-- A ladder has mass `k a`. -/
theorem mass_ladder (c : Fin T.N) : σ.mass (T.L c) = T.k * T.a := by
  rw [σ.mass_eq_sum (T.filtration c)]
  simp only [T.norm_charge_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    T.length_eq, nsmul_eq_mul]

/-- A ladder that starts at or below `s` has phases at most `s`. -/
theorem leProp_ladder (c : Fin T.N) {s : ℝ} (hψ : T.ψ c ≤ s) :
    σ.slicing.leProp C s (T.L c) := by
  by_cases hn : 0 < (T.filtration c).n
  · refine σ.slicing.leProp_of_hn C (T.filtration c) s (fun j ↦ ?_) hn
    rw [T.phase_eq]
    linarith [(Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ (j : ℕ))]
  · exact Or.inl ((T.filtration c).isZero_of_length_zero (by omega))

end LadderFamily

variable [IsTriangulated C]

/-! ### The mass of the part above a cut -/

/-- The mass of the first term of a distinguished triangle `X → Q → Y → X⟦1⟧`, read off any HN
filtration of `Q`, when a predicate `p` on phases holds on the HN phases of `X` and fails on
those of `Y`, all of which are lower. -/
private theorem mass_eq_sum_ite_aux (p : ℝ → Prop) [DecidablePred p] {X Q Y : C} {i : X ⟶ Q}
    {π : Q ⟶ Y} {q : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk i π q ∈ distTriang C)
    (FX : HNFiltration C σ.slicing.P X) (FY : HNFiltration C σ.slicing.P Y)
    (hX : ∀ i, p (FX.φ i)) (hY : ∀ j, ¬p (FY.φ j)) (hsep : ∀ i j, FY.φ j < FX.φ i)
    (F : HNFiltration C σ.slicing.P Q) :
    σ.mass X = ∑ j, if p (F.φ j) then ‖σ.charge (F.factor j)‖ else 0 := by
  obtain ⟨FQ, hn, hfirst, hsecond⟩ := HNFiltration.exists_concat FX FY hT hsep
  calc σ.mass X = ∑ i, ‖σ.charge (FX.factor i)‖ := σ.mass_eq_sum FX
    _ = ∑ j, if p (FQ.φ j) then ‖σ.charge (FQ.factor j)‖ else 0 := by
        rw [Fin.sum_eq_add_of_eq hn]
        have hz : ∑ j : Fin FY.n, (if p (FQ.φ ⟨FX.n + j, by omega⟩) then
            ‖σ.charge (FQ.factor ⟨FX.n + j, by omega⟩)‖ else 0) = 0 :=
          Finset.sum_eq_zero fun j _ ↦ by rw [(hsecond j).1, ite_eq_right (hY j)]
        rw [hz, add_zero]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        obtain ⟨hφ, ⟨e⟩⟩ := hfirst j
        rw [hφ, ite_eq_left (hX j)]
        simp only [charge_def, classOf_iso C v e]
    _ = ∑ j, if p (F.φ j) then ‖σ.charge (F.factor j)‖ else 0 :=
        HNFiltration.sum_factor_eq σ.slicing (fun φ X ↦ if p φ then ‖σ.charge X‖ else 0)
          (fun _ _ _ e ↦ by simp only [charge_def, classOf_iso C v e])
          (fun _ _ hX ↦ by simp [charge_isZero σ hX]) FQ F

/-- **The mass above a cut, from any HN filtration.** For a distinguished triangle
`X → Q → Y → X⟦1⟧` with `X` of phases above `s` and `Y` of phases at most `s`, and any HN
filtration of `Q` with factors `A_j` of phases `φ_j`, `m(X) = ∑_{φ_j > s} |Z(A_j)|`. -/
theorem mass_eq_sum_ite_of_gtProp_leProp {s : ℝ} {X Q Y : C} {i : X ⟶ Q} {p : Q ⟶ Y}
    {q : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk i p q ∈ distTriang C)
    (hX : σ.slicing.gtProp C s X) (hY : σ.slicing.leProp C s Y)
    (F : HNFiltration C σ.slicing.P Q) :
    σ.mass X = ∑ j, if s < F.φ j then ‖σ.charge (F.factor j)‖ else 0 := by
  obtain ⟨FX, hFX⟩ := σ.exists_hn_of_gtProp hX
  obtain ⟨FY, hFY⟩ := σ.exists_hn_of_leProp hY
  exact σ.mass_eq_sum_ite_aux (s < ·) hT FX FY hFX (fun j ↦ not_lt.2 (hFY j))
    (fun i j ↦ (hFY j).trans_lt (hFX i)) F

/-- **The mass at or above a cut, from any HN filtration.** For a distinguished triangle
`X → Q → Y → X⟦1⟧` with `X` of phases at least `s` and `Y` of phases below `s`, and any HN
filtration of `Q` with factors `A_j` of phases `φ_j`, `m(X) = ∑_{φ_j ≥ s} |Z(A_j)|`. -/
theorem mass_eq_sum_ite_of_geProp_ltProp {s : ℝ} {X Q Y : C} {i : X ⟶ Q} {p : Q ⟶ Y}
    {q : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk i p q ∈ distTriang C)
    (hX : σ.slicing.geProp C s X) (hY : σ.slicing.ltProp C s Y)
    (F : HNFiltration C σ.slicing.P Q) :
    σ.mass X = ∑ j, if s ≤ F.φ j then ‖σ.charge (F.factor j)‖ else 0 := by
  obtain ⟨FX, hFX⟩ := σ.exists_hn_of_geProp hX
  obtain ⟨FY, hFY⟩ := σ.exists_hn_of_ltProp hY
  exact σ.mass_eq_sum_ite_aux (s ≤ ·) hT FX FY hFX (fun j ↦ not_le.2 (hFY j))
    (fun i j ↦ (hFY j).trans_le (hFX i)) F

/-- **The part above a cut of a finite biproduct.** Let `X → ⨁ S → Y → X⟦1⟧` and
`U i → S i → Y₀ i → (U i)⟦1⟧` be distinguished, with `X` and the `U i` of phases above `s` and
`Y` and the `Y₀ i` of phases at most `s`. Then `m(X) = ∑ i, m(U i)`. -/
theorem mass_eq_sum_mass_of_biproduct {ι : Type*} [Fintype ι] {s : ℝ} {S U Y₀ : ι → C}
    {u : ∀ i, U i ⟶ S i} {π₀ : ∀ i, S i ⟶ Y₀ i} {ε₀ : ∀ i, Y₀ i ⟶ (U i)⟦(1 : ℤ)⟧}
    (h₀ : ∀ i, Triangle.mk (u i) (π₀ i) (ε₀ i) ∈ distTriang C)
    (hU : ∀ i, σ.slicing.gtProp C s (U i)) (hY₀ : ∀ i, σ.slicing.leProp C s (Y₀ i))
    {X Y : C} {x : X ⟶ ⨁ S} {y : ⨁ S ⟶ Y} {z : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk x y z ∈ distTriang C) (hX : σ.slicing.gtProp C s X)
    (hY : σ.slicing.leProp C s Y) : σ.mass X = ∑ i, σ.mass (U i) := by
  obtain ⟨e, -⟩ := σ.slicing.exists_iso_biproduct_of_leProp h₀ hU hY₀ hT hX hY
  have h₁ := σ.mass_eq_add_of_triangle hT hX hY
  have h₂ : ∀ i, σ.mass (S i) = σ.mass (U i) + σ.mass (Y₀ i) := fun i ↦
    σ.mass_eq_add_of_triangle (h₀ i) (hU i) (hY₀ i)
  rw [σ.mass_biproduct, σ.mass_iso e, σ.mass_biproduct] at h₁
  simp only [h₂, Finset.sum_add_distrib] at h₁
  linarith

/-! ### The mass of a sum of ladders -/

namespace LadderFamily

variable {σ} (T : σ.LadderFamily)

/-- **The mass of a sum of ladders**: an object `Q ≅ ⨁_c L_c` has mass `N k a`. -/
theorem mass_eq_of_iso {Q : C} (e : Q ≅ ⨁ T.L) : σ.mass Q = T.N * T.k * T.a := by
  rw [σ.mass_iso e, σ.mass_biproduct]
  simp only [T.mass_ladder, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The cells of a ladder above a cut.** For every truncation `X → L c → Y` of the ladder `c` at
`s` (`X` of phases above `s`, `Y` of phases at most `s`), `m(X) = a · min{k, ⌈ψ c - s⌉₊}`: the
cell `j`, of phase `ψ c - j`, lies above `s` exactly when `j < ψ c - s`. -/
theorem mass_ladder_of_gtProp_leProp (c : Fin T.N) {s : ℝ} {X Y : C} {i : X ⟶ T.L c}
    {p : T.L c ⟶ Y} {q : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk i p q ∈ distTriang C)
    (hX : σ.slicing.gtProp C s X) (hY : σ.slicing.leProp C s Y) :
    σ.mass X = T.a * (min T.k ⌈T.ψ c - s⌉₊ : ℕ) := by
  rw [σ.mass_eq_sum_ite_of_gtProp_leProp hT hX hY (T.filtration c)]
  simp only [T.phase_eq, T.norm_charge_eq]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ if s < T.ψ c - j then T.a else 0),
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, T.length_eq,
    Nat.card_filter_range_lt_sub_eq_min_ceil, mul_comm]

/-- **The cells of a sum of ladders above a cut.** For `Q ≅ ⨁_c L_c` and every truncation
`X → Q → Y` at `s` (`X` of phases above `s`, `Y` of phases at most `s`),
`m(X) = a ∑_c min{k, ⌈ψ c - s⌉₊}`. -/
theorem mass_of_gtProp_leProp {Q : C} (e : Q ≅ ⨁ T.L) {s : ℝ} {X Y : C} {i : X ⟶ Q}
    {p : Q ⟶ Y} {q : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk i p q ∈ distTriang C)
    (hX : σ.slicing.gtProp C s X) (hY : σ.slicing.leProp C s Y) :
    σ.mass X = T.a * (∑ c, min T.k ⌈T.ψ c - s⌉₊ : ℕ) := by
  have hT' : Triangle.mk (i ≫ e.hom) (e.inv ≫ p) q ∈ distTriang C := by
    refine isomorphic_distinguished _ hT _
      (Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_) <;> simp
  choose U Y₀ u π₀ ε₀ h₀ hU hY₀ using fun c ↦ σ.slicing.exists_split_gtProp_leProp s (T.L c)
  rw [σ.mass_eq_sum_mass_of_biproduct h₀ hU hY₀ hT' hX hY, Nat.cast_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ ↦ T.mass_ladder_of_gtProp_leProp c (h₀ c) (hU c) (hY₀ c)

/-- A sum of ladders that all start at or below `s` has phases at most `s`. -/
theorem leProp_of_iso {Q : C} (e : Q ≅ ⨁ T.L) {s : ℝ} (hψ : ∀ c, T.ψ c ≤ s) :
    σ.slicing.leProp C s Q := by
  refine (σ.slicing.leProp C s).prop_of_iso e.symm ?_
  exact σ.slicing.leProp_iff_hom_eq_zero.2 fun X hX g ↦ biproduct.hom_ext _ _ fun c ↦ by
    rw [zero_comp]
    exact σ.slicing.leProp_iff_hom_eq_zero.1 (T.leProp_ladder c (hψ c)) hX _

/-- **The bound for a negative twist power.** Let `L' → F → E → L'⟦1⟧` be distinguished, with
`L' ≅ ⨁_c L_c` a sum of ladders as the first term and `E` of phases at most `s`. Under Ikeda
subadditivity, `0 ≤ m(E) + N k a - m(F) ≤ 2a ∑_c (k - min{k, ⌈ψ c - s⌉₊})`: by the dual cut-loss
lemma, the loss is at most twice the mass of the cells of phase at most `s`. -/
theorem inverse_twist_bound (hσ : σ.MassSubadditive) {L' F E : C} {u : L' ⟶ F} {f : F ⟶ E}
    {h : E ⟶ L'⟦(1 : ℤ)⟧} (hT : Triangle.mk u f h ∈ distTriang C) (e : L' ≅ ⨁ T.L) {s : ℝ}
    (hE : σ.slicing.leProp C s E) :
    0 ≤ σ.mass E + T.N * T.k * T.a - σ.mass F ∧
      σ.mass E + T.N * T.k * T.a - σ.mass F ≤
        2 * T.a * (∑ c, (T.k - min T.k ⌈T.ψ c - s⌉₊) : ℕ) := by
  have hL := T.mass_eq_of_iso e
  obtain ⟨X, Y, i, p, q, hTX, hX, hY⟩ := σ.slicing.exists_split_gtProp_leProp s L'
  have hXm := T.mass_of_gtProp_leProp e hTX hX hY
  have hsplit := σ.mass_eq_add_of_triangle hTX hX hY
  have hlow := σ.mass_add_mass_sub_two_mul_le_dual hσ hT hE hTX
    (σ.slicing.geProp_of_gtProp C _ hX) hY
  have hup := σ.mass_le_mass_add_mass hσ hT
  have hcount : ((∑ c, (T.k - min T.k ⌈T.ψ c - s⌉₊) : ℕ) : ℝ) =
      T.N * T.k - (∑ c, min T.k ⌈T.ψ c - s⌉₊ : ℕ) := by
    rw [Nat.cast_sum, Nat.cast_sum]
    simp only [Nat.cast_sub (min_le_left _ _), Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hcount]
  constructor <;> nlinarith

end LadderFamily

/-! ### The mass of a twist power -/

namespace TwistLadderHypotheses

variable {σ} {E F : C} {f : E ⟶ F} (T : σ.TwistLadderHypotheses f)

/-- **The mass of the cone**: `m(cone) = N k a`. -/
theorem mass_cone : σ.mass T.cone = T.N * T.k * T.a :=
  T.mass_eq_of_iso T.iso

/-- **The part of the cone above a cut.** For every `s`, the `(> s, ≤ s)` truncation of the cone
has first term of mass `a ∑_c min{k, ⌈ψ c - s⌉₊}`. -/
theorem exists_split_cone (s : ℝ) :
    ∃ (X Y : C) (i : X ⟶ T.cone) (p : T.cone ⟶ Y) (q : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk i p q ∈ distTriang C ∧ σ.slicing.gtProp C s X ∧ σ.slicing.leProp C s Y ∧
        σ.mass X = T.a * (∑ c, min T.k ⌈T.ψ c - s⌉₊ : ℕ) := by
  obtain ⟨X, Y, i, p, q, hT, hX, hY⟩ := σ.slicing.exists_split_gtProp_leProp s T.cone
  exact ⟨X, Y, i, p, q, hT, hX, hY, T.mass_of_gtProp_leProp T.iso hT hX hY⟩

/-- **The twist bound**, the mass of a positive twist power. Under Ikeda subadditivity
(`MassSubadditive`), if `E` has phases at least `s`, then
`0 ≤ m(E) + N k a - m(F) ≤ 2a ∑_c min{k, ⌈ψ c - s⌉₊}`. With `s = φ⁻(E)` and `ψ c = φ + 1 - p_c`,
the right side is `2a ∑_p h^p min{k, ⌈φ + 1 - p - s⌉₊}`. The constant `2` cannot be improved in
general: the one-cell ladder `E → 0 → E⟦1⟧` of a semistable `E` attains the bound
(`K3TwistsTest/TwistLadderModel.lean`). -/
theorem twist_bound (hσ : σ.MassSubadditive) {s : ℝ} (hE : σ.slicing.geProp C s E) :
    0 ≤ σ.mass E + T.N * T.k * T.a - σ.mass F ∧
      σ.mass E + T.N * T.k * T.a - σ.mass F ≤
        2 * T.a * (∑ c, min T.k ⌈T.ψ c - s⌉₊ : ℕ) := by
  obtain ⟨X, Y, i, p, q, hTX, hX, hY, hXm⟩ := T.exists_split_cone s
  have hup := σ.mass_le_mass_add_mass hσ T.dist
  have hlow := σ.mass_add_mass_sub_two_mul_le hσ T.dist hE hTX
    (σ.slicing.geProp_of_gtProp C _ hX) hY
  rw [T.mass_cone] at hup hlow
  rw [hXm] at hlow
  constructor <;> linarith

/-- **The twist bound uniformly in the power.** The loss is at most `2a ∑_c ⌈ψ c - s⌉₊`, which
does not depend on `k`. So if the spread `ψ c - s` between the phases of the centre and the lowest
phase of `E` stays bounded along a family of stability conditions, then
`m(T_A^k E) = m(E) + k a h_A(E) + O_E(a)` uniformly in `k`. -/
theorem twist_bound_uniform (hσ : σ.MassSubadditive) {s : ℝ} (hE : σ.slicing.geProp C s E) :
    0 ≤ σ.mass E + T.N * T.k * T.a - σ.mass F ∧
      σ.mass E + T.N * T.k * T.a - σ.mass F ≤ 2 * T.a * (∑ c, ⌈T.ψ c - s⌉₊ : ℕ) := by
  obtain ⟨h0, h1⟩ := T.twist_bound hσ hE
  refine ⟨h0, h1.trans ?_⟩
  have hsum : (∑ c, min T.k ⌈T.ψ c - s⌉₊ : ℕ) ≤ ∑ c, ⌈T.ψ c - s⌉₊ :=
    Finset.sum_le_sum fun c _ ↦ min_le_right _ _
  have hcast : ((∑ c, min T.k ⌈T.ψ c - s⌉₊ : ℕ) : ℝ) ≤ ((∑ c, ⌈T.ψ c - s⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast hsum
  exact mul_le_mul_of_nonneg_left hcast (by have := T.a_nonneg; positivity)

/-- **Zero loss.** If `E` has phases at least `s` and no ladder starts above `s` (`ψ c ≤ s`), then
`m(F) = m(E) + N k a` exactly. No subadditivity is needed: the cone has phases at most `s`, and
equal-phase additivity applies. -/
theorem zero_loss {s : ℝ} (hE : σ.slicing.geProp C s E) (hψ : ∀ c, T.ψ c ≤ s) :
    σ.mass F = σ.mass E + T.N * T.k * T.a := by
  rw [σ.mass_eq_add_of_geProp_leProp T.dist hE (T.leProp_of_iso T.iso hψ), T.mass_cone]

open AlgebraicGeometry.K3 in
/-- **The opening example is the zero-loss case.** At the base point `z = (1 + 4i)/3` of the
opening example (`d = 1`), the point `𝒪_x` has phase `1` and the cells `𝒪_X[1 - j]` of the ladder
of `Tⁿ𝒪_x` have mass `|Z(𝒪_X)| = 10/9` and phases below `1`. For a twist ladder with `N = 1`,
`k = n`, `a = |Z(𝒪_X[1])|` and `m(E) = |Z(𝒪_x)|`, zero loss gives `m(F) = 1 + 10n/9`, the value
`AlgebraicGeometry.K3.PicardRankOne.opening_mass_Tpow`. -/
theorem mass_eq_opening {n : ℕ} (hN : T.N = 1) (hk : T.k = n)
    (ha : T.a = ‖PicardRankOne.charge 1 PicardRankOne.ζ PicardRankOne.classS‖)
    (hEm : σ.mass E = ‖PicardRankOne.charge 1 PicardRankOne.ζ MukaiVector.point‖) {s : ℝ}
    (hE : σ.slicing.geProp C s E) (hψ : ∀ c, T.ψ c ≤ s) : σ.mass F = 1 + 10 * n / 9 := by
  rw [T.zero_loss hE hψ, hN, hk, ha, hEm, Nat.cast_one, one_mul]
  exact PicardRankOne.opening_mass_Tpow n

end TwistLadderHypotheses

end PreStabilityCondition.WithClassMap

end CategoryTheory.Triangulated
