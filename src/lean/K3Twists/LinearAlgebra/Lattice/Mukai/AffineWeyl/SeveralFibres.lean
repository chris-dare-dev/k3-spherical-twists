/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.Group
import K3Twists.LinearAlgebra.Matrix.ZMatrix.OneSummand

/-!
# Several exceptional fibres

A contraction of `(-2)`-curves can have several singular points, one connected exceptional fibre
`F a` (`Mukai.FundamentalCycle`) over each, with the curves of different fibres orthogonal. The
fibre lattices are even and negative definite, so **a `(-2)`-class supported on several fibres
lies on one of them** (`FundamentalCycle.exists_forall_ne_eq_zero_of_root`), by the one-summand
lemma `LinearMap.BilinForm.exists_forall_ne_eq_zero`. So the fundamental-alcove theorem extends
fibre by fibre:

* if `β` lies in the fundamental alcove of every fibre, `Z = β·c - s ≠ 0` on every rank-zero root
  `(0, c, s)` with `c` in the sum of the fibre lattices (`fibreCharge_ne_zero_of_sum`);
* with the Riemann–Roch membership field for several fibres, stated as the hypothesis that every
  `(-2)`-class orthogonal to `H` lies in the sum of the fibre lattices, `Z ≠ 0` on every rank-zero
  root orthogonal to `H` (`fibreCharge_ne_zero_of_mem_sum`).
-/

namespace Mukai.FundamentalCycle

variable {N : Type*} [AddCommGroup N] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ} {A : Type*} [Fintype A]
  {ι : A → Type*} [∀ a, Fintype (ι a)]

omit [Fintype A] in
/-- Classes on orthogonal fibres are orthogonal. -/
theorem apply_eq_zero_of_mem_rootLattice (F : ∀ a, FundamentalCycle b (ι a)) {a a' : A}
    (horth : ∀ i j, b ((F a).curve i) ((F a').curve j) = 0) {c c' : N}
    (hc : c ∈ (F a).rootLattice) (hc' : c' ∈ (F a').rootLattice) : b c c' = 0 := by
  obtain ⟨d, rfl⟩ := hc
  obtain ⟨d', rfl⟩ := hc'
  simp [combination_apply, map_sum, LinearMap.sum_apply, horth]

/-- **A `(-2)`-class supported on mutually orthogonal fibres lies on one of them.** -/
theorem exists_forall_ne_eq_zero_of_root (hb : ∀ x y, b x y = b y x)
    (F : ∀ a, FundamentalCycle b (ι a))
    (horth : ∀ a a', a ≠ a' → ∀ i j, b ((F a).curve i) ((F a').curve j) = 0) {c : A → N}
    (hc : ∀ a, c a ∈ (F a).rootLattice) (hroot : b (∑ a, c a) (∑ a, c a) = -2) :
    ∃ a, ∀ a', a' ≠ a → c a' = 0 := by
  refine LinearMap.BilinForm.exists_forall_ne_eq_zero b
    (fun a a' h => apply_eq_zero_of_mem_rootLattice F (horth a a' h) (hc a) (hc a'))
    (fun a ha => ?_) hroot
  obtain ⟨d, hd⟩ := hc a
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact ha (by rw [← hd, map_zero])
  have hlt := (F a).negDef d hd0
  obtain ⟨m, hm⟩ := (F a).even_self_of_mem_rootLattice hb (hc a)
  rw [← combination_apply, hd] at hlt
  omega

/-- **The fundamental-alcove theorem for several fibres.** If `β` lies in the fundamental alcove of
every fibre, then `Z = β·c - s ≠ 0` on every rank-zero root `(0, c, s)` with `c` in the sum of the
fibre lattices. -/
theorem fibreCharge_ne_zero_of_sum (hb : ∀ x y, b x y = b y x)
    (F : ∀ a, FundamentalCycle b (ι a))
    (horth : ∀ a a', a ≠ a' → ∀ i j, b ((F a).curve i) ((F a').curve j) = 0) {β : N →+ ℝ}
    (hβ : ∀ a, (F a).IsInFundamentalAlcove β) {c : A → N} (hc : ∀ a, c a ∈ (F a).rootLattice)
    (hroot : b (∑ a, c a) (∑ a, c a) = -2) (s : ℤ) :
    fibreCharge β ((0, ∑ a, c a, s) : MukaiLattice ℤ N) ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_forall_ne_eq_zero_of_root hb F horth hc hroot
  have hsum : ∑ a, c a = c a :=
    Finset.sum_eq_single a (fun a' _ h => ha a' h) (by simp)
  rw [hsum] at hroot ⊢
  exact (F a).fibreCharge_ne_zero hb (hβ a) ⟨rfl, hc a, hroot⟩

/-- **The fundamental-alcove theorem with the Riemann–Roch membership field for several
fibres**: if every `(-2)`-class orthogonal to `H` lies in the sum of the fibre lattices and `β`
lies in the fundamental alcove of every fibre, then `Z ≠ 0` on every rank-zero root orthogonal to
`H`. -/
theorem fibreCharge_ne_zero_of_mem_sum (hb : ∀ x y, b x y = b y x)
    (F : ∀ a, FundamentalCycle b (ι a))
    (horth : ∀ a a', a ≠ a' → ∀ i j, b ((F a).curve i) ((F a').curve j) = 0) {H : N}
    (hRR : ∀ c : N, b c H = 0 → b c c = -2 →
      ∃ c' : A → N, (∀ a, c' a ∈ (F a).rootLattice) ∧ c = ∑ a, c' a)
    {β : N →+ ℝ} (hβ : ∀ a, (F a).IsInFundamentalAlcove β) {c : N} (hcH : b c H = 0)
    (hc : b c c = -2) (s : ℤ) : fibreCharge β ((0, c, s) : MukaiLattice ℤ N) ≠ 0 := by
  obtain ⟨c', hc', rfl⟩ := hRR c hcH hc
  exact fibreCharge_ne_zero_of_sum hb F horth hβ hc' hc s

end Mukai.FundamentalCycle
