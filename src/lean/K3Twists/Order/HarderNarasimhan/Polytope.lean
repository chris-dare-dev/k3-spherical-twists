/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Order.HarderNarasimhan
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull

/-!
# The Harder–Narasimhan polytope

Let `c` be a charge function on a bounded lattice `L`. Its *charge points* are the points
`(rk x, deg x)` of `K × K`, `x : L` (`ChargeFunction.points`). The HN filtration reads the upper
boundary of their convex hull, as in the HN polytopes of Baumann, Kamnitzer and Tingley
(arXiv:1110.3661, §3.2), now with a vertical edge when there is torsion:

* `ChargeFunction.HNChain.weight_le_edge`: every charge point lies on or below the line through
  each edge of finite phase `μ`, the line of slope `μ` through the points of the prefixes at its
  ends (`HNChain.weight_factorPhase_succ`);
* `ChargeFunction.rk_bot_le_of_mem_convexHull`: the hull lies to the right of the vertical line
  `p.1 = rk ⊥`; a vertical edge is the first one and lies on that line
  (`HNChain.val_eq_zero_of_factorPhase_eq_top`, `HNChain.rk_chain_succ_eq_of_factorPhase_eq_top`);
* `ChargeFunction.HNChain.convexHull_subset`: the hull lies in the intersection of these
  half-planes;
* `ChargeFunction.HNChain.exists_exposed_succ`: the point of every nonzero prefix is exposed: it
  is the only point of the hull where some linear function `p.2 - θ p.1` is maximal;
* `ChargeFunction.lex_le_of_mem_convexHull`: the point of `⊥` is the lexicographic minimum of the
  hull. When the first edge is vertical no function `p.2 - θ p.1` exposes it
  (`ChargeFunction.HNChain.mem_range_chain_iff`): it is the lower end of the vertical edge.

For a slope function, `SlopeFunction.HNFiltration.convexHull_subset` and
`SlopeFunction.HNFiltration.weight_ge_edge_of_neg` give the upper and lower boundaries.
-/

namespace Order

section Convex

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The lexicographic upper set `{p | (a, b) ≤ p}` of `K × K` is convex. -/
theorem convex_setOf_lex_le (a b : K) :
    Convex K {p : K × K | a ≤ p.1 ∧ (p.1 = a → b ≤ p.2)} := by
  intro x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ t u ht hu htu
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  have e₁ : t * x.1 + u * y.1 - a = t * (x.1 - a) + u * (y.1 - a) := by
    linear_combination a * htu
  have p₁ : 0 ≤ t * (x.1 - a) := mul_nonneg ht (by linarith)
  have p₂ : 0 ≤ u * (y.1 - a) := mul_nonneg hu (by linarith)
  refine ⟨by linarith, fun h ↦ ?_⟩
  have z₁ : t * (x.1 - a) = 0 := by linarith
  have z₂ : u * (y.1 - a) = 0 := by linarith
  have q₁ : 0 ≤ t * (x.2 - b) := by
    rcases mul_eq_zero.mp z₁ with h0 | h0
    · rw [h0, zero_mul]
    · exact mul_nonneg ht (by linarith [hx₂ (by linarith)])
  have q₂ : 0 ≤ u * (y.2 - b) := by
    rcases mul_eq_zero.mp z₂ with h0 | h0
    · rw [h0, zero_mul]
    · exact mul_nonneg hu (by linarith [hy₂ (by linarith)])
  have e₂ : t * x.2 + u * y.2 - b = t * (x.2 - b) + u * (y.2 - b) := by
    linear_combination b * htu
  linarith

/-- The open half-plane below a line, together with one point on the line, is convex. -/
theorem convex_setOf_lt_union_singleton (θ w : K) {q : K × K} (hq : q.2 - θ * q.1 = w) :
    Convex K ({p : K × K | p.2 - θ * p.1 < w} ∪ {q}) := by
  have hl : ∀ (x y : K × K) (t u : K), t + u = 1 →
      (t • x + u • y).2 - θ * (t • x + u • y).1 - w =
        t * (x.2 - θ * x.1 - w) + u * (y.2 - θ * y.1 - w) := fun x y t u htu ↦ by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination w * htu
  intro x hx y hy t u ht hu htu
  have hx' : x.2 - θ * x.1 - w ≤ 0 := by
    rcases hx with hx | rfl
    · exact (sub_neg.mpr hx).le
    · rw [hq, sub_self]
  have hy' : y.2 - θ * y.1 - w ≤ 0 := by
    rcases hy with hy | rfl
    · exact (sub_neg.mpr hy).le
    · rw [hq, sub_self]
  by_cases hxq : x = q
  · by_cases hyq : y = q
    · right
      rw [hxq, hyq, ← add_smul, htu, one_smul, Set.mem_singleton_iff]
    · have hy'' : y.2 - θ * y.1 - w < 0 := by
        rcases hy with hy | hy
        · exact sub_neg.mpr hy
        · exact absurd hy hyq
      rcases hu.lt_or_eq with hu' | hu'
      · left
        have := hl x y t u htu
        have := mul_neg_of_pos_of_neg hu' hy''
        have := mul_nonpos_of_nonneg_of_nonpos ht hx'
        show _ < w
        linarith
      · right
        rw [← hu', zero_smul, add_zero, show t = 1 by linarith, one_smul, hxq]
        rfl
  · have hx'' : x.2 - θ * x.1 - w < 0 := by
      rcases hx with hx | hx
      · exact sub_neg.mpr hx
      · exact absurd hx hxq
    rcases ht.lt_or_eq with ht' | ht'
    · left
      have := hl x y t u htu
      have := mul_neg_of_pos_of_neg ht' hx''
      have := mul_nonpos_of_nonneg_of_nonpos hu hy'
      show _ < w
      linarith
    · rw [← ht', zero_smul, zero_add, show u = 1 by linarith, one_smul]
      exact hy

end Convex

namespace ChargeFunction

variable {L K : Type*} [Lattice L] [BoundedOrder L] [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] (c : ChargeFunction L K)

/-- The charge points `(rk x, deg x)`, `x : L`. -/
def points : Set (K × K) := Set.range fun x ↦ (c.rk x, c.deg x)

/-- **The hull lies to the right of the vertical line through `⊥`.** -/
theorem rk_bot_le_of_mem_convexHull {p : K × K} (hp : p ∈ convexHull K c.points) :
    c.rk ⊥ ≤ p.1 := by
  refine convexHull_min ?_ (convex_halfSpace_ge ?_ (c.rk ⊥)) hp
  · rintro _ ⟨x, rfl⟩
    exact c.rk_mono bot_le
  · exact ⟨fun p q ↦ rfl, fun a p ↦ rfl⟩

/-- **The point of `⊥` is the lexicographic minimum of the hull.** -/
theorem lex_le_of_mem_convexHull {p : K × K} (hp : p ∈ convexHull K c.points) :
    c.rk ⊥ ≤ p.1 ∧ (p.1 = c.rk ⊥ → c.deg ⊥ ≤ p.2) := by
  refine convexHull_min ?_ (convex_setOf_lex_le (c.rk ⊥) (c.deg ⊥)) hp
  rintro _ ⟨x, rfl⟩
  exact ⟨c.rk_mono bot_le, fun h ↦ c.deg_le_of_le_of_rk_eq bot_le h.symm⟩

namespace HNChain

variable {c} (F : c.HNFiltration)

/-- The weight of a finite factor phase takes the same value at both ends of the factor. -/
theorem weight_factorPhase_succ (i : Fin F.n) {μ : K} (hμ : F.factorPhase i = μ) :
    c.weight μ (F.chain i.succ) = c.weight μ (F.chain i.castSucc) := by
  have hlt := F.strictMono i.castSucc_lt_succ
  have h₁ := (c.coe_le_phase_iff hlt μ).mp hμ.ge
  have h₂ := (c.phase_le_coe_iff hlt μ).mp hμ.le
  simp only [weight]
  linarith

/-- **The edges of finite phase support the points from above.** For a factor of finite phase
`μ`, `w_μ x ≤ w_μ (chain i)`: the point `(rk x, deg x)` lies on or below the line through the
`i`th edge. -/
theorem weight_le_edge (i : Fin F.n) {μ : K} (hμ : F.factorPhase i = μ) (x : L) :
    c.weight μ x ≤ c.weight μ (F.chain i.castSucc) := by
  refine F.weight_le i.castSucc (fun j hj ↦ hμ ▸ F.phase_strictAnti.antitone ?_)
    (fun j hj ↦ hμ ▸ F.phase_strictAnti.antitone ?_) x
  · rw [Fin.le_def] at hj ⊢
    simp only [Fin.val_succ, Fin.val_castSucc] at hj
    omega
  · rwa [Fin.castSucc_le_castSucc_iff] at hj

omit [IsStrictOrderedRing K] in
/-- Only the first factor can be vertical. -/
theorem val_eq_zero_of_factorPhase_eq_top {i : Fin F.n} (h : F.factorPhase i = ⊤) :
    (i : ℕ) = 0 := by
  by_contra hi
  have hlt : F.factorPhase i < F.factorPhase ⟨0, by omega⟩ :=
    F.phase_strictAnti (Fin.mk_lt_mk.mpr (Nat.pos_of_ne_zero hi))
  rw [h] at hlt
  exact not_top_lt hlt

omit [IsStrictOrderedRing K] in
/-- A vertical edge lies on the vertical line `p.1 = rk ⊥`. -/
theorem rk_chain_succ_eq_of_factorPhase_eq_top {i : Fin F.n} (h : F.factorPhase i = ⊤) :
    c.rk (F.chain i.castSucc) = c.rk ⊥ ∧ c.rk (F.chain i.succ) = c.rk ⊥ := by
  have hi : i.castSucc = 0 := Fin.ext (F.val_eq_zero_of_factorPhase_eq_top h)
  have hr := (c.phase_eq_top_iff).mp h
  rw [hi, F.chain_zero] at hr ⊢
  exact ⟨rfl, hr.symm⟩

/-- **The HN filtration reads the upper boundary of the convex hull** of the charge points: the
hull lies to the right of the vertical line through `⊥` and below the line through every edge
of finite phase. -/
theorem convexHull_subset :
    convexHull K c.points ⊆ {p | c.rk ⊥ ≤ p.1} ∩
      ⋂ (i : Fin F.n) (μ : K) (_ : F.factorPhase i = μ),
        {p : K × K | p.2 - μ * p.1 ≤ c.weight μ (F.chain i.castSucc)} := by
  refine convexHull_min ?_ ((convex_halfSpace_ge ⟨fun p q ↦ rfl, fun a p ↦ rfl⟩ _).inter
    (convex_iInter fun i ↦ convex_iInter fun μ ↦ convex_iInter fun _ ↦
      convex_halfSpace_le ⟨fun p q ↦ ?_, fun a p ↦ ?_⟩ _))
  · rintro _ ⟨x, rfl⟩
    refine ⟨c.rk_mono bot_le, ?_⟩
    simp only [Set.mem_iInter]
    exact fun i μ hμ ↦ F.weight_le_edge i hμ x
  · simp only [Prod.fst_add, Prod.snd_add]
    ring
  · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- **Nonzero prefixes are exposed points of the hull.** For every nonzero prefix there is a
`θ` such that the point of the prefix is the only point of the hull where `p.2 - θ p.1` is
maximal. -/
theorem exists_exposed_succ (j : Fin F.n) : ∃ θ : K, ∀ p ∈ convexHull K c.points,
    p.2 - θ * p.1 ≤ c.weight θ (F.chain j.succ) ∧
      (p.2 - θ * p.1 = c.weight θ (F.chain j.succ) →
        p = (c.rk (F.chain j.succ), c.deg (F.chain j.succ))) := by
  rcases (F.mem_range_chain_iff (F.chain j.succ)).mp ⟨j.succ, rfl⟩ with h | ⟨θ, hθ⟩
  · have := F.strictMono (Fin.succ_pos j)
    rw [F.chain_zero, h] at this
    exact absurd this (lt_irrefl _)
  refine ⟨θ, fun p hp ↦ ?_⟩
  have hsub : convexHull K c.points ⊆
      {p : K × K | p.2 - θ * p.1 < c.weight θ (F.chain j.succ)} ∪
        {(c.rk (F.chain j.succ), c.deg (F.chain j.succ))} := by
    refine convexHull_min ?_ (convex_setOf_lt_union_singleton θ _ rfl)
    rintro _ ⟨y, rfl⟩
    rcases ((hθ y).1).lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr (by rw [(hθ y).2 heq]; rfl)
  rcases hsub hp with hlt | rfl
  · exact ⟨hlt.le, fun h ↦ absurd h hlt.ne⟩
  · exact ⟨le_rfl, fun _ ↦ rfl⟩

end HNChain

end ChargeFunction

namespace SlopeFunction.HNFiltration

variable {L K : Type*} [Lattice L] [BoundedOrder L] [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] {s : SlopeFunction L K} (F : s.HNFiltration)

/-- **The edges of the HN polygon support the points from above.** For the slope `μᵢ` of the
`i`th factor, `w_{μᵢ} x ≤ w_{μᵢ} (chain i) = w_{μᵢ} (chain (i + 1))`: the point
`(rk x, deg x)` lies on or below the line through the `i`th edge. -/
theorem weight_le_edge (i : Fin F.n) (x : L) :
    s.weight (F.factorSlope i) x ≤ s.weight (F.factorSlope i) (F.chain i.castSucc) :=
  F.toCharge.weight_le_edge i (F.toCharge_factorPhase i) x

/-- **The HN filtration reads the upper boundary of the convex hull** of the points
`(rk x, deg x)`: the hull lies below every edge line of the polygon through the points
`(rk (chain k), deg (chain k))`, which are among the points. -/
theorem convexHull_subset :
    convexHull K (Set.range fun x : L ↦ (s.rk x, s.deg x)) ⊆
      ⋂ i : Fin F.n, {p : K × K | p.2 - F.factorSlope i * p.1 ≤
        s.weight (F.factorSlope i) (F.chain i.castSucc)} := by
  refine convexHull_min ?_ (convex_iInter fun i ↦ convex_halfSpace_le ?_ _)
  · rintro _ ⟨x, rfl⟩
    exact Set.mem_iInter.mpr fun i ↦ F.weight_le_edge i x
  · exact ⟨fun p q ↦ by simp only [Prod.fst_add, Prod.snd_add]; ring,
      fun a p ↦ by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩

/-- **The opposite HN filtration reads the lower boundary.** For an HN filtration of `s.neg`
with factor slopes `μ'ᵢ`, every point `(rk x, deg x)` lies on or above the line of slope `-μ'ᵢ`
through its `i`th edge. -/
theorem weight_ge_edge_of_neg (F : s.neg.HNFiltration) (i : Fin F.n) (x : L) :
    s.weight (-F.factorSlope i) (F.chain i.castSucc) ≤ s.weight (-F.factorSlope i) x := by
  have := F.weight_le_edge i x
  rw [neg_weight, neg_weight] at this
  linarith

end SlopeFunction.HNFiltration

end Order
