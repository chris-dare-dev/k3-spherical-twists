/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The squeeze: exactness of dominated counts along a tight orbit

Let `α` be a partially ordered set with a *modulus* `N : α → α` and a *sign map* `φ : α → α`
such that `x ≤ N(φ x)`. Think of `α` as count vectors, `φ` as attaching signs to a count vector
and `N` as taking entrywise absolute values. Along a sequence of letters, counts `c_n` are
dominated by count maps `P_n`, `c_{n+1} ≤ P_n(c_n)`, signed classes `v_n` move by signed maps
`E_n`, `v_{n+1} = E_n(v_n)`, and are bounded by the counts, `N(v_n) ≤ c_n`. If the seed is tight,
`v_0 = φ(c_0)`, and `E_n(φ(c_n)) = φ(P_n(c_n))` along the orbit, then every domination
inequality is an equality and every `v_n` is tight (`Order.squeeze_orbit`).

The proof is an induction on the length of the word in which nothing about `P_n` is used: no
linearity, monotonicity or nonnegativity, and no axiom at all.

## The intertwining hypothesis

`Order.squeeze` asks for `E_n ∘ φ = φ ∘ P_n` on all of `α`. That form is too strong for
nonlinear count maps: if `φ` and `E_n` are additive and `φ` is injective, it forces `P_n` to be
additive (`Order.map_add_of_intertwine`). In the setting of spherical twists the signed action
on classes is linear, so the all-`x` form only covers additive count maps. The orbit form
`Order.squeeze_orbit` asks for the intertwining only at the points `c_n` of the orbit, which is
all the proof uses; whether a nonadditive count map of interest satisfies it is not decided
here.

## Main results

* `Order.squeeze_step`, `Order.squeeze_orbit`, `Order.squeeze`: exactness and tightness along
  the orbit;
* `Order.squeeze_flag`: the flag form, for an additive count map on an ordered cancellative
  monoid: if the count of an object is bounded by the sum of the counts of the pieces of a flag,
  each piece dominated, and the signed class is tight, every inequality is an equality;
* `Order.map_add_of_intertwine`: the all-`x` intertwining forces additivity.
-/

namespace Order

section Squeeze

variable {α : Type*} [PartialOrder α]

/-- **One step of the squeeze.** If `x ≤ N(φ x)`, `c' ≤ P c`, `v' = E v`, `N v' ≤ c'`,
`v = φ c` and `E (φ c) = φ (P c)`, then `c' = P c` and `v' = φ c'`. -/
theorem squeeze_step (N φ P E : α → α) {c c' v v' : α}
    (hφ : ∀ x, x ≤ N (φ x)) (hE : E (φ c) = φ (P c))
    (hdom : c' ≤ P c) (hv : v' = E v) (hvc : N v' ≤ c') (htight : v = φ c) :
    c' = P c ∧ v' = φ c' := by
  have h1 : v' = φ (P c) := by rw [hv, htight, hE]
  have h2 : c' = P c := le_antisymm hdom ((hφ (P c)).trans (by rw [← h1]; exact hvc))
  exact ⟨h2, by rw [h1, h2]⟩

/-- **The squeeze along one orbit.** With `x ≤ N(φ x)`, counts `c_{n+1} ≤ P_n(c_n)`, signed
classes `v_{n+1} = E_n(v_n)` with `N(v_n) ≤ c_n`, a tight seed `v_0 = φ(c_0)`, and the
intertwining `E_n(φ(c_n)) = φ(P_n(c_n))` along the orbit only: every `v_n` is tight and every
domination is an equality. -/
theorem squeeze_orbit (N φ : α → α) (P E : ℕ → α → α) (c v : ℕ → α)
    (hφ : ∀ x, x ≤ N (φ x)) (hE : ∀ n, E n (φ (c n)) = φ (P n (c n)))
    (hdom : ∀ n, c (n + 1) ≤ P n (c n)) (hv : ∀ n, v (n + 1) = E n (v n))
    (hvc : ∀ n, N (v n) ≤ c n) (h0 : v 0 = φ (c 0)) :
    ∀ n, v n = φ (c n) ∧ c (n + 1) = P n (c n) := by
  have key : ∀ n, v n = φ (c n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      exact (squeeze_step N φ (P n) (E n) hφ (hE n) (hdom n) (hv n) (hvc (n + 1)) ih).2
  exact fun n => ⟨key n,
    (squeeze_step N φ (P n) (E n) hφ (hE n) (hdom n) (hv n) (hvc (n + 1)) (key n)).1⟩

/-- **The squeeze**, with the intertwining `E_n ∘ φ = φ ∘ P_n` on all of `α`. When `φ` and `E_n`
are additive and `φ` is injective, this hypothesis forces `P_n` to be additive
(`map_add_of_intertwine`); `squeeze_orbit` needs it only along the orbit. -/
theorem squeeze (N φ : α → α) (P E : ℕ → α → α) (c v : ℕ → α)
    (hφ : ∀ x, x ≤ N (φ x)) (hE : ∀ n x, E n (φ x) = φ (P n x))
    (hdom : ∀ n, c (n + 1) ≤ P n (c n)) (hv : ∀ n, v (n + 1) = E n (v n))
    (hvc : ∀ n, N (v n) ≤ c n) (h0 : v 0 = φ (c 0)) :
    ∀ n, v n = φ (c n) ∧ c (n + 1) = P n (c n) :=
  squeeze_orbit N φ P E c v hφ (fun n => hE n (c n)) hdom hv hvc h0

end Squeeze

/-- **The flag form of the squeeze.** In an ordered cancellative commutative monoid, let `M` be an
additive count map, `cP` the count of an object with a flag whose pieces have counts `cE a`
(`∑ cE a = cP`), and `cWP`, `cWE a` the counts after a word, with `cWP ≤ ∑ cWE a` and
`cWE a ≤ M(cE a)`. If the signed class after the word is `φ(M cP)` and bounded by `cWP`, then
`cWP = M cP` and `cWE a = M(cE a)` for every piece. Monotonicity of `M` is not used. -/
theorem squeeze_flag {β ι : Type*} [AddCommMonoid β] [PartialOrder β]
    [IsOrderedCancelAddMonoid β]
    (N φ : β → β) (M : β →+ β) (s : Finset ι) (cE cWE : ι → β) (cP cWP vWP : β)
    (hφ : ∀ x, x ≤ N (φ x)) (hv : vWP = φ (M cP)) (hvc : N vWP ≤ cWP)
    (hsub : cWP ≤ ∑ a ∈ s, cWE a) (hdom : ∀ a ∈ s, cWE a ≤ M (cE a))
    (hsum : ∑ a ∈ s, cE a = cP) :
    cWP = M cP ∧ ∀ a ∈ s, cWE a = M (cE a) := by
  have hup : ∑ a ∈ s, cWE a ≤ M cP := by
    rw [← hsum, map_sum]; exact Finset.sum_le_sum hdom
  have hlow : M cP ≤ cWP := (hφ _).trans (by rw [← hv]; exact hvc)
  refine ⟨le_antisymm (hsub.trans hup) hlow, ?_⟩
  have heq : ∑ a ∈ s, cWE a = ∑ a ∈ s, M (cE a) := by
    rw [← map_sum, hsum]; exact le_antisymm hup (hlow.trans hsub)
  exact (Finset.sum_eq_sum_iff_of_le hdom).1 heq

/-- **The all-`x` intertwining forces additivity.** If `φ` and `E` are additive, `φ` is
injective and `E (φ x) = φ (P x)` for every `x`, then `P` is additive. -/
theorem map_add_of_intertwine {β : Type*} [AddCommGroup β] (φ E : β →+ β) (P : β → β)
    (hφ : Function.Injective φ) (hE : ∀ x, E (φ x) = φ (P x)) (x y : β) :
    P (x + y) = P x + P y := by
  apply hφ
  rw [map_add, ← hE, ← hE, ← hE, map_add, map_add]

end Order
