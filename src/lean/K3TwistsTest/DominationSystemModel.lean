/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.EulerTwistSystem

/-!
# A domination system on count vectors

`DominationSystem` asks for tests closed under pulling back along the letters and for the
one-letter bound on centres. This file builds a model in which the recursion is exact: the
objects are count vectors `n : ι → ℕ`, a letter `a` acts by its transvection
`n ↦ n + e_{c(a)} ∑_j G_a(j) n_j`, the centres are the unit vectors, and the tests are the
linear functionals `φ(n) = ∑_k φ_k n_k` with `φ ≥ 0`, pulled back by the transposed transvection.
The bound on centres holds with equality (`countModel_centre_eq`), so the model shows that the
axioms are consistent and that the constant one of the domination recursion cannot be lowered.
On the pair of pairing `3` the word `T₀ T₁` sends `S₀` to `(10, 3)`, which is the count vector the
recursion predicts.

The real-object instances of the library are the Euler-count system on a K3 surface of Picard
rank one (`AlgebraicGeometry.K3.PicardRankOne.eulerTwistSystem`, through
`HomTwistSystem.toDomination`) and the mass system
(`MassComparisonHypotheses.IsTwistSystem.toDomination`).

Built by `lake test`.
-/

namespace K3TwistsTest.DominationSystemModel

open AlgebraicGeometry.K3.PicardRankOne

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

/-- The transvection of a letter on count vectors: `n ↦ n + e_{c(a)} ∑_j G_a(j) n_j`. -/
def letterStep (c : α → ι) (G : α → ι → ℕ) (a : α) : Function.End (ι → ℕ) :=
  fun n k => n k + if k = c a then ∑ j, G a j * n j else 0

/-- The linear test `φ(n) = ∑_k φ_k n_k`. -/
def lin (φ n : ι → ℕ) : ℝ := ∑ k, (φ k : ℝ) * n k

lemma lin_single (φ : ι → ℕ) (k : ι) : lin φ (Pi.single k 1) = φ k := by
  simp [lin, Pi.single_apply]

/-- A linear test of `T_a n` is the transposed test of `n`. -/
lemma lin_letterStep (c : α → ι) (G : α → ι → ℕ) (a : α) (φ n : ι → ℕ) :
    lin φ (letterStep c G a n) = lin (fun j => φ j + φ (c a) * G a j) n := by
  simp only [lin, letterStep, Nat.cast_add, Nat.cast_ite, Nat.cast_sum, Nat.cast_mul,
    Nat.cast_zero, mul_add, add_mul, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The count-vector domination system**: centres `e_k`, letters the transvections, tests the
linear functionals `φ(n) = ∑_k φ_k n_k`, pulled back by `φ ↦ φ + φ_{c(a)} G_a`. -/
def countModel (c : α → ι) (G : α → ι → ℕ) :
    DominationSystem (Function.End (ι → ℕ)) (ι → ℕ) ι α (ι → ℕ) where
  S k := Pi.single k 1
  T := letterStep c G
  c := c
  G := G
  test := lin
  pull a φ := fun j => φ j + φ (c a) * G a j
  test_pull a φ n := (lin_letterStep c G a φ n).symm
  centre_le a φ k := by
    show lin φ (letterStep c G a (Pi.single k 1)) ≤
      lin φ (Pi.single k 1) + (G a k : ℝ) * lin φ (Pi.single (c a) 1)
    rw [lin_letterStep, lin_single, lin_single, lin_single]
    push_cast
    linarith

/-- In the count model the bound on centres is an equality. -/
theorem countModel_centre_eq (c : α → ι) (G : α → ι → ℕ) (a : α) (φ : ι → ℕ) (k : ι) :
    (countModel c G).test φ ((countModel c G).T a • (countModel c G).S k) =
      (countModel c G).test φ ((countModel c G).S k) +
        (countModel c G).G a k *
          (countModel c G).test φ ((countModel c G).S ((countModel c G).c a)) := by
  show lin φ (letterStep c G a (Pi.single k 1)) =
    lin φ (Pi.single k 1) + (G a k : ℝ) * lin φ (Pi.single (c a) 1)
  rw [lin_letterStep, lin_single, lin_single, lin_single]
  push_cast
  ring

/-- The domination recursion on the count model. -/
example (c : α → ι) (G : α → ι → ℕ) (w : List α) (j : ι) (φ : ι → ℕ) :
    (countModel c G).test φ ((countModel c G).word w • (countModel c G).S j) ≤
      ∑ k, ((countModel c G).dom w (Pi.single j 1) k : ℝ) *
        (countModel c G).test φ ((countModel c G).S k) :=
  (countModel c G).test_word_le w j φ

/-- The pair of pairing `3`: each letter has the other vertex as its only neighbour. -/
def pairCoupling (a k : Fin 2) : ℕ := if k = a then 0 else 3

/-- On the pair of pairing `3`, `T₀ T₁` sends `S₀ = (1, 0)` to `(10, 3)`. -/
example : (countModel id pairCoupling).word [0, 1] • (countModel id pairCoupling).S 0 = ![10, 3] := by
  decide

/-- The recursion predicts the same count vector `(10, 3)`. -/
example : (countModel id pairCoupling).dom [0, 1] (Pi.single 0 1) = ![10, 3] := by
  decide

/-- The Euler-count system of a K3 surface of Picard rank one is a domination system, with the
zero-diagonal coupling. -/
example (d : ℤ) : DominationSystem (mukaiIsometries d) (MukaiVector ℤ) (Fin 2) (Fin 2)
    (MukaiVector ℤ) :=
  (eulerTwistSystem d).toDomination

end K3TwistsTest.DominationSystemModel
