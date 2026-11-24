/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.WallArithmetic
import K3Twists.RepresentationTheory.Quiver.Kronecker.RigidRep

/-!
# Arrows in both directions at a rigid wall

The example of the article with this title. At a wall with two spherical simples `S₀, S₁` of
pairing `g = 3`, the iterated extensions are the nilpotent representations of the doubled
`3`-Kronecker quiver with the preprojective relations (see
`K3Twists.RepresentationTheory.Quiver.Kronecker.Preprojective`). Take `W = k³` with basis `e_i`,
`H' = (W ⊗ W)/⟨∑ e_i ⊗ e_i⟩`, vertex spaces `H' ⊕ k·u` and `W`, `A_i(h + s u) = s e_i` and
`B_i(w) = [e_i ⊗ w]`: this is `Quiver.Kronecker.rigidRep k (Fin 3)`, of dimension vector `(9, 3)`.

* `rigidWall_isPreprojective`, `rigidWall_A_comp_B`: the relations hold and every path of length
  three vanishes;
* `rigidWall_finrank_End`: `dim End = 9 = 9² + 3² - 3·9·3`, so the object is rigid;
* `rigidWall_dimVec_mem`: a subrepresentation has dimension vector `(9, 3)` or `(8, 3)`, or
  `(i, j)` with `j < 3` and `3j ≤ i ≤ 8`;
* `rigidWall_upper`, `rigidWall_lower`: plotting `(i, j)` at `(i + j, j)`, the upper boundary of
  the convex hull is `(0, 0) → (11, 3) → (12, 3)`, through `(H', W)`, and the lower boundary is
  `(0, 0) → (8, 0) → (12, 3)`, through `(H', 0)`;
* `rigidWall_upperCorner_stable`, `rigidWall_quotient_stable`: on the side where the phase
  increases with `j/(i + j)`, the subrepresentation `(H', W)` of dimension `(8, 3)` is stable and
  every other subrepresentation has smaller slope, so the HN filtration is `(H', W) ⊂ M` with
  quotients the stable root `(8, 3)` and the simple at vertex zero; on the other side `(H', 0)`
  is the semisimple `S₀⁸`, and `M/(H', 0)`, of dimension `(1, 3)`, is stable;
* `rigidWall_stable_roots`: `(8, 3) = R₂` and `(1, 3) = L₁` are real roots.

On each side the first piece of the filtration is the unique largest subrepresentation of
maximal slope and the quotient is stable of smaller slope; these inequalities are what make the
two filtrations the HN filtrations of the wall object for the two orders of the phases.
-/

namespace AlgebraicGeometry.K3.PicardRankOne

open Module Quiver.Kronecker Quiver.Kronecker.RigidRep

variable (k : Type*) [Field k]

/-- The relations of the example hold. -/
theorem rigidWall_isPreprojective : (rigidRep k (Fin 3)).IsPreprojective :=
  rigidRep_isPreprojective

/-- `A_j B_i = 0`, so every path of length three vanishes: the representation is nilpotent. -/
theorem rigidWall_A_comp_B (i j : Fin 3) :
    (rigidRep k (Fin 3)).A j ∘ₗ (rigidRep k (Fin 3)).B i = 0 ∧
      (rigidRep k (Fin 3)).IsNilpotent :=
  ⟨rigidRep_A_comp_B i j, rigidRep_isNilpotent⟩

/-- The wall object has dimension vector `(9, 3)`. -/
theorem rigidWall_dimVec : DoubledRep.dimVec (⊤ : (rigidRep k (Fin 3)).subreps) = (9, 3) := by
  rw [dimVec_top, Fintype.card_fin]
  rfl

/-- **Rigidity.** `dim End = 9 = 9² + 3² - 3·9·3`. -/
theorem rigidWall_finrank_End :
    finrank k (DoubledRep.Hom (rigidRep k (Fin 3)) (rigidRep k (Fin 3))) = 9 ∧
      kroneckerForm 3 9 3 = 9 := by
  refine ⟨?_, rigid_example.1⟩
  rw [finrank_rigidRep_End, Fintype.card_fin]
  norm_num

variable {k}

/-- **The subrepresentations.** If the subspace at vertex one has dimension `j < 3`, the
vertex-zero subspace lies in `H'` and contains the `3j`-dimensional image of `W ⊗ U₁`; at `j = 3`
the vertex-zero dimension is `8` or `9`. -/
theorem rigidWall_dimVec_mem (N : (rigidRep k (Fin 3)).subreps) :
    DoubledRep.dimVec N = (9, 3) ∨ DoubledRep.dimVec N = (8, 3) ∨
      ((DoubledRep.dimVec N).2 < 3 ∧ 3 * (DoubledRep.dimVec N).2 ≤ (DoubledRep.dimVec N).1 ∧
        (DoubledRep.dimVec N).1 ≤ 8) := by
  simpa using dimVec_mem N

/-- **The upper boundary** `(0, 0) → (11, 3) → (12, 3)`. The points `(i + j, j)` of `0`, `(H', W)`
and `M` are its vertices; every point lies on or below both edges, `11 j ≤ 3 (i + j)` and
`j ≤ 3`, and only `0` and `(H', W)` lie on the first edge. -/
theorem rigidWall_upper :
    DoubledRep.dimVec (upperCorner : (rigidRep k (Fin 3)).subreps) = (8, 3) ∧
      ∀ N : (rigidRep k (Fin 3)).subreps,
        (11 * (DoubledRep.dimVec N).2 ≤ 3 * ((DoubledRep.dimVec N).1 + (DoubledRep.dimVec N).2) ∧
          (DoubledRep.dimVec N).2 ≤ 3) ∧
        (11 * (DoubledRep.dimVec N).2 = 3 * ((DoubledRep.dimVec N).1 + (DoubledRep.dimVec N).2) →
          N = ⊥ ∨ N = upperCorner) := by
  refine ⟨by simpa using dimVec_upperCorner (k := k) (ι := Fin 3), fun N ↦ ⟨?_, fun h ↦ ?_⟩⟩
  · simpa using dimVec_upper N
  · exact dimVec_upper_eq (by simpa using h)

/-- **The lower boundary** `(0, 0) → (8, 0) → (12, 3)`. The points of `0`, `(H', 0)` and `M` are
its vertices; every point lies on or above the second edge, `3 i ≤ 24 + j`, only `(H', 0)` and
`M` lie on it, and the points on the first edge `j = 0` are the subrepresentations of
`(H', 0)`. -/
theorem rigidWall_lower :
    DoubledRep.dimVec (lowerCorner : (rigidRep k (Fin 3)).subreps) = (8, 0) ∧
      ∀ N : (rigidRep k (Fin 3)).subreps,
        3 * (DoubledRep.dimVec N).1 ≤ 24 + (DoubledRep.dimVec N).2 ∧
        (3 * (DoubledRep.dimVec N).1 = 24 + (DoubledRep.dimVec N).2 →
          N = lowerCorner ∨ N = ⊤) ∧
        ((DoubledRep.dimVec N).2 = 0 → N ≤ lowerCorner) := by
  refine ⟨by simpa using dimVec_lowerCorner (k := k) (ι := Fin 3), fun N ↦ ⟨?_, fun h ↦ ?_,
    le_lowerCorner_of_dimVec_snd⟩⟩
  · simpa using dimVec_lower N
  · exact dimVec_lower_eq (by simpa using h)

/-- **Stability of `(H', W)`**, for the phase increasing with `j/(i + j)`: every nonzero proper
subrepresentation `N` of `(H', W)` has `j/(i + j) < 3/11`. -/
theorem rigidWall_upperCorner_stable {N : (rigidRep k (Fin 3)).subreps} (hN : N < upperCorner)
    (h0 : N ≠ ⊥) :
    11 * (DoubledRep.dimVec N).2 < 3 * ((DoubledRep.dimVec N).1 + (DoubledRep.dimVec N).2) := by
  refine lt_of_le_of_ne ((rigidWall_upper).2 N).1.1 fun h ↦ ?_
  rcases ((rigidWall_upper).2 N).2 h with h' | h'
  · exact h0 h'
  · exact hN.ne h'

/-- **Stability of `M/(H', 0)`**, of dimension `(1, 3)`, for the phase increasing with
`i/(i + j)`: a subrepresentation strictly between `(H', 0)` and `M` gives a subobject
`(i - 8, j)` of the quotient with `(i - 8)/(i - 8 + j) < 1/4`, that is `3 i < 24 + j`. -/
theorem rigidWall_quotient_stable {N : (rigidRep k (Fin 3)).subreps} (h₁ : lowerCorner < N)
    (h₂ : N ≠ ⊤) :
    3 * (DoubledRep.dimVec N).1 < 24 + (DoubledRep.dimVec N).2 := by
  refine lt_of_le_of_ne ((rigidWall_lower).2 N).1 fun h ↦ ?_
  rcases ((rigidWall_lower).2 N).2.1 h with h' | h'
  · exact h₁.ne' h'
  · exact h₂ h'

/-- `(H', 0)` is semisimple: every arrow vanishes on it, so each of its subspaces is a
subrepresentation, and it is `S₀⁸`. -/
theorem rigidWall_lowerCorner_semisimple (i : Fin 3) {v : H k (Fin 3) × k}
    (hv : v ∈ (lowerCorner : (rigidRep k (Fin 3)).subreps).1.1) :
    (rigidRep k (Fin 3)).A i v = 0 := by
  obtain ⟨h, rfl⟩ := hv
  simp

/-- **The stable roots.** The stable factor `(8, 3)` of the first side is the real root
`R₂ = (u₃, u₂)`, and the stable factor `(1, 3)` of the other side is `L₁ = (u₁, u₂)`. -/
theorem rigidWall_stable_roots :
    (DoubledRep.dimVec (upperCorner : (rigidRep k (Fin 3)).subreps)) =
        ((u 3 3).toNat, (u 3 2).toNat) ∧
      ((DoubledRep.dimVec (⊤ : (rigidRep k (Fin 3)).subreps)).1 -
          (DoubledRep.dimVec (lowerCorner : (rigidRep k (Fin 3)).subreps)).1,
        (DoubledRep.dimVec (⊤ : (rigidRep k (Fin 3)).subreps)).2 -
          (DoubledRep.dimVec (lowerCorner : (rigidRep k (Fin 3)).subreps)).2) =
        ((u 3 1).toNat, (u 3 2).toNat) ∧
      kroneckerForm 3 8 3 = 1 ∧ kroneckerForm 3 1 3 = 1 := by
  obtain ⟨h2, h3⟩ := u_three_values
  refine ⟨?_, ?_, rigid_example.2.1, rigid_example.2.2.1⟩
  · rw [(rigidWall_upper (k := k)).1, h3, h2]
    rfl
  · rw [rigidWall_dimVec, (rigidWall_lower (k := k)).1, u_one, h2]
    rfl

end AlgebraicGeometry.K3.PicardRankOne
