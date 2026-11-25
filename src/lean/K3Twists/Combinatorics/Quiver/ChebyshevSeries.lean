/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Combinatorics.Quiver.Kronecker.RealRoots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Matrix Chebyshev series and the Koszul shadow

For a square matrix `C`, the matrix Chebyshev series is `S_m(C) = aeval C (Chebyshev.S R m)`,
Mathlib's rescaled Chebyshev polynomials of the second kind evaluated at `C`
(`Matrix.chebyshevS`): `S_0(C) = 1`, `S_1(C) = C`, `S_{m+2}(C) = C S_{m+1}(C) - S_m(C)`, so that
`∑ S_m(C) tᵐ = (1 - Ct + t²)⁻¹`.

Let `C` be the matrix of dimensions of `Ext¹` between a finite collection of spherical objects of
one phase in a 2-Calabi–Yau category. Their `Ext` algebra has Hilbert matrix `1 + Ct + t²`.
Inverting it gives the matrix Chebyshev series, which is therefore the Euler characteristic of the
routed (bar) complexes between two of the objects; by Koszul duality it is the Hilbert series of
the preprojective algebra of the `Ext` graph when no component of the graph is Dynkin.

## Main results

* `Polynomial.Chebyshev.coeff_S_self`, `coeff_S_of_lt`: `S_m = Xᵐ + (lower terms)` for `m : ℕ`.
* `Matrix.chebyshevS` with `chebyshevS_zero`, `chebyshevS_one`, `chebyshevS_add_two`.
* **Reachability at the graph distance**: `Matrix.chebyshevS_apply_eq_zero`,
  `Matrix.chebyshevS_apply_eq_pow_apply`. If `(Cʲ)_{ab} = 0` for every `j < d`, then
  `S_j(C)_{ab} = 0` for `j < d` and `S_d(C)_{ab} = (C^d)_{ab}`. For the adjacency matrix of a simple
  graph (`SimpleGraph.chebyshevS_adjMatrix_apply_of_lt_dist`,
  `SimpleGraph.chebyshevS_adjMatrix_apply_dist`): `S_m(A)_{uv} = 0` below the graph distance, and at
  the distance it is the number of walks of that length, positive when `v` is reachable from `u`
  (`SimpleGraph.chebyshevS_adjMatrix_apply_dist_pos`). With no walk at all it vanishes in every
  degree (`SimpleGraph.chebyshevS_adjMatrix_apply_of_not_reachable`).
* **The Euler characteristic of the bar complex** (`Matrix.barEuler_eq_chebyshevS`). For a
  graded algebra with Hilbert matrix `1 + Ct + t²` (a semisimple degree-zero part over the marked
  objects, `C` in degree one, the identity in degree two), the normalized bar complex in internal
  degree `m` with `l` bar factors has dimension matrix `barTerm C m l`, the coefficient of `tᵐ` in
  `(Ct + t²)ˡ`. Counting each term with the sign of its cohomological degree `m - l`, the Euler
  characteristic `barEuler C m` is `S_m(C)`.
* **The two-vertex instance**: for `C = g · [[0, 1], [1, 0]]` (two spheres with `g` arrows each
  way), `S_m(C)` is `S_m(g)` on the diagonal for even `m` and off the diagonal for odd `m`, the
  Kronecker sequence `u_{m+1}` of the real roots (`Matrix.chebyshevS_kronecker_apply_zero_one`).
* **The Tor part of the transport rule**, from the Chebyshev core and the fields below
  (`SimpleGraph.routedEuler_eq_zero_of_lt_dist`, `SimpleGraph.routedTor_dist_pos`): the routed
  Euler characteristic between `u` and `v` vanishes below the graph distance and counts the
  shortest walks at it; with exact dimensions, `Tor` vanishes below the distance and is nonzero at
  it.

## The fields

Mathlib has no dg algebras, `Tor` or bar complexes, so two inputs stay fields, as hypotheses of
the last two theorems.

* The Euler characteristic of the routed complex in internal degree `m` is the matrix Chebyshev
  coefficient `S_m(C)`. Proved here for the bar complex of the formal `Ext` algebra
  (`barEuler_eq_chebyshevS`); that the routed complex is this bar complex rests on formality of
  the `Ext` algebra of the spherical objects (Davison, arXiv:2106.07692, Proposition 7.8) and on
  the bar construction computing the derived tensor product.
* Exact dimensions: `Tor` in internal degree `m` has dimension `S_m(C)`. This holds only when no
  connected component of the `Ext` graph is Dynkin: classical Koszulity of the preprojective
  algebra, whose Hilbert series is then `(1 - Ct + t²)⁻¹` (Malkin–Ostrik–Vybornov,
  arXiv:math/0403222; Etingof–Eu, arXiv:math/0606403). On a Dynkin component the preprojective
  algebra is finite-dimensional and the series has cancellations.

Koszul duality and formality themselves stay cited.
-/

open Polynomial

namespace Polynomial.Chebyshev

variable (R : Type*) [CommRing R]

/-- `S_m` is monic of degree `m`, in the form needed below: its coefficient of `Xᵐ` is one, and
every coefficient above vanishes. -/
theorem coeff_S_self_and_of_lt : ∀ m : ℕ,
    (S R m).coeff m = 1 ∧ ∀ j, m < j → (S R m).coeff j = 0 := by
  have step : ∀ m : ℕ, ((S R m).coeff m = 1 ∧ ∀ j, m < j → (S R m).coeff j = 0) ∧
      ((S R (m + 1 : ℕ)).coeff (m + 1) = 1 ∧ ∀ j, m + 1 < j → (S R (m + 1 : ℕ)).coeff j = 0) := by
    intro m
    induction m with
    | zero =>
      refine ⟨⟨by simp, fun j hj ↦ ?_⟩, ⟨by simp, fun j hj ↦ ?_⟩⟩
      · simp [coeff_one, Nat.pos_iff_ne_zero.mp hj]
      · simp only [zero_add, Nat.cast_one, S_one, coeff_X, ite_eq_right_iff]
        intro h
        omega
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have e : ((m + 1 + 1 : ℕ) : ℤ) = (m : ℤ) + 2 := by push_cast; ring
      rw [e, S_add_two]
      have e1 : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1]
      refine ⟨?_, fun j hj ↦ ?_⟩
      · rw [coeff_sub, coeff_X_mul, ih.2.1, ih.1.2 _ (by omega), sub_zero]
      · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [coeff_sub, coeff_X_mul, ih.2.2 _ (by omega), ih.1.2 _ (by omega), sub_zero]
  exact fun m ↦ (step m).1

theorem coeff_S_self (m : ℕ) : (S R m).coeff m = 1 := (coeff_S_self_and_of_lt R m).1

theorem coeff_S_of_lt {m j : ℕ} (h : m < j) : (S R m).coeff j = 0 :=
  (coeff_S_self_and_of_lt R m).2 j h

theorem natDegree_S_le (m : ℕ) : (S R m).natDegree ≤ m :=
  natDegree_le_iff_coeff_eq_zero.2 fun _ hj ↦ coeff_S_of_lt R (by exact_mod_cast hj)

end Polynomial.Chebyshev

namespace Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (C : Matrix ι ι R)

/-- **The matrix Chebyshev series** `S_m(C) = aeval C (Chebyshev.S R m)`. -/
noncomputable def chebyshevS (m : ℤ) : Matrix ι ι R := aeval C (Chebyshev.S R m)

@[simp] lemma chebyshevS_zero : C.chebyshevS 0 = 1 := by simp [chebyshevS]

@[simp] lemma chebyshevS_one : C.chebyshevS 1 = C := by simp [chebyshevS]

@[simp] lemma chebyshevS_neg_one : C.chebyshevS (-1) = 0 := by
  simp [chebyshevS, Chebyshev.S_neg_one]

/-- The three-term recursion `S_{m+2}(C) = C S_{m+1}(C) - S_m(C)`. -/
lemma chebyshevS_add_two (m : ℤ) :
    C.chebyshevS (m + 2) = C * C.chebyshevS (m + 1) - C.chebyshevS m := by
  simp [chebyshevS, Chebyshev.S_add_two]

/-- `S_m(C) = ∑_{j ≤ m} s_{m,j} Cʲ` with `s_{m,m} = 1`. -/
lemma chebyshevS_natCast_eq_sum (m : ℕ) :
    C.chebyshevS m = ∑ j ∈ Finset.range (m + 1), (Chebyshev.S R m).coeff j • C ^ j :=
  aeval_eq_sum_range' (Nat.lt_succ_of_le (Chebyshev.natDegree_S_le R m)) C

/-- **Reachability at the graph distance, the leading term.** If `(Cʲ)_{ab} = 0` for every
`j < m`, then `S_m(C)_{ab} = (Cᵐ)_{ab}`. -/
theorem chebyshevS_apply_eq_pow_apply {m : ℕ} {a b : ι} (h : ∀ j < m, (C ^ j) a b = 0) :
    C.chebyshevS m a b = (C ^ m) a b := by
  rw [chebyshevS_natCast_eq_sum, Finset.sum_range_succ, Matrix.add_apply, Matrix.sum_apply,
    Finset.sum_eq_zero fun j hj ↦ by
      rw [Matrix.smul_apply, h j (Finset.mem_range.mp hj), smul_zero],
    Matrix.smul_apply, Chebyshev.coeff_S_self, one_smul, zero_add]

/-- **Reachability at the graph distance, below it.** If `(Cʲ)_{ab} = 0` for every `j ≤ m`, then
`S_m(C)_{ab} = 0`. -/
theorem chebyshevS_apply_eq_zero {m : ℕ} {a b : ι} (h : ∀ j ≤ m, (C ^ j) a b = 0) :
    C.chebyshevS m a b = 0 := by
  rw [C.chebyshevS_apply_eq_pow_apply fun j hj ↦ h j hj.le, h m le_rfl]

/-! ### The Euler characteristic of the bar complex -/

/-- **The terms of the normalized bar complex** of a graded algebra with Hilbert matrix
`1 + Ct + t²`: the dimension matrix of the part with `l` bar factors in internal degree `m`, that
is the coefficient of `tᵐ` in `(Ct + t²)ˡ`. A bar factor has internal degree one (a copy of `C`)
or two (the identity). -/
def barTerm : ℕ → ℕ → Matrix ι ι R
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | 1, l + 1 => C * barTerm 0 l
  | m + 2, l + 1 => C * barTerm (m + 1) l + barTerm m l

lemma barTerm_eq_zero_of_lt : ∀ {m l : ℕ}, m < l → C.barTerm m l = 0
  | 0, _ + 1, _ => by simp [barTerm]
  | 1, l + 1, h => by
    rw [barTerm, barTerm_eq_zero_of_lt (m := 0) (l := l) (by omega), mul_zero]
  | m + 2, l + 1, h => by
    rw [barTerm, barTerm_eq_zero_of_lt (m := m + 1) (l := l) (by omega),
      barTerm_eq_zero_of_lt (m := m) (l := l) (by omega), mul_zero, add_zero]

/-- **The Euler characteristic of the bar complex** in internal degree `m`: the alternating sum
of `barTerm C m l` over the number `l` of bar factors, each term with the sign of its
cohomological degree `m - l`. -/
noncomputable def barEuler (m : ℕ) : Matrix ι ι R :=
  ∑ l ∈ Finset.range (m + 1), (-1 : R) ^ (m + l) • C.barTerm m l

lemma barEuler_zero : C.barEuler 0 = 1 := by simp [barEuler, barTerm]

lemma barEuler_one : C.barEuler 1 = C := by
  simp [barEuler, barTerm, Finset.sum_range_succ]

lemma barEuler_add_two (m : ℕ) :
    C.barEuler (m + 2) = C * C.barEuler (m + 1) - C.barEuler m := by
  simp only [barEuler]
  rw [Finset.sum_range_succ' _ (m + 2)]
  simp only [barTerm, smul_zero, add_zero, smul_add, Finset.sum_add_distrib, Finset.mul_sum,
    mul_smul_comm]
  rw [Finset.sum_range_succ (fun l ↦ (-1 : R) ^ (m + 2 + (l + 1)) • C.barTerm m l) (m + 1),
    C.barTerm_eq_zero_of_lt (by omega : m < m + 1), smul_zero, add_zero, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun l _ ↦ ?_
    congr 1
    ring
  · refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← neg_smul]
    congr 1
    ring

/-- **The bar Euler characteristic is the matrix Chebyshev series**: `barEuler C m = S_m(C)`,
the coefficient of `tᵐ` in `(1 - Ct + t²)⁻¹`. -/
theorem barEuler_eq_chebyshevS : ∀ m : ℕ, C.barEuler m = C.chebyshevS m
  | 0 => by simp [barEuler_zero]
  | 1 => by simp [barEuler_one]
  | m + 2 => by
    rw [barEuler_add_two, barEuler_eq_chebyshevS (m + 1), barEuler_eq_chebyshevS m]
    have := C.chebyshevS_add_two m
    push_cast at this ⊢
    rw [this]

/-! ### The two-vertex instance -/

/-- **Two spheres with `g` arrows each way.** For `C = g · [[0, 1], [1, 0]]`, `S_m(C)` is
`S_m(g)` times the identity for even `m` and times `[[0, 1], [1, 0]]` for odd `m`. -/
theorem chebyshevS_kronecker (g : R) : ∀ m : ℕ,
    (g • !![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R).chebyshevS m =
      (Chebyshev.S R m).eval g • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R) ^ m := by
  have hσ : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R) ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  intro m
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more m ih₀ ih₁ =>
    have e : ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 := by push_cast; ring
    rw [e, chebyshevS_add_two, show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring, ih₀, ih₁,
      Chebyshev.S_add_two, show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring]
    simp only [eval_sub, eval_mul, eval_X, smul_mul_smul_comm, ← pow_succ', sub_smul,
      mul_smul]
    rw [pow_add (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R) m 2, hσ, mul_one]

/-- The off-diagonal entry of the two-vertex series at odd degree is the Kronecker sequence:
`S_{2j+1}(C)_{01} = u_{2j+2}`. -/
theorem chebyshevS_kronecker_apply_zero_one (g : ℤ) (j : ℕ) :
    (g • !![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).chebyshevS (2 * j + 1 : ℕ) 0 1 =
      Quiver.Kronecker.u g (2 * j + 2) := by
  have hσ : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ (2 * j + 1) = !![0, 1; 1, 0] := by
    rw [pow_succ, pow_mul]
    have : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
    rw [this, one_pow, one_mul]
  rw [chebyshevS_kronecker, hσ, Quiver.Kronecker.u, Matrix.smul_apply]
  simp only [of_apply, cons_val', cons_val_one, cons_val_zero, empty_val', cons_val_fin_one,
    smul_eq_mul, mul_one]
  congr 2
  push_cast
  ring

end Matrix

/-! ### Graphs: reachability at the graph distance -/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Below the graph distance there is no walk of length `j`. -/
lemma adjMatrix_pow_apply_eq_zero_of_lt_dist {j : ℕ} {u v : V} (h : j < G.dist u v) :
    (G.adjMatrix ℤ ^ j) u v = 0 := by
  rw [adjMatrix_pow_apply_eq_card_walk]
  norm_cast
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun ⟨p, hp⟩ ↦ absurd (G.dist_le p) (by simp only [Set.mem_ofPred_eq] at hp; omega)⟩

/-- **Below the graph distance** the matrix Chebyshev series of the adjacency matrix vanishes. -/
theorem chebyshevS_adjMatrix_apply_of_lt_dist {m : ℕ} {u v : V} (h : m < G.dist u v) :
    (G.adjMatrix ℤ).chebyshevS m u v = 0 :=
  Matrix.chebyshevS_apply_eq_zero _ fun _ hj ↦
    G.adjMatrix_pow_apply_eq_zero_of_lt_dist (lt_of_le_of_lt hj h)

/-- **At the graph distance** the matrix Chebyshev series counts the walks of that length, that
is the shortest walks. -/
theorem chebyshevS_adjMatrix_apply_dist (u v : V) :
    (G.adjMatrix ℤ).chebyshevS (G.dist u v) u v =
      Fintype.card {p : G.Walk u v | p.length = G.dist u v} := by
  rw [Matrix.chebyshevS_apply_eq_pow_apply _ fun _ hj ↦
    G.adjMatrix_pow_apply_eq_zero_of_lt_dist hj, adjMatrix_pow_apply_eq_card_walk]

/-- At the graph distance of a reachable vertex the series is positive. -/
theorem chebyshevS_adjMatrix_apply_dist_pos {u v : V} (h : G.Reachable u v) :
    0 < (G.adjMatrix ℤ).chebyshevS (G.dist u v) u v := by
  rw [chebyshevS_adjMatrix_apply_dist]
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  have : 0 < Fintype.card {p : G.Walk u v | p.length = G.dist u v} :=
    Fintype.card_pos_iff.mpr ⟨⟨p, hp⟩⟩
  exact_mod_cast this

/-- With no walk from `u` to `v`, the series vanishes in every degree. -/
theorem chebyshevS_adjMatrix_apply_of_not_reachable {u v : V} (h : ¬ G.Reachable u v) (m : ℕ) :
    (G.adjMatrix ℤ).chebyshevS m u v = 0 := by
  refine Matrix.chebyshevS_apply_eq_zero _ fun j _ ↦ ?_
  rw [adjMatrix_pow_apply_eq_card_walk]
  norm_cast
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun ⟨p, _⟩ ↦ h p.reachable⟩

/-! ### The Tor part of the transport rule, from the fields -/

/-- **The routed Euler characteristic.** Let `euler m` be the matrix of Euler characteristics in
internal degree `m` of the routed complexes between the vertices of the `Ext` graph `G` of a
collection of spherical objects with one `Ext¹` per edge, and assume the field `heuler`: it is the
matrix Chebyshev coefficient `S_m(A)` of the adjacency matrix (proved for the bar complex of the
formal `Ext` algebra, `Matrix.barEuler_eq_chebyshevS`). Then it vanishes below the graph distance
from `u` to `v`, and at the distance it is the number of shortest walks. -/
theorem routedEuler_eq_zero_of_lt_dist (euler : ℕ → Matrix V V ℤ)
    (heuler : ∀ m, euler m = (G.adjMatrix ℤ).chebyshevS m) {u v : V} :
    (∀ m < G.dist u v, euler m u v = 0) ∧
      euler (G.dist u v) u v = Fintype.card {p : G.Walk u v | p.length = G.dist u v} :=
  ⟨fun m hm ↦ by rw [heuler]; exact G.chebyshevS_adjMatrix_apply_of_lt_dist hm,
    by rw [heuler]; exact G.chebyshevS_adjMatrix_apply_dist u v⟩

/-- **The Tor part of the transport rule, exact form.** Assume moreover the field `hdim`: the
dimension of `Tor` in internal degree `m` is `S_m(A)`, which holds only when no component of the
`Ext` graph is Dynkin (classical Koszulity). Then `Tor` vanishes below the graph distance, is
nonzero at it when `v` is reachable from `u`, and vanishes in every degree otherwise. -/
theorem routedTor_dist_pos (tor : ℕ → Matrix V V ℕ)
    (hdim : ∀ m, (tor m).map (Nat.cast : ℕ → ℤ) = (G.adjMatrix ℤ).chebyshevS m) {u v : V} :
    (∀ m < G.dist u v, tor m u v = 0) ∧ (G.Reachable u v → 0 < tor (G.dist u v) u v) ∧
      (¬ G.Reachable u v → ∀ m, tor m u v = 0) := by
  have key : ∀ m, (tor m u v : ℤ) = (G.adjMatrix ℤ).chebyshevS m u v := fun m ↦ by
    rw [← hdim m, Matrix.map_apply]
  refine ⟨fun m hm ↦ ?_, fun h ↦ ?_, fun h m ↦ ?_⟩
  · have := key m
    rw [G.chebyshevS_adjMatrix_apply_of_lt_dist hm] at this
    exact_mod_cast this
  · have := key (G.dist u v)
    have hpos := G.chebyshevS_adjMatrix_apply_dist_pos h
    rw [← this] at hpos
    exact_mod_cast hpos
  · have := key m
    rw [G.chebyshevS_adjMatrix_apply_of_not_reachable h] at this
    exact_mod_cast this

end SimpleGraph
