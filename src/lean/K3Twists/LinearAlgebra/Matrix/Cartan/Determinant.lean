/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Determinants of the Cartan matrices of types `A` and `D`

Mathlib computes the determinants of `E₆`, `E₇`, `E₈` (`CartanMatrix.E₆_det` and its siblings);
this file adds the two infinite series:

* `CartanMatrix.A_det`: Mathlib's `CartanMatrix.A n`, the `n × n` Cartan matrix of the path with
  `n` nodes (type `Aₙ`), has determinant `n + 1`;
* `CartanMatrix.D_det`: Mathlib's `CartanMatrix.D n` has determinant `4` for `n ≥ 2` (type `Dₙ`,
  with `D₂ = A₁ × A₁` and `D₃ = A₃`).

Both come from one expansion, `Matrix.det_eq_of_leaf`: deleting a node `0` joined by one simple edge
to the node `1` and to nothing else gives `det M = 2 det M' - det M''`, where `M'` deletes the
node `0` and `M''` deletes the nodes `0` and `1`. Deleting the first node of `Aₙ` leaves `Aₙ₋₁`,
and of `Dₙ` (`n ≥ 4`), whose fork is at the last nodes, leaves `Dₙ₋₁`.

The values `n + 1`, `4`, `3`, `2`, `1` are the orders of the fundamental groups `P^∨/Q^∨` of the
simply laced root systems (Bourbaki, *Groupes et algèbres de Lie*, Ch. VI, Plates I–VII).
-/

namespace Matrix

/-- **A leaf of the Dynkin diagram.** If the node `0` of `M` has `2` on the diagonal, is joined to
the node `1` by entries `-1` and to no other node, then `det M = 2 det M' - det M''`, where `M'`
deletes the node `0` and `M''` deletes the nodes `0` and `1`. -/
theorem det_eq_of_leaf {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (h00 : M 0 0 = 2) (h01 : M 0 1 = -1) (h10 : M 1 0 = -1)
    (h0j : ∀ j : Fin n, M 0 j.succ.succ = 0) (hi0 : ∀ i : Fin n, M i.succ.succ 0 = 0) :
    M.det = 2 * (M.submatrix Fin.succ Fin.succ).det -
      (M.submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ)).det := by
  have hcol : (M.submatrix Fin.succ (Fin.succAbove 1)).det =
      -(M.submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ)).det := by
    rw [det_succ_column_zero, Fin.sum_univ_succ]
    have hsub : ((M.submatrix Fin.succ (Fin.succAbove 1)).submatrix (Fin.succAbove 0) Fin.succ) =
        M.submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ) := by
      ext i j
      simp only [submatrix_apply, Fin.succAbove_zero, Function.comp_apply]
      congr 1
    have hrest : ∀ i : Fin n, (M.submatrix Fin.succ (Fin.succAbove 1)) i.succ 0 = 0 := by
      intro i
      simp only [submatrix_apply]
      rw [show (Fin.succAbove 1 0 : Fin (n + 2)) = 0 from rfl]
      exact hi0 i
    simp only [hsub, hrest, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero,
      pow_zero, one_mul, submatrix_apply]
    rw [show (Fin.succAbove 1 0 : Fin (n + 2)) = 0 from rfl, show Fin.succ (0 : Fin (n + 1)) = 1
      from rfl, h10]
    ring
  rw [det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.val_succ, h00]
  rw [show Fin.succ (0 : Fin (n + 1)) = 1 from rfl, h01, hcol]
  simp only [h0j, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, pow_one]
  ring

end Matrix

namespace CartanMatrix

open Matrix

theorem A_submatrix_succ (n : ℕ) : (A (n + 1)).submatrix Fin.succ Fin.succ = A n := by
  ext i j
  simp only [A, submatrix_apply, of_apply, Fin.succ_inj, Fin.val_succ]
  grind

/-- `det Aₙ = 2 det Aₙ₋₁ - det Aₙ₋₂`. -/
theorem det_A_add_two (n : ℕ) : (A (n + 2)).det = 2 * (A (n + 1)).det - (A n).det := by
  rw [det_eq_of_leaf (A (n + 2)) (by simp [A]) (by simp [A]) (by simp [A])
    (fun j => by simp [A, eq_comm (a := (0 : Fin (n + 2)))]) (fun i => by simp [A]),
    A_submatrix_succ, ← submatrix_submatrix, A_submatrix_succ, A_submatrix_succ]

/-- **The determinant of `Aₙ` is `n + 1`**, for Mathlib's `n × n` matrix `CartanMatrix.A n`. -/
theorem A_det (n : ℕ) : (A n).det = n + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => decide
  | more n ih1 ih2 =>
    rw [det_A_add_two, ih1, ih2]
    push_cast
    ring

theorem D_submatrix_succ {n : ℕ} (hn : 3 ≤ n) : (D (n + 1)).submatrix Fin.succ Fin.succ = D n := by
  ext i j
  simp only [D, submatrix_apply, of_apply, Fin.succ_inj, Fin.val_succ]
  grind

/-- `det Dₙ = 2 det Dₙ₋₁ - det Dₙ₋₂` for `n - 2 ≥ 3`. -/
theorem det_D_add_two {n : ℕ} (hn : 3 ≤ n) :
    (D (n + 2)).det = 2 * (D (n + 1)).det - (D n).det := by
  rw [det_eq_of_leaf (D (n + 2)) (by simp [D]) (by simp [D]; lia) (by simp [D]; lia)
    (fun j => by simp [D]; grind) (fun i => by simp [D]; grind), D_submatrix_succ (by lia),
    ← submatrix_submatrix, D_submatrix_succ (by lia), D_submatrix_succ hn]

/-- **The determinant of `Dₙ` is `4`** for `n ≥ 2`. -/
theorem D_det {n : ℕ} (hn : 2 ≤ n) : (D n).det = 4 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · decide
    · rw [show n + 2 + 2 = (n + 2) + 2 by ring, det_D_add_two (by lia), ih2 (by lia),
        ih1 (by lia)]
      norm_num

end CartanMatrix
