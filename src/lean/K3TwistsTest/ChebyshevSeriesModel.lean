/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Combinatorics.Quiver.ChebyshevSeries

/-!
# Matrix Chebyshev series on small graphs

* The chain `1 - 2 - 3`: the series between the two ends vanishes in degrees `0` and `1` and is
  `1` in degree `2`, the graph distance, where there is one walk.
* Two spheres with `g = 3` arrows each way: the off-diagonal entry in degree `3` is the Kronecker
  number `u_4 = 21`.
* The bar Euler characteristic in degree two is `C² - 1`.
* Two spheres with `g = 3` arrows each way, with the field of exact dimensions: `Tor` between them
  vanishes in degree `0` and has dimension `3` in degree `1`, the length of the shortest path.
-/

open Matrix

/-- The adjacency matrix of the chain `1 - 2 - 3`. -/
def chainMatrix : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 0; 1, 0, 1; 0, 1, 0]

example : chainMatrix.chebyshevS 0 0 2 = 0 := by simp

example : chainMatrix.chebyshevS 1 0 2 = 0 := by simp [chainMatrix]

/-- At the distance two the series is `(A² - 1)_{13} = 1`. -/
example : chainMatrix.chebyshevS 2 0 2 = 1 := by
  have := chainMatrix.chebyshevS_add_two 0
  norm_num at this
  rw [this]
  simp [chainMatrix]

/-- Two spheres with three arrows each way: `S_3(C)_{01} = u_4 = 21`. -/
example : ((3 : ℤ) • !![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).chebyshevS (2 * 1 + 1 : ℕ) 0 1 =
    21 := by
  rw [chebyshevS_kronecker_apply_zero_one]
  have h3 := Quiver.Kronecker.u_add_one 3 2
  have h4 := Quiver.Kronecker.u_add_one 3 3
  norm_num at h3 h4
  norm_num [h4, h3]

/-- The bar Euler characteristic in internal degree two. -/
example (C : Matrix (Fin 2) (Fin 2) ℤ) : C.barEuler 2 = C * C - 1 := by
  rw [barEuler_eq_chebyshevS]
  have := C.chebyshevS_add_two 0
  norm_num at this
  exact this

/-- Two spheres with three arrows each way: under the field of exact dimensions, `Tor` between
them vanishes in degree `0` and has dimension three in degree one. -/
example (tor : ℕ → Matrix (Fin 2) (Fin 2) ℕ)
    (hdim : ∀ m, (tor m).map (Nat.cast : ℕ → ℤ) =
      ((!![0, 3; 3, 0] : Matrix (Fin 2) (Fin 2) ℕ).map (Nat.cast : ℕ → ℤ)).chebyshevS m) :
    tor 0 0 1 = 0 ∧ tor 1 0 1 = 3 := by
  obtain ⟨h₁, h₂⟩ := Matrix.routedTor_of_pow_apply_eq_zero _ tor hdim (u := 0) (v := 1) (d := 1)
    fun j hj => by
      obtain rfl : j = 0 := by omega
      simp
  exact ⟨h₁ 0 one_pos, by simpa using h₂⟩
