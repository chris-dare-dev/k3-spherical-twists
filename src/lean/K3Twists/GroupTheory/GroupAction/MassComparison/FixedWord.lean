/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.GroupAction.MassComparison

/-!
# The fixed-word formula

Let `H` be a twist system of spherical objects for the inputs `I` (its letters are the twists
along its centres or their inverses, and its count is total `Ext`), `W` a fixed word and `E` an
object of positive mass. Write `d(Y) = max_i h(S_i, Y)` for the largest count from a centre
(`HomTwistSystem₀.centreCount`). Then the masses of `Wⁿ E` grow at the rate of the counts from the
centres, or not at all:

  `limsup m_σ(Wⁿ E)^{1/n} = max(1, limsup d(Wⁿ E)^{1/n})`

(`MassComparisonHypotheses.IsTwistSystem.limsup_mass_pow`). In particular the rate does not depend
on `σ`, and an object seen weakly by the centres can grow more slowly than the word does on the
centres themselves.

* **Upper bound.** By the mass form of the one-letter bound, a letter adds at most
  `h(S_{c(a)}, Y) m_σ(S_{c(a)})` to the mass of `Y`, and by the count form it multiplies `d` by at
  most `1 + g`, `g = max h(S_i, S_k)`. So `m_σ(Wⁿ E) ≤ m_σ(E) + K ∑_{k<n} d(W^k E)`
  (`IsTwistSystem.mass_word_pow_le`), and a sum of terms of rate `ρ ≥ 1` has rate `ρ`.
* **Lower bound.** The comparison gives `d(Y) ≤ A_σ m_σ(Y)`
  (`IsTwistSystem.centreCount_le_mul_mass`). If some `d(W^N E) = 0`, then every letter fixes
  `W^N E` (`T_S V = V` when `h(S, V) = 0`; `IsTwistSystem.word_smul_eq_of_centreCount_eq_zero`),
  so the masses are eventually constant and positive and the rate is one.

## Implementation notes

The limits superior are taken in `ℝ`; both sequences are bounded, so they are the usual ones.
-/

open Filter Topology Real

namespace HomTwistSystem₀

variable {G Obj ι α : Type*} [Group G] [MulAction G Obj] (H : HomTwistSystem₀ G Obj ι α)
variable [Fintype ι]

/-- `d(Y) = max_i h(S_i, Y)`, the largest count from a centre to `Y`. -/
noncomputable def centreCount (Y : Obj) : ℕ :=
  Finset.univ.sup fun i => H.h (H.S i) Y

lemma le_centreCount (i : ι) (Y : Obj) : H.h (H.S i) Y ≤ H.centreCount Y :=
  Finset.le_sup (f := fun i => H.h (H.S i) Y) (Finset.mem_univ i)

/-- One letter multiplies `d` by at most `1 + g`, `g = max h(S_i, S_k)`. -/
lemma centreCount_letter_le (a : α) (Y : Obj) :
    H.centreCount (H.T a • Y) ≤ (1 + H.centreMax) * H.centreCount Y := by
  refine Finset.sup_le fun i _ => ?_
  calc H.h (H.S i) (H.T a • Y)
      ≤ H.h (H.S i) Y + H.h (H.S i) (H.S (H.c a)) * H.h (H.S (H.c a)) Y := H.upper a _ _
    _ ≤ H.centreCount Y + H.centreMax * H.centreCount Y :=
        add_le_add (H.le_centreCount i Y)
          (Nat.mul_le_mul (H.le_centreMax i _) (H.le_centreCount _ Y))
    _ = (1 + H.centreMax) * H.centreCount Y := by ring

/-- A word of length `ℓ` multiplies `d` by at most `(1 + g)^ℓ`. -/
lemma centreCount_word_le (w : List α) (Y : Obj) :
    H.centreCount (H.word w • Y) ≤ (1 + H.centreMax) ^ w.length * H.centreCount Y := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [word_cons, mul_smul, List.length_cons, pow_succ']
    calc H.centreCount (H.T a • H.word w • Y)
        ≤ (1 + H.centreMax) * H.centreCount (H.word w • Y) := H.centreCount_letter_le a _
      _ ≤ (1 + H.centreMax) * ((1 + H.centreMax) ^ w.length * H.centreCount Y) :=
          Nat.mul_le_mul_left _ ih
      _ = (1 + H.centreMax) * (1 + H.centreMax) ^ w.length * H.centreCount Y := by ring

/-- Along the powers of a word, `d(Wⁿ Y) ≤ ((1 + g)^ℓ)ⁿ d(Y)`. -/
lemma centreCount_word_pow_le (w : List α) (Y : Obj) (n : ℕ) :
    (H.centreCount (H.word w ^ n • Y) : ℝ) ≤
      ((1 + (H.centreMax : ℝ)) ^ w.length) ^ n * H.centreCount Y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, pow_succ']
    have h := H.centreCount_word_le w (H.word w ^ n • Y)
    have h' : (H.centreCount (H.word w • H.word w ^ n • Y) : ℝ) ≤
        (1 + (H.centreMax : ℝ)) ^ w.length * H.centreCount (H.word w ^ n • Y) := by
      exact_mod_cast h
    have hQ : (0 : ℝ) ≤ (1 + (H.centreMax : ℝ)) ^ w.length := by positivity
    calc (H.centreCount (H.word w • H.word w ^ n • Y) : ℝ)
        ≤ (1 + (H.centreMax : ℝ)) ^ w.length * H.centreCount (H.word w ^ n • Y) := h'
      _ ≤ (1 + (H.centreMax : ℝ)) ^ w.length *
            (((1 + (H.centreMax : ℝ)) ^ w.length) ^ n * H.centreCount Y) := by gcongr
      _ = _ := by ring

end HomTwistSystem₀

namespace MassComparisonHypotheses

variable {Obj Γ Stab κ : Type*} [Group Γ] [MulAction Γ Obj] [MulAction Γ Stab] [Fintype κ]
  {I : MassComparisonHypotheses Obj Γ Stab κ} {ι α : Type*} [Fintype ι]
  {H : HomTwistSystem₀ Γ Obj ι α}

/-- Masses stay positive along any orbit: `m_σ(g E) = m_{g⁻¹ σ}(E) > 0`. -/
lemma mass_smul_pos {σ : Stab} {E : Obj} (hE : 0 < I.mass σ E) (g : Γ) : 0 < I.mass σ (g • E) := by
  rw [I.mass_smul_eq]
  exact I.toMassDistanceBound.mass_pos_of_pos hE

/-- **(U_m) through `d`**: `m_σ(T_a Y) ≤ m_σ(Y) + M₀ d(Y)`, with `M₀ = ∑_i m_σ(S_i)`. -/
theorem IsTwistSystem.mass_letter_le_centreCount (hH : I.IsTwistSystem H) (a : α) (σ : Stab)
    (Y : Obj) :
    I.mass σ (H.T a • Y) ≤ I.mass σ Y + (∑ i, I.mass σ (H.S i)) * H.centreCount Y := by
  have h1 := hH.mass_letter_le a σ Y
  have h2 : (H.h (H.S (H.c a)) Y : ℝ) ≤ H.centreCount Y := by
    exact_mod_cast H.le_centreCount _ Y
  have h3 : I.mass σ (H.S (H.c a)) ≤ ∑ i, I.mass σ (H.S i) :=
    Finset.single_le_sum (f := fun i => I.mass σ (H.S i)) (fun i _ => I.mass_nonneg σ _)
      (Finset.mem_univ _)
  have h4 := I.mass_nonneg σ (H.S (H.c a))
  have h5 : (0 : ℝ) ≤ H.h (H.S (H.c a)) Y := Nat.cast_nonneg _
  calc I.mass σ (H.T a • Y)
      ≤ I.mass σ Y + H.h (H.S (H.c a)) Y * I.mass σ (H.S (H.c a)) := h1
    _ ≤ I.mass σ Y + H.centreCount Y * ∑ i, I.mass σ (H.S i) := by gcongr
    _ = I.mass σ Y + (∑ i, I.mass σ (H.S i)) * H.centreCount Y := by ring

/-- **The mass along a word**: `m_σ(W Y) ≤ m_σ(Y) + ℓ (1 + g)^ℓ M₀ d(Y)` for `|W| = ℓ`. -/
theorem IsTwistSystem.mass_word_le_centreCount (hH : I.IsTwistSystem H) (σ : Stab)
    (w : List α) (Y : Obj) :
    I.mass σ (H.word w • Y) ≤ I.mass σ Y + w.length * (1 + (H.centreMax : ℝ)) ^ w.length *
      (∑ i, I.mass σ (H.S i)) * H.centreCount Y := by
  have hM₀ : 0 ≤ ∑ i, I.mass σ (H.S i) := Finset.sum_nonneg fun i _ => I.mass_nonneg σ _
  have hd : (0 : ℝ) ≤ H.centreCount Y := Nat.cast_nonneg _
  have hg : (1 : ℝ) ≤ 1 + (H.centreMax : ℝ) := by
    linarith [(Nat.cast_nonneg H.centreMax : (0 : ℝ) ≤ H.centreMax)]
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [HomTwistSystem₀.word_cons, mul_smul]
    have h1 := hH.mass_letter_le_centreCount a σ (H.word w • Y)
    have h2 : (H.centreCount (H.word w • Y) : ℝ) ≤
        (1 + (H.centreMax : ℝ)) ^ w.length * H.centreCount Y := by
      exact_mod_cast H.centreCount_word_le w Y
    have hQ : (1 + (H.centreMax : ℝ)) ^ w.length ≤ (1 + (H.centreMax : ℝ)) ^ (w.length + 1) :=
      pow_le_pow_right₀ hg (Nat.le_succ _)
    have hQ0 : (0 : ℝ) ≤ (1 + (H.centreMax : ℝ)) ^ w.length := by positivity
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    calc I.mass σ (H.T a • H.word w • Y)
        ≤ I.mass σ (H.word w • Y) + (∑ i, I.mass σ (H.S i)) * H.centreCount (H.word w • Y) := h1
      _ ≤ (I.mass σ Y + w.length * (1 + (H.centreMax : ℝ)) ^ w.length *
            (∑ i, I.mass σ (H.S i)) * H.centreCount Y) +
          (∑ i, I.mass σ (H.S i)) * ((1 + (H.centreMax : ℝ)) ^ w.length * H.centreCount Y) := by
          gcongr
      _ = I.mass σ Y + (w.length + 1) * (1 + (H.centreMax : ℝ)) ^ w.length *
            (∑ i, I.mass σ (H.S i)) * H.centreCount Y := by ring
      _ ≤ I.mass σ Y + (w.length + 1) * (1 + (H.centreMax : ℝ)) ^ (w.length + 1) *
            (∑ i, I.mass σ (H.S i)) * H.centreCount Y := by gcongr

/-- **The mass along the powers of a word**:
`m_σ(Wⁿ E) ≤ m_σ(E) + K ∑_{k<n} d(W^k E)` with `K = ℓ (1 + g)^ℓ M₀`. -/
theorem IsTwistSystem.mass_word_pow_le (hH : I.IsTwistSystem H) (σ : Stab) (w : List α)
    (E : Obj) (n : ℕ) :
    I.mass σ (H.word w ^ n • E) ≤ I.mass σ E + w.length * (1 + (H.centreMax : ℝ)) ^ w.length *
      (∑ i, I.mass σ (H.S i)) *
        ∑ k ∈ Finset.range n, (H.centreCount (H.word w ^ k • E) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, Finset.sum_range_succ]
    have h := hH.mass_word_le_centreCount σ w (H.word w ^ n • E)
    calc I.mass σ (H.word w • H.word w ^ n • E)
        ≤ I.mass σ (H.word w ^ n • E) + w.length * (1 + (H.centreMax : ℝ)) ^ w.length *
            (∑ i, I.mass σ (H.S i)) * H.centreCount (H.word w ^ n • E) := h
      _ ≤ (I.mass σ E + w.length * (1 + (H.centreMax : ℝ)) ^ w.length *
            (∑ i, I.mass σ (H.S i)) *
              ∑ k ∈ Finset.range n, (H.centreCount (H.word w ^ k • E) : ℝ)) +
          w.length * (1 + (H.centreMax : ℝ)) ^ w.length *
            (∑ i, I.mass σ (H.S i)) * H.centreCount (H.word w ^ n • E) := by gcongr
      _ = _ := by ring

/-- **The comparison through `d`**: `d(Y) ≤ K (∑_i h(S_i, G)) L_σ m_σ(Y)`. -/
theorem IsTwistSystem.centreCount_le_mul_mass (hH : I.IsTwistSystem H) (σ : Stab) (Y : Obj) :
    (H.centreCount Y : ℝ) ≤
      I.K * (∑ i, I.hom (H.S i) I.G) * I.lowerConst σ * I.mass σ Y := by
  have hsum : 0 ≤ ∑ i, I.hom (H.S i) I.G := Finset.sum_nonneg fun i _ => I.hom_nonneg _ _
  have hL := I.lowerConst_nonneg σ
  have hm := I.mass_nonneg σ Y
  have hK := I.K_pos.le
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : H.centreCount Y = 0 := by simp [HomTwistSystem₀.centreCount, Finset.univ_eq_empty]
    rw [this, Nat.cast_zero]
    positivity
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ι) Finset.univ_nonempty
    (fun i => H.h (H.S i) Y)
  have e : H.centreCount Y = H.h (H.S i) Y := hi
  rw [e, hH.count_eq]
  have h₁ := I.hom_le_mul_mass σ (H.S i) Y
  have h₃ : I.hom (H.S i) I.G ≤ ∑ i, I.hom (H.S i) I.G :=
    Finset.single_le_sum (f := fun i => I.hom (H.S i) I.G) (fun i _ => I.hom_nonneg _ _)
      (Finset.mem_univ i)
  calc I.hom (H.S i) Y ≤ I.K * I.hom (H.S i) I.G * I.lowerConst σ * I.mass σ Y := h₁
    _ ≤ I.K * (∑ i, I.hom (H.S i) I.G) * I.lowerConst σ * I.mass σ Y := by gcongr

/-- If no centre sees `Y`, every letter fixes it: `T_S V = V` when `h(S, V) = 0`. -/
theorem IsTwistSystem.letter_smul_eq_of_centreCount_eq_zero (hH : I.IsTwistSystem H) {Y : Obj}
    (hY : H.centreCount Y = 0) (a : α) : H.T a • Y = Y := by
  have h0 : I.hom (H.S (H.c a)) Y = 0 := by
    rw [← hH.count_eq]
    have := H.le_centreCount (H.c a) Y
    rw [hY, Nat.le_zero] at this
    rw [this, Nat.cast_zero]
  have ht := I.twist_smul_of_hom_eq_zero _ Y (hH.spherical _) h0
  rcases hH.letter a with h | h <;> rw [h]
  · exact ht
  · exact inv_smul_eq_iff.2 ht.symm

theorem IsTwistSystem.word_smul_eq_of_centreCount_eq_zero (hH : I.IsTwistSystem H) {Y : Obj}
    (hY : H.centreCount Y = 0) (w : List α) : H.word w • Y = Y := by
  induction w with
  | nil => rw [HomTwistSystem₀.word_nil, one_smul]
  | cons a w ih =>
    rw [HomTwistSystem₀.word_cons, mul_smul, ih, hH.letter_smul_eq_of_centreCount_eq_zero hY a]

/-- **The fixed-word formula.** For a fixed word `W` of a twist system of spherical objects and an
object `E` of positive mass,
`limsup m_σ(Wⁿ E)^{1/n} = max(1, limsup d(Wⁿ E)^{1/n})`, `d(Y) = max_i h(S_i, Y)`. -/
theorem IsTwistSystem.limsup_mass_pow (hH : I.IsTwistSystem H) (σ : Stab) (w : List α)
    {E : Obj} (hE : 0 < I.mass σ E) :
    limsup (fun n : ℕ => I.mass σ (H.word w ^ n • E) ^ (n : ℝ)⁻¹) atTop =
      max 1 (limsup (fun n : ℕ => (H.centreCount (H.word w ^ n • E) : ℝ) ^ (n : ℝ)⁻¹)
        atTop) := by
  set W := H.word w with hW
  set m : ℕ → ℝ := fun n => I.mass σ (W ^ n • E) with hm
  set d : ℕ → ℝ := fun n => (H.centreCount (W ^ n • E) : ℝ) with hd
  set Q : ℝ := (1 + (H.centreMax : ℝ)) ^ w.length with hQ
  have hQ1 : 1 ≤ Q := one_le_pow₀ (by
    linarith [(Nat.cast_nonneg H.centreMax : (0 : ℝ) ≤ H.centreMax)])
  set M₀ := ∑ i, I.mass σ (H.S i) with hM₀
  have hM₀0 : 0 ≤ M₀ := Finset.sum_nonneg fun i _ => I.mass_nonneg σ _
  set K : ℝ := w.length * (1 + (H.centreMax : ℝ)) ^ w.length * M₀ with hK
  have hK0 : 0 ≤ K := by positivity
  set A : ℝ := max (I.K * (∑ i, I.hom (H.S i) I.G) * I.lowerConst σ) 1 with hA
  have hA1 : 1 ≤ A := le_max_right _ _
  have hA0 : 0 < A := one_pos.trans_le hA1
  -- the basic facts
  have hm0 : ∀ n, 0 < m n := fun n => mass_smul_pos hE (W ^ n)
  have hd0 : ∀ n, 0 ≤ d n := fun n => Nat.cast_nonneg _
  have hmE : m 0 = I.mass σ E := by simp [hm]
  have hm_up : ∀ n, m n ≤ m 0 + K * ∑ k ∈ Finset.range n, d k := fun n => by
    rw [hmE]
    exact hH.mass_word_pow_le σ w E n
  have hd_up : ∀ n, d n ≤ Q ^ n * d 0 := fun n => by
    have := H.centreCount_word_pow_le w E n
    simpa [hd, hQ] using this
  have hdm : ∀ n, d n ≤ A * m n := fun n =>
    (hH.centreCount_le_mul_mass σ _).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hm0 n).le)
  set a : ℕ → ℝ := fun n => m n ^ (n : ℝ)⁻¹ with ha
  set b : ℕ → ℝ := fun n => d n ^ (n : ℝ)⁻¹ with hb
  have ha0 : ∀ n, 0 ≤ a n := fun n => Real.rpow_nonneg (hm0 n).le _
  have hb0 : ∀ n, 0 ≤ b n := fun n => Real.rpow_nonneg (hd0 n) _
  -- `b` is bounded: `d n ≤ (Q (1 + d 0))ⁿ`
  have hb_bdd : ∀ n, b n ≤ Q * (1 + d 0) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [hb, CharP.cast_eq_zero, inv_zero, Real.rpow_zero]
      nlinarith [hd0 0]
    have h1 : d n ≤ (Q * (1 + d 0)) ^ n := by
      calc d n ≤ Q ^ n * d 0 := hd_up n
        _ ≤ Q ^ n * (1 + d 0) ^ n := by
            gcongr
            calc d 0 ≤ 1 + d 0 := by linarith
              _ ≤ (1 + d 0) ^ n := le_self_pow₀ (by linarith [hd0 0]) hn.ne'
        _ = (Q * (1 + d 0)) ^ n := (mul_pow _ _ _).symm
    calc b n ≤ ((Q * (1 + d 0)) ^ n) ^ (n : ℝ)⁻¹ :=
          Real.rpow_le_rpow (hd0 n) h1 (by positivity)
      _ = Q * (1 + d 0) := Real.pow_rpow_inv_natCast (by nlinarith [hd0 0]) hn.ne'
  -- `a` is bounded: `m n ≤ ((1 + m 0 + K d 0) Q)ⁿ`
  have ha_bdd : ∀ n, a n ≤ (1 + m 0 + K * d 0) * Q := by
    intro n
    have hx : 0 ≤ m 0 + K * d 0 := by nlinarith [hm0 0, hd0 0]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [ha, CharP.cast_eq_zero, inv_zero, Real.rpow_zero]
      nlinarith
    have hsum : ∑ k ∈ Finset.range n, d k ≤ n * (Q ^ n * d 0) := by
      calc ∑ k ∈ Finset.range n, d k ≤ ∑ _k ∈ Finset.range n, Q ^ n * d 0 :=
            Finset.sum_le_sum fun k hk => (hd_up k).trans
              (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ1 (Finset.mem_range.1 hk).le)
                (hd0 0))
        _ = n * (Q ^ n * d 0) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hQn : 1 ≤ Q ^ n := one_le_pow₀ hQ1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hbern : 1 + n * (m 0 + K * d 0) ≤ (1 + (m 0 + K * d 0)) ^ n :=
      one_add_mul_le_pow (by linarith) n
    have h1 : m n ≤ ((1 + m 0 + K * d 0) * Q) ^ n := by
      calc m n ≤ m 0 + K * (n * (Q ^ n * d 0)) :=
            (hm_up n).trans (by gcongr)
        _ ≤ (1 + n * (m 0 + K * d 0)) * Q ^ n := by
            have h2 : m 0 ≤ m 0 * Q ^ n := le_mul_of_one_le_right (hm0 0).le hQn
            have h3 : 0 ≤ K * d 0 := mul_nonneg hK0 (hd0 0)
            have h4 : m 0 * Q ^ n ≤ n * m 0 * Q ^ n := by
              have : 0 ≤ m 0 * Q ^ n := mul_nonneg (hm0 0).le (pow_nonneg (by linarith) n)
              nlinarith
            nlinarith
        _ ≤ (1 + (m 0 + K * d 0)) ^ n * Q ^ n := by gcongr
        _ = ((1 + m 0 + K * d 0) * Q) ^ n := by rw [← mul_pow, add_assoc]
    calc a n ≤ (((1 + m 0 + K * d 0) * Q) ^ n) ^ (n : ℝ)⁻¹ :=
          Real.rpow_le_rpow (hm0 n).le h1 (by positivity)
      _ = (1 + m 0 + K * d 0) * Q :=
          Real.pow_rpow_inv_natCast (mul_nonneg (by linarith) (by linarith)) hn.ne'
  have hbB : IsBoundedUnder (· ≤ ·) atTop b :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hb_bdd)
  have haB : IsBoundedUnder (· ≤ ·) atTop a :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall ha_bdd)
  have hbC : IsCoboundedUnder (· ≤ ·) atTop b := isCoboundedUnder_le_of_le atTop hb0
  have haC : IsCoboundedUnder (· ≤ ·) atTop a := isCoboundedUnder_le_of_le atTop ha0
  set L := limsup b atTop with hL
  show limsup a atTop = max 1 L
  apply le_antisymm
  · -- the upper bound
    refine le_of_forall_gt_imp_ge_of_dense fun R hR => ?_
    obtain ⟨R', hR'1, hR'2⟩ := exists_between hR
    have hR'one : 1 < R' := lt_of_le_of_lt (le_max_left _ _) hR'1
    have hLR' : L < R' := lt_of_le_of_lt (le_max_right _ _) hR'1
    have hR'0 : 0 < R' := one_pos.trans hR'one
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((eventually_lt_of_limsup_lt hLR' hbB).and (eventually_ne_atTop 0))
    set C₀ := ∑ k ∈ Finset.range N, d k with hC₀
    have hC₀0 : 0 ≤ C₀ := Finset.sum_nonneg fun k _ => hd0 k
    have hdk : ∀ k, d k ≤ C₀ + R' ^ k := by
      intro k
      rcases lt_or_ge k N with hk | hk
      · have := Finset.single_le_sum (f := d) (fun i _ => hd0 i) (Finset.mem_range.2 hk)
        linarith [pow_nonneg hR'0.le k]
      · obtain ⟨h1, h2⟩ := hN k hk
        have := (Real.rpow_inv_le_iff_of_pos (hd0 k) hR'0.le
          (by exact_mod_cast Nat.pos_of_ne_zero h2)).1 h1.le
        rw [Real.rpow_natCast] at this
        linarith
    set c := K * (C₀ + 1) with hc
    have hc0 : 0 ≤ c := by positivity
    have hmn : ∀ n : ℕ, m n ≤ (1 + m 0 + c * n) * R' ^ n := by
      intro n
      have hRn : 1 ≤ R' ^ n := one_le_pow₀ hR'one.le
      have hsum : ∑ k ∈ Finset.range n, d k ≤ n * (C₀ + R' ^ n) := by
        calc ∑ k ∈ Finset.range n, d k ≤ ∑ _k ∈ Finset.range n, (C₀ + R' ^ n) :=
              Finset.sum_le_sum fun k hk => (hdk k).trans (by
                gcongr
                · exact hR'one.le
                · exact (Finset.mem_range.1 hk).le)
          _ = n * (C₀ + R' ^ n) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      calc m n ≤ m 0 + K * (n * (C₀ + R' ^ n)) := (hm_up n).trans (by gcongr)
        _ ≤ (1 + m 0 + c * n) * R' ^ n := by
            rw [hc]
            have h1 : m 0 ≤ m 0 * R' ^ n := le_mul_of_one_le_right (hm0 0).le hRn
            have h2 : K * n * C₀ ≤ K * n * C₀ * R' ^ n :=
              le_mul_of_one_le_right (mul_nonneg (mul_nonneg hK0 hn0) hC₀0) hRn
            nlinarith
    have hpoly : Tendsto (fun n : ℕ => (1 + m 0 + c * n) ^ (n : ℝ)⁻¹) atTop (𝓝 1) := by
      have hpos : ∀ n : ℕ, 0 ≤ c * n := fun n => mul_nonneg hc0 (Nat.cast_nonneg n)
      have h := Real.tendsto_rpow_inv_of_log_div (H := fun n : ℕ => 1 + m 0 + c * n)
        (fun n => by linarith [hm0 0, hpos n])
        (Real.tendsto_log_div_zero_of_poly (A := 1 + m 0) (B := c)
          (fun n => by linarith [hm0 0, hpos n])
          (fun n => by
            have hq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
              rcases Nat.eq_zero_or_pos n with h0 | h0
              · simp [h0]
              · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
                nlinarith
            have := mul_le_mul_of_nonneg_left hq hc0
            linarith))
      rwa [Real.exp_zero] at h
    have hlim' : Tendsto (fun n : ℕ => (1 + m 0 + c * n) ^ (n : ℝ)⁻¹ * R') atTop (𝓝 R') := by
      simpa using hpoly.mul_const R'
    refine limsup_le_of_le haC ?_
    filter_upwards [hlim'.eventually (gt_mem_nhds hR'2), eventually_ne_atTop 0] with n hn hn0
    refine le_trans ?_ hn.le
    calc a n = m n ^ (n : ℝ)⁻¹ := rfl
      _ ≤ ((1 + m 0 + c * n) * R' ^ n) ^ (n : ℝ)⁻¹ :=
          Real.rpow_le_rpow (hm0 n).le (hmn n) (by positivity)
      _ = (1 + m 0 + c * n) ^ (n : ℝ)⁻¹ * R' := by
          have : 0 ≤ 1 + m 0 + c * n := by
            linarith [hm0 0, mul_nonneg hc0 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
          rw [Real.mul_rpow this (by positivity), Real.pow_rpow_inv_natCast hR'0.le hn0]
  · -- the lower bound
    refine le_of_forall_lt_imp_le_of_dense fun R hR => ?_
    refine le_limsup_of_frequently_le ?_ haB
    rcases lt_or_ge R 1 with hR1 | hR1
    · -- the masses stay above a positive constant, so their roots tend to one
      obtain ⟨c₀, hc₀, hev⟩ : ∃ c₀ > 0, ∀ᶠ n in atTop, c₀ ≤ m n := by
        by_cases hall : ∀ n, 1 ≤ d n
        · refine ⟨1 / A, by positivity, Eventually.of_forall fun n => ?_⟩
          rw [div_le_iff₀ hA0]
          linarith [hdm n, hall n]
        · push Not at hall
          obtain ⟨N, hN⟩ := hall
          have hN0 : H.centreCount (W ^ N • E) = 0 := by
            have h1 : (H.centreCount (W ^ N • E) : ℝ) < 1 := hN
            exact Nat.lt_one_iff.1 (by exact_mod_cast h1)
          have hfix : ∀ k : ℕ, W ^ k • (W ^ N • E) = W ^ N • E := by
            intro k
            induction k with
            | zero => rw [pow_zero, one_smul]
            | succ k ih =>
              rw [pow_succ', mul_smul, ih, hW]
              exact hH.word_smul_eq_of_centreCount_eq_zero hN0 w
          refine ⟨m N, hm0 N, ?_⟩
          filter_upwards [eventually_ge_atTop N] with n hn
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
          have e : W ^ (N + k) • E = W ^ N • E := by
            rw [add_comm, pow_add, mul_smul, hfix k]
          show I.mass σ (W ^ N • E) ≤ I.mass σ (W ^ (N + k) • E)
          rw [e]
      have hlim : Tendsto (fun n : ℕ => c₀ ^ (n : ℝ)⁻¹) atTop (𝓝 1) :=
        Real.tendsto_const_rpow_inv hc₀
      refine Eventually.frequently ?_
      filter_upwards [hev, hlim.eventually (lt_mem_nhds hR1)] with n hn h1
      calc R ≤ c₀ ^ (n : ℝ)⁻¹ := h1.le
        _ ≤ m n ^ (n : ℝ)⁻¹ := Real.rpow_le_rpow hc₀.le hn (by positivity)
    · -- frequently `d n > R''ⁿ`, and `m n ≥ d n / A`
      have hRL : R < L := by
        rcases lt_max_iff.1 hR with h | h
        · linarith
        · exact h
      obtain ⟨R'', hR''1, hR''2⟩ := exists_between hRL
      have hR''0 : 0 < R'' := by linarith
      have hfreq := frequently_lt_of_lt_limsup hbC hR''2
      have hlimA : Tendsto (fun n : ℕ => A⁻¹ ^ (n : ℝ)⁻¹ * R'') atTop (𝓝 R'') := by
        simpa using (Real.tendsto_const_rpow_inv (inv_pos.2 hA0)).mul_const R''
      refine (hfreq.and_eventually ((hlimA.eventually (lt_mem_nhds hR''1)).and
        (eventually_ne_atTop 0))).mono ?_
      rintro n ⟨hbn, hRn, hn0⟩
      have hdn : R'' ^ n < d n := by
        have h1 : R'' ^ n < (b n) ^ n := pow_lt_pow_left₀ hbn hR''0.le hn0
        rwa [hb, Real.rpow_inv_natCast_pow (hd0 n) hn0] at h1
      have hmn : A⁻¹ * R'' ^ n ≤ m n := by
        rw [inv_mul_le_iff₀ hA0]
        linarith [hdm n]
      calc R ≤ A⁻¹ ^ (n : ℝ)⁻¹ * R'' := hRn.le
        _ = (A⁻¹ * R'' ^ n) ^ (n : ℝ)⁻¹ := by
            rw [Real.mul_rpow (by positivity) (by positivity),
              Real.pow_rpow_inv_natCast hR''0.le hn0]
        _ ≤ m n ^ (n : ℝ)⁻¹ := Real.rpow_le_rpow (by positivity) hmn (by positivity)

end MassComparisonHypotheses
