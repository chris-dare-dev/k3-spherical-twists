/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.GroupAction.MassComparison

/-!
# Mass growth under a set of spherical twists: Theorem C

For a twist system of spherical objects (`MassComparisonHypotheses.IsTwistSystem`) with an
inverse-closed alphabet, split the centres into components that are pairwise Ext-orthogonal. For
an object `E` and a stability condition `σ`, let `M_n(E) = max_{|W| = n} m_σ(W E)` over the words of
length exactly `n`. **Theorem C**:

  `lim log M_n(E)/n = max({0} ∪ {η_B : B meets E})`,

where `η_B` is the exponent of the centre counts of the component `B` (the twist-system exponent
theorem for the subsystem of `B`) and `B` meets `E` when `Ext^*(S, E) ≠ 0` for some centre `S`
of `B` (`MassComparisonHypotheses.IsTwistSystem.tendsto_log_lenMax`). The proof has three parts:

* **(3a) σ-independence**: `m_σ ≤ e^{δ(σ, τ)} m_τ` moves `M_n(E)` by a bounded factor, so its rate
  does not depend on `σ` (`MassComparisonHypotheses.lenMax_le_exp_δ`,
  `tendsto_log_lenMax_iff`).
* **(3b) component decomposition**: twists at Ext-orthogonal centres commute, by the conjugation
  formula (`MassComparisonHypotheses.twist_commute`), so a word is the product of its subword in
  the letters of a component `B` and of the rest (`List.prod_map_eq_filter_mul_filter`), and the
  rest fixes the centres of `B`; hence `h(S, W E) = h(S, W_B E)` for every centre `S` of `B`
  (`MassComparisonHypotheses.IsTwistSystem.hom_word_eq_hom_filter`).
* **The analytic core**: the mass form of the one-letter bound gives
  `M_n(E) ≤ m(E) + C n Σ_{B meets E} M^B_n`, the lower bound (L_m) along connecting chains gives
  `M^B_q ≤ 2^{d+1} max_{k ≤ q+d+1} M_k(E)` for every `B` that meets `E`, and padding with a
  one-sided step bound turns the running maximum into `M_n(E)`
  (`Real.tendsto_log_div_of_family`, with `Real.tendsto_log_div_of_runningMax`).

The file also contains the formal envelope over any monoid (the extremal function
`μ₀ = sup_k e^{-ηk} M_k`: `extremal_smul_le`, `le_extremal`, `extremal_tri`,
`lenMax_le_of_subeigen`), whose only content is `BddAbove (e^{-ηk} M_k(P))`, and the periodic
witness (`HomTwistSystem.le_homExponent_of_theta`): for two centres with `M = h(S, B) ≥ 2`, the
word `(T_S T_B)ⁿ` gives `η ≥ log(M - 1)`.

## Main definitions

* `Monoid.lenMax T m k P`: `M_k(P) = max_{|W| = k} m(W P)`.
* `Monoid.extremal T m η P`: `μ₀(P) = sup_k e^{-ηk} M_k(P)`.
* `HomTwistSystem₀.restrict H p`: the subsystem on the centres where `p` holds.

## Tags

mass growth, spherical twist, joint spectral radius, Rota–Strang
-/

open Filter Topology Real Finset

/-! ### Words of a fixed length in a monoid -/

namespace Monoid

section WordMax

variable {M Obj α : Type*} [Monoid M] [MulAction M Obj] [Fintype α] [Nonempty α]

/-- `M_k(P) = max_{|W| = k} m(W P)` over the words `W` of length exactly `k` in the letters `T`. -/
noncomputable def lenMax (T : α → M) (m : Obj → ℝ) (k : ℕ) (P : Obj) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun w : Fin k → α => m ((List.ofFn (T ∘ w)).prod • P)

lemma lenMax_zero (T : α → M) (m : Obj → ℝ) (P : Obj) : lenMax T m 0 P = m P := by
  simp [lenMax, Finset.univ_unique]

lemma le_lenMax (T : α → M) (m : Obj → ℝ) {k : ℕ} (w : Fin k → α) (P : Obj) :
    m ((List.ofFn (T ∘ w)).prod • P) ≤ lenMax T m k P :=
  Finset.le_sup' (fun w : Fin k → α => m ((List.ofFn (T ∘ w)).prod • P)) (Finset.mem_univ w)

/-- Every word of length `k`, given as a list, is bounded by `M_k`. -/
lemma le_lenMax_list (T : α → M) (m : Obj → ℝ) (l : List α) (P : Obj) :
    m ((l.map T).prod • P) ≤ lenMax T m l.length P := by
  have := le_lenMax T m l.get P
  have e : List.ofFn (T ∘ l.get) = l.map T := by rw [← List.map_ofFn, List.ofFn_get]
  rwa [e] at this

lemma exists_lenMax_eq (T : α → M) (m : Obj → ℝ) (k : ℕ) (P : Obj) :
    ∃ l : List α, l.length = k ∧ lenMax T m k P = m ((l.map T).prod • P) := by
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty
    (fun w : Fin k → α => m ((List.ofFn (T ∘ w)).prod • P))
  refine ⟨List.ofFn w, by simp, ?_⟩
  rw [lenMax, hw, List.map_ofFn]

lemma lenMax_smul_le (T : α → M) (m : Obj → ℝ) (k : ℕ) (a : α) (P : Obj) :
    lenMax T m k (T a • P) ≤ lenMax T m (k + 1) P := by
  refine Finset.sup'_le _ _ fun w _ => ?_
  have e : (List.ofFn (T ∘ (Fin.snoc w a : Fin (k + 1) → α))).prod =
      (List.ofFn (T ∘ w)).prod * T a := by
    rw [List.ofFn_succ', List.prod_concat]
    simp [Function.comp_def]
  have := le_lenMax T m (Fin.snoc w a : Fin (k + 1) → α) P
  rwa [e, mul_smul] at this

/-- `μ₀(P) = sup_k e^{-ηk} M_k(P)`, the extremal function of the Rota–Strang envelope. -/
noncomputable def extremal (T : α → M) (m : Obj → ℝ) (η : ℝ) (P : Obj) : ℝ :=
  ⨆ k : ℕ, exp (-(η * k)) * lenMax T m k P

variable (T : α → M) (m : Obj → ℝ) (η : ℝ)

/-- `μ₀` dominates `m`, once the envelope is bounded. -/
theorem le_extremal {P : Obj}
    (hbdd : BddAbove (Set.range fun k : ℕ => exp (-(η * k)) * lenMax T m k P)) :
    m P ≤ extremal T m η P := by
  have := le_ciSup hbdd 0
  unfold extremal
  simpa [lenMax_zero] using this

/-- **`μ₀` is a sub-eigenfunction**: every letter multiplies it by at most `e^η`. -/
theorem extremal_smul_le
    (hbdd : ∀ P, BddAbove (Set.range fun k : ℕ => exp (-(η * k)) * lenMax T m k P))
    (a : α) (P : Obj) : extremal T m η (T a • P) ≤ exp η * extremal T m η P := by
  refine ciSup_le fun k => ?_
  calc exp (-(η * k)) * lenMax T m k (T a • P)
      ≤ exp (-(η * k)) * lenMax T m (k + 1) P := by gcongr; exact lenMax_smul_le T m k a P
    _ = exp η * (exp (-(η * ((k + 1 : ℕ) : ℝ))) * lenMax T m (k + 1) P) := by
        rw [← mul_assoc, ← exp_add]; push_cast; ring_nf
    _ ≤ exp η * extremal T m η P := by
        gcongr
        exact le_ciSup (hbdd P) (k + 1)

/-- **`μ₀` inherits subadditivity on triangles.** The relation `Tri` must be invariant under every
element of the monoid, not only under the letters; this holds for triangles under
autoequivalences. -/
theorem extremal_tri {Tri : Obj → Obj → Obj → Prop}
    (hTri : ∀ (g : M) X Y Z, Tri X Y Z → Tri (g • X) (g • Y) (g • Z))
    (hm : ∀ X Y Z, Tri X Y Z → m Y ≤ m X + m Z)
    (hbdd : ∀ P, BddAbove (Set.range fun k : ℕ => exp (-(η * k)) * lenMax T m k P))
    {X Y Z : Obj} (h : Tri X Y Z) :
    extremal T m η Y ≤ extremal T m η X + extremal T m η Z := by
  refine ciSup_le fun k => ?_
  have hk : lenMax T m k Y ≤ lenMax T m k X + lenMax T m k Z := by
    refine Finset.sup'_le _ _ fun w _ => ?_
    exact (hm _ _ _ (hTri _ _ _ _ h)).trans (add_le_add (le_lenMax T m w X) (le_lenMax T m w Z))
  calc exp (-(η * k)) * lenMax T m k Y
      ≤ exp (-(η * k)) * lenMax T m k X + exp (-(η * k)) * lenMax T m k Z := by
        rw [← mul_add]; gcongr
    _ ≤ _ := add_le_add (le_ciSup (hbdd X) k) (le_ciSup (hbdd Z) k)

/-- **Rota–Strang, the easy direction**: a sub-eigenfunction `μ` comparable to `m` bounds the
growth, `M_k(P) ≤ (C/c) λ^k m(P)`. -/
theorem lenMax_le_of_subeigen {μ : Obj → ℝ} {c C lam : ℝ} (hc : 0 < c) (hlam : 0 ≤ lam)
    (hμ : ∀ a P, μ (T a • P) ≤ lam * μ P) (hlow : ∀ P, c * m P ≤ μ P)
    (hhigh : ∀ P, μ P ≤ C * m P) (k : ℕ) (P : Obj) :
    lenMax T m k P ≤ C / c * lam ^ k * m P := by
  have hword : ∀ (k : ℕ) (w : Fin k → α) (P : Obj),
      μ ((List.ofFn (T ∘ w)).prod • P) ≤ lam ^ k * μ P := by
    intro k
    induction k with
    | zero => intro w P; simp
    | succ k ih =>
      intro w P
      rw [List.ofFn_succ, List.prod_cons, mul_smul]
      calc μ ((T ∘ w) 0 • (List.ofFn fun i => (T ∘ w) i.succ).prod • P)
          ≤ lam * μ ((List.ofFn fun i => (T ∘ w) i.succ).prod • P) := hμ _ _
        _ ≤ lam * (lam ^ k * μ P) := by
            gcongr
            exact ih (fun i => w i.succ) P
        _ = lam ^ (k + 1) * μ P := by ring
  refine Finset.sup'_le _ _ fun w _ => ?_
  have h1 := hlow ((List.ofFn (T ∘ w)).prod • P)
  have h2 := hword k w P
  have h3 := hhigh P
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc]
  have : 0 ≤ lam ^ k := pow_nonneg hlam k
  nlinarith

end WordMax

end Monoid

/-! ### Products over a split word -/

/-- If the letters where `p` holds commute with those where it fails, the product of a word is the
product of its `p`-subword times the product of the rest. -/
theorem List.prod_map_eq_filter_mul_filter {M α : Type*} [Monoid M] (f : α → M) (p : α → Bool)
    (hcomm : ∀ a b, p a = true → p b = false → Commute (f a) (f b)) :
    ∀ l : List α, (l.map f).prod =
      ((l.filter p).map f).prod * ((l.filter fun a => !p a).map f).prod
  | [] => by simp
  | a :: l => by
    have ih := List.prod_map_eq_filter_mul_filter f p hcomm l
    cases ha : p a
    · have hc : Commute (f a) ((l.filter p).map f).prod := by
        refine Commute.list_prod_right _ _ fun y hy => ?_
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
        exact (hcomm b a (List.mem_filter.mp hb).2 ha).symm
      simp only [List.map_cons, List.prod_cons, List.filter_cons, ha, Bool.not_false,
        ite_true, Bool.false_eq_true, ite_false, ih]
      rw [← mul_assoc, hc.eq, mul_assoc]
    · simp only [List.map_cons, List.prod_cons, List.filter_cons, ha, ite_true, Bool.not_true,
        Bool.false_eq_true, ite_false, ih, mul_assoc]

/-! ### Subsystems -/

namespace HomTwistSystem₀

variable {G Obj ι α : Type*} [Group G] [MulAction G Obj] (H : HomTwistSystem₀ G Obj ι α)

/-- The **subsystem** on the centres where `p` holds, with the letters whose centre is one of
them. -/
def restrict (p : ι → Prop) : HomTwistSystem₀ G Obj {i // p i} {a // p (H.c a)} where
  S i := H.S i
  T a := H.T a
  c a := ⟨H.c a, a.2⟩
  h := H.h
  h_smul := H.h_smul
  upper a U V := H.upper a U V

lemma restrict_word (p : ι → Prop) (w : List {a // p (H.c a)}) :
    (H.restrict p).word w = H.word (w.map Subtype.val) := by
  simp only [word, List.map_map]
  rfl

lemma lowerBound_restrict (hL : H.LowerBound) (p : ι → Prop) : (H.restrict p).LowerBound :=
  fun a U Y => hL a.1 U Y

lemma isSpherical_restrict (hsph : H.IsSpherical) (p : ι → Prop) : (H.restrict p).IsSpherical :=
  fun i => hsph i.1

/-- The inverse of the product of a word is the product of the reversed word of inverse letters. -/
lemma word_reverse_map_inv (inv : α → α) (hinv : ∀ a, H.T (inv a) = (H.T a)⁻¹) :
    ∀ u : List α, H.word (u.reverse.map inv) = (H.word u)⁻¹
  | [] => by simp
  | a :: u => by
    rw [List.reverse_cons, List.map_append, word_append, word_reverse_map_inv inv hinv u,
      word_cons, mul_inv_rev]
    simp [word, hinv]

end HomTwistSystem₀

/-- Lift a list whose entries satisfy `p` to the subtype. -/
def List.liftSubtype {α : Type*} (p : α → Prop) : (u : List α) → (∀ a ∈ u, p a) → List {a // p a}
  | [], _ => []
  | a :: u, h => ⟨a, h a (by simp)⟩ :: List.liftSubtype p u fun b hb => h b (by simp [hb])

lemma List.map_val_liftSubtype {α : Type*} (p : α → Prop) :
    ∀ (u : List α) (h : ∀ a ∈ u, p a), (List.liftSubtype p u h).map Subtype.val = u
  | [], _ => rfl
  | a :: u, h => by simp [List.liftSubtype, List.map_val_liftSubtype p u]

lemma List.length_liftSubtype {α : Type*} (p : α → Prop) (u : List α) (h : ∀ a ∈ u, p a) :
    (List.liftSubtype p u h).length = u.length := by
  rw [← List.length_map (f := Subtype.val), List.map_val_liftSubtype]

/-! ### The analytic core -/

/-- **Rates from a finite family through a running maximum.** Let `x_n ≥ c > 0` with the one-sided
step bound `x_n ≤ L x_{n+1}`, and `B` a running maximum of `x`. Let `A_b`, `b ∈ s`, be positive
sequences with rates `η_b`, such that `x_n ≤ C₀ + C₁ n Σ_b A_b(n)` and
`A_b(n) ≤ C₂ B(n + D)`. Then `log x_n / n → max({0} ∪ {η_b})`. -/
theorem Real.tendsto_log_div_of_family {β : Type*} (s : Finset β) {x B : ℕ → ℝ}
    {A : β → ℕ → ℝ} {η : β → ℝ} {c L C₀ C₁ C₂ : ℝ} {D : ℕ} (hc : 0 < c) (hx : ∀ n, c ≤ x n)
    (hL : 1 ≤ L) (hstep : ∀ n, x n ≤ L * x (n + 1)) (hxB : ∀ n, x n ≤ B n)
    (hBatt : ∀ n, ∃ k ≤ n, B n ≤ x k) (hA : ∀ b ∈ s, ∀ n, 0 < A b n)
    (hrate : ∀ b ∈ s, Tendsto (fun n : ℕ => log (A b n) / n) atTop (𝓝 (η b)))
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 < C₂)
    (hup : ∀ n, x n ≤ C₀ + C₁ * n * ∑ b ∈ s, A b n)
    (hlow : ∀ b ∈ s, ∀ n, A b n ≤ C₂ * B (n + D)) :
    Tendsto (fun n : ℕ => log (x n) / n) atTop (𝓝 (sSup (insert 0 (η '' (s : Set β))))) := by
  set ηs := sSup (insert 0 (η '' (s : Set β))) with hηs
  have hfin : (insert 0 (η '' (s : Set β)) : Set ℝ).Finite := (s.finite_toSet.image η).insert 0
  have hbdd := hfin.bddAbove
  have h0le : 0 ≤ ηs := le_csSup hbdd (Set.mem_insert _ _)
  have hble : ∀ b ∈ s, η b ≤ ηs := fun b hb =>
    le_csSup hbdd (Set.mem_insert_of_mem _ ⟨b, hb, rfl⟩)
  have hmem : ηs ∈ insert 0 (η '' (s : Set β)) := (Set.insert_nonempty _ _).csSup_mem hfin
  have hxpos : ∀ n, 0 < x n := fun n => lt_of_lt_of_le hc (hx n)
  have hBpos : ∀ n, 0 < B n := fun n => lt_of_lt_of_le (hxpos n) (hxB n)
  refine tendsto_log_div_of_runningMax hc hx hL hstep hxB hBatt ?_
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b' hb' => ?_⟩
  · rcases hmem with h | ⟨b, hb, hbη⟩
    · rw [h] at ha
      have hc0 : Tendsto (fun n : ℕ => log c / n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      filter_upwards [hc0.eventually (lt_mem_nhds ha)] with n hn
      exact hn.trans_le (div_le_div_of_nonneg_right
        (log_le_log hc ((hx n).trans (hxB n))) (Nat.cast_nonneg _))
    · rw [← hbη] at ha
      set a' := (a + η b) / 2 with ha'
      have h1 := (hrate b hb).eventually (lt_mem_nhds (show a' < η b by rw [ha']; linarith))
      obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 h1
      have herr : Tendsto (fun n : ℕ => (a' * D + log C₂) / n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      filter_upwards [eventually_ge_atTop (N₁ + 1 + D),
        herr.eventually (gt_mem_nhds (show (0 : ℝ) < a' - a by rw [ha']; linarith))]
        with n hn hn'
      obtain ⟨m, rfl⟩ : ∃ m, n = m + D := ⟨n - D, by omega⟩
      have hm1 : N₁ ≤ m := by omega
      have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hnpos : (0 : ℝ) < (m + D : ℕ) := by exact_mod_cast (show 0 < m + D by omega)
      have hA1 : a' * m < log (A b m) := by
        have := hN₁ m hm1
        rwa [lt_div_iff₀ hmpos] at this
      have hA2 : log (A b m) ≤ log C₂ + log (B (m + D)) := by
        rw [← log_mul hC₂.ne' (hBpos _).ne']
        exact log_le_log (hA b hb m) (hlow b hb m)
      have hn'' : a' * D + log C₂ < (a' - a) * ((m + D : ℕ) : ℝ) := by
        have := hn'
        rwa [div_lt_iff₀ hnpos] at this
      rw [lt_div_iff₀ hnpos]
      have hcast : ((m + D : ℕ) : ℝ) = m + D := by push_cast; ring
      rw [hcast] at hn'' ⊢
      nlinarith
  · set b'' := (ηs + b') / 2 with hb''
    have hb''pos : 0 < b'' := by rw [hb'']; linarith
    have hev : ∀ᶠ n in atTop, ∀ b ∈ s, log (A b n) / n < b'' :=
      (Filter.eventually_all_finset s).2 fun b hb =>
        (hrate b hb).eventually (gt_mem_nhds (by have := hble b hb; rw [hb'']; linarith))
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
    set M : ℝ := ∑ b ∈ s, ∑ k ∈ Finset.range (N₀ + 1), A b k with hM
    have hM0 : 0 ≤ M := Finset.sum_nonneg fun b hb =>
      Finset.sum_nonneg fun k _ => (hA b hb k).le
    have hsum : ∀ k : ℕ, ∑ b ∈ s, A b k ≤ M + s.card * exp (b'' * k) := by
      intro k
      rcases le_or_gt k N₀ with hk | hk
      · have : ∑ b ∈ s, A b k ≤ M :=
          Finset.sum_le_sum fun b hb => Finset.single_le_sum (f := fun k => A b k)
            (fun k _ => (hA b hb k).le) (Finset.mem_range.2 (by omega))
        have : (0 : ℝ) ≤ s.card * exp (b'' * k) := by positivity
        linarith
      · have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
        have : ∑ b ∈ s, A b k ≤ ∑ _b ∈ s, exp (b'' * k) := Finset.sum_le_sum fun b hb => by
          have := hN₀ k hk.le b hb
          rw [div_lt_iff₀ hkpos, mul_comm] at this
          rw [mul_comm b'']
          exact ((log_lt_iff_lt_exp (hA b hb k)).mp this).le
        rw [Finset.sum_const, nsmul_eq_mul] at this
        linarith
    set K : ℝ := C₀ + C₁ * (M + s.card) + 1 with hK
    have hKpos : 0 < K := by rw [hK]; positivity
    have hxk : ∀ k : ℕ, x k ≤ K * ((k : ℝ) + 1) * exp (b'' * k) := by
      intro k
      have he1 : 1 ≤ exp (b'' * k) := one_le_exp (by positivity)
      have h1 := hup k
      have h2 := hsum k
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      calc x k ≤ C₀ + C₁ * k * ∑ b ∈ s, A b k := h1
        _ ≤ C₀ + C₁ * k * (M + s.card * exp (b'' * k)) := by gcongr
        _ ≤ K * ((k : ℝ) + 1) * exp (b'' * k) := by
            rw [hK]
            set E := exp (b'' * k)
            have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
            have hE0 : 0 ≤ E := (exp_pos _).le
            have h1 : C₀ ≤ C₀ * E := le_mul_of_one_le_right hC₀ he1
            have h2 : C₁ * k * M ≤ C₁ * k * M * E :=
              le_mul_of_one_le_right (by positivity) he1
            have n1 : 0 ≤ C₀ * k * E := by positivity
            have n2 : 0 ≤ C₁ * M * E := by positivity
            have n3 : 0 ≤ C₁ * s.card * E := by positivity
            have n4 : 0 ≤ ((k : ℝ) + 1) * E := by positivity
            nlinarith
    have hBn : ∀ n : ℕ, B n ≤ K * ((n : ℝ) + 1) * exp (b'' * n) := by
      intro n
      obtain ⟨k, hkn, hk⟩ := hBatt n
      have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
      refine hk.trans ((hxk k).trans ?_)
      gcongr
    have herr : Tendsto (fun n : ℕ => (log K + log ((n : ℝ) + 1)) / n) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => log K / n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun n : ℕ => log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
        have h3 : Tendsto (fun n : ℕ => log ((n : ℝ) + 1) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
          have := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
            (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
          refine this.congr fun n => ?_
          simp
        have h4 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
          have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
            tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
          rw [add_zero] at this
          refine this.congr' ?_
          filter_upwards [eventually_gt_atTop 0] with n hn
          have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
          field_simp
        have := h3.mul h4
        rw [zero_mul] at this
        refine this.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with n hn
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp
      have := h1.add h2
      rw [add_zero] at this
      exact this.congr fun n => by rw [add_div]
    filter_upwards [herr.eventually (gt_mem_nhds (show (0 : ℝ) < b' - b'' by rw [hb'']; linarith)),
      eventually_gt_atTop 0] with n hn hnpos
    have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hlog : log (B n) ≤ log K + log ((n : ℝ) + 1) + b'' * n := by
      have := log_le_log (hBpos n) (hBn n)
      rwa [log_mul (by positivity) (exp_pos _).ne', log_mul hKpos.ne' (by positivity),
        log_exp] at this
    rw [div_lt_iff₀ hn']
    rw [div_lt_iff₀ hn'] at hn
    nlinarith

/-! ### Theorem C -/

namespace MassComparisonHypotheses

variable {Obj Γ Stab κ : Type*} [Group Γ] [MulAction Γ Obj] [MulAction Γ Stab] [Fintype κ]
  {I : MassComparisonHypotheses Obj Γ Stab κ} {ι α : Type*} {H : HomTwistSystem₀ Γ Obj ι α}

/-! #### (3a): σ-independence -/

section Independence

variable [Fintype α] [Nonempty α]

variable (I) in
/-- `M_n(E)` at `σ` is at most `e^{δ(σ, τ)}` times `M_n(E)` at `τ`. -/
theorem lenMax_le_exp_δ (T : α → Γ) (σ τ : Stab) (n : ℕ) (E : Obj) :
    Monoid.lenMax T (I.mass σ) n E ≤ exp (I.δ σ τ) * Monoid.lenMax T (I.mass τ) n E := by
  refine Finset.sup'_le _ _ fun w _ => (I.mass_le_exp_δ σ τ _).trans ?_
  gcongr
  exact Monoid.le_lenMax T (I.mass τ) w E

variable (I) in
/-- **(3a) σ-independence of the growth rate.** If `M_n(E) > 0` at `σ`, its exponential rate is the
same at every `τ`: the two differ by at most `δ(σ, τ)/n`. -/
theorem tendsto_log_lenMax_iff (T : α → Γ) (σ τ : Stab) (E : Obj)
    (hpos : ∀ n, 0 < Monoid.lenMax T (I.mass σ) n E) (η : ℝ) :
    Tendsto (fun n : ℕ => log (Monoid.lenMax T (I.mass σ) n E) / n) atTop (𝓝 η) ↔
      Tendsto (fun n : ℕ => log (Monoid.lenMax T (I.mass τ) n E) / n) atTop (𝓝 η) := by
  have h₁ : ∀ n, Monoid.lenMax T (I.mass σ) n E ≤
      exp (I.δ σ τ) * Monoid.lenMax T (I.mass τ) n E := fun n => I.lenMax_le_exp_δ T σ τ n E
  have h₂ : ∀ n, Monoid.lenMax T (I.mass τ) n E ≤
      exp (I.δ σ τ) * Monoid.lenMax T (I.mass σ) n E := fun n => by
    rw [I.δ_symm]; exact I.lenMax_le_exp_δ T τ σ n E
  have hpos' : ∀ n, 0 < Monoid.lenMax T (I.mass τ) n E := fun n => by
    have := h₁ n
    have := hpos n
    by_contra hle
    have : Monoid.lenMax T (I.mass τ) n E ≤ 0 := not_lt.mp hle
    nlinarith [exp_pos (I.δ σ τ)]
  exact ⟨Real.tendsto_log_div_of_le_exp_mul hpos hpos' h₁ h₂,
    Real.tendsto_log_div_of_le_exp_mul hpos' hpos h₂ h₁⟩

end Independence

namespace IsTwistSystem

variable (hH : I.IsTwistSystem H)
include hH

/-! #### (3b): the component decomposition -/

/-- A letter fixes every object that is Ext-orthogonal to its centre. -/
theorem letter_smul_of_hom_eq_zero (a : α) {V : Obj} (h : I.hom (H.S (H.c a)) V = 0) :
    H.T a • V = V := by
  rcases hH.letter a with e | e <;> rw [e]
  · exact I.twist_smul_of_hom_eq_zero _ V (hH.spherical _) h
  · rw [inv_smul_eq_iff]
    exact (I.twist_smul_of_hom_eq_zero _ V (hH.spherical _) h).symm

/-- A word fixes every object that is Ext-orthogonal to the centres of its letters. -/
theorem word_smul_of_hom_eq_zero (u : List α) {V : Obj}
    (h : ∀ a ∈ u, I.hom (H.S (H.c a)) V = 0) : H.word u • V = V := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [HomTwistSystem₀.word_cons, mul_smul, ih fun b hb => h b (by simp [hb]),
      hH.letter_smul_of_hom_eq_zero a (h a (by simp))]

/-- **Letters at Ext-orthogonal centres commute**, by the conjugation formula. -/
theorem letter_commute (a b : α) (h : I.hom (H.S (H.c a)) (H.S (H.c b)) = 0) :
    Commute (H.T a) (H.T b) := by
  have hc := I.twist_commute (hH.spherical (H.c a)) (hH.spherical (H.c b)) h
  rcases hH.letter a with ea | ea <;> rcases hH.letter b with eb | eb <;> rw [ea, eb]
  · exact hc
  · exact hc.inv_right
  · exact hc.inv_left
  · exact hc.inv_inv

variable {β : Type*} [DecidableEq β] {comp : ι → β}

omit hH [DecidableEq β] in
lemma hom_eq_zero_of_comp_ne (hH : I.IsTwistSystem H)
    (hcomp : ∀ i j, comp i ≠ comp j → H.h (H.S i) (H.S j) = 0) {i j : ι}
    (h : comp i ≠ comp j) : I.hom (H.S i) (H.S j) = 0 := by
  rw [← hH.count_eq, hcomp i j h, Nat.cast_zero]

/-- **(3b) The component decomposition.** If the components of the centres are pairwise
Ext-orthogonal, then for every centre `S_b` the count `h(S_b, W E)` depends only on the subword of
`W` in the letters of the component of `b`: the other letters commute past it and fix it. -/
theorem hom_word_eq_hom_filter (hcomp : ∀ i j, comp i ≠ comp j → H.h (H.S i) (H.S j) = 0)
    (b : ι) (v : List α) (E : Obj) :
    H.h (H.S b) (H.word v • E) =
      H.h (H.S b) (H.word (v.filter fun a => decide (comp (H.c a) = comp b)) • E) := by
  set p : α → Bool := fun a => decide (comp (H.c a) = comp b) with hp
  have hcomm : ∀ a a', p a = true → p a' = false → Commute (H.T a) (H.T a') := by
    intro a a' ha ha'
    refine hH.letter_commute a a' (hH.hom_eq_zero_of_comp_ne hcomp ?_)
    simp only [hp, decide_eq_true_eq, decide_eq_false_iff_not] at ha ha'
    rw [ha]; exact fun h => ha' h.symm
  have hsplit : H.word v = H.word (v.filter p) * H.word (v.filter fun a => !p a) :=
    List.prod_map_eq_filter_mul_filter H.T p hcomm v
  set uB := v.filter p
  set uR := v.filter fun a => !p a
  have hfixX : H.word uR • ((H.word uB)⁻¹ • H.S b) = (H.word uB)⁻¹ • H.S b := by
    refine hH.word_smul_of_hom_eq_zero uR fun a' ha' => ?_
    have ha'R : comp (H.c a') ≠ comp b := by
      have := (List.mem_filter.mp ha').2
      simpa [hp] using this
    have hfixS : H.word uB • H.S (H.c a') = H.S (H.c a') := by
      refine hH.word_smul_of_hom_eq_zero uB fun a ha => ?_
      have haB : comp (H.c a) = comp b := by
        have := (List.mem_filter.mp ha).2
        simpa [hp] using this
      exact hH.hom_eq_zero_of_comp_ne hcomp (by rw [haB]; exact fun h => ha'R h.symm)
    calc I.hom (H.S (H.c a')) ((H.word uB)⁻¹ • H.S b)
        = I.hom (H.word uB • H.S (H.c a')) (H.S b) := by rw [I.hom_smul_left]
      _ = 0 := by rw [hfixS]; exact hH.hom_eq_zero_of_comp_ne hcomp ha'R
  calc H.h (H.S b) (H.word v • E) = H.h (H.S b) (H.word uB • H.word uR • E) := by
        rw [hsplit, mul_smul]
    _ = H.h ((H.word uB)⁻¹ • H.S b) (H.word uR • E) := (H.h_inv_smul _ _ _).symm
    _ = H.h ((H.word uR)⁻¹ • (H.word uB)⁻¹ • H.S b) E := (H.h_inv_smul _ _ _).symm
    _ = H.h ((H.word uB)⁻¹ • H.S b) E := by rw [inv_smul_eq_iff.mpr hfixX.symm]
    _ = H.h (H.S b) (H.word uB • E) := H.h_inv_smul _ _ _

/-- The subsystem of a twist system of spherical objects is one. -/
theorem restrict (p : ι → Prop) : I.IsTwistSystem (H.restrict p) where
  count_eq := hH.count_eq
  spherical i := hH.spherical i.1
  letter a := hH.letter a.1

/-- With an inverse-closed alphabet, the twist along the centre of every letter is a letter. -/
theorem exists_twist_letter (inv : α → α) (hinvT : ∀ a, H.T (inv a) = (H.T a)⁻¹)
    (hinvc : ∀ a, H.c (inv a) = H.c a) (a : α) :
    ∃ a', H.c a' = H.c a ∧ H.T a' = I.twist (H.S (H.c a)) := by
  rcases hH.letter a with e | e
  · exact ⟨a, rfl, e⟩
  · exact ⟨inv a, hinvc a, by rw [hinvT, e, inv_inv]⟩

omit hH in
/-- (L_m) conjugated by `g`: `h(S, V) m_σ(gS) ≤ m_σ(gV) + m_σ(g T_S V)`. -/
theorem _root_.MassComparisonHypotheses.hom_mul_mass_smul_le (σ : Stab) (g : Γ) {S : Obj}
    (hS : I.Spherical S) (V : Obj) :
    I.hom S V * I.mass σ (g • S) ≤ I.mass σ (g • V) + I.mass σ (g • I.twist S • V) := by
  rw [I.mass_smul_eq, I.mass_smul_eq, I.mass_smul_eq]
  exact I.hom_mul_mass_le _ S V hS

/-- **Propagation along a chain of centres.** If the masses of the words applied to the centre
`S_i` are bounded by a monotone `Y` of their length, and the letters `a :: as` form a chain from
`S_{c(a)}` to `S_i` with consecutive counts at least one, then
`m_σ(W S_{c(a)}) ≤ 2^{|as|} Y(|W| + |as|)`: each step uses (L_m) and the twist letter. -/
theorem mass_centre_le_of_chain (inv : α → α) (hinvT : ∀ a, H.T (inv a) = (H.T a)⁻¹)
    (hinvc : ∀ a, H.c (inv a) = H.c a) (σ : Stab) {i : ι} (Y : ℕ → ℝ) (hY : Monotone Y)
    (hbase : ∀ u : List α, I.mass σ (H.word u • H.S i) ≤ Y u.length) (as : List α) :
    ∀ a : α, List.IsChain (fun a b => 1 ≤ H.h (H.S (H.c a)) (H.S (H.c b))) (a :: as) →
      H.c ((a :: as).getLast (List.cons_ne_nil _ _)) = i →
      ∀ u : List α,
        I.mass σ (H.word u • H.S (H.c a)) ≤ 2 ^ as.length * Y (u.length + as.length) := by
  induction as with
  | nil =>
    intro a _ hlast u
    simp only [List.getLast_singleton] at hlast
    simpa [hlast] using hbase u
  | cons b bs ih =>
    intro a hchain hlast u
    rw [List.isChain_cons_cons] at hchain
    rw [List.getLast_cons (List.cons_ne_nil _ _)] at hlast
    obtain ⟨a', -, hTa'⟩ := hH.exists_twist_letter inv hinvT hinvc a
    have hL := I.hom_mul_mass_smul_le σ (H.word u) (hH.spherical (H.c a)) (H.S (H.c b))
    have e : H.word u • I.twist (H.S (H.c a)) • H.S (H.c b) = H.word (u ++ [a']) • H.S (H.c b) := by
      rw [HomTwistSystem₀.word_append, mul_smul, ← hTa']
      simp [HomTwistSystem₀.word]
    rw [e] at hL
    have ih1 := ih b hchain.2 hlast u
    have ih2 := ih b hchain.2 hlast (u ++ [a'])
    have h1 : (1 : ℝ) ≤ I.hom (H.S (H.c a)) (H.S (H.c b)) := by
      rw [← hH.count_eq]; exact_mod_cast hchain.1
    have hm := I.mass_nonneg σ (H.word u • H.S (H.c a))
    have hY1 : Y (u.length + bs.length) ≤ Y (u.length + (b :: bs).length) := hY (by simp)
    have hY2 : Y ((u ++ [a']).length + bs.length) = Y (u.length + (b :: bs).length) := by
      congr 1; simp; omega
    rw [hY2] at ih2
    have h2 : (0 : ℝ) ≤ 2 ^ bs.length := by positivity
    calc I.mass σ (H.word u • H.S (H.c a))
        ≤ I.hom (H.S (H.c a)) (H.S (H.c b)) * I.mass σ (H.word u • H.S (H.c a)) := by nlinarith
      _ ≤ I.mass σ (H.word u • H.S (H.c b)) + I.mass σ (H.word (u ++ [a']) • H.S (H.c b)) := hL
      _ ≤ 2 ^ bs.length * Y (u.length + (b :: bs).length) +
          2 ^ bs.length * Y (u.length + (b :: bs).length) := by
          gcongr
          exact ih1.trans (mul_le_mul_of_nonneg_left hY1 h2)
      _ = 2 ^ (b :: bs).length * Y (u.length + (b :: bs).length) := by
          rw [List.length_cons, pow_succ]; ring

/-- **Theorem C.** Let `H` be a twist system of spherical objects with the lower one-letter bound,
sphericity and an inverse-closed alphabet, whose centres fall into pairwise Ext-orthogonal
components `comp`, each with directed connectivity in `d + 1` letters. For an object `E` with
`h(G, W E) ≥ 1` for every `W` (`E ≠ 0`) and every `σ`,

  `log M_n(E)/n → max({0} ∪ {η_B : B meets E})`,

where `M_n(E) = max_{|W| = n} m_σ(W E)`, `η_B` is the exponent of the centre counts of the subsystem
of the component `B`, and `B` meets `E` when `h(S_i, E) ≠ 0` for a centre `S_i` of `B`. The limit
does not depend on `σ`. -/
theorem tendsto_log_lenMax [Fintype ι] [Fintype α] [Nonempty α] {β : Type*} [Fintype β]
    [DecidableEq β] (hL : H.LowerBound) (hsph : H.IsSpherical) (inv : α → α)
    (hinvT : ∀ a, H.T (inv a) = (H.T a)⁻¹) (hinvc : ∀ a, H.c (inv a) = H.c a) (comp : ι → β)
    (hcomp : ∀ i j, comp i ≠ comp j → H.h (H.S i) (H.S j) = 0) {d : ℕ}
    (hconn : ∀ B, (H.restrict fun i => comp i = B).DirectedConnected d) (σ : Stab) {E : Obj}
    (hE : ∀ W : Γ, 1 ≤ I.hom I.G (W • E)) :
    Tendsto (fun n : ℕ => log (Monoid.lenMax H.T (I.mass σ) n E) / n) atTop
      (𝓝 (sSup (insert 0 (Set.range fun B : {B : β // ∃ i, comp i = B ∧ H.h (H.S i) E ≠ 0} =>
        (H.restrict fun i => comp i = B.1).homExponent)))) := by
  classical
  have := I.nonempty_summand
  set Mt := {B : β // ∃ i, comp i = B ∧ H.h (H.S i) E ≠ 0}
  set x : ℕ → ℝ := fun n => Monoid.lenMax H.T (I.mass σ) n E with hxdef
  set Bm : ℕ → ℝ := fun n => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one x
    with hBmdef
  have hne : ∀ B : Mt, Nonempty {i // comp i = B.1} := fun B => ⟨⟨B.2.choose, B.2.choose_spec.1⟩⟩
  set A : Mt → ℕ → ℝ := fun B n =>
    haveI := hne B; I.massMax (H.restrict fun i => comp i = B.1) σ n with hAdef
  set η : Mt → ℝ := fun B => (H.restrict fun i => comp i = B.1).homExponent with hηdef
  obtain ⟨a₀⟩ := ‹Nonempty α›
  have hLpos := I.lowerConst_pos σ
  have hlen : ∀ l : List α, I.mass σ (H.word l • E) ≤ x l.length := fun l =>
    Monoid.le_lenMax_list H.T (I.mass σ) l E
  have hxB : ∀ n, x n ≤ Bm n := fun n =>
    Finset.le_sup' x (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hBmono : Monotone Bm := fun m n hmn =>
    Finset.sup'_le _ _ fun k hk => Finset.le_sup' x
      (Finset.mem_range.2 (by have := Finset.mem_range.1 hk; omega))
  have hxBk : ∀ k n, k ≤ n → x k ≤ Bm n := fun k n hkn => (hxB k).trans (hBmono hkn)
  -- the lower bound `M_n(E) ≥ 1/L_σ`
  have hx : ∀ n, (I.lowerConst σ)⁻¹ ≤ x n := fun n => by
    have h1 := hlen (List.replicate n a₀)
    have h2 := I.hom_G_le_mul_mass σ (H.word (List.replicate n a₀) • E)
    have h3 := hE (H.word (List.replicate n a₀))
    rw [List.length_replicate] at h1
    rw [inv_le_iff_one_le_mul₀ hLpos]
    have := mul_le_mul_of_nonneg_left h1 hLpos.le
    linarith
  -- the step bound `M_n(E) ≤ e^{δ} M_{n+1}(E)`
  have hstep : ∀ n, x n ≤ exp (I.δ (H.T a₀ • σ) σ) * x (n + 1) := fun n => by
    obtain ⟨l, hl, he⟩ := Monoid.exists_lenMax_eq H.T (I.mass σ) n E
    rw [hxdef]; dsimp only; rw [he]
    have h1 := I.mass_smul_le (H.T a₀)⁻¹ σ (H.T a₀ • (l.map H.T).prod • E)
    rw [inv_smul_smul, inv_inv] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (exp_pos _).le)
    have := hlen (a₀ :: l)
    rw [List.length_cons, hl] at this
    simpa [HomTwistSystem₀.word, mul_smul] using this
  have hBatt : ∀ n, ∃ k ≤ n, Bm n ≤ x k := fun n => by
    obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one x
    exact ⟨k, by have := Finset.mem_range.1 hk; omega, he.le⟩
  have hBpos : ∀ n, 0 ≤ Bm n := fun n =>
    (inv_pos.mpr hLpos).le.trans ((hx n).trans (hxB n))
  -- the subsystems
  have hHB : ∀ B : Mt, I.IsTwistSystem (H.restrict fun i => comp i = B.1) := fun B =>
    hH.restrict _
  have hA : ∀ B ∈ (Finset.univ : Finset Mt), ∀ n, 0 < A B n := fun B _ n => by
    have := hne B; exact (hHB B).massMax_pos σ n
  have hrate : ∀ B ∈ (Finset.univ : Finset Mt),
      Tendsto (fun n : ℕ => log (A B n) / n) atTop (𝓝 (η B)) := fun B _ => by
    have := hne B
    exact (hHB B).tendsto_log_massMax (H.lowerBound_restrict hL _) (H.isSpherical_restrict hsph _)
      (hconn B.1) σ
  -- the pointwise bound on the leaf counts
  set Q : ℝ := I.K * I.hom I.G E * I.lowerConst σ * ∑ B : Mt, A B 0 with hQ
  set Qn : ℕ → ℝ := fun n => I.K * I.hom I.G E * I.lowerConst σ * ∑ B : Mt, A B n with hQn
  have hQn0 : ∀ n, 0 ≤ Qn n := fun n => by
    have := Finset.sum_nonneg fun B (_ : B ∈ Finset.univ) => (hA B (Finset.mem_univ _) n).le
    have := I.hom_nonneg I.G E
    have := I.K_pos.le
    positivity
  have hleaf : ∀ n (a : α) (v : List α), v.length ≤ n →
      (H.h (H.S (H.c a)) (H.word v • E) : ℝ) ≤ Qn n := by
    intro n a v hv
    rw [hH.hom_word_eq_hom_filter hcomp (H.c a) v E]
    set u := v.filter fun a' => decide (comp (H.c a') = comp (H.c a)) with hu
    have hmemu : ∀ a' ∈ u, comp (H.c a') = comp (H.c a) := fun a' ha' => by
      have := (List.mem_filter.mp ha').2
      simpa using this
    by_cases hm : ∃ i, comp i = comp (H.c a) ∧ H.h (H.S i) E ≠ 0
    · let B : Mt := ⟨comp (H.c a), hm⟩
      have := hne B
      -- the inverse word lies in the component
      set u' := u.reverse.map inv with hu'
      have hmem' : ∀ a' ∈ u', comp (H.c a') = B.1 := fun a' ha' => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha'
        rw [hinvc]; exact hmemu y (List.mem_reverse.mp hy)
      have hinvword : (H.word u)⁻¹ = H.word u' := (H.word_reverse_map_inv inv hinvT u).symm
      set w' := List.liftSubtype (fun a' => comp (H.c a') = B.1) u' hmem' with hw'
      have hww : (H.restrict fun i => comp i = B.1).word w' = H.word u' := by
        rw [HomTwistSystem₀.restrict_word, hw', List.map_val_liftSubtype]
      have hlenw : w'.length ≤ n := by
        rw [hw', List.length_liftSubtype, hu', List.length_map, List.length_reverse]
        exact (List.length_filter_le _ _).trans hv
      have hmax := I.le_massMax (H := H.restrict fun i => comp i = B.1) σ
        (⟨H.c a, rfl⟩ : {i // comp i = B.1}) w' hlenw
      rw [hww] at hmax
      change I.mass σ (H.word u' • H.S (H.c a)) ≤ A B n at hmax
      have hAB : A B n ≤ ∑ B : Mt, A B n :=
        Finset.single_le_sum (f := fun B => A B n) (fun B _ => (hA B (Finset.mem_univ _) n).le)
          (Finset.mem_univ B)
      have h1 : I.hom (H.S (H.c a)) (H.word u • E) =
          I.hom ((H.word u)⁻¹ • H.S (H.c a)) E := by
        rw [I.hom_smul_left, inv_inv]
      have h2 := I.hom_diag ((H.word u)⁻¹ • H.S (H.c a)) E
      have h3 := I.hom_G_le_mul_mass σ ((H.word u)⁻¹ • H.S (H.c a))
      rw [I.hom_comm ((H.word u)⁻¹ • H.S (H.c a)) I.G] at h2
      rw [hinvword] at h2 h3 h1
      rw [hH.count_eq, h1]
      have hK := I.K_pos.le
      have hGE := I.hom_nonneg I.G E
      have hL0 := hLpos.le
      have hm0 := I.mass_nonneg σ (H.word u' • H.S (H.c a))
      calc I.hom (H.word u' • H.S (H.c a)) E
          ≤ I.K * I.hom I.G (H.word u' • H.S (H.c a)) * I.hom I.G E := h2
        _ ≤ I.K * (I.lowerConst σ * I.mass σ (H.word u' • H.S (H.c a))) * I.hom I.G E := by
            gcongr
        _ ≤ I.K * (I.lowerConst σ * ∑ B : Mt, A B n) * I.hom I.G E := by
            gcongr; exact hmax.trans hAB
        _ = Qn n := by rw [hQn]; ring
    · push Not at hm
      have hfix : H.word u • E = E := hH.word_smul_of_hom_eq_zero u fun a' ha' => by
        rw [← hH.count_eq, hm _ (hmemu a' ha'), Nat.cast_zero]
      rw [hfix, hm _ rfl, Nat.cast_zero]
      exact hQn0 n
  -- the upper bound on `M_n(E)`
  have hupw : ∀ n (l : List α), l.length ≤ n →
      I.mass σ (H.word l • E) ≤ I.mass σ E + l.length * (I.centreMass (H := H) σ * Qn n) := by
    intro n l
    induction l with
    | nil => intro _; simp
    | cons a l ih =>
      intro hl
      simp only [List.length_cons] at hl
      have h1 := hH.mass_letter_le a σ (H.word l • E)
      have h2 := hleaf n a l (by omega)
      have h3 : I.mass σ (H.S (H.c a)) ≤ I.centreMass (H := H) σ :=
        Finset.single_le_sum (f := fun i => I.mass σ (H.S i))
          (fun i _ => I.mass_nonneg σ _) (Finset.mem_univ _)
      have hm := I.mass_nonneg σ (H.S (H.c a))
      have hQ0 := hQn0 n
      rw [HomTwistSystem₀.word_cons, mul_smul]
      calc I.mass σ (H.T a • H.word l • E)
          ≤ I.mass σ (H.word l • E) + H.h (H.S (H.c a)) (H.word l • E) * I.mass σ (H.S (H.c a)) :=
            h1
        _ ≤ (I.mass σ E + l.length * (I.centreMass (H := H) σ * Qn n)) +
            Qn n * I.centreMass (H := H) σ := by
            gcongr
            · exact ih (by omega)
        _ = I.mass σ E + ((a :: l).length : ℕ) * (I.centreMass (H := H) σ * Qn n) := by
            rw [List.length_cons]; push_cast; ring
  have hup : ∀ n, x n ≤ I.mass σ E +
      (I.centreMass (H := H) σ * I.K * I.hom I.G E * I.lowerConst σ) * n * ∑ B : Mt, A B n := by
    intro n
    obtain ⟨l, hl, he⟩ := Monoid.exists_lenMax_eq H.T (I.mass σ) n E
    have := hupw n l hl.le
    rw [hl] at this
    rw [hxdef]; dsimp only; rw [he]
    refine this.trans (le_of_eq ?_)
    rw [hQn]; ring
  -- the lower bound on the running maximum
  have hlow : ∀ B ∈ (Finset.univ : Finset Mt), ∀ n, A B n ≤ 2 ^ (d + 1) * Bm (n + (d + 1)) := by
    intro B _ n
    have := hne B
    set H₀ := H.restrict fun i => comp i = B.1 with hH₀
    obtain ⟨i₀, hi₀B, hi₀E⟩ := B.2
    have hi₀ : (1 : ℝ) ≤ I.hom (H.S i₀) E := by
      rw [← hH.count_eq]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi₀E
    -- the inverse-closed alphabet of the subsystem
    let inv₀ : {a // comp (H.c a) = B.1} → {a // comp (H.c a) = B.1} :=
      fun a => ⟨inv a.1, by rw [hinvc]; exact a.2⟩
    have hinvT₀ : ∀ a, H₀.T (inv₀ a) = (H₀.T a)⁻¹ := fun a => hinvT a.1
    have hinvc₀ : ∀ a, H₀.c (inv₀ a) = H₀.c a := fun a => Subtype.ext (hinvc a.1)
    -- a letter with centre `i₀`, and the twist along `S_{i₀}`
    obtain ⟨a₁, -, ha₁, -, -, -⟩ := hconn B.1 ⟨i₀, hi₀B⟩ ⟨i₀, hi₀B⟩
    obtain ⟨a₂, -, hTa₂⟩ := (hHB B).exists_twist_letter inv₀ hinvT₀ hinvc₀ a₁
    rw [ha₁] at hTa₂
    -- the base estimate at `S_{i₀}`
    have hbase : ∀ u : List {a // comp (H.c a) = B.1},
        I.mass σ (H₀.word u • H₀.S ⟨i₀, hi₀B⟩) ≤ 2 * Bm (u.length + 1) := by
      intro u
      have hLm := I.hom_mul_mass_smul_le σ (H₀.word u) (hH.spherical i₀) E
      have e1 : H₀.word u • I.twist (H.S i₀) • E = H₀.word (u ++ [a₂]) • E := by
        rw [HomTwistSystem₀.word_append, mul_smul]
        change _ = H₀.word u • (H₀.T a₂ * 1) • E
        rw [mul_one, hTa₂]; rfl
      rw [e1] at hLm
      have hx1 : I.mass σ (H₀.word u • E) ≤ Bm (u.length + 1) := by
        rw [HomTwistSystem₀.restrict_word]
        refine (hlen _).trans (hxBk _ _ ?_)
        rw [List.length_map]; omega
      have hx2 : I.mass σ (H₀.word (u ++ [a₂]) • E) ≤ Bm (u.length + 1) := by
        rw [HomTwistSystem₀.restrict_word]
        refine (hlen _).trans (hxBk _ _ ?_)
        simp
      change I.mass σ (H₀.word u • H.S i₀) ≤ _
      have hm := I.mass_nonneg σ (H₀.word u • H.S i₀)
      nlinarith
    -- the maximizing word and centre of the subsystem, joined to `i₀` by a chain
    obtain ⟨j, u, hu, he⟩ := I.exists_massMax_eq (H := H₀) σ n
    obtain ⟨a, as, haj, hlast, hlen', hchain⟩ := hconn B.1 ⟨i₀, hi₀B⟩ j
    have hY : Monotone fun k => 2 * Bm (k + 1) := fun k l hkl => by
      have := hBmono (Nat.add_le_add_right hkl 1)
      dsimp only; linarith
    have hprop := (hHB B).mass_centre_le_of_chain inv₀ hinvT₀ hinvc₀ σ
      (fun k => 2 * Bm (k + 1)) hY hbase as a hchain hlast u
    rw [haj] at hprop
    change A B n ≤ _
    rw [hAdef]; dsimp only; rw [he]
    refine hprop.trans ?_
    have hpow : (2 : ℝ) ^ as.length ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hlen'
    have hBm' : Bm (u.length + as.length + 1) ≤ Bm (n + (d + 1)) := hBmono (by omega)
    have := hBpos (u.length + as.length + 1)
    calc (2 : ℝ) ^ as.length * (2 * Bm (u.length + as.length + 1))
        ≤ 2 ^ d * (2 * Bm (n + (d + 1))) := by gcongr
      _ = 2 ^ (d + 1) * Bm (n + (d + 1)) := by ring
  -- the analytic core
  have hmain := Real.tendsto_log_div_of_family (Finset.univ : Finset Mt) (x := x) (B := Bm)
    (A := A) (η := η) (inv_pos.mpr hLpos) hx (one_le_exp (I.δ_nonneg _ _)) hstep hxB hBatt hA
    hrate (I.mass_nonneg σ E)
    (by have := I.K_pos.le; have := I.hom_nonneg I.G E;
        have : 0 ≤ I.centreMass (H := H) σ := Finset.sum_nonneg fun i _ => I.mass_nonneg σ _
        positivity)
    (by positivity) hup hlow
  rw [Finset.coe_univ, Set.image_univ] at hmain
  exact hmain

end IsTwistSystem

end MassComparisonHypotheses
