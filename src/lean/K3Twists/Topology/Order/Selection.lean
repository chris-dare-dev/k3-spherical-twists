/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# The selection lemma in increment form

Let `f` be a continuous real function on an interval `s` which at every point equals one of
finitely many functions `g_j`, each of which satisfies the one-sided increment bound

```
g_j(t) - g_j(u) ≥ -L (t - u)        for u ≤ t in s.
```

Then `f` satisfies the same bound (`sub_le_of_continuousOn_of_selection`). The selector
`t ↦ j(t)` may be arbitrary: no regularity of it, and none of the `g_j` beyond the increment
bound, is assumed. The case `L = 0` (`monotoneOn_of_continuousOn_of_selection`) says that a
continuous selection from finitely many monotone functions is monotone.

This is the analytic core of the variation estimates for the extremal phases `φ^±` and the mass
along a path of stability conditions: on a compact lifted path the extremal phase of an object is
at every time one of finitely many stable phases, each of which moves at bounded speed, and the
lemma transfers the speed bound to the extremal phase.

**The increments are essential.** The bound cannot be weakened to "`g_j' ≥ -L` almost
everywhere": the negative of the Cantor function has derivative `0` almost everywhere and
decreases.

## Proof

Reduce to `L = 0` by adding `L t`. If `u < t` but `f(t) < f(u)`, then for each value `c` strictly
between them let `τ(c)` be the last time in `[u, t]` at which `f = c`. By the intermediate value
theorem `c ↦ τ(c)` is strictly decreasing, and the values form an infinite set, so two of them
are selected by the same `g_j`; on those two times `g_j` decreases, a contradiction.
-/

open Set

/-- **A continuous selection from finitely many monotone functions is monotone.** If `f` is
continuous on the interval `s` and at every point of `s` equals one of the functions `g j`, each
monotone on `s`, then `f` is monotone on `s`. -/
theorem monotoneOn_of_continuousOn_of_selection {ι : Type*} [Finite ι] {s : Set ℝ}
    (hs : s.OrdConnected) {f : ℝ → ℝ} (hf : ContinuousOn f s) {g : ι → ℝ → ℝ}
    (hg : ∀ j, MonotoneOn (g j) s) (hsel : ∀ t ∈ s, ∃ j, f t = g j t) : MonotoneOn f s := by
  intro u hu t ht hut
  by_contra hlt
  push Not at hlt
  have hIcc : Icc u t ⊆ s := hs.out hu ht
  have hfc : ContinuousOn f (Icc u t) := hf.mono hIcc
  -- the last time in `[u, t]` at which `f` takes the value `c`
  let T : ℝ → Set ℝ := fun c => Icc u t ∩ f ⁻¹' {c}
  have hTc : ∀ c, IsCompact (T c) := fun c =>
    isCompact_Icc.of_isClosed_subset
      (hfc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  have hTne : ∀ c ∈ Ioo (f t) (f u), (T c).Nonempty := fun c hc => by
    obtain ⟨τ, hτ, hfτ⟩ := intermediate_value_Icc' hut hfc ⟨hc.1.le, hc.2.le⟩
    exact ⟨τ, hτ, hfτ⟩
  let τ : ℝ → ℝ := fun c => sSup (T c)
  have hτmem : ∀ c ∈ Ioo (f t) (f u), τ c ∈ T c := fun c hc =>
    (hTc c).sSup_mem (hTne c hc)
  have hτlt : ∀ c ∈ Ioo (f t) (f u), ∀ c' ∈ Ioo (f t) (f u), c < c' → τ c' < τ c := by
    intro c hc c' hc' hcc'
    obtain ⟨⟨h1, h2⟩, h3⟩ := hτmem c' hc'
    have h3 : f (τ c') = c' := h3
    have hsub : Icc (τ c') t ⊆ Icc u t := Icc_subset_Icc h1 le_rfl
    have hcmem : c ∈ Icc (f t) (f (τ c')) := ⟨hc.1.le, by rw [h3]; exact hcc'.le⟩
    obtain ⟨τ'', hτ'', hfτ''⟩ := intermediate_value_Icc' h2 (hfc.mono hsub) hcmem
    have hle : τ c' ≤ τ c :=
      hτ''.1.trans (le_csSup (hTc c).bddAbove ⟨hsub hτ'', hfτ''⟩)
    refine hle.lt_of_ne fun heq => ?_
    have := (hτmem c hc).2
    change f (τ c) = c at this
    rw [← heq, h3] at this
    exact hcc'.ne' this
  -- choose a selected function at each of these times
  have hsel' : ∀ c ∈ Ioo (f t) (f u), ∃ j, f (τ c) = g j (τ c) := fun c hc =>
    hsel _ (hIcc (hτmem c hc).1)
  have : Nonempty ι := ⟨(hsel u hu).choose⟩
  choose! J hJ using hsel'
  obtain ⟨c, hc, c', hc', hne, hJeq⟩ := (Ioo_infinite hlt).exists_ne_map_eq_of_mapsTo
    (mapsTo_univ J _) finite_univ
  -- two values selected by the same monotone function at times in the wrong order
  have key : ∀ c ∈ Ioo (f t) (f u), ∀ c' ∈ Ioo (f t) (f u), c < c' → J c = J c' → False := by
    intro c hc c' hc' hcc' hJ'
    have hlt' := hτlt c hc c' hc' hcc'
    have hmono := hg (J c) (hIcc (hτmem c' hc').1) (hIcc (hτmem c hc).1) hlt'.le
    have e1 : f (τ c) = c := (hτmem c hc).2
    have e2 : f (τ c') = c' := (hτmem c' hc').2
    rw [← hJ c hc, hJ', ← hJ c' hc', e1, e2] at hmono
    exact absurd hmono (not_le.mpr hcc')
  rcases hne.lt_or_gt with h | h
  · exact key c hc c' hc' h hJeq
  · exact key c' hc' c hc h hJeq.symm

/-- **The selection lemma in increment form.** If `f` is continuous on the interval `s` and at
every point of `s` equals one of finitely many functions `g j`, each with
`g j t - g j u ≥ -L (t - u)` for `u ≤ t` in `s`, then `f t - f u ≥ -L (t - u)` for `u ≤ t` in
`s`. -/
theorem sub_le_of_continuousOn_of_selection {ι : Type*} [Finite ι] {s : Set ℝ}
    (hs : s.OrdConnected) {f : ℝ → ℝ} (hf : ContinuousOn f s) {g : ι → ℝ → ℝ} {L : ℝ}
    (hg : ∀ j, ∀ u ∈ s, ∀ t ∈ s, u ≤ t → -L * (t - u) ≤ g j t - g j u)
    (hsel : ∀ t ∈ s, ∃ j, f t = g j t) {u t : ℝ} (hu : u ∈ s) (ht : t ∈ s) (hut : u ≤ t) :
    -L * (t - u) ≤ f t - f u := by
  have hmono : MonotoneOn (fun x => f x + L * x) s := by
    refine monotoneOn_of_continuousOn_of_selection hs
      (hf.add (continuousOn_const.mul continuousOn_id)) (g := fun j x => g j x + L * x)
      (fun j a ha b hb hab => ?_) (fun x hx => ?_)
    · have := hg j a ha b hb hab
      simp only
      linarith
    · obtain ⟨j, hj⟩ := hsel x hx
      exact ⟨j, by simp only [hj]⟩
  have := hmono hu ht hut
  simp only at this
  linarith
