import Mathlib

/-!
# Components of a finite union of closed sets

If the closed sets `S i` (`i < n`) are labelled so that sets with different labels are disjoint,
then a preconnected set inside their union lies in the union of one label class, and so its
measure is at most the sum of the measures in that class. This is the soundness of the
component step of the leaf test (Section 5.3 of the paper).
-/

noncomputable section

namespace SofaCert

open MeasureTheory

/-- The measure bound for a preconnected subset of a labelled finite union of closed sets. -/
theorem volume_le_of_groups {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} {S : ℕ → Set X} (hS : ∀ i < n, IsClosed (S i)) {a : ℕ → ℝ} (ha : ∀ i < n, 0 ≤ a i)
    (hvol : ∀ i < n, μ (S i) ≤ ENNReal.ofReal (a i)) {lab : ℕ → ℕ}
    (hsep : ∀ i < n, ∀ k < n, lab i ≠ lab k → S i ∩ S k = ∅) {T : ℝ}
    (hsum : ∀ i < n, ∑ k ∈ (Finset.range n).filter (fun k => lab k = lab i), a k ≤ T)
    {K : Set X} (hK : K ⊆ ⋃ i ∈ Finset.range n, S i) (hpre : IsPreconnected K) :
    μ K ≤ ENNReal.ofReal T := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp
  obtain ⟨i₀, hi₀, hpi₀⟩ : ∃ i ∈ Finset.range n, p ∈ S i := by
    simpa using hK hp
  have hi₀n : i₀ < n := Finset.mem_range.1 hi₀
  set I := (Finset.range n).filter (fun k => lab k = lab i₀) with hI
  set J := (Finset.range n).filter (fun k => lab k ≠ lab i₀) with hJ
  set U := ⋃ k ∈ I, S k with hU
  set V := ⋃ k ∈ J, S k with hV
  have hUc : IsClosed U := isClosed_biUnion_finset fun k hk => by
    simp only [hI, Finset.mem_filter, Finset.mem_range] at hk
    exact hS k hk.1
  have hVc : IsClosed V := isClosed_biUnion_finset fun k hk => by
    simp only [hJ, Finset.mem_filter, Finset.mem_range] at hk
    exact hS k hk.1
  have hUV : U ∩ V = ∅ := by
    ext x
    simp only [hU, hV, Set.mem_inter_iff, Set.mem_iUnion, hI, hJ, Finset.mem_filter,
      Finset.mem_range, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨k, ⟨hk, hlk⟩, hxk⟩ ⟨k', ⟨hk', hlk'⟩, hxk'⟩
    have hne : lab k ≠ lab k' := by rw [hlk]; exact fun h => hlk' h.symm
    have := hsep k hk k' hk' hne
    exact (Set.eq_empty_iff_forall_notMem.1 this) x ⟨hxk, hxk'⟩
  have hKUV : K ⊆ U ∪ V := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ : ∃ k ∈ Finset.range n, x ∈ S k := by simpa using hK hx
    by_cases hl : lab k = lab i₀
    · left
      simp only [hU, Set.mem_iUnion]
      exact ⟨k, by simp [hI, Finset.mem_range.1 hk, hl], hxk⟩
    · right
      simp only [hV, Set.mem_iUnion]
      exact ⟨k, by simp [hJ, Finset.mem_range.1 hk, hl], hxk⟩
  have hKU : K ⊆ U := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.1 hpre) U V hUc hVc hKUV
      (by rw [hUV, Set.inter_empty]) with h | h
    · exact h
    · exfalso
      have hpU : p ∈ U := by
        simp only [hU, Set.mem_iUnion]
        exact ⟨i₀, by simp [hI, hi₀n], hpi₀⟩
      have : p ∈ U ∩ V := ⟨hpU, h hp⟩
      rw [hUV] at this
      exact this
  calc μ K ≤ μ U := measure_mono hKU
    _ ≤ ∑ k ∈ I, μ (S k) := measure_biUnion_finset_le I S
    _ ≤ ∑ k ∈ I, ENNReal.ofReal (a k) := by
        refine Finset.sum_le_sum fun k hk => ?_
        simp only [hI, Finset.mem_filter, Finset.mem_range] at hk
        exact hvol k hk.1
    _ = ENNReal.ofReal (∑ k ∈ I, a k) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro k hk
        simp only [hI, Finset.mem_filter, Finset.mem_range] at hk
        exact ha k hk.1
    _ ≤ ENNReal.ofReal T := ENNReal.ofReal_le_ofReal (hsum i₀ hi₀n)

/-- The special case of a single group. -/
theorem volume_le_of_sum {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} {S : ℕ → Set X} {a : ℕ → ℝ} (ha : ∀ i < n, 0 ≤ a i)
    (hvol : ∀ i < n, μ (S i) ≤ ENNReal.ofReal (a i)) {T : ℝ}
    (hsum : ∑ k ∈ Finset.range n, a k ≤ T)
    {K : Set X} (hK : K ⊆ ⋃ i ∈ Finset.range n, S i) :
    μ K ≤ ENNReal.ofReal T := by
  calc μ K ≤ μ (⋃ i ∈ Finset.range n, S i) := measure_mono hK
    _ ≤ ∑ k ∈ Finset.range n, μ (S k) := measure_biUnion_finset_le _ S
    _ ≤ ∑ k ∈ Finset.range n, ENNReal.ofReal (a k) :=
        Finset.sum_le_sum fun k hk => hvol k (Finset.mem_range.1 hk)
    _ = ENNReal.ofReal (∑ k ∈ Finset.range n, a k) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro k hk
        exact ha k (Finset.mem_range.1 hk)
    _ ≤ ENNReal.ofReal T := ENNReal.ofReal_le_ofReal hsum

end SofaCert
