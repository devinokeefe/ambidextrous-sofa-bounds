import SofaBounds.Basic

/-!
# A generic horizontal slicing bound

If every point `(x, y)` of a set lies in the strip `0 ≤ y ≤ 1` and satisfies
`g y ≤ x ≤ g y + L` for a measurable `g`, then the set has area at most `L`
(Tonelli applied to the closed-form measurable superset).
-/

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped EuclideanGeometry

/-- Slicing bound in `ℝ × ℝ`. The set `T` need not be measurable. -/
theorem volume_prod_le_of_slice {T : Set (ℝ × ℝ)} {g : ℝ → ℝ} (hg : Measurable g) {L : ℝ}
    (h : ∀ q ∈ T, 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ g q.2 ≤ q.1 ∧ q.1 ≤ g q.2 + L) :
    volume T ≤ ENNReal.ofReal L := by
  have hSm : MeasurableSet
      {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ g q.2 ≤ q.1 ∧ q.1 ≤ g q.2 + L} := by
    refine (measurableSet_le measurable_const measurable_snd).inter ?_
    refine (measurableSet_le measurable_snd measurable_const).inter ?_
    exact (measurableSet_le (hg.comp measurable_snd) measurable_fst).inter
      (measurableSet_le measurable_fst ((hg.comp measurable_snd).add measurable_const))
  calc volume T
      ≤ volume {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ g q.2 ≤ q.1 ∧ q.1 ≤ g q.2 + L} :=
        measure_mono h
    _ = ∫⁻ y, volume ((fun x => (x, y)) ⁻¹'
          {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ g q.2 ≤ q.1 ∧ q.1 ≤ g q.2 + L}) := by
        rw [Measure.volume_eq_prod, Measure.prod_apply_symm hSm]
    _ ≤ ∫⁻ y, (Set.Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal L) y := by
        apply lintegral_mono
        intro y
        dsimp only
        by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
        · rw [Set.indicator_of_mem hy]
          have hsub : (fun x => (x, y)) ⁻¹'
              {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ g q.2 ≤ q.1 ∧ q.1 ≤ g q.2 + L} ⊆
              Set.Icc (g y) (g y + L) := fun x hx => ⟨hx.2.2.1, hx.2.2.2⟩
          calc _ ≤ volume (Set.Icc (g y) (g y + L)) := measure_mono hsub
            _ = ENNReal.ofReal L := by rw [Real.volume_Icc]; congr 1; ring
        · rw [Set.indicator_of_notMem hy]
          have hempty : (fun x => (x, y)) ⁻¹'
              {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ g q.2 ≤ q.1 ∧ q.1 ≤ g q.2 + L} = ∅ := by
            ext x
            exact ⟨fun hx => absurd ⟨hx.1, hx.2.1⟩ hy, fun hx => hx.elim⟩
          rw [hempty, measure_empty]
    _ = ENNReal.ofReal L := by
        rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc]
        simp

/-- Slicing bound in `ℝ²`. The set `s` need not be measurable. -/
theorem volume_le_of_slice {s : Set ℝ²} {g : ℝ → ℝ} (hg : Measurable g) {L : ℝ}
    (h : ∀ p ∈ s, 0 ≤ p 1 ∧ p 1 ≤ 1 ∧ g (p 1) ≤ p 0 ∧ p 0 ≤ g (p 1) + L) :
    volume s ≤ ENNReal.ofReal L := by
  rw [volume_eq_volume_prod]
  refine volume_prod_le_of_slice hg ?_
  intro q hq
  simpa using h _ hq

/-- Slicing bound with a slope: if `g y ≤ c x ≤ g y + 1` on a subset of the strip, with
`c ≠ 0`, then the area is at most `1 / |c|`. -/
theorem volume_le_of_slice_mul {s : Set ℝ²} {g : ℝ → ℝ} (hg : Measurable g) {c : ℝ}
    (hc : c ≠ 0)
    (h : ∀ p ∈ s, 0 ≤ p 1 ∧ p 1 ≤ 1 ∧ g (p 1) ≤ c * p 0 ∧ c * p 0 ≤ g (p 1) + 1) :
    volume s ≤ ENNReal.ofReal (1 / |c|) := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · -- `c < 0`: `(g y + 1) / c ≤ x ≤ g y / c`
    rw [abs_of_neg hneg]
    refine volume_le_of_slice (g := fun y => (g y + 1) / c) (hg.add_const 1 |>.div_const c) ?_
    intro p hp
    obtain ⟨h0, h1, hlo, hhi⟩ := h p hp
    refine ⟨h0, h1, ?_, ?_⟩
    · rw [div_le_iff_of_neg hneg]
      linarith
    · have : (g (p 1) + 1) / c + 1 / -c = g (p 1) / c := by
        field_simp
        ring
      rw [this, le_div_iff_of_neg hneg]
      linarith
  · -- `c > 0`: `g y / c ≤ x ≤ g y / c + 1 / c`
    rw [abs_of_pos hpos]
    refine volume_le_of_slice (g := fun y => g y / c) (hg.div_const c) ?_
    intro p hp
    obtain ⟨h0, h1, hlo, hhi⟩ := h p hp
    refine ⟨h0, h1, ?_, ?_⟩
    · rw [div_le_iff₀ hpos]
      linarith
    · have : g (p 1) / c + 1 / c = (g (p 1) + 1) / c := by ring
      rw [this, le_div_iff₀ hpos]
      linarith

end MovingSofa
