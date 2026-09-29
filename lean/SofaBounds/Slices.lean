import SofaBounds.Basic
import SofaBounds.SlicesAux.Slice

/-!
# Area estimates by horizontal slicing

Lemma 3.4(i) (two strips) and Lemma 3.6 (sideways hallways) of the paper.
-/

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped EuclideanGeometry

/-- **Lemma 3.4 (two strips).** A subset of the strip `H` whose points satisfy
`0 ≤ c x + d y + e ≤ 1` with `c ≠ 0` has area at most `1 / |c|`. -/
theorem volume_le_of_strip {s : Set ℝ²} (hs : s ⊆ strip) {c d e : ℝ} (hc : c ≠ 0)
    (h : ∀ p ∈ s, 0 ≤ c * p 0 + d * p 1 + e ∧ c * p 0 + d * p 1 + e ≤ 1) :
    volume s ≤ ENNReal.ofReal (1 / |c|) := by
  refine volume_le_of_slice_mul (g := fun y => -d * y - e) (by fun_prop) hc ?_
  intro p hp
  obtain ⟨h0, h1⟩ := hs hp
  obtain ⟨hlo, hhi⟩ := h p hp
  exact ⟨h0, h1, by linarith, by linarith⟩

/-- **Lemma 3.6 (sideways hallways).** If a subset of the strip lies in a hallway whose corner
points horizontally (a hallway rotated so that `cos = sin = c`, `c ^ 2 = 1/2`), then its area is
at most `√2`: every horizontal line meets such a hallway in a segment of length `√2`. -/
theorem volume_le_sqrt_two_of_sideways {s : Set ℝ²} (hs : s ⊆ strip) {c a b : ℝ}
    (hc : c ^ 2 = 1 / 2)
    (h : ∀ p ∈ s, InL0 (c * p 0 - c * p 1 + a) (c * p 0 + c * p 1 + b)) :
    volume s ≤ ENNReal.ofReal √2 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc
  have habs : 1 / |c| = √2 := by
    rw [← Real.sqrt_sq_eq_abs, hc, one_div, ← Real.sqrt_inv]
    norm_num
  rw [← habs]
  -- Horizontal slice: with `P = c x - c y + a`, `Q = c x + c y + b`, `InL0 P Q` gives
  -- `P ≤ 1`, `Q ≤ 1` and `0 ≤ P ∨ 0 ≤ Q`, so `c x` lies in `[m, m + 1]` with
  -- `m = min (c y - a) (-b - c y)`.
  refine volume_le_of_slice_mul (g := fun y => min (c * y - a) (-b - c * y)) (by fun_prop)
    hc0 ?_
  intro p hp
  obtain ⟨h0, h1⟩ := hs hp
  have hPQ := h p hp
  have hP1 : c * p 0 - c * p 1 + a ≤ 1 := by
    rcases hPQ with h' | h'
    · exact h'.1
    · exact h'.2.1
  have hQ1 : c * p 0 + c * p 1 + b ≤ 1 := by
    rcases hPQ with h' | h'
    · exact h'.2.2
    · exact h'.2.2
  refine ⟨h0, h1, ?_, ?_⟩
  · rcases hPQ with h' | h'
    · have := min_le_right (c * p 1 - a) (-b - c * p 1)
      linarith [h'.2.1]
    · have := min_le_left (c * p 1 - a) (-b - c * p 1)
      linarith [h'.1]
  · have := le_min (show c * p 0 - 1 ≤ c * p 1 - a by linarith)
      (show c * p 0 - 1 ≤ -b - c * p 1 by linarith)
    linarith

end MovingSofa
