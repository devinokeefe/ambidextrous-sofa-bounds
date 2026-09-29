import SofaBounds.Basic
import SofaBounds.OneHalfAux.Slice

/-!
# Proposition 3.7: one hallway at 45° on each side

In the frame of the sofa, the hallway `L_{45°}(u)` is `{p | InL0 (c x + c y + a) (-c x + c y + b)}`
and the mirrored hallway `ρ(L_{45°}(v))` is `{p | InL0 (c x + c (1-y) + a') (-c x + c (1-y) + b')}`,
where `c = √2/2`. Their intersection with the strip has area at most `2√2 - 1` (Appendix A).
-/

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped EuclideanGeometry

/-- **Proposition 3.7.** -/
theorem volume_oneHalf_le (a b a' b' : ℝ) :
    volume {p : ℝ² | 0 ≤ p 1 ∧ p 1 ≤ 1 ∧
      InL0 (√2 / 2 * p 0 + √2 / 2 * p 1 + a) (-(√2 / 2) * p 0 + √2 / 2 * p 1 + b) ∧
      InL0 (√2 / 2 * p 0 + √2 / 2 * (1 - p 1) + a')
        (-(√2 / 2) * p 0 + √2 / 2 * (1 - p 1) + b')} ≤ ENNReal.ofReal (2 * √2 - 1) := by
  rw [volume_eq_volume_prod]
  convert OneHalfAux.main a b a' b' using 3
  ext q
  simp

end MovingSofa
