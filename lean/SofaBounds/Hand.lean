import SofaBounds.Turning
import SofaBounds.OneHalf

/-!
# Theorem 1.2: every ambidextrous sofa has area at most `2√2 - 1`
-/

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped EuclideanGeometry

/-- The area of an ambidextrous sofa is at most `2√2 - 1`. -/
theorem IsAmbidextrousSofa.volume_le {s : Set ℝ²} (hs : IsAmbidextrousSofa s) :
    volume s ≤ ENNReal.ofReal (2 * √2 - 1) := by
  obtain ⟨⟨m, hm⟩, hmir⟩ := hs
  by_contra hlt
  rw [not_le] at hlt
  have h2 : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hT : √2 < 2 * √2 - 1 := by linarith
  have hC : (0 : ℝ) ≤ √2 / 2 := by positivity
  have hCS : (√2 / 2) ^ 2 + (√2 / 2) ^ 2 = 1 := by nlinarith
  have hCT : 1 ≤ √2 / 2 * (2 * √2 - 1) := by nlinarith
  obtain ⟨a, b, hab⟩ := hm.exists_rotation hT hlt hC hC hCS hCT
  obtain ⟨a', b', hab'⟩ := exists_rotation_mirror hmir hT hlt hC hC hCS hCT
  have hsub : s ⊆ {p : ℝ² | 0 ≤ p 1 ∧ p 1 ≤ 1 ∧
      InL0 (√2 / 2 * p 0 + √2 / 2 * p 1 + a) (-(√2 / 2) * p 0 + √2 / 2 * p 1 + b) ∧
      InL0 (√2 / 2 * p 0 + √2 / 2 * (1 - p 1) + a')
        (-(√2 / 2) * p 0 + √2 / 2 * (1 - p 1) + b')} := by
    intro p hp
    have hstrip := horizontalHallway_subset_strip (hm.initial hp)
    exact ⟨hstrip.1, hstrip.2, hab p hp, hab' p hp⟩
  exact absurd ((measure_mono hsub).trans (volume_oneHalf_le a b a' b')) (not_le.2 hlt)

/-- **Theorem 1.2.** The ambidextrous sofa constant is at most `2√2 - 1`. -/
theorem ambidextrousSofaConstant_le_two_sqrt_two_sub_one :
    ambidextrousSofaConstant ≤ ENNReal.ofReal (2 * √2 - 1) :=
  iSup₂_le fun _ hs => hs.volume_le

end MovingSofa
