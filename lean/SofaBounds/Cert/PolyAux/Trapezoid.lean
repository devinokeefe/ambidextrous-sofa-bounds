import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The area of one slab of a polygon

The region `{(x, y) : y0 ≤ y ≤ y1, ℓ(y) ≤ x ≤ r(y)}` between two affine functions has area at
most the trapezoid bound `(y1 - y0) * ((r - ℓ)₊(y0) + (r - ℓ)₊(y1)) / 2`: its area is
`∫ (r - ℓ)₊`, and the positive part of an affine function lies below its chord.
-/

open MeasureTheory Set

namespace SofaCert.PolyAux

/-- The chord parameter `t = (y - y0) / (y1 - y0)` of a point of `[y0, y1]`. -/
theorem chord_param {y0 y1 y : ℝ} (hy0 : y0 ≤ y) (hy1 : y ≤ y1) :
    0 ≤ (y - y0) / (y1 - y0) ∧ (y - y0) / (y1 - y0) ≤ 1 ∧
      y = y0 + (y - y0) / (y1 - y0) * (y1 - y0) := by
  rcases eq_or_lt_of_le (hy0.trans hy1) with h | h
  · have : y = y0 := le_antisymm (h ▸ hy1) hy0
    subst this
    simp [← h]
  · have hpos : 0 < y1 - y0 := sub_pos.mpr h
    refine ⟨div_nonneg (sub_nonneg.mpr hy0) hpos.le, div_le_one_of_le₀ (by linarith) hpos.le, ?_⟩
    field_simp
    ring

theorem affine_le_chord {c d y0 y1 y : ℝ} (hy0 : y0 ≤ y) (hy1 : y ≤ y1) :
    c + d * y ≤ max (c + d * y0) 0 +
      (max (c + d * y1) 0 - max (c + d * y0) 0) * ((y - y0) / (y1 - y0)) := by
  obtain ⟨ht0, ht1, hy⟩ := chord_param hy0 hy1
  set t := (y - y0) / (y1 - y0)
  have e : c + d * y = (1 - t) * (c + d * y0) + t * (c + d * y1) := by
    rw [hy]; ring
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left (le_max_left (c + d * y0) 0) (sub_nonneg.mpr ht1)
  have h2 := mul_le_mul_of_nonneg_left (le_max_left (c + d * y1) 0) ht0
  nlinarith

theorem chord_nonneg {a b y0 y1 y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hy0 : y0 ≤ y) (hy1 : y ≤ y1) :
    0 ≤ a + (b - a) * ((y - y0) / (y1 - y0)) := by
  obtain ⟨ht0, ht1, -⟩ := chord_param hy0 hy1
  set t := (y - y0) / (y1 - y0)
  have h1 := mul_nonneg ha (sub_nonneg.mpr ht1)
  have h2 := mul_nonneg hb ht0
  nlinarith

theorem integral_chord {a b y0 y1 : ℝ} (h : y0 ≤ y1) :
    ∫ y in y0..y1, (a + (b - a) * ((y - y0) / (y1 - y0))) = (y1 - y0) * (a + b) / 2 := by
  rcases eq_or_lt_of_le h with h | h
  · subst h; simp
  · have hne : y1 - y0 ≠ 0 := (sub_pos.mpr h).ne'
    have e : (fun y => a + (b - a) * ((y - y0) / (y1 - y0))) =
        fun y => (a - (b - a) / (y1 - y0) * y0) + (b - a) / (y1 - y0) * y := by
      ext y; field_simp; ring
    have hi : IntervalIntegrable (fun y : ℝ => (b - a) / (y1 - y0) * y) volume y0 y1 :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    rw [e, intervalIntegral.integral_add intervalIntegrable_const hi, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_id]
    rw [smul_eq_mul]
    field_simp
    ring

theorem volume_trapezoid_le (c0 c1 d0 d1 y0 y1 : ℝ) (h : y0 ≤ y1) :
    volume {q : ℝ × ℝ | y0 ≤ q.2 ∧ q.2 ≤ y1 ∧ c0 + c1 * q.2 ≤ q.1 ∧ q.1 ≤ d0 + d1 * q.2} ≤
      ENNReal.ofReal ((y1 - y0) * (max ((d0 + d1 * y0) - (c0 + c1 * y0)) 0 +
        max ((d0 + d1 * y1) - (c0 + c1 * y1)) 0) / 2) := by
  set S := {q : ℝ × ℝ | y0 ≤ q.2 ∧ q.2 ≤ y1 ∧ c0 + c1 * q.2 ≤ q.1 ∧ q.1 ≤ d0 + d1 * q.2}
  set a := max ((d0 + d1 * y0) - (c0 + c1 * y0)) 0
  set b := max ((d0 + d1 * y1) - (c0 + c1 * y1)) 0
  set g : ℝ → ℝ := fun y => a + (b - a) * ((y - y0) / (y1 - y0)) with hg
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_const).inter
      ((measurableSet_le (by fun_prop) measurable_fst).inter
      (measurableSet_le measurable_fst (by fun_prop))))
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
  have key : ∀ y, volume ((fun x => (x, y)) ⁻¹' S) ≤
      (Icc y0 y1).indicator (fun y => ENNReal.ofReal (g y)) y := by
    intro y
    by_cases hy : y ∈ Icc y0 y1
    · rw [indicator_of_mem hy]
      have e : (fun x => (x, y)) ⁻¹' S = Icc (c0 + c1 * y) (d0 + d1 * y) := by
        ext x; simp [S, hy.1, hy.2]
      rw [e, Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal
      have := affine_le_chord (c := d0 - c0) (d := d1 - c1) hy.1 hy.2
      simp only [hg, a, b]
      convert this using 2 <;> ring_nf
    · rw [indicator_of_notMem hy]
      have e : (fun x => (x, y)) ⁻¹' S = ∅ := by
        ext x
        simp only [S, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, -⟩
        exact hy ⟨h1, h2⟩
      simp [e]
  have ha : 0 ≤ a := le_max_right _ _
  have hb : 0 ≤ b := le_max_right _ _
  have hint : IntegrableOn g (Icc y0 y1) := by
    apply Continuous.integrableOn_Icc
    simp only [hg]
    fun_prop
  have hnn : 0 ≤ᵐ[volume.restrict (Icc y0 y1)] g :=
    (ae_restrict_mem measurableSet_Icc).mono fun y hy => chord_nonneg ha hb hy.1 hy.2
  calc ∫⁻ y, volume ((fun x => (x, y)) ⁻¹' S)
      ≤ ∫⁻ y, (Icc y0 y1).indicator (fun y => ENNReal.ofReal (g y)) y := lintegral_mono key
    _ = ∫⁻ y in Icc y0 y1, ENNReal.ofReal (g y) := lintegral_indicator measurableSet_Icc _
    _ = ENNReal.ofReal (∫ y in Icc y0 y1, g y) := (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal ((y1 - y0) * (a + b) / 2) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h, integral_chord h]

end SofaCert.PolyAux
