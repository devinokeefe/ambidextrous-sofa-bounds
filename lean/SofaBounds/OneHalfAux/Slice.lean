import SofaBounds.Basic
import SofaBounds.OneHalfAux.OneDim

/-!
# Slicing for Proposition 3.7 (Appendix A)

We slice the set of Proposition 3.7 along horizontal lines `y = const` (these are the lines
`p + q = √2 y` of Appendix A). In the coordinate `p = (x + y)/√2` the slice is covered by four
intervals (the slices of `Q_A`, `Q_B`, `C₂`, `C₁`), whose total length is at most `m̂_η`.
-/

noncomputable section

namespace MovingSofa.OneHalfAux

open MeasureTheory Set

/-- Covering of the `p`-slice by four intervals: the slices of `Q_A`, `Q_B`, `C₂`, `C₁`. -/
lemma cover {p P0 P1 α β : ℝ}
    (h1 : (p ≤ P1 ∧ α ≤ p ∧ p ≤ α + 1) ∨ (P1 - 1 ≤ p ∧ p ≤ P1 ∧ α ≤ p))
    (h2 : (p ≤ β ∧ P0 ≤ p ∧ p ≤ P0 + 1) ∨ (β - 1 ≤ p ∧ p ≤ β ∧ P0 ≤ p)) :
    p ∈ Icc (max (P1 - 1) (β - 1)) (min P1 β) ∨
    p ∈ Icc (max α P0) (min (α + 1) (P0 + 1)) ∨
    p ∈ Icc (max (max α (β - 1)) (P0 + 1)) (min (min (α + 1) β) (P1 - 1)) ∨
    p ∈ Icc (max (max (P1 - 1) P0) (α + 1)) (min (min P1 (P0 + 1)) (β - 1)) := by
  simp only [mem_Icc, max_le_iff, le_min_iff]
  rcases h1 with ⟨h11, h12, h13⟩ | ⟨h11, h12, h13⟩ <;>
    rcases h2 with ⟨h21, h22, h23⟩ | ⟨h21, h22, h23⟩
  · right; left; constructorm* _ ∧ _ <;> linarith
  · by_cases hA : P1 - 1 ≤ p
    · left; constructorm* _ ∧ _ <;> linarith
    by_cases hB : p ≤ P0 + 1
    · right; left; constructorm* _ ∧ _ <;> linarith
    right; right; left
    push Not at hA hB
    constructorm* _ ∧ _ <;> linarith
  · by_cases hA : p ≤ α + 1
    · right; left; constructorm* _ ∧ _ <;> linarith
    by_cases hB : β - 1 ≤ p
    · left; constructorm* _ ∧ _ <;> linarith
    right; right; right
    push Not at hA hB
    constructorm* _ ∧ _ <;> linarith
  · left; constructorm* _ ∧ _ <;> linarith

lemma len_tent1 (a b : ℝ) : min a b - max (a - 1) (b - 1) ≤ 1 - |b - a| := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rw [min_eq_right h, max_eq_left (by linarith), abs_of_nonpos (by linarith)]; linarith

lemma len_tent2 (a b : ℝ) : min (a + 1) (b + 1) - max a b ≤ 1 - |a - b| := by
  rcases le_total a b with h | h
  · rw [min_eq_left (by linarith), max_eq_right h, abs_of_nonpos (by linarith)]; linarith
  · rw [min_eq_right (by linarith), max_eq_left h, abs_of_nonneg (by linarith)]; linarith

/-- The total length of the four intervals is at most `m̂_η`. -/
lemma slice_len (P0 P1 α β : ℝ) :
    max (min P1 β - max (P1 - 1) (β - 1)) 0 + max (min (α + 1) (P0 + 1) - max α P0) 0
      + max (min (min (α + 1) β) (P1 - 1) - max (max α (β - 1)) (P0 + 1)) 0
      + max (min (min P1 (P0 + 1)) (β - 1) - max (max (P1 - 1) P0) (α + 1)) 0
      ≤ N (|(α - P0) - (β - P1)| / 2) (|(β - P1) + (α - P0)| / 2) := by
  have hs := sum_le (β - P1) (α - P0)
  have t1 : max (min P1 β - max (P1 - 1) (β - 1)) 0 ≤ psi (β - P1) :=
    max_le_max (len_tent1 P1 β) le_rfl
  have t2 : max (min (α + 1) (P0 + 1) - max α P0) 0 ≤ psi (α - P0) :=
    max_le_max (len_tent2 α P0) le_rfl
  have t3 : max (min (min (α + 1) β) (P1 - 1) - max (max α (β - 1)) (P0 + 1)) 0 ≤
      max (min 1 (min (-(β - P1)) (α - P0))) 0 := by
    refine max_le_max ?_ le_rfl
    have a1 := min_le_left (min (α + 1) β) (P1 - 1)
    have a2 := min_le_left (α + 1) β
    have a4 := min_le_right (min (α + 1) β) (P1 - 1)
    have b1 := le_max_left (max α (β - 1)) (P0 + 1)
    have b2 := le_max_left α (β - 1)
    have b3 := le_max_right α (β - 1)
    have b4 := le_max_right (max α (β - 1)) (P0 + 1)
    exact le_min (by linarith) (le_min (by linarith) (by linarith))
  have t4 : max (min (min P1 (P0 + 1)) (β - 1) - max (max (P1 - 1) P0) (α + 1)) 0 ≤
      max (min 1 (min (-(α - P0)) (β - P1))) 0 := by
    refine max_le_max ?_ le_rfl
    have a1 := min_le_left (min P1 (P0 + 1)) (β - 1)
    have a3 := min_le_right P1 (P0 + 1)
    have a4 := min_le_right (min P1 (P0 + 1)) (β - 1)
    have b1 := le_max_left (max (P1 - 1) P0) (α + 1)
    have b2 := le_max_left (P1 - 1) P0
    have b3 := le_max_right (P1 - 1) P0
    have b4 := le_max_right (max (P1 - 1) P0) (α + 1)
    exact le_min (by linarith) (le_min (by linarith) (by linarith))
  linarith

lemma mem_scale {p x y lo hi : ℝ} (hp : √2 * p = x + y) (h : p ∈ Icc lo hi) :
    x ∈ Icc (√2 * lo - y) (√2 * hi - y) := by
  have h0 := Real.sqrt_nonneg 2
  have k1 := mul_le_mul_of_nonneg_left h.1 h0
  have k2 := mul_le_mul_of_nonneg_left h.2 h0
  constructor <;> linarith

/-- The measure of a horizontal slice, in terms of the four intervals. -/
lemma vol_generic (S : Set ℝ) (y P0 P1 α β : ℝ)
    (h : ∀ x ∈ S, ∃ p, √2 * p = x + y ∧
      ((p ≤ P1 ∧ α ≤ p ∧ p ≤ α + 1) ∨ (P1 - 1 ≤ p ∧ p ≤ P1 ∧ α ≤ p)) ∧
      ((p ≤ β ∧ P0 ≤ p ∧ p ≤ P0 + 1) ∨ (β - 1 ≤ p ∧ p ≤ β ∧ P0 ≤ p))) :
    volume S ≤
      ENNReal.ofReal (√2 * N (|(α - P0) - (β - P1)| / 2) (|(β - P1) + (α - P0)| / 2)) := by
  have hs0 := Real.sqrt_nonneg 2
  have hsub : S ⊆
      Icc (√2 * max (P1 - 1) (β - 1) - y) (√2 * min P1 β - y) ∪
      Icc (√2 * max α P0 - y) (√2 * min (α + 1) (P0 + 1) - y) ∪
      Icc (√2 * max (max α (β - 1)) (P0 + 1) - y) (√2 * min (min (α + 1) β) (P1 - 1) - y) ∪
      Icc (√2 * max (max (P1 - 1) P0) (α + 1) - y) (√2 * min (min P1 (P0 + 1)) (β - 1) - y) := by
    intro x hx
    obtain ⟨p, hp, h1, h2⟩ := h x hx
    rcases cover h1 h2 with h' | h' | h' | h'
    · exact Or.inl (Or.inl (Or.inl (mem_scale hp h')))
    · exact Or.inl (Or.inl (Or.inr (mem_scale hp h')))
    · exact Or.inl (Or.inr (mem_scale hp h'))
    · exact Or.inr (mem_scale hp h')
  have hvol : ∀ l u : ℝ,
      volume (Icc (√2 * l - y) (√2 * u - y)) ≤ ENNReal.ofReal (√2 * max (u - l) 0) := by
    intro l u
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    have := mul_le_mul_of_nonneg_left (le_max_left (u - l) 0) hs0
    linarith
  have hm : ∀ l u : ℝ, 0 ≤ √2 * max (u - l) 0 := fun l u => mul_nonneg hs0 (le_max_right _ _)
  have hlen := slice_len P0 P1 α β
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (measure_union_le (μ := (volume : Measure ℝ)) _ _) le_rfl).trans ?_
  refine (add_le_add
    (add_le_add (measure_union_le (μ := (volume : Measure ℝ)) _ _) le_rfl) le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (hvol _ _) (hvol _ _)) (hvol _ _)) (hvol _ _)).trans ?_
  rw [← ENNReal.ofReal_add (hm _ _) (hm _ _),
    ← ENNReal.ofReal_add (add_nonneg (hm _ _) (hm _ _)) (hm _ _),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (hm _ _) (hm _ _)) (hm _ _)) (hm _ _)]
  apply ENNReal.ofReal_le_ofReal
  have := mul_le_mul_of_nonneg_left hlen hs0
  linarith

/-- The slice bound for the set of Proposition 3.7. -/
theorem slice_bound (a b a' b' y : ℝ) :
    volume {x : ℝ | InL0 (√2 / 2 * x + √2 / 2 * y + a) (-(√2 / 2) * x + √2 / 2 * y + b) ∧
      InL0 (√2 / 2 * x + √2 / 2 * (1 - y) + a') (-(√2 / 2) * x + √2 / 2 * (1 - y) + b')} ≤
    ENNReal.ofReal
      (√2 * N (|b - b' + a' - a| / 2) |√2 * y - (√2 / 2 - (a + b - a' - b') / 2)|) := by
  have key := vol_generic {x : ℝ | InL0 (√2 / 2 * x + √2 / 2 * y + a)
      (-(√2 / 2) * x + √2 / 2 * y + b) ∧
      InL0 (√2 / 2 * x + √2 / 2 * (1 - y) + a') (-(√2 / 2) * x + √2 / 2 * (1 - y) + b')}
    y (√2 / 2 + b' - 1) (1 - a) (√2 * y + b - 1) (√2 * y - √2 / 2 - a' + 1) ?_
  · have eA : |(√2 * y + b - 1 - (√2 / 2 + b' - 1)) - (√2 * y - √2 / 2 - a' + 1 - (1 - a))| / 2
        = |b - b' + a' - a| / 2 := by
      congr 2; ring
    have eB : |(√2 * y - √2 / 2 - a' + 1 - (1 - a)) + (√2 * y + b - 1 - (√2 / 2 + b' - 1))| / 2
        = |√2 * y - (√2 / 2 - (a + b - a' - b') / 2)| := by
      rw [show (√2 * y - √2 / 2 - a' + 1 - (1 - a)) + (√2 * y + b - 1 - (√2 / 2 + b' - 1))
          = 2 * (√2 * y - (√2 / 2 - (a + b - a' - b') / 2)) by ring, abs_mul, abs_two]
      ring
    rw [eA, eB] at key
    exact key
  · rintro x ⟨h1, h2⟩
    refine ⟨√2 / 2 * x + √2 / 2 * y, ?_, ?_, ?_⟩
    · have := sqrt2_sq
      linear_combination (x + y) / 2 * this
    · unfold InL0 at h1
      rcases h1 with ⟨q1, q2, q3⟩ | ⟨q1, q2, q3⟩
      · left; refine ⟨?_, ?_, ?_⟩ <;> linarith
      · right; refine ⟨?_, ?_, ?_⟩ <;> linarith
    · unfold InL0 at h2
      rcases h2 with ⟨q1, q2, q3⟩ | ⟨q1, q2, q3⟩
      · left; refine ⟨?_, ?_, ?_⟩ <;> linarith
      · right; refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- **Proposition 3.7** in `ℝ × ℝ` coordinates. -/
theorem main (a b a' b' : ℝ) :
    volume {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧
      InL0 (√2 / 2 * q.1 + √2 / 2 * q.2 + a) (-(√2 / 2) * q.1 + √2 / 2 * q.2 + b) ∧
      InL0 (√2 / 2 * q.1 + √2 / 2 * (1 - q.2) + a')
        (-(√2 / 2) * q.1 + √2 / 2 * (1 - q.2) + b')}
      ≤ ENNReal.ofReal (2 * √2 - 1) := by
  set S := {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧
      InL0 (√2 / 2 * q.1 + √2 / 2 * q.2 + a) (-(√2 / 2) * q.1 + √2 / 2 * q.2 + b) ∧
      InL0 (√2 / 2 * q.1 + √2 / 2 * (1 - q.2) + a')
        (-(√2 / 2) * q.1 + √2 / 2 * (1 - q.2) + b')} with hSdef
  have hS : MeasurableSet S := by
    simp only [hSdef, InL0]
    measurability
  set η := |b - b' + a' - a| / 2 with hη
  set m := √2 / 2 - (a + b - a' - b') / 2 with hm
  have hg : Continuous fun y : ℝ => √2 * N η |√2 * y - m| := by
    unfold N; fun_prop
  have hslice : ∀ y : ℝ, volume ((fun x => (x, y)) ⁻¹' S) ≤
      (Icc (0:ℝ) 1).indicator (fun y => ENNReal.ofReal (√2 * N η |√2 * y - m|)) y := by
    intro y
    by_cases hy : y ∈ Icc (0:ℝ) 1
    · rw [indicator_of_mem hy]
      have e : (fun x => (x, y)) ⁻¹' S =
          {x : ℝ | InL0 (√2 / 2 * x + √2 / 2 * y + a) (-(√2 / 2) * x + √2 / 2 * y + b) ∧
            InL0 (√2 / 2 * x + √2 / 2 * (1 - y) + a')
              (-(√2 / 2) * x + √2 / 2 * (1 - y) + b')} := by
        ext x
        simp [hSdef, hy.1, hy.2]
      rw [e]
      exact slice_bound a b a' b' y
    · rw [indicator_of_notMem hy]
      have e : (fun x => (x, y)) ⁻¹' S = ∅ := by
        ext x
        simp only [hSdef, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨h0, h1, -⟩
        exact hy ⟨h0, h1⟩
      rw [e, measure_empty]
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
  calc ∫⁻ y, volume ((fun x => (x, y)) ⁻¹' S)
      ≤ ∫⁻ y, (Icc (0:ℝ) 1).indicator (fun y => ENNReal.ofReal (√2 * N η |√2 * y - m|)) y :=
        lintegral_mono hslice
    _ = ∫⁻ y in Icc (0:ℝ) 1, ENNReal.ofReal (√2 * N η |√2 * y - m|) :=
        lintegral_indicator measurableSet_Icc _
    _ = ENNReal.ofReal (∫ y in Icc (0:ℝ) 1, √2 * N η |√2 * y - m|) :=
        (ofReal_integral_eq_lintegral_ofReal hg.integrableOn_Icc
          (ae_of_all _ fun y => mul_nonneg (Real.sqrt_nonneg 2) (N_nonneg _ _))).symm
    _ ≤ ENNReal.ofReal (2 * √2 - 1) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
        exact oneDim η m (by positivity)

end MovingSofa.OneHalfAux
