import SofaBounds.Basic

/-!
# Auxiliary lemmas for the Z-shaped corridor (no motions involved)

Elementary facts about the corridor `Z_D` and the two hallways that contain its lower and upper
parts, crossing times for two closed sets covering `[0, 1]`, inequalities between unit vectors
(pairs `(cos, sin)`, no angles), and the width estimate of Lemma 3.5 at `45°`.
-/

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped EuclideanGeometry unitInterval

namespace ZCorr

/-! ### Elementary facts about `InL0` and the corridor -/

theorem inL0_comm {P Q : ℝ} : InL0 P Q ↔ InL0 Q P := by
  unfold InL0
  constructor <;> rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
  · exact Or.inr ⟨h2, h3, h1⟩
  · exact Or.inl ⟨h3, h1, h2⟩
  · exact Or.inr ⟨h2, h3, h1⟩
  · exact Or.inl ⟨h3, h1, h2⟩

theorem inL0_congr {P Q P' Q' : ℝ} (h : InL0 P Q) (hP : P' = P) (hQ : Q' = Q) : InL0 P' Q' :=
  hP ▸ hQ ▸ h

theorem isClosed_setOf_inL0 {X : Type*} [TopologicalSpace X] {f g : X → ℝ} (hf : Continuous f)
    (hg : Continuous g) : IsClosed {x | InL0 (f x) (g x)} := by
  simp only [InL0, Set.ofPred_or, Set.ofPred_and]
  refine IsClosed.union ?_ ?_ <;> refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_) <;>
    exact isClosed_le (by fun_prop) (by fun_prop)

theorem mem_zCorridor_iff {D : ℝ} {q : ℝ²} : q ∈ zCorridor D ↔
    (q 0 ≤ 1 ∧ 0 ≤ q 1 ∧ q 1 ≤ 1) ∨ (0 ≤ q 0 ∧ q 0 ≤ 1 ∧ 0 ≤ q 1 ∧ q 1 ≤ D + 1) ∨
      (0 ≤ q 0 ∧ D ≤ q 1 ∧ q 1 ≤ D + 1) := by
  simp only [zCorridor, zEntry, zMiddle, zExit, Set.mem_union, Set.mem_ofPred_eq, or_assoc]

/-- Points of `Z_D` below the line `x + y = D` lie in `ρ(L_0)`. -/
theorem inL0_low_of_mem {D : ℝ} {q : ℝ²} (hq : q ∈ zCorridor D) (h : q 0 + q 1 < D) :
    InL0 (q 0) (1 - q 1) := by
  rw [mem_zCorridor_iff] at hq
  unfold InL0
  rcases hq with h1 | h1 | h1
  · exact Or.inl ⟨h1.1, by linarith, by linarith⟩
  · exact Or.inr ⟨h1.1, h1.2.1, by linarith⟩
  · exact absurd h (by linarith)

/-- Points of `Z_D` above the line `x + y = 2` lie in `R_{90°} L_0 + (1, D)`. -/
theorem inL0_up_of_mem {D : ℝ} {q : ℝ²} (hq : q ∈ zCorridor D) (h : 2 < q 0 + q 1) :
    InL0 (q 1 - D) (1 - q 0) := by
  rw [mem_zCorridor_iff] at hq
  unfold InL0
  rcases hq with h1 | h1 | h1
  · exact absurd h (by linarith)
  · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith, by linarith⟩

theorem le_of_not_inL0_low {D : ℝ} {q : ℝ²} (hq : q ∈ zCorridor D) (h : ¬ InL0 (q 0) (1 - q 1)) :
    D ≤ q 1 := by
  rw [mem_zCorridor_iff] at hq
  unfold InL0 at h
  rcases hq with h1 | h1 | h1
  · exact absurd (Or.inl ⟨h1.1, by linarith, by linarith⟩) h
  · exact absurd (Or.inr ⟨h1.1, h1.2.1, by linarith⟩) h
  · exact h1.2.1

theorem le_one_of_not_inL0_up {D : ℝ} {q : ℝ²} (hq : q ∈ zCorridor D)
    (h : ¬ InL0 (q 1 - D) (1 - q 0)) : q 1 ≤ 1 := by
  rw [mem_zCorridor_iff] at hq
  unfold InL0 at h
  rcases hq with h1 | h1 | h1
  · exact h1.2.2
  · exact absurd (Or.inl ⟨by linarith, by linarith, by linarith⟩) h
  · exact absurd (Or.inr ⟨by linarith, by linarith, by linarith⟩) h

/-- `ρ(L_0) ∩ (R_{90°} L_0 + (1, D))` lies in the vertical strip `0 ≤ x ≤ 1`. -/
theorem mem_Icc_of_inL0_low_up {D : ℝ} (hD : 1 < D) {q : ℝ²} (h1 : InL0 (q 0) (1 - q 1))
    (h2 : InL0 (q 1 - D) (1 - q 0)) : 0 ≤ q 0 ∧ q 0 ≤ 1 := by
  unfold InL0 at h1 h2
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact ⟨by linarith, by linarith⟩
    · exact absurd h1.2.2 (by linarith)
  · exact ⟨h1.1, h1.2.1⟩

theorem mem_Icc_of_mem_middle {D : ℝ} {q : ℝ²} (hq : q ∈ zCorridor D) (h1 : 1 < q 1)
    (h2 : q 1 < D) : 0 ≤ q 0 ∧ q 0 ≤ 1 := by
  rw [mem_zCorridor_iff] at hq
  rcases hq with h | h | h
  · exact absurd h.2.2 (by linarith)
  · exact ⟨h.1, h.2.1⟩
  · exact absurd h.2.1 (by linarith)

/-! ### Crossing times -/

theorem exists_cross {P Q : I → Prop} (hP : IsClosed {t | P t}) (hQ : IsClosed {t | Q t})
    (hPQ : ∀ t, P t ∨ Q t) (h0 : P 0) (h1 : Q 1) : ∃ t₀, P t₀ ∧ Q t₀ ∧ ∀ t ≤ t₀, P t := by
  set t₀ := sInf {t | Q t}
  have hQt₀ : Q t₀ := hQ.csInf_mem ⟨1, h1⟩ (OrderBot.bddBelow _)
  have hlt : ∀ t < t₀, P t := fun t ht =>
    (hPQ t).resolve_right fun hq => (not_le.2 ht) (csInf_le (OrderBot.bddBelow _) hq)
  have hPt₀ : P t₀ := by
    by_cases ht0 : t₀ = 0
    · rw [ht0]; exact h0
    have hpos : 0 < t₀ := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm ht0)
    have hsub : Set.Iio t₀ ⊆ {t | P t} := fun t ht => hlt t ht
    have := hP.closure_subset_iff.2 hsub
    rw [closure_Iio' (a := t₀) ⟨0, hpos⟩] at this
    exact this (le_refl t₀)
  refine ⟨t₀, hPt₀, hQt₀, fun t ht => ?_⟩
  rcases ht.lt_or_eq with ht | rfl
  · exact hlt t ht
  · exact hPt₀

theorem exists_cross' {P Q : I → Prop} (hP : IsClosed {t | P t}) (hQ : IsClosed {t | Q t})
    (hPQ : ∀ t, P t ∨ Q t) (h0 : P 0) (h1 : Q 1) : ∃ t₀, P t₀ ∧ Q t₀ ∧ ∀ t, t₀ ≤ t → Q t := by
  set t₀ := sSup {t | P t}
  have hPt₀ : P t₀ := hP.csSup_mem ⟨0, h0⟩ (OrderTop.bddAbove _)
  have hgt : ∀ t, t₀ < t → Q t := fun t ht =>
    (hPQ t).resolve_left fun hp => (not_le.2 ht) (le_csSup (OrderTop.bddAbove _) hp)
  have hQt₀ : Q t₀ := by
    by_cases ht1 : t₀ = 1
    · rw [ht1]; exact h1
    have hlt : t₀ < 1 := lt_of_le_of_ne unitInterval.le_one' ht1
    have hsub : Set.Ioi t₀ ⊆ {t | Q t} := fun t ht => hgt t ht
    have := hQ.closure_subset_iff.2 hsub
    rw [closure_Ioi' (a := t₀) ⟨1, hlt⟩] at this
    exact this (le_refl t₀)
  refine ⟨t₀, hPt₀, hQt₀, fun t ht => ?_⟩
  rcases ht.lt_or_eq with ht | rfl
  · exact hgt t ht
  · exact hQt₀

/-- Two unit vectors that are parallel and both in the open half-plane `x + y > 0` are equal. -/
theorem eq_of_cross_eq_zero {c s C S : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hCS : C ^ 2 + S ^ 2 = 1)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hpos : 0 < c + s) (h : S * c - C * s = 0) : c = C ∧ s = S := by
  have hdot : (c * C + s * S) ^ 2 = 1 := by nlinarith
  have hdot' : c * C + s * S = 1 ∨ c * C + s * S = -1 := by
    have : (c * C + s * S - 1) * (c * C + s * S + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h2 | h2
    · left; linarith
    · right; linarith
  rcases hdot' with h1 | h1
  · have h2 : (c - C) ^ 2 + (s - S) ^ 2 = 0 := by nlinarith
    have h3 : (c - C) ^ 2 = 0 := by nlinarith [sq_nonneg (c - C), sq_nonneg (s - S)]
    have h4 : (s - S) ^ 2 = 0 := by nlinarith [sq_nonneg (c - C), sq_nonneg (s - S)]
    exact ⟨by nlinarith [pow_eq_zero_iff (n := 2) (a := c - C) two_ne_zero |>.1 h3],
      by nlinarith [pow_eq_zero_iff (n := 2) (a := s - S) two_ne_zero |>.1 h4]⟩
  · exfalso
    have h2 : (c + C) ^ 2 + (s + S) ^ 2 = 0 := by nlinarith
    have h3 : (c + C) ^ 2 = 0 := by nlinarith [sq_nonneg (c + C), sq_nonneg (s + S)]
    have h4 : (s + S) ^ 2 = 0 := by nlinarith [sq_nonneg (c + C), sq_nonneg (s + S)]
    have h5 := pow_eq_zero_iff (n := 2) (a := c + C) two_ne_zero |>.1 h3
    have h6 := pow_eq_zero_iff (n := 2) (a := s + S) two_ne_zero |>.1 h4
    linarith

/-! ### Inequalities between unit vectors -/

theorem pos_and_two_lt_sq {T : ℝ} (hT : √2 < T) : 0 < T ∧ 2 < T ^ 2 := by
  have h2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
  have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  exact ⟨by linarith, by nlinarith⟩

theorem sq_lt_half {c T : ℝ} (hT : √2 < T) (h : |c| * T < 1) : c ^ 2 < 1 / 2 := by
  obtain ⟨hT0, hT2⟩ := pos_and_two_lt_sq hT
  have h1 : 0 ≤ |c| * T := by positivity
  have h2 : (|c| * T) ^ 2 < 1 := by nlinarith
  have h3 : (|c| * T) ^ 2 = c ^ 2 * T ^ 2 := by rw [mul_pow, sq_abs]
  nlinarith [mul_le_mul_of_nonneg_left hT2.le (sq_nonneg c)]

theorem lt_and_pos_of_sq_lt_half {c w : ℝ} (hcs : c ^ 2 + w ^ 2 = 1) (hpos : 0 < c + w)
    (h : c ^ 2 < 1 / 2) : c < w ∧ 0 < w := by
  have hw : 0 < w := by
    by_contra hn
    push Not at hn
    nlinarith [mul_pos hpos (show 0 < c - w by linarith)]
  refine ⟨?_, hw⟩
  by_contra hn
  push Not at hn
  nlinarith [mul_le_mul hn hn hw.le (by linarith)]

/-- If `|c| T < 1 ≤ C T`, `(c, w)` and `(C, S)` are unit vectors, `w > 0` and `C, S ≥ 0`, then
`S c ≤ C w`: the direction `(c, w)` is at least as steep as `(C, S)`. -/
theorem cross_le {c w C S T : ℝ} (hT : 0 < T) (hcs : c ^ 2 + w ^ 2 = 1) (hCS : C ^ 2 + S ^ 2 = 1)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hw : 0 < w) (hc : |c| * T < 1) (hCT : 1 ≤ C * T) :
    S * c ≤ C * w := by
  have habs : |c| < C := lt_of_mul_lt_mul_right (hc.trans_le hCT) hT.le
  have hc2 : c ^ 2 ≤ C ^ 2 := by
    rw [← sq_abs c]; nlinarith [abs_nonneg c]
  have hSw : S ≤ w := by
    by_contra hn
    push Not at hn
    nlinarith [mul_lt_mul'' hn hn hw.le hw.le]
  calc S * c ≤ S * |c| := mul_le_mul_of_nonneg_left (le_abs_self c) hS
    _ ≤ S * C := mul_le_mul_of_nonneg_left habs.le hS
    _ ≤ w * C := mul_le_mul_of_nonneg_right hSw hC
    _ = C * w := mul_comm _ _

/-- **Lemma 3.5 (width) at `45°`.** A connected subset of the strip that lies in a mirrored
hallway `ρ(L_{45°}(v))` has horizontal extent at most `2 + 2√2 < 5`. -/
theorem width_lt {s : Set ℝ²} (hconn : IsPreconnected s) (hs : s ⊆ strip) {k e0 e1 : ℝ}
    (hk : 0 < k) (hk2 : k ^ 2 = 1 / 2)
    (h : ∀ p ∈ s, InL0 (k * p 0 - k * p 1 + e0) (1 - (k * p 0 + k * p 1 + e1)))
    {p q : ℝ²} (hp : p ∈ s) (hq : q ∈ s) : q 0 - p 0 < 5 := by
  by_contra hge
  push Not at hge
  have hJ : IsPreconnected ((fun r : ℝ² => k * r 0) '' s) :=
    hconn.image _ ((continuous_const.mul (PiLp.continuous_apply 2 _ 0)).continuousOn)
  have hsub : Set.Icc (k * p 0) (k * q 0) ⊆
      Set.Icc (-e1 - k) (1 - e1) ∪ Set.Icc (-e0) (1 - e0 + k) := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := hJ.Icc_subset ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩ hz
    have hy : 0 ≤ r 1 ∧ r 1 ≤ 1 := hs hr
    have hky : 0 ≤ k * r 1 ∧ k * r 1 ≤ k := ⟨mul_nonneg hk.le hy.1, by nlinarith [hy.2]⟩
    rcases h r hr with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left; exact ⟨by linarith, by linarith⟩
    · right; exact ⟨by linarith, by linarith⟩
  have hle : ENNReal.ofReal (k * q 0 - k * p 0) ≤ ENNReal.ofReal (2 + 2 * k) := by
    calc ENNReal.ofReal (k * q 0 - k * p 0) = volume (Set.Icc (k * p 0) (k * q 0)) :=
          Real.volume_Icc.symm
      _ ≤ volume (Set.Icc (-e1 - k) (1 - e1) ∪ Set.Icc (-e0) (1 - e0 + k)) := measure_mono hsub
      _ ≤ volume (Set.Icc (-e1 - k) (1 - e1)) + volume (Set.Icc (-e0) (1 - e0 + k)) :=
          measure_union_le _ _
      _ = ENNReal.ofReal (1 + k) + ENNReal.ofReal (1 + k) := by
          rw [Real.volume_Icc, Real.volume_Icc]
          congr 1 <;> congr 1 <;> ring
      _ = ENNReal.ofReal (2 + 2 * k) := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1; ring
  have := (ENNReal.ofReal_le_ofReal_iff (by linarith : (0 : ℝ) ≤ 2 + 2 * k)).1 hle
  nlinarith [mul_le_mul_of_nonneg_left hge hk.le]

end ZCorr

end MovingSofa
