import SofaBounds.Turning
import SofaBounds.OneHalf
import SofaBounds.ZAux.Geometry

/-!
# The Z-shaped corridor (Section 4.2 of the paper)

Lemmas 4.4–4.6 and Theorem 4.7, in the frame of the sofa and without angles, and the Z-corridor
half of Theorem 1.2.

The orientation of the sofa at time `t` is recorded by the pair `(c, s) = (cosPart (m t),
sinPart (m t))`. Two closed conditions on `t` replace the lower and upper regions of the paper:
`HL t` says that `S_t` lies in the hallway `ρ(L_0)` (which contains `A_1 ∪ M`) and `HU t` says
that `S_t` lies in `R_{90°} L_0 + (1, D)` (which contains `M ∪ A_2`). The proof differs from the
paper in one point: Lemma 4.5 is proved without Lemma 2.3 (compactness). While the orientation is
within `45°` of horizontal the sofa is in one of the two hallways by a connectedness argument
(`corner_of_sin_lt_cos`); this is enough to find a time at which it has orientation `45°` and lies
in `ρ(L_0)` (`exists_diag`), and then Lemma 3.5 bounds its horizontal extent by `2 + 2√2 < 5`.
-/

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped EuclideanGeometry unitInterval

namespace ZCorr

/-! ### Area bounds -/

/-- Lemma 3.4 in the form used here: a subset of the strip of area greater than `T` that lies in
a strip `0 ≤ a x + b y + e ≤ 1` has `|a| T < 1`. -/
theorem abs_mul_lt_one {s : Set ℝ²} (hs : s ⊆ strip) {T : ℝ} (hvol : ENNReal.ofReal T < volume s)
    {a b e : ℝ} (h : ∀ p ∈ s, 0 ≤ a * p 0 + b * p 1 + e ∧ a * p 0 + b * p 1 + e ≤ 1) :
    |a| * T < 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have h2 := hvol.trans_le (volume_le_of_strip hs ha h)
  rw [ENNReal.ofReal_lt_ofReal_iff'] at h2
  have hpos : 0 < |a| := abs_pos.2 ha
  have := h2.1
  rw [lt_div_iff₀ hpos] at this
  linarith

/-- Lemma 3.6 in the form used here. -/
theorem false_of_sideways {s : Set ℝ²} (hs : s ⊆ strip) {T : ℝ} (hT : √2 < T)
    (hvol : ENNReal.ofReal T < volume s) {c a b : ℝ} (hc : c ^ 2 = 1 / 2)
    (h : ∀ p ∈ s, InL0 (c * p 0 - c * p 1 + a) (c * p 0 + c * p 1 + b)) : False := by
  have h1 := volume_le_sqrt_two_of_sideways hs hc h
  have h2 : ENNReal.ofReal √2 < ENNReal.ofReal T :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith [Real.sqrt_nonneg 2])).2 hT
  exact absurd (hvol.trans_le h1) (not_lt.2 h2.le)

/-! ### The two hallways of the corridor, seen from the sofa -/

section Motion

variable {D : ℝ} {s : Set ℝ²} {m : I → E(2)}

/-- `S_t ⊆ ρ(L_0)`: the hallway turning left around the lower corner. -/
def HL (s : Set ℝ²) (m : I → E(2)) (t : I) : Prop :=
  ∀ p ∈ s, InL0 ((m t p) 0) (1 - (m t p) 1)

/-- `S_t ⊆ R_{90°} L_0 + (1, D)`: the hallway turning right around the upper corner. -/
def HU (D : ℝ) (s : Set ℝ²) (m : I → E(2)) (t : I) : Prop :=
  ∀ p ∈ s, InL0 ((m t p) 1 - D) (1 - (m t p) 0)

theorem continuous_coord (hc : Continuous m) (p : ℝ²) (i : Fin 2) :
    Continuous fun t => (m t p) i :=
  (PiLp.continuous_apply 2 _ i).comp (continuous_apply_of_continuous hc p)

theorem isClosed_HL (hc : Continuous m) : IsClosed {t | HL s m t} := by
  have : {t | HL s m t} = ⋂ p ∈ s, {t | InL0 ((m t p) 0) (1 - (m t p) 1)} := by
    ext t; simp [HL]
  rw [this]
  exact isClosed_biInter fun p _ =>
    isClosed_setOf_inL0 (continuous_coord hc p 0) (continuous_const.sub (continuous_coord hc p 1))

theorem isClosed_HU (hc : Continuous m) : IsClosed {t | HU D s m t} := by
  have : {t | HU D s m t} = ⋂ p ∈ s, {t | InL0 ((m t p) 1 - D) (1 - (m t p) 0)} := by
    ext t; simp [HU]
  rw [this]
  exact isClosed_biInter fun p _ =>
    isClosed_setOf_inL0 ((continuous_coord hc p 1).sub continuous_const)
      (continuous_const.sub (continuous_coord hc p 0))

theorem coord_zero (hc : Continuous m) (h0 : m 0 = .refl ℝ ℝ²) (t : I) (p : ℝ²) :
    (m t p) 0 = cosPart (m t) * p 0 - sinPart (m t) * p 1 + (m t 0) 0 := by
  rw [apply_eq_of_path hc h0 t p]; simp

theorem coord_one (hc : Continuous m) (h0 : m 0 = .refl ℝ ℝ²) (t : I) (p : ℝ²) :
    (m t p) 1 = sinPart (m t) * p 0 + cosPart (m t) * p 1 + (m t 0) 1 := by
  rw [apply_eq_of_path hc h0 t p]; simp

theorem subset_strip' (h : PassesThroughZ D s m) : s ⊆ strip :=
  fun _ hp => ⟨(h.initial hp).2.1, (h.initial hp).2.2⟩

theorem mem_corridor (h : PassesThroughZ D s m) (t : I) {p : ℝ²} (hp : p ∈ s) :
    m t p ∈ zCorridor D :=
  h.subset_corridor t ⟨p, hp, rfl⟩

theorem HL_zero (h : PassesThroughZ D s m) : HL s m 0 := by
  intro p hp
  have := h.initial hp
  simp only [zEntry, Set.mem_ofPred_eq] at this
  rw [h.zero]
  simp only [AffineIsometryEquiv.coe_refl, id]
  exact Or.inl ⟨this.1, by linarith, by linarith⟩

theorem HU_one (h : PassesThroughZ D s m) : HU D s m 1 := by
  intro p hp
  have := h.final ⟨p, hp, rfl⟩
  simp only [zExit, Set.mem_ofPred_eq] at this
  exact Or.inr ⟨by linarith, by linarith, by linarith⟩

/-- At a time when the sofa lies in both hallways, it lies in the vertical strip, so `|c| T < 1`
(Lemma 3.4). -/
theorem abs_cos_mul_lt (h : PassesThroughZ D s m) (hD : 1 < D) {T : ℝ}
    (hvol : ENNReal.ofReal T < volume s) {t : I} (hl : HL s m t) (hu : HU D s m t) :
    |cosPart (m t)| * T < 1 := by
  apply abs_mul_lt_one (subset_strip' h) hvol (b := -sinPart (m t)) (e := (m t 0) 0)
  intro p hp
  have := mem_Icc_of_inL0_low_up hD (hl p hp) (hu p hp)
  rw [coord_zero h.continuous h.zero] at this
  constructor <;> linarith [this.1, this.2]

/-- At the end the sofa lies in the horizontal strip `D ≤ y ≤ D + 1`, so `|s| T < 1`. -/
theorem abs_sin_one_mul_lt (h : PassesThroughZ D s m) {T : ℝ}
    (hvol : ENNReal.ofReal T < volume s) : |sinPart (m 1)| * T < 1 := by
  apply abs_mul_lt_one (subset_strip' h) hvol (b := cosPart (m 1)) (e := (m 1 0) 1 - D)
  intro p hp
  have := h.final ⟨p, hp, rfl⟩
  simp only [zExit, Set.mem_ofPred_eq] at this
  rw [coord_one h.continuous h.zero] at this
  constructor <;> linarith [this.2.1, this.2.2]

/-- **Lemma 4.4.** The sofa never reaches orientation `-45°` or `135°`: `c + s > 0`. -/
theorem cos_add_sin_pos (h : PassesThroughZ D s m) (hD : 7 ≤ D) {T : ℝ} (hT : √2 < T)
    (hvol : ENNReal.ofReal T < volume s) (t : I) : 0 < cosPart (m t) + sinPart (m t) := by
  by_contra hneg
  push Not at hneg
  have hcont : Continuous fun t => cosPart (m t) + sinPart (m t) :=
    (continuous_cosPart h.continuous).add (continuous_sinPart h.continuous)
  have h0 : cosPart (m 0) + sinPart (m 0) = 1 := by rw [h.zero]; simp
  obtain ⟨t', ht'⟩ := intermediate_value_univ t 0 hcont ⟨hneg, by rw [h0]; norm_num⟩
  simp only at ht'
  set c := cosPart (m t') with hc_def
  have hs : sinPart (m t') = -c := by linarith
  have hc2 : c ^ 2 = 1 / 2 := by
    have := cosPart_sq_add_sinPart_sq (m t'); rw [hs] at this; linarith
  have hstrip := subset_strip' h
  have hX : ∀ p, (m t' p) 0 = c * p 0 + c * p 1 + (m t' 0) 0 := fun p => by
    rw [coord_zero h.continuous h.zero, hs]; ring
  have hY : ∀ p, (m t' p) 1 = -c * p 0 + c * p 1 + (m t' 0) 1 := fun p => by
    rw [coord_one h.continuous h.zero, hs]
  have hc1 : c ≤ 1 := by nlinarith
  have hc1' : -1 ≤ c := by nlinarith
  have hsum : ∀ p ∈ s, (m t' p) 0 + (m t' p) 1 ≤ (m t' 0) 0 + (m t' 0) 1 + 2 ∧
      (m t' 0) 0 + (m t' 0) 1 - 2 ≤ (m t' p) 0 + (m t' p) 1 := by
    intro p hp
    have hy : 0 ≤ p 1 ∧ p 1 ≤ 1 := hstrip hp
    rw [hX p, hY p]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 hc1) hy.1]
    · nlinarith [mul_nonneg (show 0 ≤ 1 + c by linarith) hy.1]
  by_cases hk : (m t' 0) 0 + (m t' 0) 1 ≤ 4
  · refine false_of_sideways hstrip hT hvol hc2 (a := 1 - (m t' 0) 1) (b := (m t' 0) 0)
      fun p hp => ?_
    have hl := inL0_low_of_mem (mem_corridor h t' hp) (by linarith [(hsum p hp).1])
    rw [inL0_comm, hX p, hY p] at hl
    exact inL0_congr hl (by ring) (by ring)
  · push Not at hk
    refine false_of_sideways hstrip hT hvol (c := -c) (by rw [neg_sq]; exact hc2)
      (a := (m t' 0) 1 - D) (b := 1 - (m t' 0) 0) fun p hp => ?_
    have hu := inL0_up_of_mem (mem_corridor h t' hp) (by linarith [(hsum p hp).2])
    rw [hX p, hY p] at hu
    exact inL0_congr hu (by ring) (by ring)

/-- If the sofa is in neither hallway at time `t`, it has a point in the entry arm and a point in
the exit arm. -/
theorem exists_low_high (h : PassesThroughZ D s m) {t : I} (hno : ¬ (HL s m t ∨ HU D s m t)) :
    ∃ p ∈ s, ∃ q ∈ s, (m t p) 1 ≤ 1 ∧ D ≤ (m t q) 1 := by
  rw [not_or] at hno
  obtain ⟨hnl, hnu⟩ := hno
  simp only [HL, HU, not_forall] at hnl hnu
  obtain ⟨q, hq, hq'⟩ := hnl
  obtain ⟨p, hp, hp'⟩ := hnu
  exact ⟨p, hp, q, hq, le_one_of_not_inL0_up (mem_corridor h t hp) hp',
    le_of_not_inL0_low (mem_corridor h t hq) hq'⟩

/-- **One corner at a time, while the orientation is within `45°` of horizontal.** If `s < c`
(and `c + s > 0`), the sofa lies in one of the two hallways: otherwise, being connected, it would
cross the vertical section of the corridor, of height `D - 1`, inside a strip of width `1` that
is less than `45°` from horizontal. -/
theorem corner_of_sin_lt_cos (h : PassesThroughZ D s m) (hD : 7 ≤ D)
    (hpos : ∀ t, 0 < cosPart (m t) + sinPart (m t)) {t : I}
    (hcs : sinPart (m t) < cosPart (m t)) : HL s m t ∨ HU D s m t := by
  by_contra hno
  obtain ⟨p, hp, q, hq, hpY, hqY⟩ := exists_low_high h hno
  have hcont : ContinuousOn (fun p => (m t p) 1) s :=
    ((PiLp.continuous_apply 2 _ 1).comp (m t).continuous).continuousOn
  have hIcc := h.isConnected.isPreconnected.intermediate_value hp hq hcont
  obtain ⟨r₁, hr₁, hY₁⟩ := hIcc ⟨(by linarith : (m t p) 1 ≤ 3 / 2), by linarith⟩
  obtain ⟨r₂, hr₂, hY₂⟩ := hIcc ⟨(by linarith : (m t p) 1 ≤ D - 1 / 2), by linarith⟩
  simp only at hY₁ hY₂
  have hX₁ := mem_Icc_of_mem_middle (mem_corridor h t hr₁) (by linarith) (by linarith)
  have hX₂ := mem_Icc_of_mem_middle (mem_corridor h t hr₂) (by linarith) (by linarith)
  have hy₁ : 0 ≤ r₁ 1 ∧ r₁ 1 ≤ 1 := subset_strip' h hr₁
  have hy₂ : 0 ≤ r₂ 1 ∧ r₂ 1 ≤ 1 := subset_strip' h hr₂
  have hcs1 := cosPart_sq_add_sinPart_sq (m t)
  have hpt := hpos t
  rw [coord_zero h.continuous h.zero] at hX₁ hX₂
  rw [coord_one h.continuous h.zero] at hY₁ hY₂
  set c := cosPart (m t)
  set w := sinPart (m t)
  set dX := (c * r₂ 0 - w * r₂ 1 + (m t 0) 0) - (c * r₁ 0 - w * r₁ 1 + (m t 0) 0) with hdX
  have key : r₂ 1 - r₁ 1 = c * (D - 2) - w * dX := by
    rw [hdX]
    linear_combination (r₁ 1 - r₂ 1) * hcs1 + c * hY₂ - c * hY₁
  have hdX1 : dX ≤ 1 := by rw [hdX]; linarith [hX₁.1, hX₂.2]
  have hdX2 : -1 ≤ dX := by rw [hdX]; linarith [hX₁.2, hX₂.1]
  have hc0 : 0 < c := by linarith
  have hwX : w * dX < c := by
    rcases le_total 0 w with hw | hw
    · nlinarith [mul_le_mul_of_nonneg_left hdX1 hw]
    · nlinarith [mul_le_mul_of_nonpos_left hdX2 hw]
  have h4 : c * 4 < 1 := by nlinarith
  nlinarith [mul_pos (sub_pos.2 hcs) hpt]

/-- **The sofa reaches orientation `45°` while it is still in the lower hallway.** -/
theorem exists_diag (h : PassesThroughZ D s m) (hD : 7 ≤ D) {T : ℝ} (hT : √2 < T)
    (hvol : ENNReal.ofReal T < volume s) :
    ∃ t₀, cosPart (m t₀) = sinPart (m t₀) ∧ HL s m t₀ := by
  have hpos := cos_add_sin_pos h hD hT hvol
  have hc := h.continuous
  have hQc : IsClosed {t | HU D s m t ∨ cosPart (m t) ≤ sinPart (m t)} := by
    rw [Set.ofPred_or]
    exact (isClosed_HU hc).union (isClosed_le (continuous_cosPart hc) (continuous_sinPart hc))
  obtain ⟨t₁, hl₁, hq₁, hall⟩ := exists_cross (P := HL s m)
    (Q := fun t => HU D s m t ∨ cosPart (m t) ≤ sinPart (m t)) (isClosed_HL hc) hQc
    (fun t => by
      rcases lt_or_ge (sinPart (m t)) (cosPart (m t)) with h1 | h1
      · rcases corner_of_sin_lt_cos h hD hpos h1 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h1))
    (HL_zero h) (Or.inl (HU_one h))
  have hle : cosPart (m t₁) ≤ sinPart (m t₁) := by
    rcases hq₁ with hu | hle
    · have h1 := abs_cos_mul_lt h (by linarith) hvol hl₁ hu
      exact (lt_and_pos_of_sq_lt_half (cosPart_sq_add_sinPart_sq (m t₁)) (hpos t₁)
        (sq_lt_half hT h1)).1.le
    · exact hle
  have hf : ContinuousOn (fun t => cosPart (m t) - sinPart (m t)) (Set.Icc 0 t₁) :=
    ((continuous_cosPart hc).sub (continuous_sinPart hc)).continuousOn
  have h0 : cosPart (m 0) - sinPart (m 0) = 1 := by rw [h.zero]; simp
  have hmem : (0 : ℝ) ∈ Set.Icc (cosPart (m t₁) - sinPart (m t₁))
      (cosPart (m 0) - sinPart (m 0)) := ⟨by linarith, by rw [h0]; norm_num⟩
  obtain ⟨t₀, ht₀, hz⟩ := intermediate_value_Icc' unitInterval.nonneg' hf hmem
  simp only at hz
  exact ⟨t₀, by linarith, hall t₀ ht₀.2⟩

/-- **Lemma 4.6 (one corner at a time).** A sofa of horizontal extent less than `5` is in one of
the two hallways at every time. -/
theorem corner (h : PassesThroughZ D s m) (hD : 7 ≤ D)
    (hwidth : ∀ p ∈ s, ∀ q ∈ s, q 0 - p 0 < 5) (t : I) : HL s m t ∨ HU D s m t := by
  by_contra hno
  obtain ⟨p, hp, q, hq, hpY, hqY⟩ := exists_low_high h hno
  rw [coord_one h.continuous h.zero] at hqY hpY
  have hw1 := hwidth p hp q hq
  have hw2 := hwidth q hq p hp
  have hyp : 0 ≤ p 1 ∧ p 1 ≤ 1 := subset_strip' h hp
  have hyq : 0 ≤ q 1 ∧ q 1 ≤ 1 := subset_strip' h hq
  have hcs := cosPart_sq_add_sinPart_sq (m t)
  have hw : |sinPart (m t)| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
  have hc : |cosPart (m t)| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
  have h1 : sinPart (m t) * (q 0 - p 0) < 5 :=
    calc _ ≤ |sinPart (m t) * (q 0 - p 0)| := le_abs_self _
      _ = |sinPart (m t)| * |q 0 - p 0| := abs_mul _ _
      _ ≤ |q 0 - p 0| := mul_le_of_le_one_left (abs_nonneg _) hw
      _ < 5 := abs_lt.2 ⟨by linarith, hw1⟩
  have h2 : cosPart (m t) * (q 1 - p 1) ≤ 1 :=
    calc _ ≤ |cosPart (m t) * (q 1 - p 1)| := le_abs_self _
      _ = |cosPart (m t)| * |q 1 - p 1| := abs_mul _ _
      _ ≤ |q 1 - p 1| := mul_le_of_le_one_left (abs_nonneg _) hc
      _ ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  nlinarith

end Motion

/-- **Theorem 4.7** in the frame of the sofa (see `PassesThroughZ.exists_hallways`). -/
theorem exists_hallways_aux {D T : ℝ} (hD : 7 ≤ D) (hT : √2 < T)
    {s : Set ℝ²} {m : I → E(2)} (h : PassesThroughZ D s m) (hvol : ENNReal.ofReal T < volume s) :
    (∀ C S : ℝ, 0 ≤ C → 0 ≤ S → C ^ 2 + S ^ 2 = 1 → 1 ≤ C * T → 1 ≤ S * T →
      ∃ a b : ℝ, ∀ p ∈ s, InL0 (C * p 0 + S * p 1 + a) (-S * p 0 + C * p 1 + b)) ∧
    (∀ C S : ℝ, 0 ≤ C → 0 ≤ S → C ^ 2 + S ^ 2 = 1 → 1 ≤ C * T →
      ∃ a b : ℝ, ∀ p ∈ s, InL0 (C * p 0 + S * (1 - p 1) + a) (-S * p 0 + C * (1 - p 1) + b)) := by
  have hpos := cos_add_sin_pos h hD hT hvol
  have hc := h.continuous
  have hT0 := (pos_and_two_lt_sq hT).1
  -- Lemma 4.5: the sofa reaches `45°` in the lower hallway, so it is short.
  obtain ⟨t₀, hdiag, hl₀⟩ := exists_diag h hD hT hvol
  have hwidth : ∀ p ∈ s, ∀ q ∈ s, q 0 - p 0 < 5 := by
    have hk2 : cosPart (m t₀) ^ 2 = 1 / 2 := by
      have := cosPart_sq_add_sinPart_sq (m t₀); rw [← hdiag] at this; linarith
    have hk : 0 < cosPart (m t₀) := by have := hpos t₀; rw [← hdiag] at this; linarith
    intro p hp q hq
    refine width_lt h.isConnected.isPreconnected (subset_strip' h) hk hk2
      (e0 := (m t₀ 0) 0) (e1 := (m t₀ 0) 1) (fun r hr => ?_) hp hq
    have := hl₀ r hr
    rw [coord_zero hc h.zero, coord_one hc h.zero, ← hdiag] at this
    exact inL0_congr this (by ring) (by ring)
  -- Lemma 4.6 and the times `t*`, `t**` of Theorem 4.7.
  have hcorner := corner h hD hwidth
  obtain ⟨t₁, hl₁, hu₁, hall₁⟩ :=
    exists_cross (isClosed_HL hc) (isClosed_HU hc) hcorner (HL_zero h) (HU_one h)
  obtain ⟨t₂, hl₂, hu₂, hall₂⟩ :=
    exists_cross' (isClosed_HL hc) (isClosed_HU hc) hcorner (HL_zero h) (HU_one h)
  have hc₁ := abs_cos_mul_lt h (by linarith) hvol hl₁ hu₁
  have hc₂ := abs_cos_mul_lt h (by linarith) hvol hl₂ hu₂
  have hs₁ := lt_and_pos_of_sq_lt_half (cosPart_sq_add_sinPart_sq (m t₁)) (hpos t₁)
    (sq_lt_half hT hc₁)
  have hs₂ := lt_and_pos_of_sq_lt_half (cosPart_sq_add_sinPart_sq (m t₂)) (hpos t₂)
    (sq_lt_half hT hc₂)
  have hend := abs_sin_one_mul_lt h hvol
  have hsc1 : sinPart (m 1) ^ 2 + cosPart (m 1) ^ 2 = 1 := by
    linarith [cosPart_sq_add_sinPart_sq (m 1)]
  have hend' := lt_and_pos_of_sq_lt_half hsc1 (by linarith [hpos 1]) (sq_lt_half hT hend)
  constructor
  · -- The right turn, on `[t**, 1]`.
    intro C S hC hS hCS hCT hST
    have hf : ContinuousOn (fun t => C * cosPart (m t) - S * sinPart (m t)) (Set.Icc t₂ 1) :=
      ((continuous_const.mul (continuous_cosPart hc)).sub
        (continuous_const.mul (continuous_sinPart hc))).continuousOn
    have hSC : S ^ 2 + C ^ 2 = 1 := by linarith
    have h2 := cross_le hT0 (cosPart_sq_add_sinPart_sq (m t₂)) hSC hS hC hs₂.2 hc₂ hST
    have h1 := cross_le hT0 hsc1 hCS hC hS hend'.2 hend hCT
    have hmem : (0 : ℝ) ∈ Set.Icc (C * cosPart (m t₂) - S * sinPart (m t₂))
        (C * cosPart (m 1) - S * sinPart (m 1)) := ⟨by linarith, by linarith⟩
    obtain ⟨t, ht, hz⟩ := intermediate_value_Icc unitInterval.le_one' hf hmem
    simp only at hz
    obtain ⟨hct, hst⟩ :=
      eq_of_cross_eq_zero (cosPart_sq_add_sinPart_sq (m t)) hSC hS hC (hpos t) hz
    refine ⟨(m t 0) 1 - D, 1 - (m t 0) 0, fun p hp => ?_⟩
    have := hall₂ t ht.1 p hp
    rw [coord_zero hc h.zero, coord_one hc h.zero, hct, hst] at this
    exact inL0_congr this (by ring) (by ring)
  · -- The left turn, on `[0, t*]`.
    intro C S hC hS hCS hCT
    have hf : ContinuousOn (fun t => S * cosPart (m t) - C * sinPart (m t)) (Set.Icc 0 t₁) :=
      ((continuous_const.mul (continuous_cosPart hc)).sub
        (continuous_const.mul (continuous_sinPart hc))).continuousOn
    have h1 := cross_le hT0 (cosPart_sq_add_sinPart_sq (m t₁)) hCS hC hS hs₁.2 hc₁ hCT
    have h0 : S * cosPart (m 0) - C * sinPart (m 0) = S := by rw [h.zero]; simp
    have hmem : (0 : ℝ) ∈ Set.Icc (S * cosPart (m t₁) - C * sinPart (m t₁))
        (S * cosPart (m 0) - C * sinPart (m 0)) := ⟨by linarith, by rw [h0]; exact hS⟩
    obtain ⟨t, ht, hz⟩ := intermediate_value_Icc' unitInterval.nonneg' hf hmem
    simp only at hz
    obtain ⟨hct, hst⟩ :=
      eq_of_cross_eq_zero (cosPart_sq_add_sinPart_sq (m t)) hCS hC hS (hpos t) hz
    refine ⟨(m t 0) 0 - S, 1 - C - (m t 0) 1, fun p hp => ?_⟩
    have := hall₁ t ht.2 p hp
    rw [coord_zero hc h.zero, coord_one hc h.zero, hct, hst] at this
    exact inL0_congr this (by ring) (by ring)

end ZCorr

/-- **Theorem 4.7** in the frame of the sofa. A right-turn angle `a` must satisfy
`δ_T ≤ a ≤ γ_T`, i.e. `1 ≤ S * T` and `1 ≤ C * T`; a left-turn angle `b` must satisfy
`0 ≤ b ≤ γ_T`, i.e. `1 ≤ C * T`. -/
theorem PassesThroughZ.exists_hallways {D T : ℝ} (hD : 7 ≤ D) (hT : √2 < T)
    {s : Set ℝ²} {m : I → E(2)} (h : PassesThroughZ D s m) (hvol : ENNReal.ofReal T < volume s) :
    (∀ C S : ℝ, 0 ≤ C → 0 ≤ S → C ^ 2 + S ^ 2 = 1 → 1 ≤ C * T → 1 ≤ S * T →
      ∃ a b : ℝ, ∀ p ∈ s, InL0 (C * p 0 + S * p 1 + a) (-S * p 0 + C * p 1 + b)) ∧
    (∀ C S : ℝ, 0 ≤ C → 0 ≤ S → C ^ 2 + S ^ 2 = 1 → 1 ≤ C * T →
      ∃ a b : ℝ, ∀ p ∈ s, InL0 (C * p 0 + S * (1 - p 1) + a) (-S * p 0 + C * (1 - p 1) + b)) :=
  ZCorr.exists_hallways_aux hD hT h hvol

/-- A set that passes through `Z_D` lies in the strip. -/
theorem PassesThroughZ.subset_strip {D : ℝ} {s : Set ℝ²} {m : I → E(2)}
    (h : PassesThroughZ D s m) : s ⊆ strip := fun _p hp => ⟨(h.initial hp).2.1, (h.initial hp).2.2⟩

/-- **Theorem 1.2, Z-corridor part.** -/
theorem zSofaConstant_le_two_sqrt_two_sub_one {D : ℝ} (hD : 7 ≤ D) :
    zSofaConstant D ≤ ENNReal.ofReal (2 * √2 - 1) := by
  refine iSup₂_le fun s ⟨m, hm⟩ => ?_
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
  obtain ⟨hA, hB⟩ := hm.exists_hallways hD hT hlt
  obtain ⟨a, b, hab⟩ := hA _ _ hC hC hCS hCT hCT
  obtain ⟨a', b', hab'⟩ := hB _ _ hC hC hCS hCT
  have hsub : s ⊆ {p : ℝ² | 0 ≤ p 1 ∧ p 1 ≤ 1 ∧
      InL0 (√2 / 2 * p 0 + √2 / 2 * p 1 + a) (-(√2 / 2) * p 0 + √2 / 2 * p 1 + b) ∧
      InL0 (√2 / 2 * p 0 + √2 / 2 * (1 - p 1) + a')
        (-(√2 / 2) * p 0 + √2 / 2 * (1 - p 1) + b')} := fun p hp =>
    ⟨(hm.subset_strip hp).1, (hm.subset_strip hp).2, hab p hp, hab' p hp⟩
  exact absurd ((measure_mono hsub).trans (volume_oneHalf_le a b a' b')) (not_le.2 hlt)

end MovingSofa
