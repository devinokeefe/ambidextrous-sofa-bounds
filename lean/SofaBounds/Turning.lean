import SofaBounds.Motion
import SofaBounds.Slices

/-!
# No sideways turn, and turning the right way

Lemma 4.1 and Proposition 4.2 of the paper, stated without angles: an orientation `a ∈ [0°, 90°]`
is given by `C = cos a ≥ 0`, `S = sin a ≥ 0`, and the condition `a ≤ γ_T = arccos (1/T)` becomes
`1 ≤ C * T`. The conclusion says that at some time the sofa has rotated clockwise by exactly `a`,
so that it lies in the rotated hallway `L_a(u)`, written in the frame of the sofa.
-/

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped EuclideanGeometry unitInterval

/-! ### Auxiliary lemmas -/

theorem vec2_apply_zero (a b : ℝ) : (!₂[a, b] : ℝ²) 0 = a := by simp

theorem vec2_apply_one (a b : ℝ) : (!₂[a, b] : ℝ²) 1 = b := by simp

/-- During the motion, every point of the sofa lies in the hallway, written in coordinates. -/
theorem IsMovingSofa.inL0_of_mem {s : Set ℝ²} {m : I → E(2)} (h : IsMovingSofa s m) (t : I)
    {p : ℝ²} (hp : p ∈ s) :
    InL0 (cosPart (m t) * p 0 - sinPart (m t) * p 1 + (m t 0) 0)
      (sinPart (m t) * p 0 + cosPart (m t) * p 1 + (m t 0) 1) := by
  have := h.subset_hallway t ⟨p, hp, rfl⟩
  rw [mem_hallway_iff, apply_eq_of_path h.continuous h.zero, vec2_apply_zero,
    vec2_apply_one] at this
  exact this

/-- At the end of the motion, the sofa lies in the vertical side of the hallway. -/
theorem IsMovingSofa.final_of_mem {s : Set ℝ²} {m : I → E(2)} (h : IsMovingSofa s m)
    {p : ℝ²} (hp : p ∈ s) :
    0 ≤ cosPart (m 1) * p 0 - sinPart (m 1) * p 1 + (m 1 0) 0 ∧
      cosPart (m 1) * p 0 - sinPart (m 1) * p 1 + (m 1 0) 0 ≤ 1 := by
  have := h.final ⟨p, hp, rfl⟩
  rw [mem_verticalHallway_iff, apply_eq_of_path h.continuous h.zero, vec2_apply_zero] at this
  exact ⟨this.1, this.2.1⟩

/-- A unit vector `(c, s)` orthogonal to `(S, C)` with `c > s` is `(C, -S)`. -/
theorem rotation_eq_of_orthogonal {c s C S : ℝ} (hC : 0 < C) (hS : 0 ≤ S)
    (hCS : C ^ 2 + S ^ 2 = 1) (hcs : c ^ 2 + s ^ 2 = 1) (hh : S * c + C * s = 0)
    (hpos : 0 < c - s) : c = C ∧ s = -S := by
  have e1 : c = (c * C - s * S) * C := by linear_combination (-c) * hCS + S * hh
  have e2 : s = -((c * C - s * S) * S) := by linear_combination (-s) * hCS + C * hh
  have hl2 : (c * C - s * S) ^ 2 = 1 := by
    linear_combination hcs - (c * C - s * S) ^ 2 * hCS - (c + (c * C - s * S) * C) * e1 -
      (s - (c * C - s * S) * S) * e2
  have hlpos : 0 < c * C - s * S := by
    have hsum : c - s = (c * C - s * S) * (C + S) := by linear_combination e1 - e2
    by_contra hle
    rw [not_lt] at hle
    have : (c * C - s * S) * (C + S) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle (by linarith)
    linarith
  have hl1 : c * C - s * S = 1 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [e1, hl1, one_mul]
  · rw [e2, hl1, one_mul]

/-- **Proposition 4.2 (i)** in the frame of the sofa. -/
theorem IsMovingSofa.exists_rotation {s : Set ℝ²} {m : I → E(2)} (h : IsMovingSofa s m)
    {T : ℝ} (hT : √2 < T) (hvol : ENNReal.ofReal T < volume s)
    {C S : ℝ} (hC : 0 ≤ C) (hS : 0 ≤ S) (hCS : C ^ 2 + S ^ 2 = 1) (hCT : 1 ≤ C * T) :
    ∃ a b : ℝ, ∀ p ∈ s, InL0 (C * p 0 + S * p 1 + a) (-S * p 0 + C * p 1 + b) := by
  have hs : s ⊆ strip := h.initial.trans horizontalHallway_subset_strip
  have hT0 : 0 < T := lt_of_le_of_lt (Real.sqrt_nonneg 2) hT
  have hCpos : 0 < C := lt_of_le_of_ne hC (by rintro rfl; norm_num at hCT)
  have hcc : Continuous fun t => cosPart (m t) := continuous_cosPart h.continuous
  have hsc : Continuous fun t => sinPart (m t) := continuous_sinPart h.continuous
  -- Step 1: the sofa is never in a sideways position.
  have hne : ∀ t, cosPart (m t) - sinPart (m t) ≠ 0 := by
    intro t hts
    have heq : sinPart (m t) = cosPart (m t) := by linarith
    have hk : cosPart (m t) ^ 2 = 1 / 2 := by
      have := cosPart_sq_add_sinPart_sq (m t)
      rw [heq] at this
      linarith
    have hvs := volume_le_sqrt_two_of_sideways hs hk (a := (m t 0) 0) (b := (m t 0) 1)
      (fun p hp => by
        have := h.inL0_of_mem t hp
        rw [heq] at this
        exact this)
    have h2 : ENNReal.ofReal √2 ≤ ENNReal.ofReal T := ENNReal.ofReal_le_ofReal hT.le
    exact lt_irrefl _ (hvol.trans_le (hvs.trans h2))
  have hpos : ∀ t, 0 < cosPart (m t) - sinPart (m t) := by
    intro t
    by_contra hle
    rw [not_lt] at hle
    have hsub := intermediate_value_univ t 0 (hcc.sub hsc)
    have hmem : (0 : ℝ) ∈ Set.Icc (cosPart (m t) - sinPart (m t))
        (cosPart (m 0) - sinPart (m 0)) := ⟨hle, by simp [h.zero]⟩
    obtain ⟨t', ht'⟩ := hsub hmem
    exact hne t' ht'
  -- Step 2: at the end of the motion, `|cos| < 1 / T`.
  have hc1T : |cosPart (m 1)| * T < 1 := by
    by_cases hc1 : cosPart (m 1) = 0
    · simp [hc1]
    · have h1 : ∀ p ∈ s, 0 ≤ cosPart (m 1) * p 0 + (-sinPart (m 1)) * p 1 + (m 1 0) 0 ∧
          cosPart (m 1) * p 0 + (-sinPart (m 1)) * p 1 + (m 1 0) 0 ≤ 1 := by
        intro p hp
        have := h.final_of_mem hp
        constructor <;> linarith [this.1, this.2]
      have hv := volume_le_of_strip hs hc1 h1
      have hlt := hvol.trans_le hv
      rw [ENNReal.ofReal_lt_ofReal_iff'] at hlt
      have habs : 0 < |cosPart (m 1)| := abs_pos.2 hc1
      have := (lt_div_iff₀ habs).1 hlt.1
      linarith
  -- Step 3: the final orientation.
  have hcs1 := cosPart_sq_add_sinPart_sq (m 1)
  have hpos1 := hpos 1
  have habsC : |cosPart (m 1)| < C :=
    lt_of_mul_lt_mul_right (hc1T.trans_le hCT) hT0.le
  have h2T : 2 < T ^ 2 := (Real.sqrt_lt' hT0).1 hT
  have hc1sq : cosPart (m 1) ^ 2 * 2 < 1 := by
    have hA : 0 ≤ |cosPart (m 1)| * T := by positivity
    have hB : (|cosPart (m 1)| * T) ^ 2 < 1 := by nlinarith
    have hC2 : (|cosPart (m 1)| * T) ^ 2 = cosPart (m 1) ^ 2 * T ^ 2 := by
      rw [mul_pow, sq_abs]
    nlinarith [sq_nonneg (cosPart (m 1))]
  have hs1neg : sinPart (m 1) < 0 := by
    by_contra hge
    rw [not_lt] at hge
    nlinarith
  have hs1S : sinPart (m 1) < -S := by
    have hc1C2 : cosPart (m 1) ^ 2 < C ^ 2 := by
      have := abs_nonneg (cosPart (m 1))
      have h' : |cosPart (m 1)| ^ 2 < C ^ 2 := by nlinarith
      rwa [sq_abs] at h'
    have hs1sq : S ^ 2 < sinPart (m 1) ^ 2 := by linarith
    by_contra hge
    rw [not_lt] at hge
    nlinarith
  -- Step 4: the intermediate value theorem for `S cos + C sin`.
  have hh1 : S * cosPart (m 1) + C * sinPart (m 1) < 0 := by
    have : S * cosPart (m 1) ≤ S * C := by
      have := le_abs_self (cosPart (m 1))
      nlinarith
    nlinarith
  have hhc : Continuous fun t => S * cosPart (m t) + C * sinPart (m t) :=
    (continuous_const.mul hcc).add (continuous_const.mul hsc)
  have hmem : (0 : ℝ) ∈ Set.Icc (S * cosPart (m 1) + C * sinPart (m 1))
      (S * cosPart (m 0) + C * sinPart (m 0)) := ⟨hh1.le, by simpa [h.zero] using hS⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ 1 0 hhc hmem
  -- Step 5: at that time, the sofa has turned by exactly `a`.
  obtain ⟨hcC, hsS⟩ := rotation_eq_of_orthogonal hCpos hS hCS (cosPart_sq_add_sinPart_sq (m t))
    ht (hpos t)
  refine ⟨(m t 0) 0, (m t 0) 1, fun p hp => ?_⟩
  have := h.inL0_of_mem t hp
  rw [hcC, hsS] at this
  convert this using 2
  ring

/-- **Proposition 4.2 (ii)** in the frame of the sofa: the mirror image of `s` is a moving sofa,
so `s` lies in a mirrored hallway `ρ(L_a(v))`. -/
theorem exists_rotation_mirror {s : Set ℝ²}
    (h : ∃ m, IsMovingSofa (EuclideanGeometry.reflection midline '' s) m)
    {T : ℝ} (hT : √2 < T) (hvol : ENNReal.ofReal T < volume s)
    {C S : ℝ} (hC : 0 ≤ C) (hS : 0 ≤ S) (hCS : C ^ 2 + S ^ 2 = 1) (hCT : 1 ≤ C * T) :
    ∃ a b : ℝ, ∀ p ∈ s,
      InL0 (C * p 0 + S * (1 - p 1) + a) (-S * p 0 + C * (1 - p 1) + b) := by
  obtain ⟨m, hm⟩ := h
  have hvol' : ENNReal.ofReal T < volume (EuclideanGeometry.reflection midline '' s) := by
    rwa [volume_reflection_midline_image]
  obtain ⟨a, b, hab⟩ := hm.exists_rotation hT hvol' hC hS hCS hCT
  refine ⟨a, b, fun p hp => ?_⟩
  have := hab _ ⟨p, hp, rfl⟩
  rw [reflection_midline_apply, vec2_apply_zero, vec2_apply_one] at this
  exact this

end MovingSofa
