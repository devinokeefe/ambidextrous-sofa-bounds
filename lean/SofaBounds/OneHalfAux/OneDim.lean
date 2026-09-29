import Mathlib

/-!
# One-dimensional estimates for Proposition 3.7 (Appendix A)

* `psi` is the tent function `ψ(t) = (1 - |t|)₊`.
* `N η z` is the majorant `m̂_η(ξ)` of Appendix A written as a function of `z = |ξ|`; it is
  manifestly non-increasing in `z`.
* `sum_le` is the pointwise slice bound (the sum of the slice lengths of `Q_A`, `Q_B`, `C₁`, `C₂`).
* `window` is Lemma A.1, `centred` is the centred case of Lemma A.2, and `oneDim` combines them.
-/

noncomputable section

namespace MovingSofa.OneHalfAux

open MeasureTheory intervalIntegral Set

/-- The tent function `ψ(t) = (1 - |t|)₊`. -/
def psi (t : ℝ) : ℝ := max (1 - |t|) 0

/-- The majorant `m̂_η` of Appendix A as a function of `z = |ξ|`. -/
def N (η z : ℝ) : ℝ := max (max (min (2 - η - z) (2 - 2 * z)) (min 1 (1 + η - z))) 0

lemma N_nonneg (η z : ℝ) : 0 ≤ N η z := le_max_right _ _

lemma N_anti (η : ℝ) {z w : ℝ} (h : z ≤ w) : N η w ≤ N η z := by
  unfold N
  refine max_le_max (max_le_max ?_ ?_) le_rfl
  · exact min_le_min (by linarith) (by linarith)
  · exact min_le_min le_rfl (by linarith)

lemma continuous_N_abs (η : ℝ) : Continuous fun x : ℝ => N η |x| := by
  unfold N; fun_prop

lemma psi_neg (t : ℝ) : psi (-t) = psi t := by simp [psi, abs_neg]

/-- The core pointwise inequality `m̂_η(z) ≤ N η z` for `z, η ≥ 0`. -/
lemma core (z η : ℝ) (hz : 0 ≤ z) (hη : 0 ≤ η) :
    psi (z - η) + psi (z + η) + max (min 1 (η - z)) 0 ≤ N η z := by
  have hN1 : min (2 - η - z) (2 - 2 * z) ≤ N η z := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN2 : min 1 (1 + η - z) ≤ N η z := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN3 : 0 ≤ N η z := le_max_right _ _
  have hp2 : psi (z + η) = max (1 - (z + η)) 0 := by
    rw [psi, abs_of_nonneg (by linarith : 0 ≤ z + η)]
  rw [hp2]
  rcases le_total η z with h | h
  · have hp1 : psi (z - η) = max (1 - (z - η)) 0 := by
      rw [psi, abs_of_nonneg (by linarith : 0 ≤ z - η)]
    rw [hp1, max_eq_right (min_le_of_right_le (by linarith) : min 1 (η - z) ≤ 0)]
    rw [min_eq_right (by linarith : 2 - 2 * z ≤ 2 - η - z)] at hN1
    rw [min_eq_right (by linarith : 1 + η - z ≤ 1)] at hN2
    rcases le_total (1 - (z + η)) 0 with h' | h'
    · rw [max_eq_right h']
      rcases le_total (1 - (z - η)) 0 with h'' | h''
      · rw [max_eq_right h'']; linarith
      · rw [max_eq_left h'']; linarith
    · rw [max_eq_left h', max_eq_left (by linarith : (0:ℝ) ≤ 1 - (z - η))]; linarith
  · have hp1 : psi (z - η) = max (1 - (η - z)) 0 := by
      rw [psi, abs_of_nonpos (by linarith : z - η ≤ 0), neg_sub]
    rw [hp1]
    rw [min_eq_left (by linarith : (1:ℝ) ≤ 1 + η - z)] at hN2
    rcases le_total 1 (η - z) with h' | h'
    · rw [min_eq_left h', max_eq_left zero_le_one, max_eq_right (by linarith : 1 - (η - z) ≤ 0),
        max_eq_right (by linarith : 1 - (z + η) ≤ 0)]
      linarith
    · rw [min_eq_right h', max_eq_left (by linarith : (0:ℝ) ≤ η - z),
        max_eq_left (by linarith : (0:ℝ) ≤ 1 - (η - z))]
      rw [min_eq_left (by linarith : 2 - η - z ≤ 2 - 2 * z)] at hN1
      rcases le_total (1 - (z + η)) 0 with h'' | h''
      · rw [max_eq_right h'']; linarith
      · rw [max_eq_left h'']; linarith

lemma min_eq_sub_abs (η ξ : ℝ) : min (η - ξ) (ξ + η) = η - |ξ| := by
  rcases le_total 0 ξ with h | h
  · rw [abs_of_nonneg h, min_eq_left (by linarith)]
  · rw [abs_of_nonpos h, min_eq_right (by linarith)]; ring

/-- The pointwise slice bound: `ψ(u) + ψ(v) + min(1,-u,v)₊ + min(1,-v,u)₊ ≤ m̂`. -/
lemma sum_le (u v : ℝ) :
    psi u + psi v + max (min 1 (min (-u) v)) 0 + max (min 1 (min (-v) u)) 0
      ≤ N (|v - u| / 2) (|u + v| / 2) := by
  wlog huv : u ≤ v generalizing u v
  · have := this v u (by linarith)
    rw [abs_sub_comm, add_comm v u] at this
    linarith
  have h4 : max (min 1 (min (-v) u)) 0 = 0 := by
    apply max_eq_right
    rcases le_total u 0 with h | h
    · exact min_le_of_right_le (min_le_of_right_le h)
    · exact min_le_of_right_le (min_le_of_left_le (by linarith))
  rw [h4, add_zero]
  obtain ⟨η, ξ, rfl, rfl⟩ : ∃ η ξ : ℝ, u = ξ - η ∧ v = ξ + η :=
    ⟨(v - u) / 2, (u + v) / 2, by ring, by ring⟩
  have hη0 : 0 ≤ η := by linarith
  have e1 : |ξ + η - (ξ - η)| / 2 = η := by
    rw [show ξ + η - (ξ - η) = 2 * η by ring, abs_of_nonneg (by linarith)]; ring
  have e2 : |ξ - η + (ξ + η)| / 2 = |ξ| := by
    rw [show ξ - η + (ξ + η) = 2 * ξ by ring, abs_mul, abs_two]; ring
  have e3 : min (-(ξ - η)) (ξ + η) = η - |ξ| := by
    rw [← min_eq_sub_abs]; congr 1; ring
  rw [e1, e2, e3]
  rcases le_total 0 ξ with h | h
  · rw [abs_of_nonneg h]; exact core ξ η h hη0
  · rw [abs_of_nonpos h]
    have := core (-ξ) η (by linarith) hη0
    rw [show ξ - η = -(-ξ + η) by ring, psi_neg, show ξ + η = -(-ξ - η) by ring, psi_neg]
    linarith

lemma sqrt2_gt : (1.4 : ℝ) < √2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma sqrt2_lt : √2 < 1.5 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma sqrt2_sq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- **Lemma A.1** (window lemma). -/
lemma window (φ : ℝ → ℝ) (hφ : Continuous φ) (hmono : ∀ u v : ℝ, |u| ≤ |v| → φ v ≤ φ u)
    (t ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    ∫ x in t..t + ℓ, φ x ≤ ∫ x in -(ℓ / 2)..ℓ / 2, φ x := by
  have hi : ∀ a b : ℝ, IntervalIntegrable φ volume a b := fun a b => hφ.intervalIntegrable a b
  have e1 : ∫ x in t..t + ℓ, φ x =
      (∫ x in t..-(ℓ / 2), φ x) + (∫ x in -(ℓ / 2)..ℓ / 2, φ x) + ∫ x in ℓ / 2..t + ℓ, φ x := by
    have h1 : (∫ x in t..-(ℓ / 2), φ x) + (∫ x in -(ℓ / 2)..ℓ / 2, φ x) = ∫ x in t..ℓ / 2, φ x :=
      integral_add_adjacent_intervals (hi _ _) (hi _ _)
    have h2 : (∫ x in t..ℓ / 2, φ x) + (∫ x in ℓ / 2..t + ℓ, φ x) = ∫ x in t..t + ℓ, φ x :=
      integral_add_adjacent_intervals (hi _ _) (hi _ _)
    linarith
  set x0 := t + ℓ / 2 with hx0
  have e2 : ∫ x in ℓ / 2..t + ℓ, φ x = ∫ u in (0:ℝ)..x0, φ (u + ℓ / 2) := by
    rw [integral_comp_add_right φ (ℓ / 2), zero_add, hx0]; congr 1; ring
  have e3 : ∫ x in t..-(ℓ / 2), φ x = -∫ u in (0:ℝ)..x0, φ (u - ℓ / 2) := by
    rw [integral_comp_sub_right φ (ℓ / 2), zero_sub, integral_symm, hx0]; congr 2; ring
  have key : ∫ u in (0:ℝ)..x0, φ (u + ℓ / 2) ≤ ∫ u in (0:ℝ)..x0, φ (u - ℓ / 2) := by
    have hc1 : Continuous fun u => φ (u + ℓ / 2) := by fun_prop
    have hc2 : Continuous fun u => φ (u - ℓ / 2) := by fun_prop
    rcases le_total 0 x0 with h | h
    · refine integral_mono_on h (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _) ?_
      intro u hu
      apply hmono
      exact abs_le_abs (by linarith) (by linarith [hu.1])
    · have hm : ∫ u in x0..0, φ (u - ℓ / 2) ≤ ∫ u in x0..0, φ (u + ℓ / 2) := by
        refine integral_mono_on h (hc2.intervalIntegrable _ _) (hc1.intervalIntegrable _ _) ?_
        intro u hu
        apply hmono
        rw [abs_sub_comm u]
        exact abs_le_abs (by linarith [hu.2]) (by linarith)
      have s1 : ∫ u in (0:ℝ)..x0, φ (u + ℓ / 2) = -∫ u in x0..0, φ (u + ℓ / 2) :=
        integral_symm _ _
      have s2 : ∫ u in (0:ℝ)..x0, φ (u - ℓ / 2) = -∫ u in x0..0, φ (u - ℓ / 2) :=
        integral_symm _ _
      linarith
  linarith [e1, e2, e3, key]

/-- The pointwise bound on `[0, c]` used in the centred case. -/
lemma pointwise_c (η z : ℝ) (hη : 0 ≤ η) (_hz : 0 ≤ z) (hzc : z ≤ √2 / 2) :
    N η z ≤ 2 - 2 * z + (max (z + min η (1 / 2) - √2 / 2) 0
      - max ((√2 / 2 - z) + min η (1 / 2) - √2 / 2) 0) := by
  have s1 := sqrt2_gt
  have s2 := sqrt2_lt
  rw [show (√2 / 2 - z) + min η (1 / 2) - √2 / 2 = min η (1 / 2) - z by ring]
  have k1 := le_max_left (z + min η (1 / 2) - √2 / 2) 0
  have k2 := le_max_right (z + min η (1 / 2) - √2 / 2) 0
  set k := max (z + min η (1 / 2) - √2 / 2) 0
  have m1 := min_le_left (2 - η - z) (2 - 2 * z)
  have m2 := min_le_right (2 - η - z) (2 - 2 * z)
  have m3 := min_le_left (1 : ℝ) (1 + η - z)
  have m4 := min_le_right (1 : ℝ) (1 + η - z)
  unfold N
  rcases le_total η (1 / 2) with he | he
  · rw [min_eq_left he] at k1 ⊢
    rcases le_total η z with h | h
    · rw [max_eq_right (by linarith : η - z ≤ 0)]
      refine max_le (max_le ?_ ?_) ?_ <;> linarith
    · rw [max_eq_left (by linarith : 0 ≤ η - z)]
      refine max_le (max_le ?_ ?_) ?_ <;> linarith
  · rw [min_eq_right he] at k1 ⊢
    rcases le_total (1 / 2) z with h | h
    · rw [max_eq_right (by linarith : (1 / 2 : ℝ) - z ≤ 0)]
      refine max_le (max_le ?_ ?_) ?_ <;> linarith
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 / 2 - z)]
      refine max_le (max_le ?_ ?_) ?_ <;> linarith

/-- The centred case of **Lemma A.2**. -/
lemma centred (η : ℝ) (hη : 0 ≤ η) :
    ∫ x in -(√2 / 2)..√2 / 2, N η |x| ≤ 2 * √2 - 1 := by
  have hc : Continuous fun x : ℝ => N η |x| := continuous_N_abs η
  rw [← integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have hneg : ∫ x in -(√2 / 2)..0, N η |x| = ∫ x in (0:ℝ)..√2 / 2, N η |x| := by
    have := integral_comp_neg (a := 0) (b := √2 / 2) (fun x => N η |x|)
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  rw [hneg]
  set e := min η (1 / 2)
  set c := √2 / 2 with hcdef
  let k : ℝ → ℝ := fun z => max (z + e - c) 0
  have hk : Continuous k := by fun_prop
  have hk' : Continuous fun z => k (c - z) := by fun_prop
  have hle : ∫ x in (0:ℝ)..c, N η |x| ≤ ∫ x in (0:ℝ)..c, (2 - 2 * x + (k x - k (c - x))) := by
    refine integral_mono_on (by positivity) (hc.intervalIntegrable _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    intro x hx
    rw [abs_of_nonneg hx.1]
    exact pointwise_c η x hη hx.1 hx.2
  have hval : ∫ x in (0:ℝ)..c, (2 - 2 * x + (k x - k (c - x))) = 2 * c - c ^ 2 := by
    rw [integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
      integral_sub (hk.intervalIntegrable _ _) (hk'.intervalIntegrable _ _)]
    have hsym : ∫ x in (0:ℝ)..c, k (c - x) = ∫ x in (0:ℝ)..c, k x := by
      rw [integral_comp_sub_left k c, sub_self, sub_zero]
    rw [hsym, sub_self, add_zero,
      integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    simp only [smul_eq_mul]
    ring
  have hc2 : c ^ 2 = 1 / 2 := by
    rw [hcdef, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [hval, hc2] at hle
  rw [hcdef] at hle
  linarith

/-- **Lemma A.2** in the form used for Proposition 3.7 (after the substitution `s = √2 y`). -/
theorem oneDim (η m : ℝ) (hη : 0 ≤ η) :
    ∫ y in (0:ℝ)..1, √2 * N η |√2 * y - m| ≤ 2 * √2 - 1 := by
  have hs : √2 ≠ 0 := by positivity
  rw [intervalIntegral.integral_const_mul]
  have h1 : ∫ y in (0:ℝ)..1, N η |√2 * y - m| = (√2)⁻¹ * ∫ s in (0:ℝ)..√2, N η |s - m| := by
    have := integral_comp_mul_left (fun s => N η |s - m|) (a := 0) (b := 1) hs
    simpa using this
  rw [h1, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  have h2 : ∫ s in (0:ℝ)..√2, N η |s - m| = ∫ x in -m..-m + √2, N η |x| := by
    have := integral_comp_sub_right (fun x => N η |x|) (a := 0) (b := √2) m
    rw [this]; congr 1 <;> ring
  rw [h2]
  have hw := window (fun x => N η |x|) (continuous_N_abs η)
    (fun u v h => N_anti η (by simpa using h)) (-m) √2 (by positivity)
  calc ∫ x in -m..-m + √2, N η |x| ≤ ∫ x in -(√2 / 2)..√2 / 2, N η |x| := hw
    _ ≤ 2 * √2 - 1 := centred η hη

end MovingSofa.OneHalfAux
