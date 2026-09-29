import SofaBounds.Cert.Spec

/-!
# Normalisation (Lemma 5.1)

If `λ*(B_W ∩ X(u)) ≤ T` for all parameters `u` in the root box, then every connected subset of
the strip that lies in the four hallways has area at most `T`. The proof uses the width lemma
(Lemma 3.5) for hallway 0 to translate the set into `B_W`, and then moves each parameter into the
root box without losing the set.
-/

noncomputable section

namespace SofaCert

open MeasureTheory MovingSofa
open scoped EuclideanGeometry

namespace Normalise

/-! ### Elementary facts about a single hallway -/

/-- Both arms of a hallway satisfy `f ≤ u₁ + 1` and `g ≤ u₂ + 1`. -/
theorem inHall_le {f g u₁ u₂ : ℝ} (h : InHall f g u₁ u₂) : f ≤ u₁ + 1 ∧ g ≤ u₂ + 1 := by
  rcases h with ⟨_, h2, h3⟩ | ⟨h1, _, h3⟩
  · exact ⟨h2, h3⟩
  · exact ⟨h1, h3⟩

/-- Shifting the coordinates shifts the parameters. -/
theorem inHall_shift {f g u₁ u₂ a b : ℝ} (h : InHall (f + a) (g + b) u₁ u₂) :
    InHall f g (u₁ - a) (u₂ - b) := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith, by linarith⟩

/-- Clamping the parameters from above (proof of Lemma 5.1): if `f ≤ F` and `g ≤ G`, then
replacing `u₁` by `min u₁ F` and `u₂` by `min u₂ G` keeps the point in the hallway. (If `u₁ > F`
the point is in the second arm, which only needs `f ≤ u₁ + 1`; symmetrically for `u₂`.) -/
theorem inHall_clamp {f g u₁ u₂ F G : ℝ} (h : InHall f g u₁ u₂) (hf : f ≤ F) (hg : g ≤ G) :
    InHall f g (min u₁ F) (min u₂ G) := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left
    rw [min_eq_left (h1.trans hf)]
    refine ⟨h1, h2, ?_⟩
    rcases le_total u₂ G with h | h
    · rw [min_eq_left h]; exact h3
    · rw [min_eq_right h]; linarith
  · right
    rw [min_eq_left (h2.trans hg)]
    refine ⟨?_, h2, h3⟩
    rcases le_total u₁ F with h | h
    · rw [min_eq_left h]; exact h1
    · rw [min_eq_right h]; linarith

/-! ### The root box -/

/-- On `B_W`, the coordinates of hallway `j` range inside the root box entries: `f_j` over
`[lo₁ + 1, hi₁]` and `g_j` over `[lo₂ + 1, hi₂]` (these are exactly `min f - 1`, `max f`,
`min g - 1`, `max g` over `B_W`). -/
theorem rootBox_bounds (j : Fin 4) {q : ℝ × ℝ} (hq : q ∈ BW) :
    ((rootBox[i₁ j]).1 : ℝ) + 1 ≤ fR j q ∧ fR j q ≤ ((rootBox[i₁ j]).2 : ℝ) ∧
    ((rootBox[i₂ j]).1 : ℝ) + 1 ≤ gR j q ∧ gR j q ≤ ((rootBox[i₂ j]).2 : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hq
  fin_cases j <;>
  · simp [fR, gR, yOf, hCos, hSin, hMir, rootBox, i₁, i₂]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Every parameter coordinate belongs to some hallway. -/
theorem exists_hallway (k : Fin 8) : ∃ j : Fin 4, k = i₁ j ∨ k = i₂ j := by
  revert k; decide

/-- The change of the parameters under the translation `x ↦ x - x₀` is `cShift k * x₀`:
`-cos` for the coordinate `u₁` and `sin` for the coordinate `u₂` of each hallway. -/
def cShift : Fin 8 → ℝ := ![-(4 / 5), 3 / 5, -(3 / 5), 4 / 5, -(4 / 5), 3 / 5, -(3 / 5), 4 / 5]

theorem cShift_i₁ (j : Fin 4) : cShift (i₁ j) = -(hCos j : ℝ) := by
  fin_cases j <;> simp [cShift, i₁, hCos]

theorem cShift_i₂ (j : Fin 4) : cShift (i₂ j) = (hSin j : ℝ) := by
  fin_cases j <;> simp [cShift, i₂, hSin]

/-! ### Width (Lemma 3.5) for hallway 0 -/

/-- An interval inside the union of two intervals is at most as long as both together. -/
theorem sub_le_of_Icc_subset_union {a b c₁ d₁ c₂ d₂ : ℝ}
    (h : Set.Icc a b ⊆ Set.Icc c₁ d₁ ∪ Set.Icc c₂ d₂) (h1 : c₁ ≤ d₁) (h2 : c₂ ≤ d₂) :
    b - a ≤ (d₁ - c₁) + (d₂ - c₂) := by
  have := (measure_mono (μ := volume) h).trans (measure_union_le _ _)
  rw [Real.volume_Icc, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_add (by linarith) (by linarith)] at this
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 this

/-- A point of the strip in hallway 0 has its `x`-coordinate in one of two intervals, of
lengths 2 (first arm) and 3 (second arm). -/
theorem width_mem {x y u₁ u₂ : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (h : InHall (fR 0 (x, y)) (gR 0 (x, y)) u₁ u₂) :
    x ∈ Set.Icc ((5 * u₁ - 3) / 4) ((5 * u₁ + 5) / 4) ∪
      Set.Icc ((-5 * u₂ - 5) / 3) ((-5 * u₂ + 4) / 3) := by
  simp only [InHall, fR, gR, yOf, hCos, hSin, hMir] at h
  push_cast at h
  rcases h with ⟨h1, h2, _⟩ | ⟨_, h2, h3⟩
  · exact Or.inl ⟨by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

end Normalise

open Normalise in
theorem volume_le_of_good {T : ℚ} (hgood : ∀ u, rootBox.mem u → Good T u)
    {K : Set ℝ²} (hK : IsPreconnected K) (hstrip : K ⊆ strip) (u : Fin 8 → ℝ)
    (hhall : ∀ j : Fin 4, ∀ p ∈ K,
      InHall (fR j (p 0, p 1)) (gR j (p 0, p 1)) (u (i₁ j)) (u (i₂ j))) :
    volume K ≤ ENNReal.ofReal T := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp
  /- Step 1: width. The `x`-projection of `K` is an interval inside the union of the two
  intervals of `width_mem`, so any two `x`-coordinates differ by at most `2 + 3 = 5`. -/
  let π : ℝ² → ℝ := fun p => p 0
  have hπc : Continuous π := by fun_prop
  have hdiff : ∀ p ∈ K, ∀ q ∈ K, q 0 - p 0 ≤ 5 := by
    intro p hp q hq
    rcases le_total (p 0) (q 0) with hpq | hpq
    · have hsub : Set.Icc (p 0) (q 0) ⊆
          Set.Icc ((5 * u (i₁ 0) - 3) / 4) ((5 * u (i₁ 0) + 5) / 4) ∪
            Set.Icc ((-5 * u (i₂ 0) - 5) / 3) ((-5 * u (i₂ 0) + 4) / 3) := by
        intro x hx
        obtain ⟨r, hr, rfl⟩ :=
          (hK.image π hπc.continuousOn).Icc_subset ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩ hx
        exact width_mem (hstrip hr).1 (hstrip hr).2 (hhall 0 r hr)
      have := sub_le_of_Icc_subset_union hsub (by linarith) (by linarith)
      linarith
    · linarith
  have hbdd : BddBelow (π '' K) := by
    refine ⟨p₀ 0 - 5, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    have := hdiff q hq p₀ hp₀
    simp only [π]
    linarith
  set x₀ := sInf (π '' K) with hx₀
  have hlo : ∀ q ∈ K, x₀ ≤ q 0 := fun q hq => csInf_le hbdd ⟨q, hq, rfl⟩
  have hhi : ∀ q ∈ K, q 0 ≤ x₀ + 5 := by
    intro q hq
    have : q 0 - 5 ≤ x₀ := by
      refine le_csInf ⟨_, p₀, hp₀, rfl⟩ ?_
      rintro _ ⟨r, hr, rfl⟩
      have := hdiff r hr q hq
      simp only [π]
      linarith
    linarith
  /- Step 2: translation by `(-x₀, 0)`, combined with the transfer to `ℝ × ℝ`. -/
  let e : ℝ² ≃ᵐ ℝ × ℝ := toProd.trans (MeasurableEquiv.addRight ((-x₀, 0) : ℝ × ℝ))
  have he_apply : ∀ p, e p = (p 0 - x₀, p 1) := by
    intro p; simp [e, sub_eq_add_neg]
  have he : MeasurePreserving e volume volume :=
    (measurePreserving_add_right volume _).comp measurePreserving_toProd
  have hvol : volume (e '' K) = volume K := by
    rw [← he.measure_preimage_equiv (e '' K), e.preimage_image]
  have hcont : Continuous e := by
    have : (e : ℝ² → ℝ × ℝ) = fun p => (p 0 - x₀, p 1) := funext he_apply
    rw [this]; fun_prop
  have hBW : ∀ p ∈ K, e p ∈ BW := by
    intro p hp
    rw [he_apply]
    have := hlo p hp
    have := hhi p hp
    exact ⟨by simp only; linarith, by simp only; linarith, (hstrip hp).1, (hstrip hp).2⟩
  have hshift : ∀ j : Fin 4, ∀ p ∈ K, InHall (fR j (e p)) (gR j (e p))
      (u (i₁ j) + cShift (i₁ j) * x₀) (u (i₂ j) + cShift (i₂ j) * x₀) := by
    intro j p hp
    have h := hhall j p hp
    have hf : fR j (p 0, p 1) = fR j (e p) + hCos j * x₀ := by
      rw [he_apply]; simp only [fR]; ring
    have hg : gR j (p 0, p 1) = gR j (e p) + (-(hSin j : ℝ) * x₀) := by
      rw [he_apply]; simp only [gR]; ring
    rw [hf, hg] at h
    have h' := inHall_shift h
    rw [cShift_i₁, cShift_i₂]
    convert h' using 2 <;> ring
  /- Step 3: clamp the parameters into the root box. The lower bounds hold because `K` is
  nonempty; the upper bounds are enforced by `min`, which keeps `K` by `inHall_clamp`. -/
  let u' : Fin 8 → ℝ := fun k => min (u k + cShift k * x₀) ((rootBox[k]).2 : ℝ)
  have hbox : rootBox.mem u' := by
    intro k
    refine ⟨?_, min_le_right _ _⟩
    obtain ⟨j, rfl | rfl⟩ := exists_hallway k
    · obtain ⟨b1, b2, -, -⟩ := rootBox_bounds j (hBW p₀ hp₀)
      have := (inHall_le (hshift j p₀ hp₀)).1
      exact le_min (by linarith) (by linarith)
    · obtain ⟨-, -, b1, b2⟩ := rootBox_bounds j (hBW p₀ hp₀)
      have := (inHall_le (hshift j p₀ hp₀)).2
      exact le_min (by linarith) (by linarith)
  have hsub : e '' K ⊆ paramSet u' := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨hBW p hp, Set.mem_iInter.2 fun j => ?_⟩
    obtain ⟨-, b2, -, b4⟩ := rootBox_bounds j (hBW p hp)
    exact inHall_clamp (hshift j p hp) b2 b4
  /- Step 4: apply the hypothesis to the translate. -/
  rw [← hvol]
  exact hgood u' hbox (e '' K) hsub (hK.image e hcont.continuousOn)

end SofaCert
