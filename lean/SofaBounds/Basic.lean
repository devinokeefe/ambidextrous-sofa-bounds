import SofaBounds.Defs

/-!
# Basic API: coordinates, the strip, and measure transfer to `ℝ × ℝ`
-/

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped EuclideanGeometry

/-- Membership in the hallway $L_0$, written in coordinates `(P, Q)`. -/
def InL0 (P Q : ℝ) : Prop := (P ≤ 1 ∧ 0 ≤ Q ∧ Q ≤ 1) ∨ (0 ≤ P ∧ P ≤ 1 ∧ Q ≤ 1)

theorem mem_horizontalHallway_iff (p : ℝ²) :
    p ∈ horizontalHallway ↔ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := by
  constructor
  · rintro ⟨x, y, h, rfl⟩
    simpa using h
  · intro h
    exact ⟨p 0, p 1, h, by ext i; fin_cases i <;> rfl⟩

theorem mem_verticalHallway_iff (p : ℝ²) :
    p ∈ verticalHallway ↔ 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ p 1 ≤ 1 := by
  constructor
  · rintro ⟨x, y, h, rfl⟩
    simpa using h
  · intro h
    exact ⟨p 0, p 1, h, by ext i; fin_cases i <;> rfl⟩

theorem mem_hallway_iff (p : ℝ²) : p ∈ hallway ↔ InL0 (p 0) (p 1) := by
  simp only [hallway, Set.mem_union, mem_horizontalHallway_iff, mem_verticalHallway_iff, InL0]

/-- The horizontal strip $H = \mathbb{R} \times [0, 1]$. -/
def strip : Set ℝ² := {p | 0 ≤ p 1 ∧ p 1 ≤ 1}

theorem horizontalHallway_subset_strip : horizontalHallway ⊆ strip := fun p hp => by
  rw [mem_horizontalHallway_iff] at hp
  exact ⟨hp.2.1, hp.2.2⟩

theorem reflection_midline_involutive (q : ℝ²) :
    EuclideanGeometry.reflection midline (EuclideanGeometry.reflection midline q) = q :=
  EuclideanGeometry.reflection_reflection midline q

theorem mem_reflection_midline_image (s : Set ℝ²) (q : ℝ²) :
    q ∈ EuclideanGeometry.reflection midline '' s ↔ !₂[q 0, 1 - q 1] ∈ s := by
  rw [← reflection_midline_apply]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rwa [reflection_midline_involutive]
  · intro h
    exact ⟨_, h, reflection_midline_involutive q⟩

/-- The coordinate map `ℝ² → ℝ × ℝ`, `p ↦ (p 0, p 1)`, as a measurable equivalence. -/
def toProd : ℝ² ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.finTwoArrow)

@[simp] theorem toProd_apply (p : ℝ²) : toProd p = (p 0, p 1) := by
  simp [toProd, MeasurableEquiv.finTwoArrow]

theorem measurePreserving_toProd : MeasurePreserving toProd volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
    (volume_preserving_finTwoArrow ℝ)

/-- Areas in `ℝ²` can be computed in `ℝ × ℝ`. -/
theorem toProd_symm_apply (q : ℝ × ℝ) : toProd.symm q = !₂[q.1, q.2] :=
  toProd.injective (by rw [MeasurableEquiv.apply_symm_apply, toProd_apply]; simp)

/-- Areas in `ℝ²` can be computed in `ℝ × ℝ`. -/
theorem volume_eq_volume_prod (s : Set ℝ²) :
    volume s = volume {q : ℝ × ℝ | !₂[q.1, q.2] ∈ s} := by
  have h := measurePreserving_toProd.symm
  have : {q : ℝ × ℝ | !₂[q.1, q.2] ∈ s} = toProd.symm ⁻¹' s := by
    ext q
    simp only [Set.mem_preimage, toProd_symm_apply]
    rfl
  rw [this, h.measure_preimage_equiv]

/-- Isometries of the plane preserve area. -/
theorem measurePreserving_affineIsometryEquiv (g : ℝ² ≃ᵃⁱ[ℝ] ℝ²) :
    MeasurePreserving g volume volume := by
  have : (g : ℝ² → ℝ²) = (fun v => v + g 0) ∘ g.linearIsometryEquiv := by
    funext v
    simp only [Function.comp_apply]
    have := g.map_vadd 0 v
    simp only [vadd_eq_add, add_zero] at this
    rw [this]
  rw [this]
  exact (measurePreserving_add_right volume (g 0)).comp
    g.linearIsometryEquiv.measurePreserving

theorem volume_image_affineIsometryEquiv (g : ℝ² ≃ᵃⁱ[ℝ] ℝ²) (s : Set ℝ²) :
    volume (g '' s) = volume s := by
  let e : ℝ² ≃ᵐ ℝ² := g.symm.toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e volume volume := measurePreserving_affineIsometryEquiv g.symm
  have : g '' s = e ⁻¹' s := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa [e] using hp
    · intro hq
      exact ⟨g.symm q, hq, by simp⟩
  rw [this, he.measure_preimage_equiv]

theorem volume_reflection_midline_image (s : Set ℝ²) :
    volume (EuclideanGeometry.reflection midline '' s) = volume s :=
  volume_image_affineIsometryEquiv _ s

end MovingSofa
