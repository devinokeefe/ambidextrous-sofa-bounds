import SofaBounds.Basic

/-!
# Rigid motions along a path

A continuous path `m : I → E(2)` with `m 0 = id` consists of orientation-preserving isometries:
each `m t` is a rotation, with matrix `[[c, -s], [s, c]]`, followed by a translation. We record
the rotation by the pair `(c, s) = (cosPart (m t), sinPart (m t))`, the image of the first basis
vector, and never need an angle.
-/

noncomputable section

namespace MovingSofa

open scoped EuclideanGeometry unitInterval RealInnerProductSpace

/-- The first entry of the image of `e₀` under the linear part of `g`. -/
def cosPart (g : E(2)) : ℝ := g.linearIsometryEquiv (EuclideanSpace.single 0 1) 0

/-- The second entry of the image of `e₀` under the linear part of `g`. -/
def sinPart (g : E(2)) : ℝ := g.linearIsometryEquiv (EuclideanSpace.single 0 1) 1

/-! ### Auxiliary facts -/

/-- The linear part of an isometry, expressed through the isometry itself. -/
theorem linearIsometryEquiv_apply_eq_sub (g : E(2)) (v : ℝ²) :
    g.linearIsometryEquiv v = g v - g 0 := by
  have := g.map_vadd 0 v
  simp only [vadd_eq_add, add_zero] at this
  rw [this]
  simp

/-- The inner product in `ℝ²`, in coordinates. -/
theorem inner_eq_coord (x y : ℝ²) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- Every point is a combination of the two basis vectors. -/
theorem eq_coord_smul_single (p : ℝ²) :
    p = p 0 • (EuclideanSpace.single 0 1 : ℝ²) + p 1 • (EuclideanSpace.single 1 1 : ℝ²) := by
  ext i
  fin_cases i <;> simp

/-- The columns of the matrix of the linear part of an isometry are orthonormal. -/
theorem columns_orthonormal (g : E(2)) :
    let u := g.linearIsometryEquiv (EuclideanSpace.single 0 1)
    let w := g.linearIsometryEquiv (EuclideanSpace.single 1 1)
    u 0 * u 0 + u 1 * u 1 = 1 ∧ w 0 * w 0 + w 1 * w 1 = 1 ∧ u 0 * w 0 + u 1 * w 1 = 0 := by
  intro u w
  have h00 := g.linearIsometryEquiv.inner_map_map (EuclideanSpace.single 0 1)
    (EuclideanSpace.single 0 1)
  have h11 := g.linearIsometryEquiv.inner_map_map (EuclideanSpace.single 1 1)
    (EuclideanSpace.single 1 1)
  have h01 := g.linearIsometryEquiv.inner_map_map (EuclideanSpace.single 0 1)
    (EuclideanSpace.single 1 1)
  rw [inner_eq_coord, inner_eq_coord] at h00 h11 h01
  norm_num at h00 h11 h01
  exact ⟨h00, h11, h01⟩

theorem cosPart_sq_add_sinPart_sq (g : E(2)) : cosPart g ^ 2 + sinPart g ^ 2 = 1 := by
  have h := (columns_orthonormal g).1
  simp only [cosPart, sinPart]
  linear_combination h

@[simp] theorem cosPart_refl : cosPart (.refl ℝ ℝ²) = 1 := by
  simp [cosPart, linearIsometryEquiv_apply_eq_sub]

@[simp] theorem sinPart_refl : sinPart (.refl ℝ ℝ²) = 0 := by
  simp [sinPart, linearIsometryEquiv_apply_eq_sub]

/-- Evaluation at a point is continuous along a continuous path of isometries. -/
theorem continuous_apply_of_continuous {m : I → E(2)} (hc : Continuous m) (p : ℝ²) :
    Continuous fun t => m t p := by
  have h1 : Continuous fun t => (m t).toAffineIsometry.toContinuousAffineMap :=
    continuous_induced_dom.comp hc
  have h2 : Continuous fun t => (m t).toAffineIsometry.toContinuousAffineMap p :=
    (continuous_eval_const p).comp h1
  exact h2

/-- The entries of the matrix of the linear part vary continuously. -/
theorem continuous_linearIsometryEquiv_apply {m : I → E(2)} (hc : Continuous m) (v : ℝ²)
    (i : Fin 2) : Continuous fun t => (m t).linearIsometryEquiv v i := by
  simp_rw [linearIsometryEquiv_apply_eq_sub]
  have := (continuous_apply_of_continuous hc v).sub (continuous_apply_of_continuous hc 0)
  exact (PiLp.continuous_apply 2 _ i).comp this

theorem continuous_cosPart {m : I → E(2)} (hc : Continuous m) :
    Continuous fun t => cosPart (m t) :=
  continuous_linearIsometryEquiv_apply hc _ 0

theorem continuous_sinPart {m : I → E(2)} (hc : Continuous m) :
    Continuous fun t => sinPart (m t) :=
  continuous_linearIsometryEquiv_apply hc _ 1

/-- Along a continuous path of isometries starting at the identity, the determinant of the
linear part is `1`. -/
theorem det_eq_one_of_path {m : I → E(2)} (hc : Continuous m) (h0 : m 0 = .refl ℝ ℝ²)
    (t : I) :
    (m t).linearIsometryEquiv (EuclideanSpace.single 0 1) 0 *
        (m t).linearIsometryEquiv (EuclideanSpace.single 1 1) 1 -
      (m t).linearIsometryEquiv (EuclideanSpace.single 0 1) 1 *
        (m t).linearIsometryEquiv (EuclideanSpace.single 1 1) 0 = 1 := by
  set D : I → ℝ := fun t =>
    (m t).linearIsometryEquiv (EuclideanSpace.single 0 1) 0 *
        (m t).linearIsometryEquiv (EuclideanSpace.single 1 1) 1 -
      (m t).linearIsometryEquiv (EuclideanSpace.single 0 1) 1 *
        (m t).linearIsometryEquiv (EuclideanSpace.single 1 1) 0 with hD
  change D t = 1
  have hDc : Continuous D :=
    ((continuous_linearIsometryEquiv_apply hc _ 0).mul
        (continuous_linearIsometryEquiv_apply hc _ 1)).sub
      ((continuous_linearIsometryEquiv_apply hc _ 1).mul
        (continuous_linearIsometryEquiv_apply hc _ 0))
  have hD2 : ∀ t, D t * D t = 1 := by
    intro t
    obtain ⟨h00, h11, h01⟩ := columns_orthonormal (m t)
    simp only [hD]
    set u := (m t).linearIsometryEquiv (EuclideanSpace.single 0 1)
    set w := (m t).linearIsometryEquiv (EuclideanSpace.single 1 1)
    linear_combination (w 0 * w 0 + w 1 * w 1) * h00 + h11 - (u 0 * w 0 + u 1 * w 1) * h01
  have hD0 : D 0 = 1 := by
    simp [hD, h0, linearIsometryEquiv_apply_eq_sub]
  have hfac : (D t - 1) * (D t + 1) = 0 := by linear_combination hD2 t
  rcases mul_eq_zero.1 hfac with h | h
  · linarith
  · exfalso
    have hsub := intermediate_value_univ t 0 hDc
    rw [hD0] at hsub
    have hmem : (0 : ℝ) ∈ Set.Icc (D t) 1 := ⟨by linarith, by norm_num⟩
    obtain ⟨t', ht'⟩ := hsub hmem
    have := hD2 t'
    rw [ht'] at this
    norm_num at this

/-- A continuous path of isometries that starts at the identity consists of rotations followed
by translations (the determinant is continuous with values in `{±1}`, hence constant). -/
theorem apply_eq_of_path {m : I → E(2)} (hc : Continuous m) (h0 : m 0 = .refl ℝ ℝ²)
    (t : I) (p : ℝ²) :
    m t p = !₂[cosPart (m t) * p 0 - sinPart (m t) * p 1 + (m t 0) 0,
      sinPart (m t) * p 0 + cosPart (m t) * p 1 + (m t 0) 1] := by
  have hd := det_eq_one_of_path hc h0 t
  obtain ⟨h00, h11, h01⟩ := columns_orthonormal (m t)
  have hp : m t p = (m t).linearIsometryEquiv p + m t 0 := by
    rw [linearIsometryEquiv_apply_eq_sub]
    abel
  have hL : (m t).linearIsometryEquiv p =
      p 0 • (m t).linearIsometryEquiv (EuclideanSpace.single 0 1) +
        p 1 • (m t).linearIsometryEquiv (EuclideanSpace.single 1 1) := by
    conv_lhs => rw [eq_coord_smul_single p]
    rw [map_add, map_smul, map_smul]
  simp only [cosPart, sinPart]
  set u := (m t).linearIsometryEquiv (EuclideanSpace.single 0 1) with hu
  set w := (m t).linearIsometryEquiv (EuclideanSpace.single 1 1) with hw
  have hw0 : w 0 = -u 1 := by
    linear_combination u 0 * h01 - w 0 * h00 - u 1 * hd
  have hw1 : w 1 = u 0 := by
    linear_combination u 1 * h01 - w 1 * h00 + u 0 * hd
  rw [hp, hL]
  ext i
  fin_cases i
  · simp [hw0]
    ring
  · simp [hw1]
    ring

end MovingSofa
