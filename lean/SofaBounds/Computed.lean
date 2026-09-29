import SofaBounds.Turning
import SofaBounds.ZCorridor
import SofaBounds.Cert.Tree
import SofaBounds.Cert.Normalise

/-!
# Theorem 1.1: the computer-assisted bound

`checkCert T bytes = true` implies that every ambidextrous sofa, and every sofa that passes
through `Z_D` with `D ≥ 7`, has area at most `T`. The function `checkCert` is executed, as
compiled code, on the certificate file by the program `checkcert` (see `CheckCertMain.lean`).
-/

noncomputable section

namespace MovingSofa

open MeasureTheory SofaCert
open scoped EuclideanGeometry

/-- Conversion between the two ways of writing a hallway. -/
theorem inL0_iff_inHall (f g a b : ℝ) : InL0 (f + a) (g + b) ↔ InHall f g (-a) (-b) := by
  unfold InL0 InHall
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inr ⟨by linarith, by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inr ⟨by linarith, by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩

/-- The two angles `arcsin (3/5)` and `arcsin (4/5)`, as `(cos, sin)` pairs, are admissible
for every threshold `T ≥ 5/3`. -/
private theorem admissible {T : ℚ} (hT : 5 / 3 ≤ T) :
    √2 < (T : ℝ) ∧ 1 ≤ (4 / 5 : ℝ) * T ∧ 1 ≤ (3 / 5 : ℝ) * T := by
  have hT' : (5 / 3 : ℝ) ≤ T := by
    have := (Rat.cast_le (K := ℝ)).mpr hT
    push_cast at this
    exact this
  refine ⟨?_, by linarith, by linarith⟩
  have : √2 < 5 / 3 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-- If `s` lies in the strip and in the four hallways of the certificate (in the form produced
by the reduction), then `λ(s) ≤ T`. -/
private theorem volume_le_of_hallways {T : ℚ} (hgood : ∀ u, rootBox.mem u → Good T u)
    {s : Set ℝ²} (hs : IsPreconnected s) (hstrip : s ⊆ strip) {a b : Fin 4 → ℝ}
    (hab : ∀ j : Fin 4, ∀ p ∈ s, InL0 (fR j (p 0, p 1) + a j) (gR j (p 0, p 1) + b j)) :
    volume s ≤ ENNReal.ofReal T := by
  let u : Fin 8 → ℝ := fun k => if k.1 % 2 = 0 then -a ⟨k.1 / 2, by omega⟩ else -b ⟨k.1 / 2, by omega⟩
  refine volume_le_of_good hgood hs hstrip u fun j p hp => ?_
  have hu1 : u (i₁ j) = -a j := by
    simp only [u, i₁]
    rw [ite_eq_left (by omega)]
    congr 2
    ext
    simp only
    omega
  have hu2 : u (i₂ j) = -b j := by
    simp only [u, i₂]
    rw [ite_eq_right (by omega)]
    congr 2
    ext
    simp only
    omega
  rw [hu1, hu2, ← inL0_iff_inHall]
  exact hab j p hp

/-- The four hallway memberships given by the reduction, in the form used by the checker. -/
private theorem hallways_of {s : Set ℝ²}
    (h0 : ∃ a b : ℝ, ∀ p ∈ s, InL0 (4 / 5 * p 0 + 3 / 5 * p 1 + a) (-(3 / 5) * p 0 + 4 / 5 * p 1 + b))
    (h1 : ∃ a b : ℝ, ∀ p ∈ s, InL0 (3 / 5 * p 0 + 4 / 5 * p 1 + a) (-(4 / 5) * p 0 + 3 / 5 * p 1 + b))
    (h2 : ∃ a b : ℝ, ∀ p ∈ s,
      InL0 (4 / 5 * p 0 + 3 / 5 * (1 - p 1) + a) (-(3 / 5) * p 0 + 4 / 5 * (1 - p 1) + b))
    (h3 : ∃ a b : ℝ, ∀ p ∈ s,
      InL0 (3 / 5 * p 0 + 4 / 5 * (1 - p 1) + a) (-(4 / 5) * p 0 + 3 / 5 * (1 - p 1) + b)) :
    ∃ a b : Fin 4 → ℝ, ∀ j : Fin 4, ∀ p ∈ s,
      InL0 (fR j (p 0, p 1) + a j) (gR j (p 0, p 1) + b j) := by
  obtain ⟨a0, b0, h0⟩ := h0
  obtain ⟨a1, b1, h1⟩ := h1
  obtain ⟨a2, b2, h2⟩ := h2
  obtain ⟨a3, b3, h3⟩ := h3
  refine ⟨![a0, a1, a2, a3], ![b0, b1, b2, b3], fun j p hp => ?_⟩
  fin_cases j <;>
    simp [fR, gR, yOf, hCos, hSin, hMir] <;> norm_num
  · simpa using h0 p hp
  · simpa using h1 p hp
  · simpa using h2 p hp
  · simpa using h3 p hp

/-- **Theorem 1.1 (conditional form).** If the compiled checker accepts a certificate for the
threshold `T ≥ 5/3`, then every ambidextrous sofa has area at most `T`. -/
theorem ambidextrousSofaConstant_le_of_checkCert {T : ℚ} (hT : 5 / 3 ≤ T) {bytes : ByteArray}
    (h : checkCert T bytes = true) : ambidextrousSofaConstant ≤ ENNReal.ofReal T := by
  have hgood := checkCert_sound h
  obtain ⟨hT2, hC1, hC2⟩ := admissible hT
  refine iSup₂_le fun s hs => ?_
  obtain ⟨⟨m, hm⟩, hmir⟩ := hs
  by_contra hlt
  rw [not_le] at hlt
  have hstrip : s ⊆ strip := fun p hp => horizontalHallway_subset_strip (hm.initial hp)
  have e0 := hm.exists_rotation hT2 hlt (C := 4/5) (S := 3/5) (by norm_num) (by norm_num)
    (by norm_num) hC1
  have e1 := hm.exists_rotation hT2 hlt (C := 3/5) (S := 4/5) (by norm_num) (by norm_num)
    (by norm_num) hC2
  have e2 := exists_rotation_mirror hmir hT2 hlt (C := 4/5) (S := 3/5) (by norm_num)
    (by norm_num) (by norm_num) hC1
  have e3 := exists_rotation_mirror hmir hT2 hlt (C := 3/5) (S := 4/5) (by norm_num)
    (by norm_num) (by norm_num) hC2
  obtain ⟨a, b, hab⟩ := hallways_of e0 e1 e2 e3
  exact absurd (volume_le_of_hallways hgood hm.isConnected.isPreconnected hstrip hab)
    (not_le.2 hlt)

/-- **Theorem 1.1 for the Z-shaped corridor (conditional form).** -/
theorem zSofaConstant_le_of_checkCert {T : ℚ} (hT : 5 / 3 ≤ T) {bytes : ByteArray}
    (h : checkCert T bytes = true) {D : ℝ} (hD : 7 ≤ D) : zSofaConstant D ≤ ENNReal.ofReal T := by
  have hgood := checkCert_sound h
  obtain ⟨hT2, hC1, hC2⟩ := admissible hT
  refine iSup₂_le fun s ⟨m, hm⟩ => ?_
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨hA, hB⟩ := hm.exists_hallways hD hT2 hlt
  have e0 := hA (4/5) (3/5) (by norm_num) (by norm_num) (by norm_num) hC1 hC2
  have e1 := hA (3/5) (4/5) (by norm_num) (by norm_num) (by norm_num) hC2 hC1
  have e2 := hB (4/5) (3/5) (by norm_num) (by norm_num) (by norm_num) hC1
  have e3 := hB (3/5) (4/5) (by norm_num) (by norm_num) (by norm_num) hC2
  obtain ⟨a, b, hab⟩ := hallways_of e0 e1 e2 e3
  exact absurd (volume_le_of_hallways hgood hm.isConnected.isPreconnected hm.subset_strip hab)
    (not_le.2 hlt)

end MovingSofa
