import SofaCertCore.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order

/-!
# Combinatorics of valid slab lists

A valid slab list (`slabsValid`) has all its slabs `ok`, and its slabs cover `[0, 1]`: every
`y ∈ [0, 1]` lies in some slab `[s.y0, s.y1]`.
-/

namespace SofaCert.PolyAux

theorem ok_iff {P : Poly} {s : Slab} :
    s.ok P = true ↔ s.y0 ≤ s.y1 ∧ s.l < P.lo.size ∧ s.r < P.hi.size := by
  simp [Slab.ok, and_assoc]

theorem go_ok {P : Poly} :
    ∀ (prev : Slab) (ss : List Slab), slabsValid.go P prev ss = true → ∀ s ∈ ss, s.ok P = true
  | _, [], _ => by simp
  | _, s :: ss, h => by
    simp only [slabsValid.go, Bool.and_eq_true] at h
    intro s' hs'
    rcases List.mem_cons.mp hs' with rfl | hs'
    · exact h.1.2
    · exact go_ok s ss h.2 s' hs'

theorem ok_of_slabsValid {P : Poly} {ss : List Slab} (h : slabsValid P ss = true) :
    ∀ s ∈ ss, s.ok P = true := by
  cases ss with
  | nil => simp [slabsValid] at h
  | cons s ss =>
    simp only [slabsValid, Bool.and_eq_true] at h
    intro s' hs'
    rcases List.mem_cons.mp hs' with rfl | hs'
    · exact h.1.2
    · exact go_ok s ss h.2 s' hs'

theorem go_cover {P : Poly} :
    ∀ (prev : Slab) (ss : List Slab), slabsValid.go P prev ss = true →
      ∀ y : ℝ, (prev.y0 : ℝ) ≤ y → y ≤ 1 → ∃ s ∈ prev :: ss, (s.y0 : ℝ) ≤ y ∧ y ≤ s.y1
  | prev, [], h, y, hy0, hy1 => by
      simp only [slabsValid.go, beq_iff_eq] at h
      exact ⟨prev, by simp, hy0, by rw [h]; exact_mod_cast hy1⟩
  | prev, s :: ss, h, y, hy0, hy1 => by
      simp only [slabsValid.go, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hs0, -⟩, hgo⟩ := h
      by_cases hy : y ≤ prev.y1
      · exact ⟨prev, by simp, hy0, hy⟩
      · obtain ⟨s', hs', h1, h2⟩ :=
          go_cover s ss hgo y (by rw [hs0]; exact (not_le.mp hy).le) hy1
        exact ⟨s', List.mem_cons_of_mem _ hs', h1, h2⟩

/-- The slabs of a valid slab list cover `[0, 1]`. -/
theorem cover_of_slabsValid {P : Poly} {ss : List Slab} (h : slabsValid P ss = true) {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : ∃ s ∈ ss, (s.y0 : ℝ) ≤ y ∧ y ≤ s.y1 := by
  cases ss with
  | nil => simp [slabsValid] at h
  | cons s ss =>
    simp only [slabsValid, Bool.and_eq_true, beq_iff_eq] at h
    exact go_cover s ss h.2 y (by rw [h.1.1]; simpa using hy0) hy1

theorem getD_mem {α : Type*} [Inhabited α] {a : Array α} {i : Nat} (h : i < a.size) :
    a.getD i default ∈ a := by
  simp [Array.getD, h]

end SofaCert.PolyAux
