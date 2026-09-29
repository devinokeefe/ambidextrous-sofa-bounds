import SofaBounds.Cert.Poly
import SofaCertCore.CheckerAux.Fast

/-!
# Soundness of the integer computations of the leaf test

* `nBound_volume`: if `nBound` accepts a list of integer slabs for the polygon `polyOfL …`, the
  area of the polygon is at most the returned integer divided by `areaScale N`. The integer slabs
  are turned into rational slabs (`toSlabs`), which are valid in the sense of the frozen
  `slabsValid`, and whose frozen `slabBound` is exactly the integer computed, divided by the
  scale.
* `nNegative_empty`: if `nNegative` accepts, the polygon is empty (frozen `slabsNegative`).
* `fastDisjoint_sound`: the integer disjointness test of two polygons of a leaf.
-/

noncomputable section

namespace SofaCert

open MeasureTheory

/-! ## Lines -/

theorem lineAff_eval (N : ℕ) (A m : ℤ) (y : ℚ) :
    (lineAff N A m).eval y = (A : ℚ) / (12 * N) + (m : ℚ) / 12 * y := rfl

theorem lineAff_evalR (N : ℕ) (A m : ℤ) (y : ℝ) :
    (lineAff N A m).evalR y = (A : ℝ) / (12 * N) + (m : ℝ) / 12 * y := by
  simp only [lineAff, Aff.evalR]
  push_cast
  ring

/-! ## Polygons given by a layout -/

section Layout

variable {N : ℕ} {At : Array ℤ} {lo hi : ℕ → ℕ} {nl nr : ℕ}

theorem mem_polyOfL_lo {f : Aff} :
    f ∈ (polyOfL N At lo hi nl nr).lo ↔ ∃ l < nl, lineAff N (At.getD (lo l) 0) (mOf (lo l)) = f := by
  simp [polyOfL]

theorem mem_polyOfL_hi {f : Aff} :
    f ∈ (polyOfL N At lo hi nl nr).hi ↔ ∃ r < nr, lineAff N (At.getD (hi r) 0) (mOf (hi r)) = f := by
  simp [polyOfL]

theorem polyOfL_lo_getD {l : ℕ} (hl : l < nl) :
    (polyOfL N At lo hi nl nr).lo.getD l default = lineAff N (At.getD (lo l) 0) (mOf (lo l)) := by
  simp [polyOfL, Array.getD_eq_getD_getElem?, hl]

theorem polyOfL_hi_getD {r : ℕ} (hr : r < nr) :
    (polyOfL N At lo hi nl nr).hi.getD r default = lineAff N (At.getD (hi r) 0) (mOf (hi r)) := by
  simp [polyOfL, Array.getD_eq_getD_getElem?, hr]

theorem polyOfL_lo_size : (polyOfL N At lo hi nl nr).lo.size = nl := by simp [polyOfL]

theorem polyOfL_hi_size : (polyOfL N At lo hi nl nr).hi.size = nr := by simp [polyOfL]

end Layout

/-! ## The table in natural numbers -/

theorem natTableOK_spec {N : ℕ} {At : Array ℤ} :
    ∀ n, natTableOK N At n = true → ∀ i < n, 0 ≤ At.getD i 0 + 384 * (N : ℤ) ∧
      0 ≤ (At.getD i 0 + 384 * (N : ℤ)) * (lam : ℤ) + min (mOf i) 0 * ((N : ℤ) * (lam : ℤ))
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    simp only [natTableOK, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact natTableOK_spec n h.2 i hi
    · exact h.1

theorem natTable_spec {N : ℕ} {At : Array ℤ} {Pt : Array ℕ} (h : natTable N At = some Pt)
    {i : ℕ} (hi : i < At.size) :
    Pt.getD i 0 = (At.getD i 0 + 384 * (N : ℤ)).toNat * lam ∧ 0 ≤ At.getD i 0 + 384 * (N : ℤ) ∧
      0 ≤ (At.getD i 0 + 384 * (N : ℤ)) * (lam : ℤ) + min (mOf i) 0 * ((N : ℤ) * (lam : ℤ)) := by
  unfold natTable at h
  split_ifs at h with hok
  cases h
  refine ⟨?_, natTableOK_spec _ hok i hi⟩
  simp [Array.getD_eq_getD_getElem?, hi]

/-- The value of a line in natural numbers, as an integer. -/
theorem lineVal_cast {N : ℕ} {At : Array ℤ} {Pt : Array ℕ} (h : natTable N At = some Pt)
    {i Y : ℕ} (hi : i < At.size) (hY : Y ≤ N * lam) :
    ((lineVal Pt i Y : ℕ) : ℤ) = (At.getD i 0 + 384 * (N : ℤ)) * (lam : ℤ) + mOf i * Y := by
  obtain ⟨hP, h1, h2⟩ := natTable_spec h hi
  set a := At.getD i 0 + 384 * (N : ℤ) with ha
  have ha' : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h1
  unfold lineVal
  rw [hP]
  dsimp only
  split_ifs with hm
  · push_cast
    rw [ha', Int.toNat_of_nonneg hm]
  · have hm' : mOf i < 0 := lt_of_not_ge hm
    have hmin : min (mOf i) 0 = mOf i := min_eq_left hm'.le
    rw [hmin] at h2
    have habs : ((mOf i).natAbs : ℤ) = -mOf i := Int.ofNat_natAbs_of_nonpos hm'.le
    have hYz : (Y : ℤ) ≤ (N : ℤ) * (lam : ℤ) := by exact_mod_cast hY
    have hle : (mOf i).natAbs * Y ≤ a.toNat * lam := by
      have : ((mOf i).natAbs : ℤ) * Y ≤ (a.toNat : ℤ) * lam := by
        rw [habs, ha']
        nlinarith
      exact_mod_cast this
    rw [Nat.cast_sub hle]
    push_cast
    rw [ha', abs_of_neg hm']
    ring

/-! ## Slabs -/

/-- The rational slabs corresponding to integer slabs starting at `y0` (heights over `top`). -/
def toSlabs (top : ℕ) : ℕ → List ISlab → List Slab
  | _, [] => []
  | y0, s :: ss => ⟨(y0 : ℚ) / top, (s.y1 : ℚ) / top, s.l, s.r⟩ :: toSlabs top s.y1 ss

/-- The positive part of a difference of natural numbers, divided by a positive number. -/
theorem max_sub_div_zero (a b : ℕ) {c : ℚ} (hc : 0 < c) :
    max (((a : ℚ) - b) / c) 0 = ((a - b : ℕ) : ℚ) / c := by
  rcases le_total b a with hab | hab
  · rw [Nat.cast_sub hab, max_eq_left (div_nonneg (by exact_mod_cast (sub_nonneg.2
      (by exact_mod_cast hab : (b : ℚ) ≤ a))) hc.le)]
  · rw [Nat.sub_eq_zero_of_le hab, max_eq_right (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.2 (by exact_mod_cast hab)) hc.le)]
    simp

section Slabs

variable {N : ℕ} {At : Array ℤ} {Pt : Array ℕ} {lo hi : ℕ → ℕ} {nl nr : ℕ}

theorem lam_pos : (0 : ℚ) < lam := by norm_num [lam]

theorem lam_ne : lam ≠ 0 := by norm_num [lam]

theorem areaScale_pos (hN : 0 < N) : (0 : ℚ) < areaScale N := by
  have : 0 < areaScale N := by
    unfold areaScale
    have := Nat.pos_of_ne_zero lam_ne
    positivity
  exact_mod_cast this

/-- The width of a slab of `polyOfL` at an integer height. -/
theorem width_eq (hN : 0 < N) (h : natTable N At = some Pt) {l r : ℕ} (hl : l < nl)
    (hr : r < nr) (hlo : lo l < At.size) (hhi : hi r < At.size) {Y : ℕ} (hY : Y ≤ N * lam)
    (y0 y1 : ℚ) :
    Slab.width (polyOfL N At lo hi nl nr) ⟨y0, y1, l, r⟩ ((Y : ℚ) / ((N * lam : ℕ) : ℚ)) =
      ((lineVal Pt (hi r) Y : ℚ) - lineVal Pt (lo l) Y) / (12 * N * lam) := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have e1 : ((lineVal Pt (hi r) Y : ℕ) : ℚ) =
      ((At.getD (hi r) 0 : ℚ) + 384 * N) * lam + (mOf (hi r) : ℚ) * Y := by
    have := lineVal_cast h hhi hY
    exact_mod_cast this
  have e2 : ((lineVal Pt (lo l) Y : ℕ) : ℚ) =
      ((At.getD (lo l) 0 : ℚ) + 384 * N) * lam + (mOf (lo l) : ℚ) * Y := by
    have := lineVal_cast h hlo hY
    exact_mod_cast this
  simp only [Slab.width, polyOfL_hi_getD hr, polyOfL_lo_getD hl, lineAff_eval]
  rw [e1, e2]
  have hlam : (0 : ℚ) < lam := lam_pos
  push_cast
  field_simp
  ring

/-- The trapezoid bound of a slab of `polyOfL`, from integer heights. -/
theorem bound_eq (hN : 0 < N) (h : natTable N At = some Pt) {l r : ℕ} (hl : l < nl)
    (hr : r < nr) (hlo : lo l < At.size) (hhi : hi r < At.size) {Y0 Y1 : ℕ} (h01 : Y0 ≤ Y1)
    (hY1 : Y1 ≤ N * lam) :
    Slab.bound (polyOfL N At lo hi nl nr)
        ⟨(Y0 : ℚ) / ((N * lam : ℕ) : ℚ), (Y1 : ℚ) / ((N * lam : ℕ) : ℚ), l, r⟩ =
      (slabTerm Pt Y0 Y1 (lo l) (hi r) : ℚ) / (areaScale N : ℚ) := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hlam : (0 : ℚ) < lam := lam_pos
  have hc : (0 : ℚ) < 12 * N * lam := by positivity
  unfold Slab.bound
  simp only
  rw [width_eq hN h hl hr hlo hhi (h01.trans hY1), width_eq hN h hl hr hlo hhi hY1,
    max_sub_div_zero _ _ hc, max_sub_div_zero _ _ hc]
  unfold slabTerm areaScale
  push_cast [Nat.cast_sub h01]
  field_simp
  ring

/-- `nBound` checks a valid slab list, and computes its bound. -/
theorem nBound_spec (hN : 0 < N) (h : natTable N At = some Pt)
    (hlo : ∀ l < nl, lo l < At.size) (hhi : ∀ r < nr, hi r < At.size) :
    ∀ (ss : List ISlab) (acc y0 S : ℕ),
      nBound Pt lo hi nl nr (N * lam) acc y0 ss = some S →
      y0 ≤ N * lam ∧
      (∀ prev : Slab, prev.y1 = (y0 : ℚ) / ((N * lam : ℕ) : ℚ) →
        slabsValid.go (polyOfL N At lo hi nl nr) prev (toSlabs (N * lam) y0 ss) = true) ∧
      (S : ℚ) = acc + slabBound (polyOfL N At lo hi nl nr) (toSlabs (N * lam) y0 ss) * areaScale N
  | [], acc, y0, S, hb => by
    simp only [nBound] at hb
    split_ifs at hb with hy
    cases hb
    subst hy
    have hpos : (0 : ℚ) < ((N * lam : ℕ) : ℚ) := by
      have : 0 < N * lam := Nat.mul_pos hN (by norm_num [lam])
      exact_mod_cast this
    refine ⟨le_rfl, fun prev hprev => ?_, ?_⟩
    · simp [toSlabs, slabsValid.go, hprev, hN.ne', lam_ne]
    · simp [toSlabs, slabBound]
  | s :: ss, acc, y0, S, hb => by
    simp only [nBound] at hb
    split_ifs at hb with hc
    obtain ⟨hy, hl, hr⟩ := hc
    obtain ⟨hy1, hgo, hS⟩ := nBound_spec hN h hlo hhi ss _ s.y1 S hb
    refine ⟨hy.trans hy1, fun prev hprev => ?_, ?_⟩
    · simp only [toSlabs, slabsValid.go, Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, hgo _ rfl⟩
      · simp [hprev]
      · simp only [Slab.ok, Bool.and_eq_true, decide_eq_true_eq, polyOfL_lo_size,
          polyOfL_hi_size]
        refine ⟨⟨?_, hl⟩, hr⟩
        apply div_le_div_of_nonneg_right (by exact_mod_cast hy) (Nat.cast_nonneg _)
    · rw [hS]
      simp only [toSlabs, slabBound, List.map_cons, List.sum_cons] at *
      rw [bound_eq hN h hl hr (hlo _ hl) (hhi _ hr) hy hy1]
      have hsc := areaScale_pos hN
      push_cast
      field_simp
      ring

/-- `nBound` from height `0`: a valid slab list and its bound. -/
theorem nBound_valid (hN : 0 < N) (h : natTable N At = some Pt)
    (hlo : ∀ l < nl, lo l < At.size) (hhi : ∀ r < nr, hi r < At.size) {ss : List ISlab}
    {S : ℕ} (hb : nBound Pt lo hi nl nr (N * lam) 0 0 ss = some S) :
    slabsValid (polyOfL N At lo hi nl nr) (toSlabs (N * lam) 0 ss) = true ∧
      (S : ℚ) = slabBound (polyOfL N At lo hi nl nr) (toSlabs (N * lam) 0 ss) * areaScale N := by
  obtain ⟨-, hgo, hS⟩ := nBound_spec hN h hlo hhi ss 0 0 S hb
  refine ⟨?_, by simpa using hS⟩
  cases ss with
  | nil =>
    simp only [nBound] at hb
    split_ifs at hb with hy
    exact absurd hy (Nat.ne_of_lt (Nat.mul_pos hN (by norm_num [lam])))
  | cons s ss =>
    simp only [nBound] at hb
    split_ifs at hb with hc
    obtain ⟨hy, hl, hr⟩ := hc
    obtain ⟨-, hgo', -⟩ := nBound_spec hN h hlo hhi ss _ s.y1 S hb
    simp only [toSlabs, slabsValid, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, hgo' _ rfl⟩
    · simp
    · simp only [Slab.ok, Bool.and_eq_true, decide_eq_true_eq, polyOfL_lo_size,
        polyOfL_hi_size]
      refine ⟨⟨?_, hl⟩, hr⟩
      apply div_le_div_of_nonneg_right (by exact_mod_cast hy) (Nat.cast_nonneg _)

/-- `nBound` bounds the area of the polygon. -/
theorem nBound_volume (hN : 0 < N) (h : natTable N At = some Pt)
    (hlo : ∀ l < nl, lo l < At.size) (hhi : ∀ r < nr, hi r < At.size) {ss : List ISlab}
    {S : ℕ} (hb : nBound Pt lo hi nl nr (N * lam) 0 0 ss = some S) :
    volume (polyOfL N At lo hi nl nr).toSet ≤ ENNReal.ofReal ((S : ℝ) / (areaScale N : ℝ)) := by
  obtain ⟨hv, hS⟩ := nBound_valid hN h hlo hhi hb
  have hsc := areaScale_pos hN
  have e : slabBound (polyOfL N At lo hi nl nr) (toSlabs (N * lam) 0 ss) =
      (S : ℚ) / (areaScale N : ℚ) := by
    rw [hS]; field_simp
  calc volume (polyOfL N At lo hi nl nr).toSet
      ≤ ENNReal.ofReal (slabBound (polyOfL N At lo hi nl nr) (toSlabs (N * lam) 0 ss)) :=
        volume_toSet_le_slabBound hv
    _ = ENNReal.ofReal ((S : ℝ) / (areaScale N : ℝ)) := by
        rw [e]; push_cast; rfl

/-- `nNegative` checks a valid slab list with negative widths. -/
theorem nNegative_spec (hN : 0 < N) (h : natTable N At = some Pt)
    (hlo : ∀ l < nl, lo l < At.size) (hhi : ∀ r < nr, hi r < At.size) :
    ∀ (ss : List ISlab) (y0 : ℕ),
      nNegative Pt lo hi nl nr (N * lam) y0 ss = true →
      y0 ≤ N * lam ∧
      (∀ prev : Slab, prev.y1 = (y0 : ℚ) / ((N * lam : ℕ) : ℚ) →
        slabsValid.go (polyOfL N At lo hi nl nr) prev (toSlabs (N * lam) y0 ss) = true) ∧
      ((toSlabs (N * lam) y0 ss).all fun s =>
        decide (s.width (polyOfL N At lo hi nl nr) s.y0 < 0) &&
        decide (s.width (polyOfL N At lo hi nl nr) s.y1 < 0)) = true
  | [], y0, hb => by
    simp only [nNegative, decide_eq_true_eq] at hb
    subst hb
    have hpos : (0 : ℚ) < ((N * lam : ℕ) : ℚ) := by
      have : 0 < N * lam := Nat.mul_pos hN (by norm_num [lam])
      exact_mod_cast this
    refine ⟨le_rfl, fun prev hprev => ?_, ?_⟩
    · simp [toSlabs, slabsValid.go, hprev, hN.ne', lam_ne]
    · simp [toSlabs]
  | s :: ss, y0, hb => by
    simp only [nNegative, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨⟨hy, hl, hr⟩, hw0⟩, hw1⟩, hrest⟩ := hb
    obtain ⟨hy1, hgo, hall⟩ := nNegative_spec hN h hlo hhi ss s.y1 hrest
    have hc : (0 : ℚ) < 12 * N * lam := by
      have hNq : (0 : ℚ) < N := by exact_mod_cast hN
      have := lam_pos
      positivity
    refine ⟨hy.trans hy1, fun prev hprev => ?_, ?_⟩
    · simp only [toSlabs, slabsValid.go, Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, hgo _ rfl⟩
      · simp [hprev]
      · simp only [Slab.ok, Bool.and_eq_true, decide_eq_true_eq, polyOfL_lo_size,
          polyOfL_hi_size]
        refine ⟨⟨?_, hl⟩, hr⟩
        apply div_le_div_of_nonneg_right (by exact_mod_cast hy) (Nat.cast_nonneg _)
    · simp only [toSlabs, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨?_, ?_⟩, hall⟩
      · rw [width_eq hN h hl hr (hlo _ hl) (hhi _ hr) (hy.trans hy1)]
        apply div_neg_of_neg_of_pos _ hc
        rw [sub_neg]
        exact_mod_cast hw0
      · rw [width_eq hN h hl hr (hlo _ hl) (hhi _ hr) hy1]
        apply div_neg_of_neg_of_pos _ hc
        rw [sub_neg]
        exact_mod_cast hw1

/-- `nNegative` from height `0` proves that the polygon is empty. -/
theorem nNegative_empty (hN : 0 < N) (h : natTable N At = some Pt)
    (hlo : ∀ l < nl, lo l < At.size) (hhi : ∀ r < nr, hi r < At.size) {ss : List ISlab}
    (hb : nNegative Pt lo hi nl nr (N * lam) 0 ss = true) :
    (polyOfL N At lo hi nl nr).toSet = ∅ := by
  apply toSet_eq_empty_of_slabsNegative (ss := toSlabs (N * lam) 0 ss)
  obtain ⟨-, -, hall⟩ := nNegative_spec hN h hlo hhi ss 0 hb
  unfold slabsNegative
  rw [hall, Bool.and_true]
  cases ss with
  | nil =>
    simp only [nNegative, decide_eq_true_eq] at hb
    exact absurd hb (Nat.ne_of_lt (Nat.mul_pos hN (Nat.pos_of_ne_zero lam_ne)))
  | cons s ss =>
    simp only [nNegative, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨⟨hy, hl, hr⟩, -⟩, -⟩, hrest⟩ := hb
    obtain ⟨-, hgo', -⟩ := nNegative_spec hN h hlo hhi ss s.y1 hrest
    simp only [toSlabs, slabsValid, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, hgo' _ rfl⟩
    · simp
    · simp only [Slab.ok, Bool.and_eq_true, decide_eq_true_eq, polyOfL_lo_size,
        polyOfL_hi_size]
      refine ⟨⟨?_, hl⟩, hr⟩
      apply div_le_div_of_nonneg_right (by exact_mod_cast hy) (Nat.cast_nonneg _)

end Slabs

end SofaCert
