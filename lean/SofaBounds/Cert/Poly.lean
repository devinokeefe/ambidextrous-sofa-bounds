import SofaBounds.Cert.Spec
import SofaCertCore.Basic
import SofaBounds.Cert.PolyAux.Trapezoid
import SofaBounds.Cert.PolyAux.Slabs

/-!
# Soundness of the polygon arithmetic

A polygon `P : Poly` (defined in `SofaCertCore.Basic`) describes the closed set of points
`(x, y)` with `0 ≤ y ≤ 1`, `ℓ(y) ≤ x` for its lower bounds `ℓ` and `x ≤ r(y)` for its upper
bounds `r`. Any valid slab list gives an upper bound for its area: on each slab the width at
height `y` is at most `r(y) - ℓ(y)` for the chosen bounds, whatever they are, and the positive
part of an affine function lies below its chord.
-/

noncomputable section

namespace SofaCert

open MeasureTheory

/-- Evaluation at a real point. -/
def Aff.evalR (f : Aff) (y : ℝ) : ℝ := (f.c0 : ℝ) + (f.c1 : ℝ) * y

/-- The closed set described by a polygon. -/
def Poly.toSet (P : Poly) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ (∀ f ∈ P.lo, f.evalR q.2 ≤ q.1) ∧ (∀ f ∈ P.hi, q.1 ≤ f.evalR q.2)}

theorem Poly.toSet_inter (P Q : Poly) : (P.inter Q).toSet = P.toSet ∩ Q.toSet := by
  ext q
  simp only [Poly.toSet, Poly.inter, Set.mem_ofPred_eq, Set.mem_inter_iff, Array.mem_append]
  constructor
  · rintro ⟨h0, h1, hl, hr⟩
    exact ⟨⟨h0, h1, fun f hf => hl f (Or.inl hf), fun f hf => hr f (Or.inl hf)⟩,
      ⟨h0, h1, fun f hf => hl f (Or.inr hf), fun f hf => hr f (Or.inr hf)⟩⟩
  · rintro ⟨⟨h0, h1, hl, hr⟩, ⟨-, -, hl', hr'⟩⟩
    exact ⟨h0, h1, fun f hf => hf.elim (hl f) (hl' f), fun f hf => hf.elim (hr f) (hr' f)⟩

theorem Poly.isClosed_toSet (P : Poly) : IsClosed P.toSet := by
  have e : P.toSet = {q : ℝ × ℝ | 0 ≤ q.2} ∩ {q | q.2 ≤ 1} ∩
      (⋂ f ∈ P.lo, {q : ℝ × ℝ | f.evalR q.2 ≤ q.1}) ∩
      (⋂ f ∈ P.hi, {q : ℝ × ℝ | q.1 ≤ f.evalR q.2}) := by
    ext q
    simp [Poly.toSet, and_assoc]
  rw [e]
  refine (((isClosed_le continuous_const continuous_snd).inter
    (isClosed_le continuous_snd continuous_const)).inter
    (isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_le ?_ continuous_fst)).inter
    (isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_le continuous_fst ?_) <;>
  · unfold Aff.evalR
    fun_prop

/-! ## Slab bounds -/

/-- The part of the strip over the slab `s` between its chosen lower and upper bounds. -/
def slabSet (P : Poly) (s : Slab) : Set (ℝ × ℝ) :=
  {q | (s.y0 : ℝ) ≤ q.2 ∧ q.2 ≤ s.y1 ∧ (P.lo.getD s.l default).evalR q.2 ≤ q.1 ∧
    q.1 ≤ (P.hi.getD s.r default).evalR q.2}

theorem Aff.eval_cast (f : Aff) (y : ℚ) : ((f.eval y : ℚ) : ℝ) = f.evalR y := by
  simp [Aff.eval, Aff.evalR]

theorem Slab.bound_cast (P : Poly) (s : Slab) :
    ((s.bound P : ℚ) : ℝ) = ((s.y1 : ℝ) - s.y0) *
      (max ((P.hi.getD s.r default).evalR s.y0 - (P.lo.getD s.l default).evalR s.y0) 0 +
        max ((P.hi.getD s.r default).evalR s.y1 - (P.lo.getD s.l default).evalR s.y1) 0) / 2 := by
  simp only [Slab.bound, Slab.width]
  push_cast
  simp only [Aff.eval_cast]

theorem Slab.bound_nonneg {P : Poly} {s : Slab} (h : s.ok P = true) : 0 ≤ s.bound P := by
  have h01 : 0 ≤ s.y1 - s.y0 := sub_nonneg.mpr (PolyAux.ok_iff.mp h).1
  unfold Slab.bound
  exact div_nonneg (mul_nonneg h01 (add_nonneg (le_max_right _ _) (le_max_right _ _)))
    (by norm_num)

theorem volume_slabSet_le {P : Poly} {s : Slab} (h : s.ok P = true) :
    volume (slabSet P s) ≤ ENNReal.ofReal (s.bound P) := by
  rw [Slab.bound_cast]
  exact PolyAux.volume_trapezoid_le _ _ _ _ _ _ (by exact_mod_cast (PolyAux.ok_iff.mp h).1)

theorem slabBound_cons (P : Poly) (s : Slab) (ss : List Slab) :
    slabBound P (s :: ss) = s.bound P + slabBound P ss := by
  simp [slabBound]

theorem slabBound_nonneg {P : Poly} :
    ∀ {ss : List Slab}, (∀ s ∈ ss, s.ok P = true) → 0 ≤ slabBound P ss
  | [], _ => by simp [slabBound]
  | s :: ss, h => by
    rw [slabBound_cons]
    exact add_nonneg (Slab.bound_nonneg (h s (by simp)))
      (slabBound_nonneg fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))

theorem volume_slabs_le {P : Poly} :
    ∀ ss : List Slab, (∀ s ∈ ss, s.ok P = true) →
      volume {q | ∃ s ∈ ss, q ∈ slabSet P s} ≤ ENNReal.ofReal (slabBound P ss)
  | [], _ => by simp
  | s :: ss, h => by
    have hs := h s (by simp)
    have hss : ∀ s' ∈ ss, s'.ok P = true := fun s' hs' => h s' (List.mem_cons_of_mem _ hs')
    have e : {q | ∃ s' ∈ s :: ss, q ∈ slabSet P s'} =
        slabSet P s ∪ {q | ∃ s' ∈ ss, q ∈ slabSet P s'} := by
      ext q
      simp
    have h1 : (0 : ℝ) ≤ s.bound P := by exact_mod_cast Slab.bound_nonneg hs
    have h2 : (0 : ℝ) ≤ slabBound P ss := by exact_mod_cast slabBound_nonneg hss
    rw [e, slabBound_cons, Rat.cast_add, ENNReal.ofReal_add h1 h2]
    exact (measure_union_le _ _).trans
      (add_le_add (volume_slabSet_le hs) (volume_slabs_le ss hss))

theorem volume_toSet_le_slabBound {P : Poly} {ss : List Slab} (h : slabsValid P ss = true) :
    volume P.toSet ≤ ENNReal.ofReal (slabBound P ss) := by
  refine (measure_mono ?_).trans (volume_slabs_le ss (PolyAux.ok_of_slabsValid h))
  rintro q ⟨h0, h1, hl, hr⟩
  obtain ⟨s, hs, hy0, hy1⟩ := PolyAux.cover_of_slabsValid h h0 h1
  have hok := PolyAux.ok_iff.mp (PolyAux.ok_of_slabsValid h s hs)
  exact ⟨s, hs, hy0, hy1, hl _ (PolyAux.getD_mem hok.2.1), hr _ (PolyAux.getD_mem hok.2.2)⟩

theorem toSet_eq_empty_of_slabsNegative {P : Poly} {ss : List Slab}
    (h : slabsNegative P ss = true) : P.toSet = ∅ := by
  simp only [slabsNegative, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hv, hneg⟩ := h
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro q ⟨h0, h1, hl, hr⟩
  obtain ⟨s, hs, hy0, hy1⟩ := PolyAux.cover_of_slabsValid hv h0 h1
  have hok := PolyAux.ok_iff.mp (PolyAux.ok_of_slabsValid hv s hs)
  obtain ⟨hw0, hw1⟩ := hneg s hs
  have hl' := hl _ (PolyAux.getD_mem hok.2.1)
  have hr' := hr _ (PolyAux.getD_mem hok.2.2)
  have hw0' : ((s.width P s.y0 : ℚ) : ℝ) < 0 := by exact_mod_cast hw0
  have hw1' : ((s.width P s.y1 : ℚ) : ℝ) < 0 := by exact_mod_cast hw1
  simp only [Slab.width, Rat.cast_sub, Aff.eval_cast] at hw0' hw1'
  simp only [Aff.evalR] at hw0' hw1' hl' hr'
  rcases le_or_gt 0 (((P.hi.getD s.r default).c1 : ℝ) - (P.lo.getD s.l default).c1) with hd | hd
  · nlinarith [mul_le_mul_of_nonneg_left hy1 hd]
  · nlinarith [mul_le_mul_of_nonpos_left hy0 hd.le]

end SofaCert
