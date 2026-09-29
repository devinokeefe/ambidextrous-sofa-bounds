import SofaBounds.Cert.CheckerAux.Fast

/-!
# Integer boxes and the covering by the sixteen polygons of a leaf (Lemma 5.2)

* `IBox.mem`: membership of a parameter vector in an integer box; `IBox.root_mem`,
  `IBox.mem_split` (bisection).
* `lineTable_cover`: for `u` in a box and `q ∈ B_W ∩ X(u)`, `q` lies in the polygon `P_σ` whose
  bit `j` records whether `f_j(q) < a_j`.
* `mem_toSet_pair`: the layout `pairLo`, `pairHi` describes `P_σ ∩ P_τ`.
-/

noncomputable section

namespace SofaCert

open MeasureTheory

/-! ## Integer boxes -/

/-- Membership of a real parameter vector in an integer box. -/
def IBox.mem (B : IBox) (u : Fin 8 → ℝ) : Prop :=
  ∀ k : Fin 8, (B.t[2 * k.1] : ℝ) / (5 * 2 ^ B.dep[k]) ≤ u k ∧
    u k ≤ (B.t[2 * k.1 + 1] : ℝ) / (5 * 2 ^ B.dep[k])

theorem IBox.root_mem {u : Fin 8 → ℝ} (h : rootBox.mem u) : IBox.root.mem u := by
  intro k
  have hk := h k
  fin_cases k <;>
  · simp [rootBox, IBox.root] at hk ⊢
    constructor <;> linarith [hk.1, hk.2]

theorem IBox.mem_split {B : IBox} {u : Fin 8 → ℝ} (h : B.mem u) (k : Fin 8) :
    (B.lower k).mem u ∨ (B.upper k).mem u := by
  have hk := h k
  set lo := B.t[2 * k.1] with hlo
  set hi := B.t[2 * k.1 + 1] with hhi
  set d := B.dep[k] with hd
  have hpow : (2 : ℝ) ^ (d + 1) = 2 * 2 ^ d := by ring
  have hp : (0 : ℝ) < 2 ^ d := by positivity
  -- the other coordinates are unchanged
  have other : ∀ (C : IBox) (x y : ℤ), C = ⟨(B.t.set (2 * k.1) x).set (2 * k.1 + 1) y,
      B.dep.set k (B.dep[k] + 1)⟩ → ∀ k' : Fin 8, k' ≠ k →
      (C.t[2 * k'.1] : ℝ) / (5 * 2 ^ C.dep[k']) ≤ u k' ∧
        u k' ≤ (C.t[2 * k'.1 + 1] : ℝ) / (5 * 2 ^ C.dep[k']) := by
    rintro C x y rfl k' hk'
    have hne : k.1 ≠ k'.1 := fun e => hk' (Fin.ext e).symm
    have := h k'
    have h1 : 2 * k.1 ≠ 2 * k'.1 := by omega
    have h2 : 2 * k.1 + 1 ≠ 2 * k'.1 := by omega
    have h3 : 2 * k.1 ≠ 2 * k'.1 + 1 := by omega
    have h4 : 2 * k.1 + 1 ≠ 2 * k'.1 + 1 := by omega
    simp only [Fin.getElem_fin] at this ⊢
    simp only [Vector.getElem_set, h1, h2, h3, h4, hne, ↓reduceIte]
    exact this
  by_cases hm : u k ≤ ((lo : ℝ) + hi) / (5 * 2 ^ (d + 1))
  · left
    intro k'
    by_cases hk' : k' = k
    · subst hk'
      simp only [IBox.lower, Fin.getElem_fin]
      rw [Vector.getElem_set_ne _ _ (by omega), Vector.getElem_set_self,
        Vector.getElem_set_self, Vector.getElem_set_self]
      rw [← hlo, ← hhi]
      simp only [Fin.getElem_fin] at hd
      rw [← hd]
      refine ⟨?_, by push_cast; exact hm⟩
      rw [hpow]
      have : ((2 * lo : ℤ) : ℝ) / (5 * (2 * 2 ^ d)) = (lo : ℝ) / (5 * 2 ^ d) := by
        push_cast; field_simp
      rw [this]; exact hk.1
    · exact other _ _ _ rfl k' hk'
  · right
    intro k'
    by_cases hk' : k' = k
    · subst hk'
      simp only [IBox.upper, Fin.getElem_fin]
      rw [Vector.getElem_set_ne _ _ (by omega), Vector.getElem_set_self,
        Vector.getElem_set_self, Vector.getElem_set_self]
      rw [← hlo, ← hhi]
      simp only [Fin.getElem_fin] at hd
      rw [← hd]
      refine ⟨by push_cast; exact (lt_of_not_ge hm).le, ?_⟩
      rw [hpow]
      have : ((2 * hi : ℤ) : ℝ) / (5 * (2 * 2 ^ d)) = (hi : ℝ) / (5 * 2 ^ d) := by
        push_cast; field_simp
      rw [this]; exact hk.2
    · exact other _ _ _ rfl k' hk'

theorem IBox.dep_le_depth (B : IBox) (k : Fin 8) : B.dep[k] ≤ B.depth := by
  obtain ⟨k, hk⟩ := k
  simp only [Fin.getElem_fin, IBox.depth]
  interval_cases k <;> simp only [le_max_iff, le_refl, true_or, or_true]

/-- The endpoints of coordinate `k` of a box, as numerators over `5 · 2^D`. -/
theorem IBox.mem_num {B : IBox} {u : Fin 8 → ℝ} (h : B.mem u) {D : ℕ} (hD : B.depth ≤ D)
    (k : Fin 8) :
    (B.num D ⟨2 * k.1, by omega⟩ : ℝ) / (5 * 2 ^ D) ≤ u k ∧
      u k ≤ (B.num D ⟨2 * k.1 + 1, by omega⟩ : ℝ) / (5 * 2 ^ D) := by
  have hk := h k
  have hdk : B.dep[k] ≤ D := (B.dep_le_depth k).trans hD
  have e1 : (2 * k.1) / 2 = k.1 := by omega
  have e2 : (2 * k.1 + 1) / 2 = k.1 := by omega
  have hsc : ∀ t : ℤ, ((t * ((2 ^ (D - B.dep[k]) : ℕ) : ℤ) : ℤ) : ℝ) / (5 * 2 ^ D) =
      (t : ℝ) / (5 * 2 ^ B.dep[k]) := by
    intro t
    have : (2 : ℝ) ^ D = 2 ^ (D - B.dep[k]) * 2 ^ B.dep[k] := by
      rw [← pow_add, Nat.sub_add_cancel hdk]
    rw [this]
    push_cast
    field_simp
  simp only [IBox.num, e1, e2]
  simp only [Fin.getElem_fin] at hk hsc
  rw [hsc, hsc]
  exact hk

/-! ## Polygons given by a layout -/

/-- The value at height `y` of line `i` of the table. -/
def lineX (N : ℕ) (At : Array ℤ) (i : ℕ) (y : ℝ) : ℝ := (lineAff N (At.getD i 0) (mOf i)).evalR y

theorem mem_toSet_polyOfL {N : ℕ} {At : Array ℤ} {lo hi : ℕ → ℕ} {nl nr : ℕ} {q : ℝ × ℝ} :
    q ∈ (polyOfL N At lo hi nl nr).toSet ↔ 0 ≤ q.2 ∧ q.2 ≤ 1 ∧
      (∀ l < nl, lineX N At (lo l) q.2 ≤ q.1) ∧ (∀ r < nr, q.1 ≤ lineX N At (hi r) q.2) := by
  simp only [Poly.toSet, Set.mem_ofPred_eq, mem_polyOfL_lo, mem_polyOfL_hi, lineX]
  constructor
  · rintro ⟨h0, h1, hl, hr⟩
    exact ⟨h0, h1, fun l hl' => hl _ ⟨l, hl', rfl⟩, fun r hr' => hr _ ⟨r, hr', rfl⟩⟩
  · rintro ⟨h0, h1, hl, hr⟩
    refine ⟨h0, h1, ?_, ?_⟩
    · rintro f ⟨l, hl', rfl⟩; exact hl l hl'
    · rintro f ⟨r, hr', rfl⟩; exact hr r hr'

theorem mem_toSet_pair {N : ℕ} {At : Array ℤ} {σ τ : ℕ} {q : ℝ × ℝ} :
    q ∈ (polyOfL N At (pairLo σ τ) (pairHi σ τ) 18 18).toSet ↔
      q ∈ (polyOf N At σ).toSet ∩ (polyOf N At τ).toSet := by
  simp only [Set.mem_inter_iff, polyOf, mem_toSet_polyOfL]
  constructor
  · rintro ⟨h0, h1, hl, hr⟩
    refine ⟨⟨h0, h1, fun l hl' => ?_, fun r hr' => ?_⟩, ⟨h0, h1, fun l hl' => ?_, fun r hr' => ?_⟩⟩
    · have := hl l (by omega)
      rwa [show pairLo σ τ l = loIdx σ l by simp only [pairLo, hl', ↓reduceIte]] at this
    · have := hr r (by omega)
      rwa [show pairHi σ τ r = hiIdx σ r by simp only [pairHi, hr', ↓reduceIte]] at this
    · have := hl (l + 9) (by omega)
      rwa [show pairLo σ τ (l + 9) = loIdx τ l by
        simp only [pairLo, show ¬ (l + 9 < 9) by omega, ↓reduceIte, Nat.add_sub_cancel]] at this
    · have := hr (r + 9) (by omega)
      rwa [show pairHi σ τ (r + 9) = hiIdx τ r by
        simp only [pairHi, show ¬ (r + 9 < 9) by omega, ↓reduceIte, Nat.add_sub_cancel]] at this
  · rintro ⟨⟨h0, h1, hl, hr⟩, ⟨-, -, hl', hr'⟩⟩
    refine ⟨h0, h1, fun l hl2 => ?_, fun r hr2 => ?_⟩
    · unfold pairLo
      split_ifs with h
      · exact hl l h
      · exact hl' (l - 9) (by omega)
    · unfold pairHi
      split_ifs with h
      · exact hr r h
      · exact hr' (r - 9) (by omega)

theorem pairLo_lt {σ τ l : ℕ} (hl : l < 18) : pairLo σ τ l < 18 := by
  unfold pairLo loIdx; split_ifs <;> omega

theorem pairHi_lt {σ τ r : ℕ} (hr : r < 18) : pairHi σ τ r < 18 := by
  unfold pairHi hiIdx; split_ifs <;> omega

theorem loIdx_lt {σ l : ℕ} (hl : l < 9) : loIdx σ l < 18 := by
  unfold loIdx; split_ifs <;> omega

theorem hiIdx_lt {σ r : ℕ} (hr : r < 9) : hiIdx σ r < 18 := by
  unfold hiIdx; split_ifs <;> omega

theorem lineTable_size (N : ℤ) (a b c d : Fin 4 → ℤ) : (lineTable N a b c d).size = 18 := rfl

/-! ## The lines of the table -/

section Table

variable {N : ℕ} {a b c d : Fin 4 → ℤ}

theorem hCos_pos (j : Fin 4) : (0 : ℝ) < (hCos j : ℝ) := by
  fin_cases j <;> norm_num [hCos]

theorem hSin_pos (j : Fin 4) : (0 : ℝ) < (hSin j : ℝ) := by
  fin_cases j <;> norm_num [hSin]

theorem lineX_zero (y : ℝ) : lineX N (lineTable N a b c d) 0 y = 0 := by
  simp [lineX, lineTable, lineAff_evalR, mOf]

theorem lineX_one (hN : 0 < N) (y : ℝ) : lineX N (lineTable N a b c d) 1 y = 5 := by
  have : (N : ℝ) ≠ 0 := by positivity
  simp [lineX, lineTable, lineAff_evalR, mOf]
  field_simp
  norm_num

theorem lineX_gd (hN : 0 < N) (j : Fin 4) (q : ℝ × ℝ) :
    (hSin j : ℝ) * (q.1 - lineX N (lineTable N a b c d) (2 + 4 * j.1) q.2) =
      ((d j : ℝ) + 5 * N) / (5 * N) - gR j q := by
  have : (N : ℝ) ≠ 0 := by positivity
  fin_cases j <;>
  · simp [lineX, lineTable, lineAff_evalR, mOf, gA, gR, yOf, hCos, hSin, hMir]
    field_simp
    ring

theorem lineX_fa (hN : 0 < N) (j : Fin 4) (q : ℝ × ℝ) :
    (hCos j : ℝ) * (q.1 - lineX N (lineTable N a b c d) (3 + 4 * j.1) q.2) =
      fR j q - (a j : ℝ) / (5 * N) := by
  have : (N : ℝ) ≠ 0 := by positivity
  fin_cases j <;>
  · simp [lineX, lineTable, lineAff_evalR, mOf, fA, fR, yOf, hCos, hSin, hMir]
    field_simp
    ring

theorem lineX_fb (hN : 0 < N) (j : Fin 4) (q : ℝ × ℝ) :
    (hCos j : ℝ) * (q.1 - lineX N (lineTable N a b c d) (4 + 4 * j.1) q.2) =
      fR j q - ((b j : ℝ) + 5 * N) / (5 * N) := by
  have : (N : ℝ) ≠ 0 := by positivity
  fin_cases j <;>
  · simp [lineX, lineTable, lineAff_evalR, mOf, fA, fR, yOf, hCos, hSin, hMir]
    field_simp
    ring

theorem lineX_gc (hN : 0 < N) (j : Fin 4) (q : ℝ × ℝ) :
    (hSin j : ℝ) * (q.1 - lineX N (lineTable N a b c d) (5 + 4 * j.1) q.2) =
      (c j : ℝ) / (5 * N) - gR j q := by
  have : (N : ℝ) ≠ 0 := by positivity
  fin_cases j <;>
  · simp [lineX, lineTable, lineAff_evalR, mOf, gA, gR, yOf, hCos, hSin, hMir]
    field_simp
    ring

end Table

/-! ## The covering -/

theorem loIdx_zero (σ : ℕ) : loIdx σ 0 = 0 := rfl

theorem loIdx_mid (σ : ℕ) (j : Fin 4) : loIdx σ (1 + j.1) = 2 + 4 * j.1 := by
  simp only [loIdx, show 1 + j.1 ≠ 0 by omega, show 1 + j.1 < 5 by omega, ↓reduceIte]
  omega

theorem loIdx_top (σ : ℕ) (j : Fin 4) :
    loIdx σ (5 + j.1) = if σ.testBit j.1 then 0 else 3 + 4 * j.1 := by
  simp only [loIdx, show 5 + j.1 ≠ 0 by omega, show ¬ (5 + j.1 < 5) by omega, ↓reduceIte,
    show 5 + j.1 - 5 = j.1 by omega]

theorem hiIdx_zero (σ : ℕ) : hiIdx σ 0 = 1 := rfl

theorem hiIdx_mid (σ : ℕ) (j : Fin 4) :
    hiIdx σ (1 + j.1) = if σ.testBit j.1 then 3 + 4 * j.1 else 4 + 4 * j.1 := by
  simp only [hiIdx, show 1 + j.1 ≠ 0 by omega, show 1 + j.1 < 5 by omega, ↓reduceIte,
    show 1 + j.1 - 1 = j.1 by omega]

theorem hiIdx_top (σ : ℕ) (j : Fin 4) :
    hiIdx σ (5 + j.1) = if σ.testBit j.1 then 5 + 4 * j.1 else 1 := by
  simp only [hiIdx, show 5 + j.1 ≠ 0 by omega, show ¬ (5 + j.1 < 5) by omega, ↓reduceIte,
    show 5 + j.1 - 5 = j.1 by omega]

theorem lt9_cases {l : ℕ} (hl : l < 9) :
    l = 0 ∨ (∃ j : Fin 4, l = 1 + j.1) ∨ (∃ j : Fin 4, l = 5 + j.1) := by
  rcases Nat.lt_or_ge l 1 with h | h
  · left; omega
  · rcases Nat.lt_or_ge l 5 with h' | h'
    · right; left; exact ⟨⟨l - 1, by omega⟩, by simp; omega⟩
    · right; right; exact ⟨⟨l - 5, by omega⟩, by simp; omega⟩

/-- The facts about one hallway used by the covering. -/
theorem hall_facts {f g u₁ u₂ A B C D : ℝ} (h : InHall f g u₁ u₂) (h1 : A ≤ u₁) (h2 : u₁ ≤ B)
    (h3 : C ≤ u₂) (h4 : u₂ ≤ D) : g ≤ D + 1 ∧ f ≤ B + 1 ∧ (f < A → C ≤ g) := by
  rcases h with ⟨h5, h6, h7⟩ | ⟨h5, h6, h7⟩ <;>
  exact ⟨by linarith, by linarith, fun hf => by linarith⟩

theorem exists_sigma4 : ∀ b0 b1 b2 b3 : Bool, ∃ σ, σ < 16 ∧ σ.testBit 0 = b0 ∧
    σ.testBit 1 = b1 ∧ σ.testBit 2 = b2 ∧ σ.testBit 3 = b3 := by
  decide

theorem exists_sigma (b : Fin 4 → Bool) : ∃ σ < 16, ∀ j : Fin 4, σ.testBit j.1 = b j := by
  obtain ⟨σ, hσ, h0, h1, h2, h3⟩ := exists_sigma4 (b 0) (b 1) (b 2) (b 3)
  refine ⟨σ, hσ, fun j => ?_⟩
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- A point of `B_W ∩ X(u)` lies in the polygon `P_σ` whose bits record `f_j(q) < a_j`. -/
theorem mem_polyOf_of_mem {N : ℕ} (hN : 0 < N) {a b c d : Fin 4 → ℤ} {u : Fin 8 → ℝ}
    (hab : ∀ j, (a j : ℝ) / (5 * N) ≤ u (i₁ j) ∧ u (i₁ j) ≤ (b j : ℝ) / (5 * N))
    (hcd : ∀ j, (c j : ℝ) / (5 * N) ≤ u (i₂ j) ∧ u (i₂ j) ≤ (d j : ℝ) / (5 * N))
    {q : ℝ × ℝ} (hq : q ∈ paramSet u) {σ : ℕ}
    (hσ : ∀ j : Fin 4, σ.testBit j.1 = decide (fR j q < (a j : ℝ) / (5 * N))) :
    q ∈ (polyOf N (lineTable N a b c d) σ).toSet := by
  simp only [paramSet, BW, hallSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at hq
  obtain ⟨⟨hx0, hx5, hy0, hy1⟩, hH⟩ := hq
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have facts : ∀ j : Fin 4, gR j q ≤ (d j : ℝ) / (5 * N) + 1 ∧
      fR j q ≤ (b j : ℝ) / (5 * N) + 1 ∧
      (fR j q < (a j : ℝ) / (5 * N) → (c j : ℝ) / (5 * N) ≤ gR j q) := fun j =>
    hall_facts (hH j) (hab j).1 (hab j).2 (hcd j).1 (hcd j).2
  have e1 : ∀ j : Fin 4, ((d j : ℝ) + 5 * N) / (5 * N) = (d j : ℝ) / (5 * N) + 1 := by
    intro j; field_simp
  have e2 : ∀ j : Fin 4, ((b j : ℝ) + 5 * N) / (5 * N) = (b j : ℝ) / (5 * N) + 1 := by
    intro j; field_simp
  have bitT : ∀ j : Fin 4, σ.testBit j.1 = true → fR j q < (a j : ℝ) / (5 * N) :=
    fun j hb => by
      have := hσ j
      rw [hb] at this
      exact of_decide_eq_true this.symm
  have bitF : ∀ j : Fin 4, ¬ σ.testBit j.1 = true → ¬ fR j q < (a j : ℝ) / (5 * N) :=
    fun j hb hf => hb (by rw [hσ j]; exact decide_eq_true hf)
  rw [polyOf, mem_toSet_polyOfL]
  refine ⟨hy0, hy1, fun l hl => ?_, fun r hr => ?_⟩
  · rcases lt9_cases hl with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [loIdx_zero, lineX_zero]; exact hx0
    · rw [loIdx_mid]
      have h1 := lineX_gd (a := a) (b := b) (c := c) (d := d) hN j q
      rw [e1] at h1
      have h2 : 0 ≤ (hSin j : ℝ) * (q.1 - lineX N (lineTable N a b c d) (2 + 4 * j.1) q.2) := by
        rw [h1]; linarith [(facts j).1]
      have := (mul_nonneg_iff_of_pos_left (hSin_pos j)).1 h2
      linarith
    · rw [loIdx_top]
      split_ifs with hb
      · rw [lineX_zero]; exact hx0
      · have hf := bitF j hb
        have h1 := lineX_fa (a := a) (b := b) (c := c) (d := d) hN j q
        have h2 : 0 ≤ (hCos j : ℝ) * (q.1 - lineX N (lineTable N a b c d) (3 + 4 * j.1) q.2) := by
          rw [h1]; linarith [not_lt.1 hf]
        have := (mul_nonneg_iff_of_pos_left (hCos_pos j)).1 h2
        linarith
  · rcases lt9_cases hr with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [hiIdx_zero, lineX_one hN]; exact hx5
    · rw [hiIdx_mid]
      split_ifs with hb
      · have hf := bitT j hb
        have h1 := lineX_fa (a := a) (b := b) (c := c) (d := d) hN j q
        have h2 : (hCos j : ℝ) * (q.1 - lineX N (lineTable N a b c d) (3 + 4 * j.1) q.2) ≤ 0 := by
          rw [h1]; linarith
        have := (mul_nonpos_iff_pos_imp_nonpos.1 h2).1 (hCos_pos j)
        linarith
      · have h1 := lineX_fb (a := a) (b := b) (c := c) (d := d) hN j q
        rw [e2] at h1
        have h2 : (hCos j : ℝ) * (q.1 - lineX N (lineTable N a b c d) (4 + 4 * j.1) q.2) ≤ 0 := by
          rw [h1]; linarith [(facts j).2.1]
        have := (mul_nonpos_iff_pos_imp_nonpos.1 h2).1 (hCos_pos j)
        linarith
    · rw [hiIdx_top]
      split_ifs with hb
      · have hf := bitT j hb
        have h1 := lineX_gc (a := a) (b := b) (c := c) (d := d) hN j q
        have h2 : (hSin j : ℝ) * (q.1 - lineX N (lineTable N a b c d) (5 + 4 * j.1) q.2) ≤ 0 := by
          rw [h1]; linarith [(facts j).2.2 hf]
        have := (mul_nonpos_iff_pos_imp_nonpos.1 h2).1 (hSin_pos j)
        linarith
      · rw [lineX_one hN]; exact hx5

/-- The covering of Lemma 5.2 for a leaf box. -/
theorem leafTable_cover {B : IBox} {u : Fin 8 → ℝ} (hu : B.mem u) {q : ℝ × ℝ}
    (hq : q ∈ paramSet u) :
    ∃ σ < 16, q ∈ (polyOf (2 ^ (leafTable B).1) (leafTable B).2 σ).toSet := by
  set D := B.depth with hD
  have hN : 0 < 2 ^ D := by positivity
  set a : Fin 4 → ℤ := fun j => B.num D ⟨4 * j.1, by omega⟩ with ha
  obtain ⟨σ, hσ16, hσ⟩ := exists_sigma fun j => decide (fR j q < (a j : ℝ) / (5 * ((2 ^ D : ℕ) : ℝ)))
  refine ⟨σ, hσ16, ?_⟩
  have hnum := IBox.mem_num hu (le_refl D)
  apply mem_polyOf_of_mem hN _ _ hq hσ
  · intro j
    have := hnum (i₁ j)
    have e1 : (⟨2 * (i₁ j).1, by omega⟩ : Fin 16) = ⟨4 * j.1, by omega⟩ := by
      ext; simp [i₁]; ring
    have e2 : (⟨2 * (i₁ j).1 + 1, by omega⟩ : Fin 16) = ⟨4 * j.1 + 1, by omega⟩ := by
      ext; simp [i₁]; ring
    rw [e1, e2] at this
    push_cast
    exact this
  · intro j
    have := hnum (i₂ j)
    have e1 : (⟨2 * (i₂ j).1, by omega⟩ : Fin 16) = ⟨4 * j.1 + 2, by omega⟩ := by
      ext; simp [i₂]; ring
    have e2 : (⟨2 * (i₂ j).1 + 1, by omega⟩ : Fin 16) = ⟨4 * j.1 + 3, by omega⟩ := by
      ext; simp [i₂]; ring
    rw [e1, e2] at this
    push_cast
    exact this

end SofaCert
