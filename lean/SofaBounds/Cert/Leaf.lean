import SofaBounds.Cert.Envelope
import SofaBounds.Cert.CheckerAux.Cover
import SofaBounds.Cert.CheckerAux.Groups
import SofaCertCore.Leaf

/-!
# Soundness of the leaf test (Lemma 5.2 and Section 5.3 of the paper)

`leafOK_sound`: if `leafOK T B = true`, then `Good T u` for every `u` in the integer box `B`.

The sixteen polygons `P_σ` cover `B_W ∩ X(u)` (`leafTable_cover`). Their areas are bounded by
`nBound` (`nBound_volume`) or by `Poly.areaBound` (fallback), and the polygons in different
groups are disjoint by `fastDisjoint` (`fastDisjoint_sound`) or `Poly.disjoint`. A preconnected
subset of `B_W ∩ X(u)` lies in the union of one group (`volume_le_of_groups`).
-/

noncomputable section

namespace SofaCert

open MeasureTheory

/-! ## Lists, sums and `mapM` -/

theorem natSum_eq (l : List ℕ) : natSum l = l.sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [natSum, List.foldr_cons, List.sum_cons] at ih ⊢; rw [ih]

theorem ratSum_eq (l : List ℚ) : ratSum l = l.sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [ratSum, List.foldr_cons, List.sum_cons] at ih ⊢; rw [ih]

theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem list_sum_eq_range {M : Type*} [AddCommMonoid M] [Inhabited M] :
    ∀ l : List M, l.sum = ∑ k ∈ Finset.range l.length, l[k]!
  | [] => by simp
  | x :: xs => by
    rw [List.sum_cons, list_sum_eq_range xs, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

theorem list_mapM_some {α β : Type*} [Inhabited β] {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      ys.length = xs.length ∧ ∀ i (h : i < xs.length), f xs[i] = some ys[i]!
  | [], ys, h => by
    simp only [List.mapM_nil] at h
    cases h
    simp
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind_eq_some_iff, pure] at h
    obtain ⟨y, hy, ys', hys', h⟩ := h
    cases h
    obtain ⟨hl, hf⟩ := list_mapM_some hys'
    refine ⟨by simp [hl], fun i hi => ?_⟩
    cases i with
    | zero => simpa using hy
    | succ i => simpa using hf i (by simpa using hi)

/-! ## Rational bounds from integer inequalities -/

theorem real_le_of_den_mul {T : ℚ} {S sc : ℕ} (hsc : 0 < sc)
    (h : (T.den : ℤ) * (S : ℤ) ≤ T.num * (sc : ℤ)) : (S : ℝ) / sc ≤ (T : ℝ) := by
  have hd : (0 : ℚ) < T.den := by exact_mod_cast T.den_pos
  have hs : (0 : ℚ) < sc := by exact_mod_cast hsc
  have hq : (S : ℚ) / sc ≤ T := by
    rw [div_le_iff₀ hs]
    rw [← Rat.num_div_den T]
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    have : ((T.den : ℤ) * S : ℚ) ≤ (T.num * sc : ℤ) := by exact_mod_cast h
    push_cast at this
    linarith
  have := (Rat.cast_le (K := ℝ)).2 hq
  push_cast at this
  exact this

/-! ## The conclusion from a covering -/

theorem good_of_cover {T : ℚ} {u : Fin 8 → ℝ} {S : ℕ → Set (ℝ × ℝ)}
    (hcov : paramSet u ⊆ ⋃ i ∈ Finset.range 16, S i) (hS : ∀ i < 16, IsClosed (S i))
    {a : ℕ → ℝ} (ha : ∀ i < 16, 0 ≤ a i) (hvol : ∀ i < 16, volume (S i) ≤ ENNReal.ofReal (a i))
    (h : (∑ k ∈ Finset.range 16, a k ≤ T) ∨
      ∃ lab : ℕ → ℕ, (∀ i < 16, ∀ k < 16, i < k → lab i ≠ lab k → S i ∩ S k = ∅) ∧
        ∀ i < 16, ∑ k ∈ Finset.range 16, (if lab k = lab i then a k else 0) ≤ T) :
    Good T u := by
  intro K hK hpre
  rcases h with hsum | ⟨lab, hsep, hsum⟩
  · exact volume_le_of_sum volume ha hvol hsum (hK.trans hcov)
  · refine volume_le_of_groups volume hS ha hvol (lab := lab) ?_ ?_ (hK.trans hcov) hpre
    · intro i hi k hk hne
      rcases lt_trichotomy i k with hik | rfl | hki
      · exact hsep i hi k hk hik hne
      · exact absurd rfl hne
      · rw [Set.inter_comm]; exact hsep k hk i hi hki (Ne.symm hne)
    · intro i hi
      rw [Finset.sum_filter]
      exact hsum i hi

/-! ## The fast path -/

section Fast

variable {N : ℕ} {At : Array ℤ} {Pt : Array ℕ}

theorem fastDisjoint_sound (hN : 0 < N) (h : natTable N At = some Pt) (hsz : At.size = 18)
    {σ τ : ℕ} (hd : fastDisjoint N At Pt σ τ = true) :
    (polyOf N At σ).toSet ∩ (polyOf N At τ).toSet = ∅ := by
  have he := nNegative_empty hN h (fun l hl => hsz ▸ pairLo_lt hl)
    (fun r hr => hsz ▸ pairHi_lt hr) hd
  ext q
  rw [← mem_toSet_pair, he]

theorem fastAreas_spec (hN : 0 < N) (h : natTable N At = some Pt) (hsz : At.size = 18)
    {as : List ℕ} (hf : fastAreas N At Pt = some as) :
    as.length = 16 ∧ ∀ σ < 16, volume (polyOf N At σ).toSet ≤
      ENNReal.ofReal (((as[σ]! : ℕ) : ℝ) / (areaScale N : ℝ)) := by
  obtain ⟨hl, hs⟩ := list_mapM_some hf
  refine ⟨by simpa using hl, fun σ hσ => ?_⟩
  have := hs σ (by simpa using hσ)
  simp only [List.getElem_range] at this
  exact nBound_volume hN h (fun l hl => hsz ▸ loIdx_lt hl) (fun r hr => hsz ▸ hiIdx_lt hr) this

theorem sum_div_areaScale (f : ℕ → ℕ) (sc : ℕ) :
    ∑ k ∈ Finset.range 16, ((f k : ℝ) / sc) = ((∑ k ∈ Finset.range 16, f k : ℕ) : ℝ) / sc := by
  rw [← Finset.sum_div]; push_cast; rfl

theorem fast_sound {T : ℚ} {u : Fin 8 → ℝ} (hN : 0 < N) (h : natTable N At = some Pt)
    (hsz : At.size = 18) (hcov : paramSet u ⊆ ⋃ σ ∈ Finset.range 16, (polyOf N At σ).toSet)
    {as : List ℕ} (hf : fastAreas N At Pt = some as)
    (hok : (decide ((T.den : Int) * (natSum as : Int) ≤ T.num * (areaScale N : Int)) ||
      groupsOKN T N At Pt as.toArray (groupLabelsN N At Pt)) = true) : Good T u := by
  obtain ⟨hlen, hvol⟩ := fastAreas_spec hN h hsz hf
  have hsc : 0 < areaScale N := by exact_mod_cast areaScale_pos hN
  refine good_of_cover hcov (fun i _ => Poly.isClosed_toSet _)
    (a := fun σ => ((as[σ]! : ℕ) : ℝ) / (areaScale N : ℝ)) (fun i _ => by positivity) hvol ?_
  rcases Bool.or_eq_true_iff.1 hok with hs | hg
  · left
    have := real_le_of_den_mul hsc (of_decide_eq_true hs)
    rw [natSum_eq, list_sum_eq_range, hlen] at this
    rw [sum_div_areaScale (fun σ => as[σ]!)]
    exact this
  · right
    set lab := groupLabelsN N At Pt
    simp only [groupsOKN, labelsSeparateN, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, decide_eq_true_eq] at hg
    obtain ⟨hsep, hsum⟩ := hg
    refine ⟨fun k => lab[k]!, fun i hi k hk hik hne => ?_, fun i hi => ?_⟩
    · rcases hsep i hi k hk with (h1 | h1) | h1
      · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h1
        exact absurd hik h1
      · exact absurd (beq_iff_eq.1 h1) hne
      · exact fastDisjoint_sound hN h hsz h1
    · have := real_le_of_den_mul hsc (hsum i hi)
      rw [natSum_eq, sum_map_range] at this
      have e : ∀ k : ℕ, (if lab[k]! = lab[i]! then ((as[k]! : ℕ) : ℝ) / (areaScale N : ℝ) else 0) =
          (((if (lab[k]! == lab[i]!) = true then as.toArray[k]! else 0 : ℕ) : ℝ) /
            (areaScale N : ℝ)) := by
        intro k
        by_cases hk : lab[k]! = lab[i]!
        · simp [hk]
        · simp [hk]
      simp only [e]
      rw [sum_div_areaScale (fun k => if (lab[k]! == lab[i]!) = true then as.toArray[k]! else 0)]
      exact this

end Fast

/-! ## The fallback path -/

theorem polysOf_get {N : ℕ} {At : Array ℤ} {σ : ℕ} (hσ : σ < 16) :
    (polysOf N At)[σ]! = polyOf N At σ := by
  simp [polysOf, hσ]

theorem polysOf_size {N : ℕ} {At : Array ℤ} : (polysOf N At).size = 16 := by
  simp [polysOf]

theorem slabBound_nonneg_go {P : Poly} :
    ∀ (prev : Slab) (ss : List Slab), slabsValid.go P prev ss = true → 0 ≤ slabBound P ss
  | _, [], _ => by simp [slabBound]
  | _, s :: ss, h => by
    simp only [slabsValid.go, Bool.and_eq_true, Slab.ok, decide_eq_true_eq] at h
    obtain ⟨⟨-, ⟨⟨h01, -⟩, -⟩⟩, hgo⟩ := h
    have := slabBound_nonneg_go s ss hgo
    simp only [slabBound, List.map_cons, List.sum_cons] at this ⊢
    have hb : 0 ≤ s.bound P := by
      unfold Slab.bound
      exact div_nonneg (mul_nonneg (sub_nonneg.2 h01)
        (add_nonneg (le_max_right _ _) (le_max_right _ _))) (by norm_num)
    linarith

theorem slabBound_nonneg_of_valid {P : Poly} :
    ∀ {ss : List Slab}, slabsValid P ss = true → 0 ≤ slabBound P ss
  | [], hv => by simp [slabsValid] at hv
  | s :: ss, hv => by
    simp only [slabsValid, Bool.and_eq_true, Slab.ok, decide_eq_true_eq] at hv
    obtain ⟨⟨-, ⟨⟨h01, -⟩, -⟩⟩, hgo⟩ := hv
    have := slabBound_nonneg_go s ss hgo
    simp only [slabBound, List.map_cons, List.sum_cons] at this ⊢
    have hb : 0 ≤ s.bound P := by
      unfold Slab.bound
      exact div_nonneg (mul_nonneg (sub_nonneg.2 h01)
        (add_nonneg (le_max_right _ _) (le_max_right _ _))) (by norm_num)
    linarith

theorem areaBound_nonneg {P : Poly} {A : ℚ} (h : P.areaBound = some A) : 0 ≤ A := by
  unfold Poly.areaBound at h
  dsimp only at h
  split_ifs at h with hv
  cases h
  exact slabBound_nonneg_of_valid hv

theorem slow_sound {T : ℚ} {u : Fin 8 → ℝ} {N : ℕ} {At : Array ℤ}
    (hcov : paramSet u ⊆ ⋃ σ ∈ Finset.range 16, (polyOf N At σ).toSet)
    (hok : slowLeafOK T (polysOf N At) = true) : Good T u := by
  unfold slowLeafOK at hok
  split at hok
  · exact absurd hok (by simp)
  rename_i as has
  rw [Array.mapM_eq_mapM_toList] at has
  obtain ⟨las, hlas, rfl⟩ : ∃ las, List.mapM Poly.areaBound (polysOf N At).toList = some las ∧
      las.toArray = as := by
    cases hm : List.mapM Poly.areaBound (polysOf N At).toList with
    | none => rw [hm] at has; simp at has
    | some las => rw [hm] at has; simp at has; exact ⟨las, rfl, has⟩
  obtain ⟨hlen, hs⟩ := list_mapM_some hlas
  have hlen' : las.length = 16 := by rw [hlen]; simp [polysOf]
  have hps : ∀ σ < 16, (polysOf N At).toList[σ]! = polyOf N At σ := by
    intro σ hσ
    simp [polysOf, hσ]
  have hvol : ∀ σ < 16, volume (polyOf N At σ).toSet ≤ ENNReal.ofReal ((las[σ]! : ℚ) : ℝ) := by
    intro σ hσ
    have := hs σ (by rw [← hlen]; omega)
    rw [← getElem!_pos, hps σ hσ] at this
    exact Poly.volume_toSet_le this
  have hnn : ∀ σ < 16, (0 : ℝ) ≤ ((las[σ]! : ℚ) : ℝ) := by
    intro σ hσ
    have := hs σ (by rw [← hlen]; omega)
    rw [← getElem!_pos, hps σ hσ] at this
    exact_mod_cast areaBound_nonneg this
  refine good_of_cover hcov (fun i _ => Poly.isClosed_toSet _) (a := fun σ => ((las[σ]! : ℚ) : ℝ))
    hnn hvol ?_
  rcases Bool.or_eq_true_iff.1 hok with hsum | hg
  · left
    have hq := of_decide_eq_true hsum
    rw [ratSum_eq, List.toList_toArray, list_sum_eq_range, hlen'] at hq
    have := (Rat.cast_le (K := ℝ)).2 hq
    push_cast at this
    exact this
  · right
    set lab := groupLabels (polysOf N At)
    simp only [groupsOK, labelsSeparate, polysOf_size, Bool.and_eq_true, List.all_eq_true,
      List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hg
    obtain ⟨hsep, hsum⟩ := hg
    refine ⟨fun k => lab[k]!, fun i hi k hk hik hne => ?_, fun i hi => ?_⟩
    · rcases hsep i hi k hk with (h1 | h1) | h1
      · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h1
        exact absurd hik h1
      · exact absurd (beq_iff_eq.1 h1) hne
      · have := Poly.disjoint_sound h1
        rwa [polysOf_get hi, polysOf_get hk] at this
    · have hq := hsum i hi
      rw [ratSum_eq, sum_map_range] at hq
      have := (Rat.cast_le (K := ℝ)).2 hq
      push_cast at this
      convert this using 2 with k hk
      by_cases hl : lab[k]! = lab[i]!
      · simp [hl]
      · simp [hl]

/-! ## The leaf test -/

theorem leafOK_sound {T : ℚ} {B : IBox} (h : leafOK T B = true) {u : Fin 8 → ℝ}
    (hu : B.mem u) : Good T u := by
  have hcov : paramSet u ⊆
      ⋃ σ ∈ Finset.range 16, (polyOf (2 ^ (leafTable B).1) (leafTable B).2 σ).toSet := by
    intro q hq
    obtain ⟨σ, hσ, hmem⟩ := leafTable_cover hu hq
    exact Set.mem_biUnion (Finset.mem_range.2 hσ) hmem
  have hsz : (leafTable B).2.size = 18 := rfl
  have hN : 0 < 2 ^ (leafTable B).1 := by positivity
  unfold leafOK at h
  simp only at h
  rcases hnt : natTable (2 ^ (leafTable B).1) (leafTable B).2 with _ | Pt <;>
    simp only [hnt] at h
  · exact slow_sound hcov h
  · rcases hfa : fastAreas (2 ^ (leafTable B).1) (leafTable B).2 Pt with _ | as <;>
      simp only [hfa] at h
    · exact slow_sound hcov h
    · exact fast_sound hN hnt hsz hcov hfa h

end SofaCert
