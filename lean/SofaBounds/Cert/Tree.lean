import SofaBounds.Cert.Leaf
import SofaCertCore.Tree

/-!
# Soundness of the certificate walk: the leaves cover the root box (Proposition 5.4)

* `walk_sound`: if the sequential walk of a subtree succeeds, every point of its box is good
  (every leaf passes `leafOK`, and the two halves of a bisection cover the box).
* `collect_sound`: the tasks recorded by `collect`, together with the leaves it checks, cover
  its box.
* `checkCert_sound`: logically `(Task.spawn f).get = f ()`, so the parallel tasks are just the
  sequential walks of the recorded subtrees.
-/

noncomputable section

namespace SofaCert

theorem walk_sound {T : ℚ} {bytes : ByteArray} :
    ∀ (fuel pos : ℕ) (B : IBox) (q : ℕ), walk T bytes fuel pos B = some q →
      ∀ u, B.mem u → Good T u
  | 0, pos, B, q, h => by simp [walk] at h
  | fuel + 1, pos, B, q, h => by
    simp only [walk] at h
    split at h
    · simp at h
    · split_ifs at h with hl
      exact fun u hu => leafOK_sound hl hu
    · rename_i k _
      split at h
      · simp at h
      · rename_i q1 h1
        intro u hu
        rcases IBox.mem_split hu k with hu' | hu'
        · exact walk_sound fuel _ _ _ h1 u hu'
        · exact walk_sound fuel _ _ _ h u hu'

theorem collect_sound {T : ℚ} {bytes : ByteArray} {splits : Array ℕ} :
    ∀ (fuel pos : ℕ) (B : IBox) (acc : List (ℕ × IBox)) (q : ℕ) (acc' : List (ℕ × IBox)),
      collect T bytes splits fuel pos B acc = some (q, acc') →
      ∃ new, acc' = new ++ acc ∧
        ((∀ t ∈ new, ∀ u, t.2.mem u → Good T u) → ∀ u, B.mem u → Good T u)
  | 0, pos, B, acc, q, acc', h => by simp [collect] at h
  | fuel + 1, pos, B, acc, q, acc', h => by
    simp only [collect] at h
    by_cases hs : sortedMem splits (skipWs bytes pos) = true
    · simp only [hs, ↓reduceIte] at h
      split at h
      · simp at h
      · by_cases hl : leafOK T B = true
        · simp only [hl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ⟨[], by simp, fun _ u hu => leafOK_sound hl hu⟩
        · simp [hl] at h
      · rename_i k _
        split at h
        · simp at h
        · rename_i q1 acc1 h1
          obtain ⟨new1, rfl, hg1⟩ := collect_sound fuel _ _ _ _ _ h1
          obtain ⟨new2, rfl, hg2⟩ := collect_sound fuel _ _ _ _ _ h
          refine ⟨new2 ++ new1, by simp, fun hall u hu => ?_⟩
          rcases IBox.mem_split hu k with hu' | hu'
          · exact hg1 (fun t ht => hall t (by simp [ht])) u hu'
          · exact hg2 (fun t ht => hall t (by simp [ht])) u hu'
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨[(skipWs bytes pos, B)], rfl, fun hall u hu => ?_⟩
        exact hall (skipWs bytes pos, B) (List.mem_singleton_self _) u hu

theorem checkCert_sound {T : ℚ} {bytes : ByteArray} (h : checkCert T bytes = true) :
    ∀ u, rootBox.mem u → Good T u := by
  unfold checkCert at h
  rcases hc : collect T bytes (splitPlan bytes) maxDepth 0 IBox.root [] with _ | ⟨q, tasks⟩ <;>
    simp only [hc] at h
  · exact absurd h (by simp)
  split_ifs at h with hq
  obtain ⟨new, hnew, hgood⟩ := collect_sound _ _ _ _ _ _ hc
  rw [List.append_nil] at hnew
  subst hnew
  intro u hu
  refine hgood (fun t ht u' hu' => ?_) u (IBox.root_mem hu)
  rw [List.all_map, List.all_eq_true] at h
  have hw : (walk T bytes maxDepth t.1 t.2).isSome = true := h t ht
  obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1 hw
  exact walk_sound _ _ _ _ hq' u' hu'

end SofaCert
