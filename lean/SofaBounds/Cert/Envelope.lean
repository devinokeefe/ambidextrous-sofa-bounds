import SofaBounds.Cert.Poly
import SofaCertCore.Envelope

/-!
# Soundness of `Poly.areaBound` and `Poly.disjoint`
-/

noncomputable section

namespace SofaCert

open MeasureTheory

theorem Poly.volume_toSet_le {P : Poly} {A : ℚ} (h : P.areaBound = some A) :
    volume P.toSet ≤ ENNReal.ofReal A := by
  unfold Poly.areaBound at h
  dsimp only at h
  split_ifs at h with hv
  cases h
  exact volume_toSet_le_slabBound hv

theorem Poly.disjoint_sound {P Q : Poly} (h : P.disjoint Q = true) :
    P.toSet ∩ Q.toSet = ∅ := by
  rw [← Poly.toSet_inter]
  exact toSet_eq_empty_of_slabsNegative h

end SofaCert
