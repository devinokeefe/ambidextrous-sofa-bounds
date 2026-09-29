import SofaBounds.Basic
import SofaCertCore.Basic

/-!
# The data of the computer-assisted bound (Theorem 1.1)

Four hallways, two of each turn, at the angles `arcsin (3/5)` and `arcsin (4/5)`:

* hallway 0: `L_{α₁}(u)`,   `cos = 4/5`, `sin = 3/5`;
* hallway 1: `L_{α₂}(u)`,   `cos = 3/5`, `sin = 4/5`;
* hallway 2: `ρ(L_{α₁}(u))`;
* hallway 3: `ρ(L_{α₂}(u))`.

This matches the specification files `specs/c_3653_*.json` used by the C checker:
`[[4,3,5,1,0,0],[3,4,5,1,0,0],[4,3,5,1,0,1],[3,4,5,1,0,1]]`, `W = 5`.

Points of the plane are written `q : ℝ × ℝ` with `q.1 = x`, `q.2 = y`. Parameter vectors are
`u : Fin 8 → ℝ`, where coordinate `2j` is `u₁` and coordinate `2j+1` is `u₂` of hallway `j`,
as in the certificate format.
-/

noncomputable section

namespace SofaCert

open MeasureTheory

/-- The `y`-coordinate seen by hallway `j`: `y`, or `1 - y` for a mirrored hallway. -/
def yOf (j : Fin 4) (y : ℝ) : ℝ := if hMir j then 1 - y else y

/-- The coordinate `f_j = x cos + y' sin` of hallway `j` (equation (5.1) of the paper). -/
def fR (j : Fin 4) (q : ℝ × ℝ) : ℝ := (hCos j : ℝ) * q.1 + (hSin j : ℝ) * yOf j q.2

/-- The coordinate `g_j = -x sin + y' cos` of hallway `j`. -/
def gR (j : Fin 4) (q : ℝ × ℝ) : ℝ := -(hSin j : ℝ) * q.1 + (hCos j : ℝ) * yOf j q.2

/-- The hallway `X(u)` in its own coordinates `(f, g)`: the union of its two arms. -/
def InHall (f g u₁ u₂ : ℝ) : Prop :=
  (u₁ ≤ f ∧ f ≤ u₁ + 1 ∧ g ≤ u₂ + 1) ∨ (f ≤ u₁ + 1 ∧ u₂ ≤ g ∧ g ≤ u₂ + 1)

/-- The hallway `X_j(u₁, u₂)`. -/
def hallSet (j : Fin 4) (u₁ u₂ : ℝ) : Set (ℝ × ℝ) := {q | InHall (fR j q) (gR j q) u₁ u₂}

/-- The box `B_W = [0, W] × [0, 1]` with `W = 5`. -/
def BW : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ q.1 ≤ 5 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1}

/-- Coordinate `2j` of a parameter vector. -/
def i₁ (j : Fin 4) : Fin 8 := ⟨2 * j.1, by omega⟩

/-- Coordinate `2j + 1` of a parameter vector. -/
def i₂ (j : Fin 4) : Fin 8 := ⟨2 * j.1 + 1, by omega⟩

/-- The set `B_W ∩ X(u)` of Lemma 5.1. -/
def paramSet (u : Fin 8 → ℝ) : Set (ℝ × ℝ) := BW ∩ ⋂ j : Fin 4, hallSet j (u (i₁ j)) (u (i₂ j))

/-- `Good T u`: every preconnected subset of `B_W ∩ X(u)` has area at most `T`, i.e.
`λ*(B_W ∩ X(u)) ≤ T`. -/
def Good (T : ℚ) (u : Fin 8 → ℝ) : Prop :=
  ∀ K ⊆ paramSet u, IsPreconnected K → volume K ≤ ENNReal.ofReal T

/-- Membership of a real parameter vector in a box. -/
def Box.mem (B : Box) (u : Fin 8 → ℝ) : Prop :=
  ∀ k : Fin 8, ((B[k]).1 : ℝ) ≤ u k ∧ u k ≤ ((B[k]).2 : ℝ)

end SofaCert
