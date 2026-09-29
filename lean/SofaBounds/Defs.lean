/-
The definitions in the section `FormalConjecturesDefs` below are copied from the Formal Conjectures
project (google-deepmind/formal-conjectures), file `FormalConjectures/Wikipedia/MovingSofa.lean`,
together with the ambidextrous definitions proposed in pull request #6424 of that project
(head commit ae26cdcee112f0b0a776dd13c915a82974bb356b).

  Copyright 2026 The Formal Conjectures Authors.
  Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file
  except in compliance with the License. You may obtain a copy of the License at
      https://www.apache.org/licenses/LICENSE-2.0
  Unless required by applicable law or agreed to in writing, software distributed under the
  License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
  either express or implied. See the License for the specific language governing permissions
  and limitations under the License.

Changes: the `module`/`public import FormalConjecturesUtil` header is replaced by `import Mathlib`,
the notation `ℝ²` (defined in `FormalConjecturesForMathlib/Geometry/2d.lean`) is repeated here, and
the `@[category ...]` attributes are dropped. The definitions themselves are unchanged.
The Z-shaped corridor at the end of the file is our own.
-/
import Mathlib

noncomputable section

/-- `ℝ²` as in `FormalConjecturesForMathlib/Geometry/2d.lean`. -/
scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace MovingSofa

open Topology
open scoped Real unitInterval EuclideanGeometry

section FormalConjecturesDefs

/-- The **horizontal side** of the hallway is $(-\infty, 1] \times [0, 1]$. -/
def horizontalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1)}

/-- The **vertical side** of the hallway is $[0, 1] \times (-\infty, 1]$. -/
def verticalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : 0 ≤ x ∧ x ≤ 1 ∧ y ≤ 1)}

/-- The **hallway** is the union of its horizontal and vertical sides. -/
def hallway : Set ℝ² := horizontalHallway ∪ verticalHallway

scoped notation "E(2)" => ℝ² ≃ᵃⁱ[ℝ] ℝ²

instance : TopologicalSpace E(2) :=
  .induced (·.toAffineIsometry.toContinuousAffineMap) inferInstance

/--
A connected closed set $s$ is a **moving sofa** according to a rigid motion $m:I\to\mathrm{SE}(2)$,
if the sofa is initially in the horizontal side of the hallway and ends up in the vertical side.
Here, since $\mathrm{SE}(2)$ is not in Mathlib yet, we use $\mathrm{E}(2)$ and rely on continuity
and $m(0) = \mathrm{id}$ to ensure $m$ is in $\mathrm{SE}(2)$.
-/
structure IsMovingSofa (s : Set ℝ²) (m : I → E(2)) : Prop where
  isConnected : IsConnected s
  isClosed : IsClosed s
  continuous : Continuous m
  zero : m 0 = .refl ℝ ℝ²
  initial : s ⊆ horizontalHallway
  subset_hallway : ∀ t, m t '' s ⊆ hallway
  final : m 1 '' s ⊆ verticalHallway

open MeasureTheory
open scoped ENNReal

/-- The **sofa constant** is the maximal area of a moving sofa. -/
def sofaConstant : ℝ≥0∞ := ⨆ (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m), volume s

/-- The horizontal line $y = 1/2$, the axis of symmetry of the horizontal side of the hallway. -/
def midline : AffineSubspace ℝ ℝ² :=
  AffineSubspace.mk' !₂[0, 1 / 2] (ℝ ∙ (EuclideanSpace.basisFun (Fin 2) ℝ 0))

instance : Nonempty midline := ⟨⟨_, AffineSubspace.self_mem_mk' _ _⟩⟩

/-- Reflection in `midline` acts as $(x, y) \mapsto (x, 1 - y)$. -/
theorem reflection_midline_apply (q : ℝ²) :
    EuclideanGeometry.reflection midline q = !₂[q 0, 1 - q 1] := by
  rw [EuclideanGeometry.reflection_apply_of_mem midline q (AffineSubspace.self_mem_mk' _ _),
    midline, AffineSubspace.direction_mk', Submodule.reflection_apply,
    Submodule.starProjection_singleton]
  ext i
  fin_cases i <;> simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.vecHead] <;> ring

/-- A closed connected set is an **ambidextrous sofa** if both it and its reflection in `midline`
are moving sofas [Ro18, Thm. 5]. -/
def IsAmbidextrousSofa (s : Set ℝ²) : Prop :=
  (∃ m, IsMovingSofa s m) ∧ (∃ m, IsMovingSofa (EuclideanGeometry.reflection midline '' s) m)

/-- The **ambidextrous sofa constant** is the maximal area of an ambidextrous sofa. -/
def ambidextrousSofaConstant : ℝ≥0∞ :=
  ⨆ (s : Set ℝ²) (_ : IsAmbidextrousSofa s), volume s

end FormalConjecturesDefs

/-! ## The Z-shaped corridor (Section 2.3 of the paper) -/

section ZCorridor

/-- The entry arm $A_1 = (-\infty, 1] \times [0, 1]$ of the Z-shaped corridor. -/
def zEntry : Set ℝ² := {p | p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1}

/-- The vertical section $M = [0, 1] \times [0, D + 1]$. -/
def zMiddle (D : ℝ) : Set ℝ² := {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ D + 1}

/-- The exit arm $A_2 = [0, \infty) \times [D, D + 1]$. -/
def zExit (D : ℝ) : Set ℝ² := {p | 0 ≤ p 0 ∧ D ≤ p 1 ∧ p 1 ≤ D + 1}

/-- The Z-shaped corridor $Z_D = A_1 \cup M \cup A_2$: a left turn followed by a right turn. -/
def zCorridor (D : ℝ) : Set ℝ² := zEntry ∪ zMiddle D ∪ zExit D

/-- A closed connected set `s` **passes through** $Z_D$ with the rigid motion `m`: it starts in
the entry arm, stays in the corridor, and ends in the exit arm. The conventions (a motion
`m : I → E(2)`, continuous, starting at the identity) are those of `IsMovingSofa`. -/
structure PassesThroughZ (D : ℝ) (s : Set ℝ²) (m : I → E(2)) : Prop where
  isConnected : IsConnected s
  isClosed : IsClosed s
  continuous : Continuous m
  zero : m 0 = .refl ℝ ℝ²
  initial : s ⊆ zEntry
  subset_corridor : ∀ t, m t '' s ⊆ zCorridor D
  final : m 1 '' s ⊆ zExit D

open MeasureTheory in
/-- The largest area of a set that passes through $Z_D$. -/
def zSofaConstant (D : ℝ) : ENNReal := ⨆ (s : Set ℝ²) (_ : ∃ m, PassesThroughZ D s m), volume s

end ZCorridor

end MovingSofa
