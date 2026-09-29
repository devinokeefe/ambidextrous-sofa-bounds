import SofaCertCore.CheckerAux.Fast

/-!
# The leaf test `Γ(E) ≤ T` (computational part)

For a box `E` and hallway `j`, with `u₁ ∈ [a, b]` and `u₂ ∈ [c, d]`, Lemma 5.2 of the paper
covers the union of the hallways `X_j(u)`, `u ∈ E`, by the two convex pieces

* piece 1: `a ≤ f_j ≤ b + 1`, `g_j ≤ d + 1`;
* piece 2: `f_j ≤ a`, `c ≤ g_j ≤ d + 1`.

Every hallway constraint has a nonzero coefficient of `x` (`f_j` has `x`-coefficient
`hCos j > 0` and `g_j` has `-hSin j < 0`), so it is a lower or an upper bound for `x`, given by
an affine function of `y`. The box `B_W` gives `0 ≤ x ≤ 5` (and `0 ≤ y ≤ 1`, which is built
into `Poly.toSet`). The sixteen polygons `P_σ = B_W ∩ ⋂_j piece_{σ_j}` (`polyOf`, see
`SofaCertCore.CheckerAux.Fast`) cover `B_W ∩ X(u)` for every `u ∈ E`.

The test mirrors `eval_leaf` of the C checker `cchk.c`: pass if the sum of the areas is at most
`T`; otherwise group the polygons into the components of the "not provably disjoint" graph, and
require every group's total to be at most `T` (and, as the part of the test that soundness
relies on, that polygons in different groups are disjoint).

The areas and the disjointness tests come from the exact integer computations `fastAreas` and
`fastDisjoint`; if these fail (they do not, on valid input), the rational envelope computations
`Poly.areaBound` and `Poly.disjoint` are used instead.
-/

namespace SofaCert

/-! ## Groups -/

/-- The sum of a list of rationals. -/
def ratSum (l : List Rat) : Rat := l.foldr (· + ·) 0

/-- Polygons with different labels are disjoint. -/
def labelsSeparate (ps : Array Poly) (lab : Array Nat) : Bool :=
  (List.range ps.size).all fun i => (List.range ps.size).all fun k =>
    !(decide (i < k)) || lab[i]! == lab[k]! || Poly.disjoint ps[i]! ps[k]!

/-- The verified part of the component test, with rational areas: polygons with different
labels are disjoint, and the areas in each label class add up to at most `T`. -/
def groupsOK (T : Rat) (ps : Array Poly) (as : Array Rat) (lab : Array Nat) : Bool :=
  labelsSeparate ps lab &&
  (List.range ps.size).all fun i =>
    decide (ratSum ((List.range ps.size).map fun k =>
      if lab[k]! == lab[i]! then as[k]! else 0) ≤ T)

/-- Union–find `find` with a fuel bound (unverified; only proposes the groups). -/
def ufFind (par : Array Nat) (x : Nat) : Nat := Id.run do
  let mut y := x
  for _ in [0:par.size] do
    y := par[y]!
  return y

/-- The labels of the components of the "not provably disjoint" graph (unverified). -/
def groupLabels (ps : Array Poly) : Array Nat := Id.run do
  let n := ps.size
  let mut par : Array Nat := Array.range n
  for i in [0:n] do
    for k in [i+1:n] do
      let ri := ufFind par i
      let rk := ufFind par k
      if ri != rk then
        if !Poly.disjoint ps[i]! ps[k]! then
          par := par.set! ri rk
  return (Array.range n).map fun i => ufFind par i

/-! ## Groups, with the integer computations -/

/-- The sum of a list of natural numbers. -/
def natSum (l : List Nat) : Nat := l.foldr (· + ·) 0

/-- Polygons with different labels are disjoint (integer test). -/
def labelsSeparateN (N : Nat) (At : Array Int) (Pt : Array Nat) (lab : Array Nat) : Bool :=
  (List.range 16).all fun i => (List.range 16).all fun k =>
    !(decide (i < k)) || lab[i]! == lab[k]! || fastDisjoint N At Pt i k

/-- The verified part of the component test, with the integer computations. -/
def groupsOKN (T : Rat) (N : Nat) (At : Array Int) (Pt : Array Nat) (as : Array Nat)
    (lab : Array Nat) : Bool :=
  labelsSeparateN N At Pt lab &&
  (List.range 16).all fun i =>
    decide ((T.den : Int) * (natSum ((List.range 16).map fun k =>
      if lab[k]! == lab[i]! then as[k]! else 0) : Int) ≤ T.num * (areaScale N : Int))

/-- The labels of the components of the "not provably disjoint" graph (unverified). -/
def groupLabelsN (N : Nat) (At : Array Int) (Pt : Array Nat) : Array Nat := Id.run do
  let mut par : Array Nat := Array.range 16
  for i in [0:16] do
    for k in [i+1:16] do
      let ri := ufFind par i
      let rk := ufFind par k
      if ri != rk then
        if !fastDisjoint N At Pt i k then
          par := par.set! ri rk
  return (Array.range 16).map fun i => ufFind par i

/-! ## The leaf test -/

/-- The sixteen polygons of a leaf, as an array. -/
def polysOf (N : Nat) (At : Array Int) : Array Poly :=
  ((List.range 16).map (polyOf N At)).toArray

/-- The leaf test with rational areas (fallback). -/
def slowLeafOK (T : Rat) (ps : Array Poly) : Bool :=
  match ps.mapM Poly.areaBound with
  | none => false
  | some as => decide (ratSum as.toList ≤ T) || groupsOK T ps as (groupLabels ps)

/-- The leaf test `Γ(B) ≤ T` for an integer box. -/
def leafOK (T : Rat) (B : IBox) : Bool :=
  let tb := leafTable B
  let N := 2 ^ tb.1
  let At := tb.2
  match natTable N At with
  | none => slowLeafOK T (polysOf N At)
  | some Pt =>
    match fastAreas N At Pt with
    | none => slowLeafOK T (polysOf N At)
    | some as =>
      decide ((T.den : Int) * (natSum as : Int) ≤ T.num * (areaScale N : Int)) ||
        groupsOKN T N At Pt as.toArray (groupLabelsN N At Pt)

end SofaCert
