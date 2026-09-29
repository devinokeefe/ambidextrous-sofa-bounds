/-!
# Computational core of the certificate checker: data and exact polygon arithmetic

This library imports nothing beyond core Lean, so that the checker can be compiled to native
code without compiling Mathlib. The soundness proofs, in `SofaBounds.Cert.*`, are about exactly
these definitions.
-/

namespace SofaCert

/-! ## The data of the certificate (see `SofaBounds.Cert.Spec`) -/

/-- Cosine of the angle of hallway `j`: hallways 0, 2 have angle `arcsin (3/5)`, hallways 1, 3
angle `arcsin (4/5)`. -/
def hCos : Fin 4 → Rat
  | 0 => 4/5 | 1 => 3/5 | 2 => 4/5 | 3 => 3/5

/-- Sine of the angle of hallway `j`. -/
def hSin : Fin 4 → Rat
  | 0 => 3/5 | 1 => 4/5 | 2 => 3/5 | 3 => 4/5

/-- Whether hallway `j` is mirrored by `ρ(x, y) = (x, 1 - y)`. -/
def hMir : Fin 4 → Bool
  | 0 => false | 1 => false | 2 => true | 3 => true

/-- The width `W` of the box `B_W = [0, W] × [0, 1]`. -/
def boxW : Rat := 5

/-- A box of parameters: a pair `(lo, hi)` for each of the eight coordinates. Coordinate `2j` is
`u₁` and coordinate `2j + 1` is `u₂` of hallway `j`. -/
abbrev Box := Vector (Rat × Rat) 8

/-- The root box `E₀` of Lemma 5.1 for `W = 5`. -/
def rootBox : Box :=
  #v[(-1, 23/5), (-4, 4/5), (-1, 19/5), (-5, 3/5), (-1, 23/5), (-4, 4/5), (-1, 19/5), (-5, 3/5)]

/-! ## Polygons and slabs -/

/-- An affine function `y ↦ c0 + c1 * y` with rational coefficients. -/
structure Aff where
  c0 : Rat
  c1 : Rat
deriving Inhabited, Repr, DecidableEq

/-- Evaluation at a rational point. -/
def Aff.eval (f : Aff) (y : Rat) : Rat := f.c0 + f.c1 * y

/-- A polygon in the strip `0 ≤ y ≤ 1`: lower bounds `lo` and upper bounds `hi` for `x`. -/
structure Poly where
  lo : Array Aff
  hi : Array Aff
deriving Inhabited, Repr

/-- The intersection of two polygons: concatenate the constraints. -/
def Poly.inter (P Q : Poly) : Poly := ⟨P.lo ++ Q.lo, P.hi ++ Q.hi⟩

/-! ## Slabs (the verified part) -/

/-- A slab `y0 ≤ y ≤ y1` with the index `l` of a lower bound and `r` of an upper bound. -/
structure Slab where
  y0 : Rat
  y1 : Rat
  l : Nat
  r : Nat
deriving Inhabited, Repr

/-- The chosen indices of a slab are in range and `y0 ≤ y1`. -/
def Slab.ok (P : Poly) (s : Slab) : Bool :=
  decide (s.y0 ≤ s.y1) && decide (s.l < P.lo.size) && decide (s.r < P.hi.size)

/-- The slabs start at `0`, end at `1`, are consecutive, and their indices are in range. -/
def slabsValid (P : Poly) : List Slab → Bool
  | [] => false
  | s :: ss => s.y0 == 0 && s.ok P && go s ss
where
  go (prev : Slab) : List Slab → Bool
    | [] => prev.y1 == 1
    | s :: ss => s.y0 == prev.y1 && s.ok P && go s ss

/-- Width `r(y) - ℓ(y)` of the chosen bounds of a slab. -/
def Slab.width (P : Poly) (s : Slab) (y : Rat) : Rat :=
  (P.hi.getD s.r default).eval y - (P.lo.getD s.l default).eval y

/-- The trapezoid bound for one slab. -/
def Slab.bound (P : Poly) (s : Slab) : Rat :=
  (s.y1 - s.y0) * (max (s.width P s.y0) 0 + max (s.width P s.y1) 0) / 2

/-- The area bound given by a slab list. -/
def slabBound (P : Poly) (ss : List Slab) : Rat := (ss.map (Slab.bound P)).sum

/-- A slab list proves emptiness if the chosen width is negative at both ends of every slab. -/
def slabsNegative (P : Poly) (ss : List Slab) : Bool :=
  slabsValid P ss && ss.all fun s => decide (s.width P s.y0 < 0) && decide (s.width P s.y1 < 0)

end SofaCert
