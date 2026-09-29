import SofaCertCore.Envelope

/-!
# Integer boxes, the sixteen polygons of a leaf, and the exact integer computations

## Integer boxes

The walk of the certificate tree keeps boxes in integer form: coordinate `k` of an `IBox` is the
interval `[t[2k], t[2k+1]] / (5 · 2^dep[k])`. Bisection is exact and needs no division.

## The polygons

At a leaf let `D = max dep[k]`, `N = 2^D`, and write every endpoint as `t' / (5N)`. All the lines
of the leaf test are then `x = A / (12N) + (m / 12) y` with an integer `A` and a slope
`m ∈ {0, ±9, ±16}`. The eighteen lines of a leaf form a table `At` (see `lineTable`):

* entry `0`: `x = 0`; entry `1`: `x = 5`;
* entries `2 + 4j + e` for hallway `j`: `e = 0`: `g_j = d + 1`; `e = 1`: `f_j = a`;
  `e = 2`: `f_j = b + 1`; `e = 3`: `g_j = c`.

A polygon is given by a *layout*: `nl` lower bounds, the `l`-th being table entry `lo l`, and `nr`
upper bounds, the `r`-th being table entry `hi r` (`polyOfL`). The polygon `P_σ` (`σ < 16`, bit
`j` of `σ` = piece of hallway `j`) has nine lower and nine upper bounds (`loIdx`, `hiIdx`);
constraints absent from a piece are replaced by the redundant bounds `x ≥ 0` or `x ≤ 5`. The
intersection `P_σ ∩ P_τ` has the eighteen lower and eighteen upper bounds of both (`pairLo`,
`pairHi`).

## Exact computations in natural numbers

Heights are measured in units of `1 / (N Λ)` with `Λ = 50400`, which is divisible by every
difference of two slopes (`7, 9, 16, 18, 25, 32`); hence every crossing of two lines is at an
integer height `Y ∈ [0, N Λ]`. At height `Y`, line `i` has
`12 N Λ · (x + 32) = Pt[i] + m_i Y` with `Pt[i] = (A_i + 384 N) Λ`; the offset `32` makes all
these values nonnegative (`natTable` checks this, so that the natural-number subtraction for
negative slopes is exact). For a slab `[Y0, Y1]` with chosen lines `l`, `r`, the positive part of
the width at `Y` times `12 N Λ` is the truncated difference `V_r(Y) - V_l(Y)`, and the trapezoid
bound times `24 N² Λ²` is `(Y1 - Y0) · ((V_r(Y0) - V_l(Y0)) + (V_r(Y1) - V_l(Y1)))`.

`propose5` (unverified) computes the slabs of the two envelopes, cut at the zeros of the width.
`nBound` and `nNegative` (verified in `SofaBounds.Cert.CheckerAux.Fast`) check that the slabs are
consecutive from `0` to `N Λ`, and add up the trapezoid bounds, resp. check that the width is
negative at both ends of every slab. They agree with the frozen `slabBound` and `slabsNegative`
of the corresponding rational slabs of `polyOfL`.
-/

namespace SofaCert

/-! ## Integer boxes -/

/-- A box in integer form: coordinate `k` is `[t[2k], t[2k+1]] / (5 · 2^dep[k])`. -/
structure IBox where
  t : Vector Int 16
  dep : Vector Nat 8

/-- The root box `E₀` (`rootBox`, times 5). -/
def IBox.root : IBox :=
  ⟨#v[-5, 23, -20, 4, -5, 19, -25, 3, -5, 23, -20, 4, -5, 19, -25, 3], #v[0, 0, 0, 0, 0, 0, 0, 0]⟩

instance : Inhabited IBox := ⟨IBox.root⟩

/-- The lower half of an integer box in coordinate `k`. -/
def IBox.lower (B : IBox) (k : Fin 8) : IBox :=
  let lo := B.t[2 * k.1]
  let hi := B.t[2 * k.1 + 1]
  ⟨(B.t.set (2 * k.1) (2 * lo)).set (2 * k.1 + 1) (lo + hi), B.dep.set k (B.dep[k] + 1)⟩

/-- The upper half of an integer box in coordinate `k`. -/
def IBox.upper (B : IBox) (k : Fin 8) : IBox :=
  let lo := B.t[2 * k.1]
  let hi := B.t[2 * k.1 + 1]
  ⟨(B.t.set (2 * k.1) (lo + hi)).set (2 * k.1 + 1) (2 * hi), B.dep.set k (B.dep[k] + 1)⟩

/-- The largest depth of the coordinates of a box. -/
def IBox.depth (B : IBox) : Nat :=
  max (max (max B.dep[0] B.dep[1]) (max B.dep[2] B.dep[3]))
    (max (max B.dep[4] B.dep[5]) (max B.dep[6] B.dep[7]))

/-- Endpoint `i` (`i = 2k` lower, `i = 2k + 1` upper) of a box, as a numerator over `5 · 2^D`. -/
@[inline] def IBox.num (B : IBox) (D : Nat) (i : Fin 16) : Int :=
  B.t[i] * ((2 ^ (D - B.dep[i.1 / 2]'(by omega)) : Nat) : Int)

/-! ## The lines -/

/-- `Λ`, a common multiple of the slope differences. -/
def lam : Nat := 50400

/-- `A` of the line `f_j = t / (5N)` (as `x = A / (12N) + (m / 12) y`). -/
@[inline] def fA (j : Fin 4) (N t : Int) : Int :=
  match j with
  | 0 => 3 * t
  | 1 => 4 * t
  | 2 => 3 * (t - 3 * N)
  | 3 => 4 * (t - 4 * N)

/-- `A` of the line `g_j = t / (5N)`. -/
@[inline] def gA (j : Fin 4) (N t : Int) : Int :=
  match j with
  | 0 => -4 * t
  | 1 => -3 * t
  | 2 => 4 * (4 * N - t)
  | 3 => 3 * (3 * N - t)

/-- The slope (times 12) of entry `i` of the table of lines. -/
@[inline] def mOf (i : Nat) : Int :=
  match i with
  | 2 => 16 | 3 => -9 | 4 => -9 | 5 => 16
  | 6 => 9 | 7 => -16 | 8 => -16 | 9 => 9
  | 10 => -16 | 11 => 9 | 12 => 9 | 13 => -16
  | 14 => -9 | 15 => 16 | 16 => 16 | 17 => -9
  | _ => 0

/-- The table of the eighteen lines of a leaf, from the endpoints `a, b` (of `u₁`) and `c, d` (of
`u₂`) of each hallway, as numerators over `5N`. -/
def lineTable (N : Int) (a b c d : Fin 4 → Int) : Array Int :=
  #[0, 60 * N,
    gA 0 N (d 0 + 5 * N), fA 0 N (a 0), fA 0 N (b 0 + 5 * N), gA 0 N (c 0),
    gA 1 N (d 1 + 5 * N), fA 1 N (a 1), fA 1 N (b 1 + 5 * N), gA 1 N (c 1),
    gA 2 N (d 2 + 5 * N), fA 2 N (a 2), fA 2 N (b 2 + 5 * N), gA 2 N (c 2),
    gA 3 N (d 3 + 5 * N), fA 3 N (a 3), fA 3 N (b 3 + 5 * N), gA 3 N (c 3)]

/-- The depth `D` and the table of lines of a leaf box. -/
def leafTable (B : IBox) : Nat × Array Int :=
  let D := B.depth
  let N : Int := ((2 ^ D : Nat) : Int)
  (D, lineTable N (fun j => B.num D ⟨4 * j.1, by omega⟩) (fun j => B.num D ⟨4 * j.1 + 1, by omega⟩)
    (fun j => B.num D ⟨4 * j.1 + 2, by omega⟩) (fun j => B.num D ⟨4 * j.1 + 3, by omega⟩))

/-! ## Polygons -/

/-- The line `x = A / (12N) + (m / 12) y`. -/
def lineAff (N : Nat) (A m : Int) : Aff := ⟨(A : Rat) / (12 * (N : Rat)), (m : Rat) / 12⟩

/-- The polygon with the given layout. -/
def polyOfL (N : Nat) (At : Array Int) (lo hi : Nat → Nat) (nl nr : Nat) : Poly :=
  ⟨(Array.range nl).map fun l => lineAff N (At.getD (lo l) 0) (mOf (lo l)),
   (Array.range nr).map fun r => lineAff N (At.getD (hi r) 0) (mOf (hi r))⟩

/-- Table entry of lower bound number `l` (`l < 9`) of `P_σ`. -/
@[inline] def loIdx (σ l : Nat) : Nat :=
  if l = 0 then 0
  else if l < 5 then 2 + 4 * (l - 1)
  else if σ.testBit (l - 5) then 0 else 3 + 4 * (l - 5)

/-- Table entry of upper bound number `r` (`r < 9`) of `P_σ`. -/
@[inline] def hiIdx (σ r : Nat) : Nat :=
  if r = 0 then 1
  else if r < 5 then (if σ.testBit (r - 1) then 3 + 4 * (r - 1) else 4 + 4 * (r - 1))
  else if σ.testBit (r - 5) then 5 + 4 * (r - 5) else 1

/-- Lower bound number `l` (`l < 18`) of `P_σ ∩ P_τ`. -/
@[inline] def pairLo (σ τ l : Nat) : Nat := if l < 9 then loIdx σ l else loIdx τ (l - 9)

/-- Upper bound number `r` (`r < 18`) of `P_σ ∩ P_τ`. -/
@[inline] def pairHi (σ τ r : Nat) : Nat := if r < 9 then hiIdx σ r else hiIdx τ (r - 9)

/-- The polygon `P_σ` of a leaf with table `At` (at scale `N`). -/
def polyOf (N : Nat) (At : Array Int) (σ : Nat) : Poly :=
  polyOfL N At (loIdx σ) (hiIdx σ) 9 9

/-! ## Verified computations in natural numbers -/

/-- Lines `i < n` of the table are at `x ≥ -32` for `0 ≤ y ≤ 1`. -/
def natTableOK (N : Nat) (At : Array Int) : Nat → Bool
  | 0 => true
  | i + 1 =>
    decide (0 ≤ At.getD i 0 + 384 * (N : Int)) &&
    decide (0 ≤ (At.getD i 0 + 384 * (N : Int)) * (lam : Int) +
      min (mOf i) 0 * ((N : Int) * (lam : Int))) &&
    natTableOK N At i

/-- The table `Pt[i] = (At[i] + 384 N) Λ`, if every line is at `x ≥ -32` on `0 ≤ y ≤ 1`, so
that `Pt[i] + m_i Y ≥ 0` for `0 ≤ Y ≤ N Λ`. -/
def natTable (N : Nat) (At : Array Int) : Option (Array Nat) :=
  if natTableOK N At At.size then some (At.map fun A => (A + 384 * (N : Int)).toNat * lam)
  else none

/-- `12 N Λ (x + 32)` for line `i` at height `Y` (exact when `natTable` succeeded). -/
@[inline] def lineVal (Pt : Array Nat) (i Y : Nat) : Nat :=
  let m := mOf i
  if 0 ≤ m then Pt.getD i 0 + m.toNat * Y else Pt.getD i 0 - m.natAbs * Y

/-- A slab in integer form: it ends at height `y1` (in units `1 / (N Λ)`) and starts where the
previous one ends; `l` and `r` are the numbers of the chosen lower and upper bound. -/
structure ISlab where
  y1 : Nat
  l : Nat
  r : Nat
deriving Inhabited, Repr

/-- `24 N² Λ²` times the trapezoid bound of the slab `[y0, y1]` with table lines `il`, `ir`. -/
@[inline] def slabTerm (Pt : Array Nat) (y0 y1 il ir : Nat) : Nat :=
  (y1 - y0) * ((lineVal Pt ir y0 - lineVal Pt il y0) + (lineVal Pt ir y1 - lineVal Pt il y1))

/-- Check that the slabs are consecutive from `y0` to `top`, with `l < nl`, `r < nr`, and add
their bounds to `acc`. -/
@[specialize] def nBound (Pt : Array Nat) (lo hi : Nat → Nat) (nl nr top : Nat) :
    Nat → Nat → List ISlab → Option Nat
  | acc, y0, [] => if y0 = top then some acc else none
  | acc, y0, s :: ss =>
    if y0 ≤ s.y1 ∧ s.l < nl ∧ s.r < nr then
      nBound Pt lo hi nl nr top (acc + slabTerm Pt y0 s.y1 (lo s.l) (hi s.r)) s.y1 ss
    else none

/-- Check that the slabs are consecutive from `y0` to `top`, with `l < nl`, `r < nr`, and that the
width is negative at both ends of each slab. -/
@[specialize] def nNegative (Pt : Array Nat) (lo hi : Nat → Nat) (nl nr top : Nat) :
    Nat → List ISlab → Bool
  | y0, [] => y0 = top
  | y0, s :: ss =>
    decide (y0 ≤ s.y1 ∧ s.l < nl ∧ s.r < nr) &&
    decide (lineVal Pt (hi s.r) y0 < lineVal Pt (lo s.l) y0) &&
    decide (lineVal Pt (hi s.r) s.y1 < lineVal Pt (lo s.l) s.y1) &&
    nNegative Pt lo hi nl nr top s.y1 ss

/-! ## Unverified slab proposal for the polygons of the leaf test

Every polygon of the leaf test has, after keeping the best line of each slope, exactly one lower
bound and one upper bound of each of the five slopes `-16, -9, 0, 9, 16` (classes `0, …, 4`):
the redundant `x ≥ 0`, `x ≤ 5` are in class `2`, the lines `g_j = d + 1` fill the four other
lower classes and the lines `f_j = …` the four other upper classes. -/

/-- The best line of each slope class of one side of a polygon: `A` and layout number. -/
structure Lines5 where
  a0 : Int
  a1 : Int
  a2 : Int
  a3 : Int
  a4 : Int
  i0 : Nat
  i1 : Nat
  i2 : Nat
  i3 : Nat
  i4 : Nat
deriving Inhabited

/-- `A` of class `c`. -/
@[inline] def Lines5.a (L : Lines5) (c : Nat) : Int :=
  match c with | 0 => L.a0 | 1 => L.a1 | 2 => L.a2 | 3 => L.a3 | _ => L.a4

/-- Layout number of class `c`. -/
@[inline] def Lines5.i (L : Lines5) (c : Nat) : Nat :=
  match c with | 0 => L.i0 | 1 => L.i1 | 2 => L.i2 | 3 => L.i3 | _ => L.i4

/-- The slope (times 12) of class `c`. -/
@[inline] def sC (c : Nat) : Int :=
  match c with | 0 => -16 | 1 => -9 | 2 => 0 | 3 => 9 | _ => 16

/-- The lower bounds of `P_σ` (class `c` from layout numbers as in `loIdx`). -/
def loLines (At : Array Int) (σ : Nat) : Lines5 :=
  let A := fun i => At.getD i 0
  let b0 := σ.testBit 0
  let b1 := σ.testBit 1
  let b2 := σ.testBit 2
  let b3 := σ.testBit 3
  let (a0, i0) := if !b1 && A 10 < A 7 then (A 7, 6) else (A 10, 3)
  let (a1, i1) := if !b0 && A 14 < A 3 then (A 3, 5) else (A 14, 4)
  let (a3, i3) := if !b2 && A 6 < A 11 then (A 11, 7) else (A 6, 2)
  let (a4, i4) := if !b3 && A 2 < A 15 then (A 15, 8) else (A 2, 1)
  ⟨a0, a1, A 0, a3, a4, i0, i1, 0, i3, i4⟩

/-- The upper bounds of `P_σ` (class `c` from layout numbers as in `hiIdx`). -/
def hiLines (At : Array Int) (σ : Nat) : Lines5 :=
  let A := fun i => At.getD i 0
  let b0 := σ.testBit 0
  let b1 := σ.testBit 1
  let b2 := σ.testBit 2
  let b3 := σ.testBit 3
  let f1 := if b1 then A 7 else A 8
  let (a0, i0) := if b2 && A 13 < f1 then (A 13, 7) else (f1, 2)
  let f0 := if b0 then A 3 else A 4
  let (a1, i1) := if b3 && A 17 < f0 then (A 17, 8) else (f0, 1)
  let f2 := if b2 then A 11 else A 12
  let (a3, i3) := if b1 && A 9 < f2 then (A 9, 6) else (f2, 3)
  let f3 := if b3 then A 15 else A 16
  let (a4, i4) := if b0 && A 5 < f3 then (A 5, 5) else (f3, 4)
  ⟨a0, a1, A 1, a3, a4, i0, i1, 0, i3, i4⟩

/-- Classwise best of two sets of lower bounds (layout numbers of the second shifted by 9). -/
def Lines5.maxWith (L M : Lines5) : Lines5 :=
  let p := fun (a : Int) (i : Nat) (b : Int) (j : Nat) => if a < b then (b, j + 9) else (a, i)
  let (a0, i0) := p L.a0 L.i0 M.a0 M.i0
  let (a1, i1) := p L.a1 L.i1 M.a1 M.i1
  let (a2, i2) := p L.a2 L.i2 M.a2 M.i2
  let (a3, i3) := p L.a3 L.i3 M.a3 M.i3
  let (a4, i4) := p L.a4 L.i4 M.a4 M.i4
  ⟨a0, a1, a2, a3, a4, i0, i1, i2, i3, i4⟩

/-- Classwise best of two sets of upper bounds (layout numbers of the second shifted by 9). -/
def Lines5.minWith (L M : Lines5) : Lines5 :=
  let p := fun (a : Int) (i : Nat) (b : Int) (j : Nat) => if b < a then (b, j + 9) else (a, i)
  let (a0, i0) := p L.a0 L.i0 M.a0 M.i0
  let (a1, i1) := p L.a1 L.i1 M.a1 M.i1
  let (a2, i2) := p L.a2 L.i2 M.a2 M.i2
  let (a3, i3) := p L.a3 L.i3 M.a3 M.i3
  let (a4, i4) := p L.a4 L.i4 M.a4 M.i4
  ⟨a0, a1, a2, a3, a4, i0, i1, i2, i3, i4⟩

/-- Where line `(Af, class cf)` crosses line `(Ag, class cg)` (height in units `1/(NΛ)`). -/
@[inline] def crossC (Ag : Int) (cg : Nat) (Af : Int) (cf : Nat) : Int :=
  (Ag - Af) * ((lam : Int) / (sC cf - sC cg))

/-- Next breakpoint of the upper envelope of `lo` after class `L`: the smallest crossing with a
class `c > L` (ties: largest `c`), scanning `c = 4, 3, …` down to `L + 1`. -/
def nextUp (lo : Lines5) (L : Nat) : Nat → Int → Nat → Int × Nat
  | 0, bY, bC => (bY, bC)
  | k + 1, bY, bC =>
    let c := 4 - k
    if c ≤ L then nextUp lo L k bY bC
    else
      let y := crossC (lo.a L) L (lo.a c) c
      if y ≤ bY then nextUp lo L k y c else nextUp lo L k bY bC

/-- Next breakpoint of the lower envelope of `hi` after class `R`: the smallest crossing with a
class `c < R` (ties: smallest `c`), scanning `c = 4, 3, …` down to `0`. -/
def nextDown (hi : Lines5) (R : Nat) : Nat → Int → Nat → Int × Nat
  | 0, bY, bC => (bY, bC)
  | k + 1, bY, bC =>
    let c := 4 - k
    if R ≤ c then nextDown hi R k bY bC
    else
      let y := crossC (hi.a R) R (hi.a c) c
      if y < bY then nextDown hi R k y c else nextDown hi R k bY bC

/-- The class of the largest `A` (ties: largest class). -/
def argMaxA (L : Lines5) : Nat :=
  let (b, c) := if L.a1 ≥ L.a0 then (L.a1, 1) else (L.a0, 0)
  let (b, c) := if L.a2 ≥ b then (L.a2, 2) else (b, c)
  let (b, c) := if L.a3 ≥ b then (L.a3, 3) else (b, c)
  if L.a4 ≥ b then 4 else c

/-- The class of the smallest `A` (ties: smallest class). -/
def argMinA (L : Lines5) : Nat :=
  let (b, c) := if L.a3 ≤ L.a4 then (L.a3, 3) else (L.a4, 4)
  let (b, c) := if L.a2 ≤ b then (L.a2, 2) else (b, c)
  let (b, c) := if L.a1 ≤ b then (L.a1, 1) else (b, c)
  if L.a0 ≤ b then 0 else c

/-- The slabs of the two envelopes from height `y0` on, with current classes `L` (lower) and
`R` (upper), cut at the zero crossings of the width. -/
def slabs5 (lo hi : Lines5) (top : Int) : Nat → Int → Nat → Nat → List ISlab
  | 0, _, _, _ => []
  | fuel + 1, y0, L, R =>
    let (nl, cl) := nextUp lo L 5 top L
    let (nr, cr) := nextDown hi R 5 top R
    let y1 := if nl ≤ nr then nl else nr
    let li := lo.i L
    let ri := hi.i R
    let rest := if y1 < top then
        slabs5 lo hi top fuel y1 (if nl == y1 then cl else L) (if nr == y1 then cr else R)
      else []
    let s : ISlab := ⟨y1.toNat, li, ri⟩
    if L != R then
      -- the classes differ, so the slopes differ; the width changes sign strictly inside the
      -- slab iff its zero is strictly inside
      let ys := crossC (hi.a R) R (lo.a L) L
      if y0 < ys && ys < y1 then ⟨ys.toNat, li, ri⟩ :: s :: rest else s :: rest
    else s :: rest

/-- The proposed slabs of a polygon given by its best lines. -/
@[inline] def propose5 (N : Nat) (lo hi : Lines5) : List ISlab :=
  slabs5 lo hi ((N : Int) * (lam : Int)) 12 0 (argMaxA lo) (argMinA hi)

/-! ## The fast computations of a leaf -/

/-- The integer areas (times `24 N² Λ²`) of the sixteen polygons, if all proposals are valid. -/
def fastAreas (N : Nat) (At : Array Int) (Pt : Array Nat) : Option (List Nat) :=
  (List.range 16).mapM fun σ =>
    nBound Pt (loIdx σ) (hiIdx σ) 9 9 (N * lam) 0 0 (propose5 N (loLines At σ) (hiLines At σ))

/-- A verified test that `P_σ` and `P_τ` are disjoint. -/
def fastDisjoint (N : Nat) (At : Array Int) (Pt : Array Nat) (σ τ : Nat) : Bool :=
  nNegative Pt (pairLo σ τ) (pairHi σ τ) 18 18 (N * lam) 0
    (propose5 N ((loLines At σ).maxWith (loLines At τ)) ((hiLines At σ).minWith (hiLines At τ)))

/-- The scale `24 N² Λ²` of the integer areas. -/
def areaScale (N : Nat) : Nat := 24 * N ^ 2 * lam ^ 2

end SofaCert
