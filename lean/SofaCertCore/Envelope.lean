import SofaCertCore.Basic

/-!
# The envelope computation (unverified) and the polygon interface of the leaf test

The envelope computation only *proposes* slabs; soundness does not depend on it, because every
proposal is checked by the verified functions `slabsValid`, `slabBound` and `slabsNegative` of
`SofaCertCore.Basic`.

Completeness (that a polygon gets its exact area and that disjoint polygons are recognised) does
depend on it. The proposal is exact: the slabs are the maximal intervals on which the upper
envelope of the lower bounds and the lower envelope of the upper bounds are each given by a single
line, further cut at the zero of the width when the width changes sign inside an interval. On
each slab the width `r(y) - ℓ(y)` of the chosen lines is then the true width of the polygon at
height `y` (or its negative part), which is affine, and so the trapezoid bound is the exact area.
For an empty polygon the width is negative everywhere, hence at both ends of every slab.
-/

namespace SofaCert

/-- Indices of the lines of `fs`, one for each slope, keeping for each slope the line with the
largest constant term (if `up`) or the smallest one (if not); the result is sorted by increasing
slope. -/
def bestPerSlope (fs : Array Aff) (up : Bool) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for i in [0:fs.size] do
    let f := fs[i]!
    let mut found := false
    for t in [0:out.size] do
      if !found then
        let g := fs[out[t]!]!
        if g.c1 == f.c1 then
          found := true
          if (up && g.c0 < f.c0) || (!up && f.c0 < g.c0) then out := out.set! t i
    if !found then
      out := (out.push i).insertionSort fun a b => fs[a]!.c1 < fs[b]!.c1
  return out

/-- The envelope on `[0, 1)` of the lines `fs[i]`, `i ∈ idx`, as an array of pairs
`(start, index)`, with starts increasing from `0`. If the slopes are increasing along `idx`
this is the upper envelope; if they are decreasing, the lower envelope. In both cases a line
`f` taking over from the current line `g` does so at `(g.c0 - f.c0) / (f.c1 - g.c1)`. -/
def hull (fs : Array Aff) (idx : Array Nat) : Array (Rat × Nat) := Id.run do
  let mut st : Array (Rat × Nat) := #[]
  for i in idx do
    let f := fs[i]!
    let mut go := true
    for _ in [0:st.size + 1] do
      if go then
        if st.size == 0 then
          st := st.push (0, i)
          go := false
        else
          let (s, t) := st.back!
          let g := fs[t]!
          let x := (g.c0 - f.c0) / (f.c1 - g.c1)
          if 1 ≤ x then
            go := false
          else if x ≤ s then
            st := st.pop
          else
            st := st.push (x, i)
            go := false
  return st

/-- The slabs proposed for a polygon: the breakpoints of the two envelopes, with the zero
crossings of the width inserted. -/
def envelopeSlabs (P : Poly) : List Slab := Id.run do
  let el := hull P.lo (bestPerSlope P.lo true)
  let er := hull P.hi (bestPerSlope P.hi false).reverse
  if el.size == 0 || er.size == 0 then return []
  let mut out : Array Slab := #[]
  let mut i := 0
  let mut k := 0
  let mut y0 : Rat := 0
  let mut done := false
  for _ in [0:el.size + er.size] do
    if !done then
      let l := el[i]!.2
      let r := er[k]!.2
      let nl : Rat := if i + 1 < el.size then el[i+1]!.1 else 1
      let nr : Rat := if k + 1 < er.size then er[k+1]!.1 else 1
      let y1 := if nl ≤ nr then nl else nr
      let fl := P.lo[l]!
      let fr := P.hi[r]!
      let w0 := fr.eval y0 - fl.eval y0
      let w1 := fr.eval y1 - fl.eval y1
      if (w0 < 0 && 0 < w1) || (0 < w0 && w1 < 0) then
        let ym := (fl.c0 - fr.c0) / (fr.c1 - fl.c1)
        out := out.push ⟨y0, ym, l, r⟩
        out := out.push ⟨ym, y1, l, r⟩
      else
        out := out.push ⟨y0, y1, l, r⟩
      if nl == y1 then i := i + 1
      if nr == y1 then k := k + 1
      y0 := y1
      if y1 == 1 then done := true
  return out.toList

/-! ## The interface used by the leaf test -/

/-- An upper bound for the area of a polygon, or `none` if the proposed slabs are invalid. -/
def Poly.areaBound (P : Poly) : Option Rat :=
  let ss := envelopeSlabs P
  if slabsValid P ss then some (slabBound P ss) else none

/-- A verified test that two polygons are disjoint. -/
def Poly.disjoint (P Q : Poly) : Bool :=
  let R := P.inter Q
  slabsNegative R (envelopeSlabs R)

end SofaCert
