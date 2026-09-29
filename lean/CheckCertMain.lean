import SofaCertCore

/-!
# `checkcert`: run the certificate checker as compiled code

Usage:

* `checkcert T certfile` — e.g. `checkcert 353/200 cert_c_3653_1765.txt`. Reads the file into a
  `ByteArray`, computes exactly `SofaCert.checkCert T bytes`, prints the verdict, the number of
  leaves and the wall time, and exits with code 0 only if the certificate is accepted.
* `checkcert T certfile --bench K` — benchmark only (no verdict): checks about `K` of the
  parallel subtasks, evenly spread over the tree, and extrapolates the time of a full run.
* `checkcert T certfile --dump N stride` — cross-check only (no verdict): prints the exact
  `λ*` of the leaves `0, stride, 2 stride, …` (`N` of them), like `cchk.exe spec dump N stride`
  (with a final argument `rat`, also the value from the rational fallback computation).
* `checkcert T certfile --diag N` — profiling only (no verdict): timings of the parts of the leaf
  test on the first `N` leaves, and the number of leaves on which the integer path fails.

The verdict of the first form is the value of `SofaCert.checkCert T bytes`, about which
`SofaCert.checkCert_sound` is proved. The leaf count printed alongside it is computed separately
(by counting the letters `L`) and is for information only.
-/

open SofaCert

/-- Parse `n`, `n/d`, or a decimal `i.f`. -/
def parseRat (s : String) : Option Rat :=
  match s.splitOn "/" with
  | [n] =>
    match n.splitOn "." with
    | [i] => i.toInt?.map fun i => (i : Rat)
    | [i, f] => do
      let iv ← i.toNat?
      let fv ← f.toNat?
      pure ((iv : Rat) + (fv : Rat) / ((10 : Rat) ^ f.length))
    | _ => none
  | [n, d] => do
    let nv ← n.toInt?
    let dv ← d.toNat?
    if dv = 0 then none else pure ((nv : Rat) / (dv : Rat))
  | _ => none

/-- Number of letters `L` in `bytes[a:b]`. -/
def countL (bytes : ByteArray) (a b : Nat) : Nat := Id.run do
  let mut n := 0
  for i in [a:b] do
    if bytes[i]! == 76 then n := n + 1
  return n

/-- A rational as a decimal string with `digits` digits after the point (truncated). -/
def ratToDec (q : Rat) (digits : Nat := 12) : String :=
  let neg := q < 0
  let q := if neg then -q else q
  let scaled := (q.num.toNat * 10 ^ digits) / q.den
  let ip := scaled / 10 ^ digits
  let fp := toString (scaled % 10 ^ digits)
  let fp := String.ofList (List.replicate (digits - fp.length) '0') ++ fp
  (if neg then "-" else "") ++ toString ip ++ "." ++ fp

/-- The exact `λ*` of the union of the sixteen polygons of a box: the largest total area of a
component of the "not disjoint" graph (for cross-checks only; rational computation). -/
def leafValueQ (B : IBox) : Option Rat := do
  let tb := leafTable B
  let ps := polysOf (2 ^ tb.1) tb.2
  let as ← ps.mapM Poly.areaBound
  let lab := groupLabels ps
  let mut best : Rat := 0
  for i in [0:ps.size] do
    let mut s : Rat := 0
    for k in [0:ps.size] do
      if lab[k]! == lab[i]! then s := s + as[k]!
    if best < s then best := s
  return best

/-- The exact `λ*` as above, with the integer computations. -/
def leafValueN (B : IBox) : Option Rat := do
  let tb := leafTable B
  let N := 2 ^ tb.1
  let Pt ← natTable N tb.2
  let as ← fastAreas N tb.2 Pt
  let as := as.toArray
  let lab := groupLabelsN N tb.2 Pt
  let mut best : Nat := 0
  for i in [0:16] do
    let mut s : Nat := 0
    for k in [0:16] do
      if lab[k]! == lab[i]! then s := s + as[k]!
    if best < s then best := s
  return mkRat best (areaScale N)

/-- Walk the whole tree sequentially, calling `f` on every leaf box with its index; stop when
`f` returns `false`. Returns the number of leaves visited. -/
partial def forLeaves (bytes : ByteArray) (f : Nat → IBox → IO Bool) : IO Nat := do
  let rec go (pos : Nat) (B : IBox) (li : Nat) : IO (Option (Nat × Nat)) := do
    let p := skipWs bytes pos
    match tokenAt bytes p with
    | none => throw (IO.userError s!"bad token at {p}")
    | some none =>
      if ← f li B then return some (p + 1, li + 1) else return none
    | some (some k) =>
      match ← go (p + 1) (B.lower k) li with
      | none => return none
      | some (q, li') => go q (B.upper k) li'
  match ← go 0 IBox.root 0 with
  | none => return 0
  | some (_, n) => return n

def usage : IO UInt32 := do
  IO.println "usage: checkcert T certfile [--bench K | --dump N stride [rat] | --diag N]"
  return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | tStr :: path :: rest =>
    let some T := parseRat tStr | usage
    let t0 ← IO.monoMsNow
    let bytes ← IO.FS.readBinFile path
    IO.println s!"checkcert: T = {T}, file {path}, {bytes.size} bytes"
    let t1 ← IO.monoMsNow
    (← IO.getStdout).flush
    match rest with
    | [] =>
      -- The verdict is exactly `checkCert T bytes`. (It is printed before the second clock
      -- reading, so that its evaluation lies between the two readings; the first reading is
      -- taken before the file is read.)
      let ok := checkCert T bytes
      IO.println s!"checkCert {T} <file> = {ok}"
      let t2 ← IO.monoMsNow
      let leaves := countL bytes 0 bytes.size
      IO.println s!"leaves (letters L in the file): {leaves}"
      IO.println s!"wall time (reading the file and checkCert): {(t2 - t0).toFloat / 1000} s"
      if ok then
        IO.println s!"CERTIFICATE ACCEPTED: checkCert {T} = true"
        return 0
      else
        IO.println s!"CERTIFICATE REJECTED: checkCert {T} = false"
        return 1
    | ["--bench", kStr] =>
      let some K := kStr.toNat? | usage
      -- `if tX == 0 then … else …` makes each computation depend on the previous clock reading,
      -- and printing its result before the next reading forces it to be evaluated in between.
      let splits := if t1 == 0 then #[] else splitPlan bytes
      IO.println s!"split plan: {splits.size} split nodes"
      let t1a ← IO.monoMsNow
      IO.println s!"split plan time: {(t1a - t1).toFloat / 1000} s"
      let col := if t1a == 0 then none else collect T bytes splits maxDepth 0 IBox.root []
      match col with
      | none => IO.println "collect failed"; return 1
      | some (_, tasksRev) =>
        let tasks := tasksRev.reverse.toArray
        IO.println s!"sequential pass: {tasks.size} tasks"
        let t2 ← IO.monoMsNow
        IO.println s!"sequential pass time: {(t2 - t1).toFloat / 1000} s"
        let stride := max 1 (tasks.size / max K 1)
        let mut sample : Array (Nat × IBox) := #[]
        for i in [0:tasks.size] do
          if i % stride == stride / 2 then sample := sample.push tasks[i]!
        let mut sampleLeaves := 0
        for t in sample do
          match skipTree bytes t.1 1 with
          | some e => sampleLeaves := sampleLeaves + countL bytes t.1 e
          | none => pure ()
        let totalLeaves := countL bytes 0 bytes.size
        IO.println s!"sample: {sample.size} of {tasks.size} tasks, {sampleLeaves} of {totalLeaves} leaves"
        let t3 ← IO.monoMsNow
        let okAll := if t3 == 0 then false else
          (sample.toList.map fun t => Task.spawn fun _ => (walk T bytes maxDepth t.1 t.2).isSome).all Task.get
        IO.println s!"all sampled subtrees ok: {okAll}"
        let t4 ← IO.monoMsNow
        let secs := (t4 - t3).toFloat / 1000
        let rate := sampleLeaves.toFloat / secs
        IO.println s!"bench: {secs} s wall, {rate} leaves/s"
        IO.println s!"estimated full run: {totalLeaves.toFloat / rate / 3600} h + sequential pass {(t2 - t1).toFloat / 1000} s"
        return 0
    | "--dump" :: nStr :: sStr :: more =>
      let rat := more == ["rat"]
      let some N := nStr.toNat? | usage
      let some stride := sStr.toNat? | usage
      let printed ← IO.mkRef 0
      let _ ← forLeaves bytes fun li B => do
        if li % stride == 0 then
          let v := leafValueN B
          let s := match v with | some v => ratToDec v | none => "none"
          let ok := match v with | some v => decide (v ≤ T) | none => false
          let s2 := if rat then (match leafValueQ B with | some v => " rat " ++ ratToDec v | none => " rat none") else ""
          IO.println s!"LEAF {li} {s} {if ok then "ok" else "EXCEEDS"}{s2}"
          printed.modify (· + 1)
          return (← printed.get) < N
        return true
      return 0
    | ["--diag", nStr] =>
      let some N := nStr.toNat? | usage
      let boxes ← IO.mkRef (#[] : Array IBox)
      let _ ← forLeaves bytes fun li B => do
        boxes.modify (·.push B)
        return li + 1 < N
      let bs ← boxes.get
      let t2 ← IO.monoMsNow
      let mut nfast := 0
      let mut nnone := 0
      for B in bs do
        let tb := leafTable B
        let N := 2 ^ tb.1
        match natTable N tb.2 with
        | none => nnone := nnone + 1
        | some Pt =>
          match fastAreas N tb.2 Pt with
          | some as => if (T.den : Int) * (natSum as : Int) ≤ T.num * (areaScale N : Int) then nfast := nfast + 1
          | none => nnone := nnone + 1
      IO.println s!"{bs.size} leaves: fast pass {nfast}, fast path failed {nnone}"
      let t3a ← IO.monoMsNow
      IO.println s!"fast path time {(t3a - t2).toFloat / bs.size.toFloat} ms/leaf"
      let mut pro : Array (Array Nat × List (List ISlab)) := #[]
      for B in bs do
        let tb := leafTable B
        let N := 2 ^ tb.1
        let Pt := (natTable N tb.2).getD #[]
        let ps := (List.range 16).map fun σ => propose5 N (loLines tb.2 σ) (hiLines tb.2 σ)
        pro := pro.push (Pt, ps)
      IO.println s!"proposals {pro.size}"
      let t3b ← IO.monoMsNow
      IO.println s!"table+natTable+propose time {(t3b - t3a).toFloat / bs.size.toFloat} ms/leaf"
      let mut tot : Nat := 0
      for (Pt, ps) in pro do
        let mut σ := 0
        for sl in ps do
          match nBound Pt (loIdx σ) (hiIdx σ) 9 9 (Pt.getD 1 0 / (444 * lam) * lam) 0 0 sl with
          | some S => tot := tot + S
          | none => pure ()
          σ := σ + 1
      IO.println s!"nBound total {tot % 1000}"
      let mut nzero := 0
      let mut nslabZ := 0
      let mut nslabNZ := 0
      for (Pt, ps) in pro do
        let top := Pt.getD 1 0 / (444 * lam) * lam
        let mut σ := 0
        for sl in ps do
          match nBound Pt (loIdx σ) (hiIdx σ) 9 9 top 0 0 sl with
          | some 0 => nzero := nzero + 1; nslabZ := nslabZ + sl.length
          | some _ => nslabNZ := nslabNZ + sl.length
          | none => pure ()
          σ := σ + 1
      IO.println s!"polygons with zero area: {nzero} of {16 * pro.size}; slabs in zero polys {nslabZ}, in others {nslabNZ}"
      let t3 ← IO.monoMsNow
      IO.println s!"nBound time {(t3 - t3b).toFloat / bs.size.toFloat} ms/leaf"
      IO.println s!"fast path time {(t3 - t2).toFloat / bs.size.toFloat} ms/leaf"
      let mut nok := 0
      for B in bs do
        if leafOK T B then nok := nok + 1
      IO.println s!"leafOK true: {nok}"
      let t4 ← IO.monoMsNow
      IO.println s!"leafOK time {(t4 - t3).toFloat / bs.size.toFloat} ms/leaf"
      return 0
    | _ => usage
  | _ => usage
