import SofaCertCore.Leaf

/-!
# Walking the certificate tree (computational part)

A certificate is a byte string of whitespace-separated tokens in preorder: a digit `0`–`7` is an
internal node, bisecting its box in that coordinate at the exact midpoint (the lower half comes
first), and `L` is a leaf. The boxes are recomputed from `rootBox` (in integer form,
`IBox.root`).

`checkCert` works in three steps.

1. `planSplits` (unverified) scans the file once and chooses the internal nodes at which the
   tree is split into parallel tasks, so that every task is small.
2. `collect` walks the tree sequentially through the chosen nodes, checking the leaves it meets
   and recording every other subtree as a task (position, box), which it skips over with a token
   counter (`skipTree`).
3. The tasks are checked in parallel with `Task.spawn`, each by the sequential walk `walk`.

Logically `(Task.spawn f).get = f ()`, so the soundness proof ignores the parallelism. Soundness
depends neither on the plan nor on the token positions, only on the fact that the checked boxes
cover `rootBox`. Malformed input (bad characters, tokens not separated by white space, an
incomplete tree, trailing tokens, a tree deeper than `maxDepth`) is rejected.
-/

namespace SofaCert

/-! ## Tokens -/

/-- White space: space, tab, line feed, carriage return. -/
@[inline] def isWs (c : UInt8) : Bool := c == 32 || c == 10 || c == 13 || c == 9

/-- The first position `≥ pos` that is not white space (or `bytes.size`). -/
def skipWs (bytes : ByteArray) (pos : Nat) : Nat :=
  if h : pos < bytes.size then
    if isWs bytes[pos] then skipWs bytes (pos + 1) else pos
  else pos
termination_by bytes.size - pos

/-- A token must be followed by white space or by the end of the file. -/
@[inline] def sepOK (bytes : ByteArray) (pos : Nat) : Bool :=
  if h : pos < bytes.size then isWs bytes[pos] else true

/-- The token at position `pos` (which must not be white space): `some (some k)` for a split in
coordinate `k`, `some none` for a leaf, `none` for a bad token. -/
@[inline] def tokenAt (bytes : ByteArray) (pos : Nat) : Option (Option (Fin 8)) :=
  if h : pos < bytes.size then
    let c := bytes[pos]
    if !sepOK bytes (pos + 1) then none
    else if c == 76 then some none
    else if 48 ≤ c && c ≤ 55 then some (some ⟨(c - 48).toNat % 8, Nat.mod_lt _ (by decide)⟩)
    else none
  else none

/-- The maximal depth of a certificate tree. -/
def maxDepth : Nat := 1000

/-! ## The sequential walk -/

/-- Check the subtree whose first token is at (or after white space from) `pos`, with box `B`.
Returns the position after the subtree if the subtree is well formed and all its leaves pass. -/
def walk (T : Rat) (bytes : ByteArray) : Nat → Nat → IBox → Option Nat
  | 0, _, _ => none
  | fuel + 1, pos, B =>
    let p := skipWs bytes pos
    match tokenAt bytes p with
    | none => none
    | some none => if leafOK T B then some (p + 1) else none
    | some (some k) =>
      match walk T bytes fuel (p + 1) (B.lower k) with
      | none => none
      | some q => walk T bytes fuel q (B.upper k)

/-- Skip a subtree without checking it: count the subtrees still needed (`need`) and return the
position after the subtree (`none` if the input ends first or contains a bad token). -/
def skipTree (bytes : ByteArray) (pos need : Nat) : Option Nat :=
  if need = 0 then some pos
  else if h : pos < bytes.size then
    if isWs bytes[pos] then skipTree bytes (pos + 1) need
    else
      match tokenAt bytes pos with
      | none => none
      | some none => skipTree bytes (pos + 1) (need - 1)
      | some (some _) => skipTree bytes (pos + 1) (need + 1)
  else none
termination_by bytes.size - pos

/-! ## Splitting into tasks -/

/-- Membership in a sorted array (binary search). -/
def sortedMem (a : Array Nat) (x : Nat) : Bool := Id.run do
  let mut lo := 0
  let mut hi := a.size
  for _ in [0:64] do
    if lo < hi then
      let mid := (lo + hi) / 2
      let v := a[mid]!
      if v == x then return true
      else if v < x then lo := mid + 1
      else hi := mid
  return false

/-- Walk the tree sequentially through the nodes at the positions listed in `splits` (sorted),
checking the leaves met on the way; every other subtree is recorded as a task (position, box)
and skipped. Returns the position after the tree and the tasks (in reverse order). -/
def collect (T : Rat) (bytes : ByteArray) (splits : Array Nat) :
    Nat → Nat → IBox → List (Nat × IBox) → Option (Nat × List (Nat × IBox))
  | 0, _, _, _ => none
  | fuel + 1, pos, B, acc =>
    let p := skipWs bytes pos
    if sortedMem splits p then
      match tokenAt bytes p with
      | none => none
      | some none => if leafOK T B then some (p + 1, acc) else none
      | some (some k) =>
        match collect T bytes splits fuel (p + 1) (B.lower k) acc with
        | none => none
        | some (q, acc') => collect T bytes splits fuel q (B.upper k) acc'
    else
      match skipTree bytes p 1 with
      | none => none
      | some q => some (q, (p, B) :: acc)

/-- Scan the file once and choose the nodes at which the tree is split into tasks (unverified;
it only affects the running time): every node of depth `< minDepth`, and every node of depth
`< maxDepthPlan` whose subtree has more than `maxBytes` bytes. Returns their positions, sorted. -/
def planSplits (bytes : ByteArray) (minDepth maxDepthPlan maxBytes : Nat) : Array Nat :=
  (go (2 * bytes.size + 2) 0 false #[] #[] #[]).qsort (· < ·)
where
  /-- The scan, as a single tail-recursive loop. `stStart` and `stState` are the stack of open
  internal nodes (position, whether the lower subtree is complete); in `closing` mode the
  subtrees completed by the leaf at `pos` are closed one by one. -/
  go : Nat → Nat → Bool → Array Nat → Array Bool → Array Nat → Array Nat
    | 0, _, _, _, _, marks => marks
    | fuel + 1, pos, closing, stStart, stState, marks =>
      if closing then
        if stStart.size == 0 then marks
        else if stState.back! then
          let start := stStart.back!
          let stStart := stStart.pop
          let depth := stStart.size
          let marks :=
            if depth < minDepth || (depth < maxDepthPlan && pos + 1 - start > maxBytes) then
              marks.push start
            else marks
          go fuel pos true stStart stState.pop marks
        else go fuel (pos + 1) false stStart (stState.set! (stState.size - 1) true) marks
      else if h : pos < bytes.size then
        let c := bytes[pos]
        if c == 76 then go fuel pos true stStart stState marks
        else if 48 ≤ c && c ≤ 55 then
          go fuel (pos + 1) false (stStart.push pos) (stState.push false) marks
        else go fuel (pos + 1) false stStart stState marks
      else marks

/-- The split points used by `checkCert`. -/
def splitPlan (bytes : ByteArray) : Array Nat := planSplits bytes 8 40 (1 <<< 17)

/-! ## The checker -/

/-- Check a certificate for `λ*(B_W ∩ X(u)) ≤ T` over the root box. -/
def checkCert (T : Rat) (bytes : ByteArray) : Bool :=
  match collect T bytes (splitPlan bytes) maxDepth 0 IBox.root [] with
  | none => false
  | some (q, tasks) =>
    if skipWs bytes q == bytes.size then
      let ts := tasks.map fun t => Task.spawn fun _ => (walk T bytes maxDepth t.1 t.2).isSome
      ts.all Task.get
    else false

end SofaCert
