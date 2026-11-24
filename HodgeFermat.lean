/-
  HodgeFermat.lean  --  Lean 4 translation of hodge_fermat.py
  (Hodge classes on Fermat varieties, Shioda's criterion)

  X = X_m^n : x_0^m + ... + x_{n+1}^m = 0  in  P^{n+1},   dim X = n (n even).

  * The primitive cohomology is a sum of 1-dimensional eigenspaces, one for each
    alpha = (a_0,...,a_{n+1}) with a_i in {1..m-1} and sum a_i = 0 (mod m).
  * <alpha> := sum a_i / m,  Hodge type (p,q) with q = <alpha> - 1, p = n - q.
  * Shioda's criterion: <t*alpha> = n/2 + 1 for every t in (Z/m)^*.
  * "Decomposable" alpha: alpha can be split into pairs {a, m-a}
    (these come from linear subspaces, hence are algebraic).
  * Indecomposable Hodge alphas are classes not explained by the linear-subspace
    method. This alone does not prove they are non-algebraic; their algebraicity
    is a separate question.

  Uses only the Lean core library and Std (Mathlib is not required).

  Usage (Lean 4 >= 4.15 recommended):
    lean --run HodgeFermat.lean selftest
    lean --run HodgeFermat.lean hodge 4 2
    lean --run HodgeFermat.lean list 6 4 --limit 3
    lean --run HodgeFermat.lean table 2 30 --n 2

  For large parameters, compiling is much faster than interpreting:
    lake new hodgefermat && (put HodgeFermat.lean in place of Main.lean)
    lake build && .lake/build/bin/hodgefermat table 2 30 --n 2
-/
import Std.Data.HashMap

namespace HodgeFermat

/-! ## General helpers -/

def sumList (l : List Nat) : Nat := l.foldl (· + ·) 0

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Insertion sort; `lt` is a strict less-than relation. -/
def insertBy {α : Type} (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt y x then y :: insertBy lt x ys else x :: y :: ys

def sortBy {α : Type} (lt : α → α → Bool) (l : List α) : List α :=
  l.foldr (insertBy lt) []

def sortNat (l : List Nat) : List Nat :=
  sortBy (fun a b => decide (a < b)) l

/-- Strict lexicographic order: mirrors Python's tuple comparison. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: xs, b :: ys => if a < b then true else if a == b then lexLt xs ys else false

/-- Association list standing in for Python's `Counter`/dict: add v to the count of key k. -/
def addCount {α : Type} [BEq α] (l : List (α × Nat)) (k : α) (v : Nat) : List (α × Nat) :=
  match l with
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k' == k then (k', v' + v) :: rest else (k', v') :: addCount rest k v

def getCount (c : List (Nat × Nat)) (b : Nat) : Nat :=
  match c.find? (fun p => p.1 == b) with
  | some p => p.2
  | none => 0

def counts (alpha : List Nat) : List (Nat × Nat) :=
  alpha.foldl (fun acc a => addCount acc a 1) []

def showTuple (l : List Nat) : String :=
  "(" ++ ", ".intercalate (l.map toString) ++ ")"

def padLeft (s : String) (w : Nat) : String :=
  String.join (List.replicate (w - s.length) " ") ++ s

/-! ## Core algorithms -/

/-- (Z/m)^* : the numbers in 1..m-1 that are coprime to m. -/
def units (m : Nat) : List Nat :=
  (List.range' 1 (m - 1)).filter fun t => Nat.gcd t m == 1

/-- Number of distinct permutations of a sorted alpha (number of ordered alphas). -/
def multiplicity (alpha : List Nat) : Nat :=
  (counts alpha).foldl (fun r p => r / fact p.2) (fact alpha.length)

/-- `combinations_with_replacement(range(lo, hi+1), k)`: non-decreasing lists of length k. -/
def combsWithRepl (hi : Nat) : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | k + 1, lo =>
    (List.range' lo (hi + 1 - lo)).flatMap fun a =>
      (combsWithRepl hi k a).map (a :: ·)

/-- All multisets with sum = 0 (mod m) and a_i in 1..m-1 (as sorted lists). -/
def multisets (m n : Nat) : List (List Nat) :=
  (combsWithRepl (m - 1) (n + 2) 1).filter fun alpha => sumList alpha % m == 0

/-- Shioda's criterion: sum_i (t*a_i mod m) = (n/2+1)*m for every t in (Z/m)^*. -/
def isHodge (alpha : List Nat) (m n : Nat) (U : List Nat) : Bool :=
  let target := (n / 2 + 1) * m
  U.all fun t => sumList (alpha.map fun a => (t * a) % m) == target

/-- Does a perfect matching into pairs {a, m-a} exist? -/
def isDecomposable (alpha : List Nat) (m : Nat) : Bool :=
  let c := counts alpha
  c.all fun p =>
    let a := p.1
    let k := p.2
    let b := m - a
    if a == b then k % 2 == 0 else getCount c b == k

/-- Lexicographically smallest representative of the Galois orbit. -/
def galoisOrbitRep (alpha : List Nat) (m : Nat) (U : List Nat) : List Nat :=
  let cands := U.map fun t => sortNat (alpha.map fun a => (t * a) % m)
  match cands with
  | [] => alpha
  | c :: cs => cs.foldl (fun best x => if lexLt x best then x else best) c

/-- `Except String` in place of Python's `ValueError`. -/
def validate (m n : Nat) : Except String Unit :=
  if m < 2 then throw "m >= 2 required"
  else if n % 2 ≠ 0 ∨ n < 2 then throw "n must be even and >= 2"
  else pure ()

/-- Primitive Hodge numbers h^{p,q}_prim with q = <alpha> - 1, sorted by the key (p,q). -/
def hodgeNumbers (m n : Nat) : Except String (List ((Nat × Nat) × Nat)) := do
  validate m n
  let mut h : List ((Nat × Nat) × Nat) := []
  for alpha in multisets m n do
    let q := sumList alpha / m - 1
    h := addCount h (n - q, q) (multiplicity alpha)
  return sortBy
    (fun (x y : (Nat × Nat) × Nat) => decide (x.1.1 < y.1.1 ∨ (x.1.1 = y.1.1 ∧ x.1.2 < y.1.2))) h

structure Analysis where
  prim   : Nat
  hodge  : Nat
  decomp : Nat
  /-- orbit representative -> number of ordered alphas in that orbit family -/
  bad    : Std.HashMap (List Nat) Nat

/-- (primitive dimension, |Hodge|, |decomposable|, dictionary of indecomposable orbits) -/
def analyse (m n : Nat) : Except String Analysis := do
  validate m n
  let U := units m
  let mut prim := 0
  let mut hodge := 0
  let mut decomp := 0
  let mut bad : Std.HashMap (List Nat) Nat := {}
  for alpha in multisets m n do
    let mult := multiplicity alpha
    prim := prim + mult
    if !isHodge alpha m n U then continue
    hodge := hodge + mult
    if isDecomposable alpha m then
      decomp := decomp + mult
    else
      let rep := galoisOrbitRep alpha m U
      bad := bad.insert rep (bad.getD rep 0 + mult)
  return { prim := prim, hodge := hodge, decomp := decomp, bad := bad }

/-! ## Commands -/

def cmdHodge (m n : Nat) : IO Unit := do
  let h ← IO.ofExcept (hodgeNumbers m n)
  IO.println s!"X_{m}^{n}: primitive Hodge numbers"
  let mut tot := 0
  for ((p, q), v) in h do
    IO.println s!"  h^({p},{q})_prim = {v}"
    tot := tot + v
  IO.println s!"  total primitive dimension = {tot}"

def cmdList (m n limit : Nat) : IO Unit := do
  let r ← IO.ofExcept (analyse m n)
  IO.println s!"X_{m}^{n}: primitive dim={r.prim}, Hodge classes={r.hodge}, decomposable (linear subspace)={r.decomp}, indecomposable={r.hodge - r.decomp}"
  if r.bad.isEmpty then
    IO.println "No indecomposable Hodge classes: all Hodge classes are generated by linear subspaces."
    return
  let items := sortBy (fun (a b : List Nat × Nat) => lexLt a.1 b.1) r.bad.toList
  IO.println s!"Indecomposable Galois-orbit representatives ({items.length} total, first {limit}):"
  let mut i := 0
  for (rep, cnt) in items do
    if i >= limit then
      IO.println "  ..."
      break
    IO.println s!"  alpha={showTuple rep}  (this orbit family: {cnt} ordered alphas)"
    i := i + 1

def cmdTable (mlo mhi n : Nat) : IO Unit := do
  IO.println s!"n={n}  (X_m^n: x_0^m+...+x_{n+1}^m=0)"
  let hdr := padLeft "m" 3 ++ " " ++ padLeft "prim" 9 ++ " " ++ padLeft "Hodge" 7 ++ " "
    ++ padLeft "decomp." 7 ++ " " ++ padLeft "indecomp." 9
  IO.println (if n == 2 then hdr ++ " " ++ padLeft "rho" 6 else hdr)
  for m in List.range' mlo (mhi + 1 - mlo) do
    let r ← IO.ofExcept (analyse m n)
    let row := padLeft (toString m) 3 ++ " " ++ padLeft (toString r.prim) 9 ++ " "
      ++ padLeft (toString r.hodge) 7 ++ " " ++ padLeft (toString r.decomp) 7 ++ " "
      ++ padLeft (toString (r.hodge - r.decomp)) 9
    IO.println (if n == 2 then row ++ " " ++ padLeft (toString (r.hodge + 1)) 6 else row)

/-! ## Self-test -/

def isErr {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def expect (cond : Bool) (msg : String) : IO Unit :=
  if !cond then throw (IO.userError s!"selftest FAILED: {msg}") else pure ()

def selftest : IO Unit := do
  -- Invalid parameters must be rejected explicitly.
  for (m, n) in [(1, 2), (0, 2)] do
    expect (isErr (hodgeNumbers m n)) s!"hodgeNumbers did not reject m={m}"
    expect (isErr (analyse m n)) s!"analyse did not reject m={m}"
  for (m, n) in [(4, 1), (4, 0), (4, 3)] do
    expect (isErr (hodgeNumbers m n)) s!"hodgeNumbers did not reject n={n}"
    expect (isErr (analyse m n)) s!"analyse did not reject n={n}"
  -- K3 (Fermat quartic surface): h^{2,0}=1, h^{1,1}_prim=19, h^{0,2}=1
  let h ← IO.ofExcept (hodgeNumbers 4 2)
  expect (h == [((0, 2), 1), ((1, 1), 19), ((2, 0), 1)]) "K3 Hodge numbers"
  -- Known Picard numbers (rho = Hodge + 1, n = 2)
  for (m, rho) in [(3, 7), (4, 20), (5, 37), (7, 91)] do
    let r ← IO.ofExcept (analyse m 2)
    expect (r.hodge + 1 == rho) s!"Picard number for m={m}: {r.hodge + 1} != {rho}"
  -- Decomposable => Hodge (consistency)
  for m in List.range' 2 11 do
    for n in [2, 4] do
      let U := units m
      for a in multisets m n do
        if isDecomposable a m then
          expect (isHodge a m n U) s!"decomposable but not Hodge: m={m} n={n} alpha={showTuple a}"
  -- m prime => no indecomposable classes (Pham/Ran/Shioda)
  for m in [3, 5, 7, 11] do
    let r ← IO.ofExcept (analyse m 2)
    expect (r.hodge == r.decomp) s!"m={m} is prime but an indecomposable class exists"
  IO.println "selftest OK"

/-! ## Command line -/

def usage : String :=
  "Usage:\n  selftest\n  hodge m n\n  list m n [--limit L]\n  table mlo mhi [--n N]"

def parseNat (s : String) : IO Nat :=
  match s.toNat? with
  | some v => pure v
  | none => throw (IO.userError s!"invalid integer: {s}")

/-- Looks for an `--option value` pair; returns the default if absent. -/
def findOpt (args : List String) (name : String) (dflt : Nat) : IO Nat :=
  match args with
  | [] => pure dflt
  | a :: rest =>
    if a == name then
      match rest with
      | v :: _ => parseNat v
      | [] => throw (IO.userError s!"missing value for {name}")
    else findOpt rest name dflt

end HodgeFermat

open HodgeFermat in
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["selftest"] => selftest
    | "hodge" :: m :: n :: _ =>
      let mv ← parseNat m
      let nv ← parseNat n
      cmdHodge mv nv
    | "list" :: m :: n :: rest =>
      let mv ← parseNat m
      let nv ← parseNat n
      let lim ← findOpt rest "--limit" 40
      cmdList mv nv lim
    | "table" :: lo :: hi :: rest =>
      let lov ← parseNat lo
      let hiv ← parseNat hi
      let nv ← findOpt rest "--n" 2
      cmdTable lov hiv nv
    | _ =>
      IO.eprintln usage
      return 2
    return 0
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1
