import CubeChains.Machinery.Braid.PermWord

/-!
# Testing/Pi1/Presentation — π₁ of the nerve of a finite poset

`FreeGroupoid C` is the localization of `C`, so for a thin acyclic `C` its vertex group is
`π₁(|N C|)` and an arrow *is* a pair `a ≤ b`.  Tietze-reducing "generators = arrows, relations =
composable pairs" against a spanning forest of the Hasse graph leaves: generators = the non-tree
Hasse edges, relations = the strict chains `a < b < c`.  Each arrow carries a signed Artin word,
so each generator also carries the braid word of its loop.  Input and output are `ℕ`-indexed
`Array` data, so nothing here knows how the poset was produced.

Not built by `lake build CubeChains`.
-/

namespace CubeChains

/-! ## Bitmasks

Up-sets are `Nat` bitmasks: the union in the Hasse computation is then one GMP word-op per
element instead of an `Array` merge. -/

/-- Set difference of bitmasks (`Nat` has no complement). -/
@[inline] def maskDiff (m k : ℕ) : ℕ := m ^^^ (m &&& k)

/-- The set a bitmask denotes, increasing — `O(size)`. -/
def maskList (size m : ℕ) : List ℕ := (List.range size).filter (m.testBit ·)

/-! ## Input -/

/-- A finite poset as index data: `le[a][b]` is the arrow `a ⟶ b`, carrying a signed Artin word. -/
structure PosetData where
  size : ℕ
  le : Array (Array Bool)
  label : ℕ → ℕ → List ℤ

namespace PosetData

/-- Total lookup: out-of-range indices are incomparable. -/
@[inline] def leq (d : PosetData) (a b : ℕ) : Bool := (d.le.getD a #[]).getD b false

@[inline] def lt (d : PosetData) (a b : ℕ) : Bool := a != b && d.leq a b

/-- Strict up-sets as bitmasks — `O(n²)`. -/
def upMask (d : PosetData) : Array ℕ :=
  (List.range d.size).foldl
    (fun M a => M.push
      ((List.range d.size).foldl (fun m b => if d.lt a b then m ||| (1 <<< b) else m) 0)) #[]

/-- Hasse successors: an up-set minus everything reachable through a strict intermediate —
`O(n)` mask-ors per node. -/
def coverMask (d : PosetData) (up : Array ℕ) : Array ℕ :=
  up.map fun m => maskDiff m ((maskList d.size m).foldl (fun s c => s ||| up.getD c 0) 0)

/-- Nodes by decreasing down-set size: a reverse linear extension (bucketed, `O(n²)`), the order in
which `canonTable` can fill each entry from already-filled ones. -/
def revLinExt (d : PosetData) : List ℕ :=
  let buckets := (List.range d.size).foldl
    (fun B a => B.modify ((List.range d.size).countP (d.leq · a)) (a :: ·))
    (Array.replicate (d.size + 1) ([] : List ℕ))
  (List.range (d.size + 1)).foldl (fun acc k => buckets.getD k [] ++ acc) []

end PosetData

/-- Hasse edges as source-ordered pairs, from the successor lists. -/
def coverPairs (size : ℕ) (coverSucc : Array (List ℕ)) : Array (ℕ × ℕ) :=
  (List.range size).foldl (fun A a => (coverSucc.getD a []).foldl (fun A b => A.push (a, b)) A) #[]

/-- The Hasse diagram — the standalone entry point; `present` shares its own copy. -/
def PosetData.covers (d : PosetData) : Array (ℕ × ℕ) :=
  coverPairs d.size ((d.coverMask d.upMask).map (maskList d.size))

/-- Travel `w`, then `v`.  `Conc (f ≫ g) = Conc g * Conc f` while `wordZToBraid` turns `++` into
`*`, so the *later* arrow's word goes on the left. -/
@[inline] def thenW (w v : List ℤ) : List ℤ := v ++ w

/-! ## Spanning forest of the undirected Hasse graph -/

/-- BFS state: each node's component root and the braid word of its tree path from that root,
plus which Hasse edges (by index) are tree edges. -/
structure Forest where
  root : Array ℕ
  word : Array (List ℤ)
  tree : Array Bool
  seen : Array Bool
  frontier : List ℕ

/-- One BFS level, over adjacency `(neighbour, edge index, step word)`. -/
def Forest.expand (adj : Array (Array (ℕ × ℕ × List ℤ))) (F : Forest) : Forest :=
  F.frontier.foldl
    (fun F v => (adj.getD v #[]).foldl
      (fun F e =>
        if F.seen.getD e.1 false then F
        else { F with
                 seen := F.seen.set! e.1 true
                 root := F.root.set! e.1 (F.root.getD v v)
                 word := F.word.set! e.1 (thenW (F.word.getD v []) e.2.2)
                 tree := F.tree.set! e.2.1 true
                 frontier := e.1 :: F.frontier }) F)
    { F with frontier := [] }

/-- Grow one component to exhaustion; the fuel bounds the BFS depth. -/
def Forest.grow (adj : Array (Array (ℕ × ℕ × List ℤ))) : ℕ → Forest → Forest
  | 0, F => F
  | k + 1, F => if F.frontier.isEmpty then F else Forest.grow adj k (F.expand adj)

/-- The spanning forest, seeded at the least unvisited node — `O(n + E)` total. -/
def spanningForest (d : PosetData) (ncov : ℕ) (adj : Array (Array (ℕ × ℕ × List ℤ))) : Forest :=
  (List.range d.size).foldl
    (fun F v =>
      if F.seen.getD v false then F
      else Forest.grow adj d.size
        { F with seen := F.seen.set! v true, root := F.root.set! v v, frontier := [v] })
    { root := Array.replicate d.size 0, word := Array.replicate d.size [],
      tree := Array.replicate ncov false, seen := Array.replicate d.size false, frontier := [] }

/-! ## Words in the cover generators -/

/-- Every comparable pair's word in the cover generators, at index `a * size + b`; a non-cover
factors through the least Hasse successor of `a` still below `b`. -/
def canonTable (d : PosetData) (ncov : ℕ) (covIdx : Array ℕ) (coverSucc upStrict : Array (List ℕ))
    (genWord : Array (List ℤ)) : Array (List ℤ) :=
  d.revLinExt.foldl
    (fun T a => (upStrict.getD a []).foldl
      (fun T b =>
        let ci := covIdx.getD (a * d.size + b) ncov
        T.set! (a * d.size + b) <|
          if ci < ncov then genWord.getD ci []
          else match (coverSucc.getD a []).find? (d.leq · b) with
            | none => []
            | some m =>
              thenW (genWord.getD (covIdx.getD (a * d.size + m) ncov) [])
                (T.getD (m * d.size + b) [])) T)
    (Array.replicate (d.size * d.size) ([] : List ℤ))


/-- Cancel adjacent inverse letters: the trivially-true relators reduce to `[]`. -/
def freeReduce (w : List ℤ) : List ℤ :=
  (w.foldl (fun st x =>
    match st with
    | y :: rest => if x != 0 && y + x == 0 then rest else x :: y :: rest
    | [] => [x]) []).reverse

/-- Distinct words, in order of first appearance. -/
def dedupWords (ws : Array (List ℤ)) : Array (List ℤ) :=
  (ws.foldl (fun (p : Std.HashSet (List ℤ) × Array (List ℤ)) w =>
    if p.1.contains w then p else (p.1.insert w, p.2.push w)) (∅, #[])).2

/-! ## Output -/

/-- A finite presentation of `π₁`: `words` is the braid word of each generator's loop, `rels` are
words in the signed 1-based generator indices.  Across `components > 1` it is their free product,
not any one vertex group. -/
structure Presentation where
  nGens : ℕ
  gens : Array (ℕ × ℕ)
  words : Array (List ℤ)
  rels : Array (List ℤ)
  components : ℕ

/-- **The presentation**, each phase computed once and shared.  With `n` nodes, `E` Hasse edges and
`U = Σₐ |up a|`: masks `O(n²)`, Hasse `O(U)` word-ops, forest `O(n+E)`, `canonTable` `O(U)` lookups,
relations `O(Σ_{a<b} |up b|)` — no phase revisits an earlier one. -/
def present (d : PosetData) : Presentation :=
  let n := d.size
  let up := d.upMask
  let cm := d.coverMask up
  let upStrict : Array (List ℕ) := up.map (maskList n)
  let coverSucc : Array (List ℕ) := cm.map (maskList n)
  let cov : Array (ℕ × ℕ) := coverPairs n coverSucc
  let ncov := cov.size
  let covIdx : Array ℕ :=
    (List.range ncov).foldl
      (fun T i => let e := cov.getD i (0, 0); T.set! (e.1 * n + e.2) i)
      (Array.replicate (n * n) ncov)
  let adj : Array (Array (ℕ × ℕ × List ℤ)) :=
    (List.range ncov).foldl
      (fun A i =>
        let e := cov.getD i (0, 0)
        let w := d.label e.1 e.2
        (A.modify e.1 (·.push (e.2, i, w))).modify e.2 (·.push (e.1, i, invWordZ w)))
      (Array.replicate n #[])
  let F := spanningForest d ncov adj
  let gens : Array (ℕ × ℕ) :=
    (List.range ncov).foldl
      (fun G i => if F.tree.getD i false then G else G.push (cov.getD i (0, 0))) #[]
  let genWord : Array (List ℤ) :=
    ((List.range ncov).foldl
      (fun (p : Array (List ℤ) × ℕ) i =>
        if F.tree.getD i false then (p.1.push [], p.2)
        else (p.1.push [(p.2 : ℤ) + 1], p.2 + 1)) (#[], 0)).1
  let canon := canonTable d ncov covIdx coverSucc upStrict genWord
  let rels : Array (List ℤ) :=
    (List.range n).foldl
      (fun R a => (upStrict.getD a []).foldl
        (fun R b => (upStrict.getD b []).foldl
          (fun R c =>
            let r := freeReduce (thenW (thenW (canon.getD (a * n + b) [])
              (canon.getD (b * n + c) [])) (invWordZ (canon.getD (a * n + c) [])))
            if r.isEmpty then R else R.push r) R) R) #[]
  { nGens := gens.size
    gens := gens
    words := gens.map fun e =>
      thenW (thenW (F.word.getD e.1 []) (d.label e.1 e.2)) (invWordZ (F.word.getD e.2 []))
    rels := dedupWords rels
    components := (List.range n).countP fun v => F.root.getD v v == v }

/-! ## Tietze simplification

A relator in which some generator occurs exactly once solves for that generator, so substituting
it away costs one generator and one relator and leaves the group untouched.  Iterating to a fixed
point turns the Hasse-edge presentation into something a reader can recognise.

A surviving generator names the same loop it always did, so its braid word is carried, not
rewritten: `words` is the image of a homomorphism, and elimination only ever deletes.  Relators are
kept cyclically reduced and deduplicated up to conjugacy and inversion, since that is exactly the
ambiguity in a relator. -/

/-- Cancel matching ends after free reduction — a relator only matters up to conjugacy. -/
def cycTrim : ℕ → List ℤ → List ℤ
  | 0, w => w
  | k + 1, w =>
    match w with
    | [] => []
    | a :: t =>
      match t.getLast? with
      | none => w
      | some b => if a + b == 0 then cycTrim k t.dropLast else w

/-- Free- then cyclically-reduce. -/
def cycReduce (w : List ℤ) : List ℤ := let v := freeReduce w; cycTrim v.length v

def lexLt : List ℤ → List ℤ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: u, b :: v => if a < b then true else if b < a then false else lexLt u v

/-- Least rotation of `w` or of `w⁻¹` — the canonical form under the conjugacy/inversion ambiguity,
so that `dedupWords` sees genuinely equal relators as equal. -/
def cycCanon (w : List ℤ) : List ℤ :=
  let v := cycReduce w
  if v.isEmpty then [] else
    let iv := invWordZ v
    let rots := (List.range v.length).map (fun k => v.drop k ++ v.take k)
      ++ (List.range v.length).map (fun k => iv.drop k ++ iv.take k)
    rots.foldl (fun best r => if lexLt r best then r else best) v

/-- The generator (as a `1`-based label) occurring exactly once in `w`. -/
def uniqueGen (w : List ℤ) : Option ℕ :=
  (w.find? fun x => w.countP (fun y => y.natAbs == x.natAbs) == 1).map Int.natAbs

/-- Solve `g^ε · t = 1` for `g`, cycling the relator so the sole occurrence leads. -/
def solveFor (g : ℕ) (r : List ℤ) : Option (List ℤ) :=
  (r.findIdx? fun x => x.natAbs == g).map fun i =>
    let t := r.drop (i + 1) ++ r.take i
    if 0 < r.getD i 0 then invWordZ t else t

/-- Replace every `±g` by `s`, resp. `s⁻¹`. -/
def substGen (g : ℕ) (s : List ℤ) (w : List ℤ) : List ℤ :=
  w.foldr (fun x acc =>
    (if x.natAbs == g then (if 0 < x then s else invWordZ s) else [x]) ++ acc) []

/-- Relators over the original generator labels; `alive` records which generators survive. -/
structure Tietze where
  rels : Array (List ℤ)
  alive : Array Bool

def Tietze.total (T : Tietze) : ℕ := T.rels.foldl (fun s w => s + w.length) 0

/-- Delete `g` and its defining relator, substituting `s` everywhere else. -/
def Tietze.elim (T : Tietze) (i g : ℕ) (s : List ℤ) : Tietze :=
  { rels := (T.rels.set! i []).map fun w =>
      if w.any (fun x => x.natAbs == g) then cycReduce (substGen g s w) else w
    alive := T.alive.set! (g - 1) false }

/-- Live relator indices by increasing length: the substituted word is shortest there. -/
def Tietze.byLength (T : Tietze) : List ℕ :=
  let maxL := T.rels.foldl (fun m w => max m w.length) 0
  let B := (List.range T.rels.size).foldl
    (fun B i => let w := T.rels.getD i []
                if w.isEmpty then B else B.modify w.length (i :: ·))
    (Array.replicate (maxL + 1) ([] : List ℕ))
  (List.range (maxL + 1)).foldr (fun k acc => B.getD k [] ++ acc) []

/-- One greedy sweep in increasing relator length; an elimination that would push the total word
length past `cap` is skipped rather than taken. -/
def Tietze.pass (cap : ℕ) (T : Tietze) : Tietze × Bool :=
  T.byLength.foldl
    (fun p i =>
      let T := p.1
      let w := T.rels.getD i []
      match uniqueGen w with
      | none => p
      | some g =>
        match solveFor g w with
        | none => p
        | some s => let T' := T.elim i g s; if T'.total > cap then p else (T', true))
    (T, false)

/-- Sweep to a fixed point; each successful sweep kills a generator, so `nGens` fuel suffices. -/
def Tietze.run (cap : ℕ) : ℕ → Tietze → Tietze
  | 0, T => T
  | k + 1, T => let (T', ch) := T.pass cap; if ch then Tietze.run cap k T' else T'

/-- Tietze-reduce, carrying each surviving generator's Hasse edge and braid word. -/
def Presentation.simplify (P : Presentation) : Presentation :=
  let start := dedupWords ((P.rels.map cycCanon).filter fun w => !w.isEmpty)
  let T := Tietze.run (4 * (Tietze.total ⟨start, #[]⟩) + 4 * P.nGens + 1024) (P.nGens + 1)
    ⟨start, Array.replicate P.nGens true⟩
  let keep := (List.range P.nGens).filter fun g => T.alive.getD g false
  let idx : Array ℕ :=
    keep.zipIdx.foldl (fun A p => A.set! (p.1 + 1) (p.2 + 1)) (Array.replicate (P.nGens + 1) 0)
  { nGens := keep.length
    gens := keep.toArray.map fun g => P.gens.getD g (0, 0)
    words := keep.toArray.map fun g => P.words.getD g []
    rels := dedupWords (((T.rels.map fun w =>
      cycCanon (w.map fun x => let j := (idx.getD x.natAbs 0 : ℤ); if 0 < x then j else -j)).filter
        fun w => !w.isEmpty))
    components := P.components }

/-! ## Rendering -/

/-- A signed word over a GAP generator-list variable. -/
def gapWord (v : String) (w : List ℤ) : String :=
  if w.isEmpty then "One(F)"
  else String.intercalate "*" (w.map fun x => if x < 0 then s!"{v}[{-x}]^-1" else s!"{v}[{x}]")

/-- The presented group, as a GAP script. -/
def Presentation.gap (P : Presentation) : String :=
  s!"F := FreeGroup({P.nGens});;\nf := GeneratorsOfGroup(F);;\nrels := [\n  "
    ++ String.intercalate ",\n  " (P.rels.toList.map (gapWord "f"))
    ++ "\n];;\nG := F/rels;;\n"

/-- Each generator's Hasse edge and the braid word of its loop. -/
def Presentation.braids (P : Presentation) : String :=
  String.intercalate "\n" ((List.range P.nGens).map fun i =>
    s!"g{i + 1} : {(P.gens.getD i (0, 0)).1} -> {(P.gens.getD i (0, 0)).2}  =  "
      ++ gapWord "s" (P.words.getD i []))

instance : ToString Presentation where
  toString P :=
    s!"generators={P.nGens} relations={P.rels.size} components={P.components}\n"
      ++ P.braids ++ "\n" ++ P.gap

/-! ## Abelianization

`H₁` is the cokernel of the exponent-sum matrix (rows = relators, columns = generators); mathlib's
Smith normal form is `noncomputable`, so the elimination is bespoke, and in two stages because a
dense `2796 × 673` is out of reach for the interpreter.  Stage one is sparse: a row echelon whose
pivot coefficients are all `±1`.  Such an echelon spans a *direct summand* of `ℤⁿ`, so when nothing
is left over the quotient is free of rank `n − #pivots` and no Smith normal form is needed.  Stage
two runs the dense algorithm on the rows that admitted no unit pivot. -/

/-- A sparse row, strictly increasing in column, no zero coefficients. -/
abbrev SVec := List (ℕ × ℤ)

/-- `u + k • v`, merging supports — `O(|u| + |v|)`. -/
def svAxpy (k : ℤ) (u v : SVec) : SVec :=
  match u, v with
  | u, [] => u
  | [], v => v.map fun p => (p.1, k * p.2)
  | (i, a) :: u', (j, b) :: v' =>
    if i < j then (i, a) :: svAxpy k u' ((j, b) :: v')
    else if j < i then (j, k * b) :: svAxpy k ((i, a) :: u') v'
    else
      let c := a + k * b
      if c == 0 then svAxpy k u' v' else (i, c) :: svAxpy k u' v'
  termination_by u.length + v.length

/-- The exponent-sum vector of a relator: the signed count of each generator. -/
def relRow (nGens : ℕ) (w : List ℤ) : SVec :=
  let cnt := w.foldl
    (fun A x => let j := x.natAbs - 1; if j < nGens then A.modify j (· + x.sign) else A)
    (Array.replicate nGens (0 : ℤ))
  (List.range nGens).foldr
    (fun j acc => if cnt.getD j 0 == 0 then acc else (j, cnt.getD j 0) :: acc) []

/-! ### Stage one: the unimodular echelon -/

/-- Clear the leading column against a unit pivot until the leading column has none; the leading
column strictly increases, so `nGens + 1` fuel always suffices. -/
def svReduce (piv : Array SVec) : ℕ → SVec → SVec
  | 0, r => r
  | k + 1, r =>
    match r with
    | [] => []
    | (c, a) :: _ =>
      match piv.getD c [] with
      | [] => r
      | (_, b) :: _ => svReduce piv k (svAxpy (-(a / b)) r (piv.getD c []))

/-- Echelon pivots indexed by their leading column, plus the rows that had no unit pivot. -/
structure Echelon where
  piv : Array SVec
  left : Array SVec
  count : ℕ

/-- Install a reduced row as a pivot when its leading coefficient is a unit, else defer it. -/
def Echelon.absorb (nGens : ℕ) (E : Echelon) (r0 : SVec) : Echelon :=
  match svReduce E.piv (nGens + 1) r0 with
  | [] => E
  | (c, a) :: t =>
    if a.natAbs == 1 then { E with piv := E.piv.set! c ((c, a) :: t), count := E.count + 1 }
    else { E with left := E.left.push ((c, a) :: t) }

/-- Re-absorb the deferred rows until no new pivot appears; `count` bounds the passes. -/
def echelonize (nGens : ℕ) : ℕ → Echelon → Echelon
  | 0, E => E
  | k + 1, E =>
    let E' := (E.left).foldl (Echelon.absorb nGens) { E with left := #[] }
    if E'.count == E.count then E' else echelonize nGens k E'

/-- Project a leftover row along the pivot lattice: pivot columns ascend and each pivot's support
lies to its right, so one pass zeroes every pivot coordinate for good. -/
def clearPivots (piv : Array SVec) (cols : List ℕ) (r : SVec) : SVec :=
  cols.foldl (fun r c =>
    match piv.getD c [] with
    | [] => r
    | p => match r.find? (fun q => q.1 == c) with
      | none => r
      | some (_, a) => svAxpy (-(a / (p.head?.map Prod.snd).getD 1)) r p) r

/-! ### Stage two: dense Smith normal form -/

/-- Entry `(i, j)`, total. -/
@[inline] def mGet (M : Array (Array ℤ)) (i j : ℕ) : ℤ := (M.getD i #[]).getD j 0

/-- `row i += k • row t`. -/
def rowAxpy (M : Array (Array ℤ)) (ncols i : ℕ) (k : ℤ) (t : ℕ) : Array (Array ℤ) :=
  let rt := M.getD t #[]
  M.modify i fun ri => ((List.range ncols).map fun j => ri.getD j 0 + k * rt.getD j 0).toArray

/-- `col j += k • col t`. -/
def colAxpy (M : Array (Array ℤ)) (j : ℕ) (k : ℤ) (t : ℕ) : Array (Array ℤ) :=
  M.map fun r => r.modify j (· + k * r.getD t 0)

def swapRows (M : Array (Array ℤ)) (i t : ℕ) : Array (Array ℤ) :=
  if i == t then M else (M.set! i (M.getD t #[])).set! t (M.getD i #[])

def swapCols (M : Array (Array ℤ)) (j t : ℕ) : Array (Array ℤ) :=
  if j == t then M else
    M.map fun r => let a := r.getD j 0; (r.modify j fun _ => r.getD t 0).modify t fun _ => a

/-- The nonzero entry of least absolute value in the trailing submatrix — pivoting on it is what
makes the remainders shrink. -/
def pivotAt (nrows ncols t : ℕ) (M : Array (Array ℤ)) : Option (ℕ × ℕ) :=
  (List.range nrows).foldl (fun best i =>
    if i < t then best else
    (List.range ncols).foldl (fun best j =>
      if j < t then best else
      let v := mGet M i j
      if v == 0 then best
      else match best with
        | none => some (i, j)
        | some (bi, bj) => if v.natAbs < (mGet M bi bj).natAbs then some (i, j) else best)
      best) none

/-- Diagonalize: clear the pivot's row and column, then force divisibility, restarting at `t`
whenever a remainder survives.  Every restart strictly drops `|M t t|`, so the fuel is slack. -/
def snfRun (nrows ncols : ℕ) : ℕ → ℕ → Array (Array ℤ) → Array (Array ℤ)
  | 0, _, M => M
  | fuel + 1, t, M =>
    if t ≥ nrows || t ≥ ncols then M else
    match pivotAt nrows ncols t M with
    | none => M
    | some (pi, pj) =>
      let M := swapCols (swapRows M pi t) pj t
      let d := mGet M t t
      let M := (List.range nrows).foldl
        (fun M i => if i ≤ t then M else
          let q := mGet M i t / d
          if q == 0 then M else rowAxpy M ncols i (-q) t) M
      if (List.range nrows).any (fun i => t < i && mGet M i t != 0) then
        snfRun nrows ncols fuel t M
      else
        let M := (List.range ncols).foldl
          (fun M j => if j ≤ t then M else
            let q := mGet M t j / d
            if q == 0 then M else colAxpy M j (-q) t) M
        if (List.range ncols).any (fun j => t < j && mGet M t j != 0) then
          snfRun nrows ncols fuel t M
        else
          match (List.range nrows).find? (fun i =>
              t < i && (List.range ncols).any fun j => t < j && mGet M i j % d != 0) with
          | some i => snfRun nrows ncols fuel t (rowAxpy M ncols t 1 i)
          | none => snfRun nrows ncols fuel (t + 1) M

/-- The nonzero Smith diagonal, as positive integers. -/
def snfDiag (nrows ncols : ℕ) (M : Array (Array ℤ)) : List ℕ :=
  let D := snfRun nrows ncols ((nrows + ncols) * 256 + 256) 0 M
  ((List.range (min nrows ncols)).map fun t => (mGet D t t).natAbs).filter (· != 0)

/-! ### `H₁` -/

/-- `H₁` of the presented group: `(free rank, torsion invariant factors)`. -/
def Presentation.homology (P : Presentation) : ℕ × List ℕ :=
  let n := P.nGens
  let E := echelonize n (n + 1)
    (P.rels.foldl (fun E w => E.absorb n (relRow n w)) ⟨Array.replicate n [], #[], 0⟩)
  let free := n - E.count
  if E.left.isEmpty then (free, [])
  else
    let pivCols := (List.range n).filter fun c => !(E.piv.getD c []).isEmpty
    let freeCols := (List.range n).filter fun c => (E.piv.getD c []).isEmpty
    let idx : Array ℕ := (freeCols.zipIdx.foldl (fun A p => A.set! p.1 p.2) (Array.replicate n 0))
    let m := freeCols.length
    let dense : Array (Array ℤ) := E.left.map fun r =>
      (clearPivots E.piv pivCols r).foldl
        (fun row q => row.modify (idx.getD q.1 0) fun _ => q.2) (Array.replicate m (0 : ℤ))
    let d := snfDiag E.left.size m dense
    (m - d.length, d.filter (· != 1))

/-! ## Sanity

`{0,1} < {2,3}`: four Hasse edges, no strict chain of length two, so the nerve is a 4-cycle and
`π₁ = ℤ` — one generator, no relations, `H₁ = ℤ`.

```
#eval toString (present squarePoset)        -- generators=1 relations=0 components=1
#eval (present squarePoset).homology        -- (1, [])
```
-/

/-- The 4-cycle poset, with each arrow labelled by a distinct Artin letter. -/
def squarePoset : PosetData where
  size := 4
  le := #[#[true, false, true, true], #[false, true, true, true],
          #[false, false, true, false], #[false, false, false, true]]
  label := fun a b => [((a * 4 + b : ℕ) : ℤ) + 1]

end CubeChains
