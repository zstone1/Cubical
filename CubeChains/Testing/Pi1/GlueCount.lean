import CubeChains.Testing.Pi1.Merges

/-!
# Testing/Pi1/GlueCount — the size of the glue presentation of `Ch(Hbp □ⁿ)[W⁻¹]`

The copies, 0-cells, 1-cells and overlap identifications of `glueOn (wedgeHoms (Hbp □ⁿ))
runLabels (chGlueV '' MaximalChains (Hbp □ⁿ))`, counted in the
model of `Testing/Pi1/Merges`: a chain is a permutation word cut into nonempty blocks, a
`Ch Zbp` morphism is an `allWedges` datum, `W` is `isMono`, and `crossPerm` is `flatWedge`.

Not built by `lake build CubeChains`.
-/

namespace CubeChains

namespace GlueCount

/-- A chain of `Hbp □ⁿ`: one ordered block of directions per bead. -/
abbrev Chart := List (List ℕ)

/-- A morphism of `Ch Zbp`: one group of increasing faces per target bead. -/
abbrev Wedge := List (List (List ℕ))

/-- The bead dimensions of a chart. -/
def dimsOf (X : Chart) : List ℕ := X.map List.length

/-- Insert `x` in every position. -/
def insertAll (x : ℕ) : List ℕ → List (List ℕ)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAll x ys).map (y :: ·)

/-- Every rearrangement of a list. -/
def permsOf : List ℕ → List (List ℕ)
  | [] => [[]]
  | x :: xs => (permsOf xs).flatMap (insertAll x)

/-- The objects of `Ch (Hbp □ⁿ)`: a permutation word cut into nonempty blocks. -/
def charts (n : ℕ) : List Chart :=
  (permsOf (List.range n)).flatMap fun w => (comps n).map fun c => regroup c w

/-- The chain a coarse chart restricts to along a wedge map — `wedgeHoms`' action. -/
def pullChart (Y : Chart) (w : Wedge) : Chart :=
  (Y.zip w).flatMap fun bg => bg.2.map fun c => c.map fun x => bg.1.getD x 0

/-- Inversions of a one-line word — `permLen` of `flatWedge`. -/
def invCount : List ℕ → ℕ
  | [] => 0
  | x :: xs => (xs.countP fun y => decide (y < x)) + invCount xs

/-- Duplicate removal through a hash set — `List.eraseDups` is quadratic. -/
def dedup {α : Type} [BEq α] [Hashable α] (l : List α) : List α :=
  (l.foldl (fun s x => s.insert x) (∅ : Std.HashSet α)).toList

/-! ## The pieces of `glueOn` -/

/-- The morphisms of `Ch Zbp` at total dimension `n`, grouped by their target. -/
def wedgesByTgt (n : ℕ) : List (List ℕ × List Wedge) :=
  (comps n).map fun c => (c, (allWedges n).filter fun w => wtgt w == c)

/-- Every arrow of `Ch (Hbp □ⁿ)`, as `⟨coarse, wedge map, fine⟩`. -/
def chArrows (n : ℕ) : List (Chart × Wedge × Chart) :=
  let B := wedgesByTgt n
  (charts n).flatMap fun Y =>
    ((B.lookup (dimsOf Y)).getD []).map fun w => (Y, w, pullChart Y w)

/-- `MaximalChains (Hbp □ⁿ)`: no arrow out that drops a bead. -/
def maximalCharts (n : ℕ) : List Chart :=
  let bad : Std.HashSet Chart :=
    (chArrows n).foldl (fun s a => if dimsOf a.1 == dimsOf a.2.2 then s else s.insert a.2.2) ∅
  (charts n).filter fun X => !bad.contains X

/-- `RunOver d`: the morphisms of `Ch Zbp` from the run to `d`. -/
def runOver (n : ℕ) (d : List ℕ) : List Wedge :=
  (allWedges n).filter fun w => (wsrc w == List.replicate n 1) && (wtgt w == d)

/-- The 1-cells of `runPoly d`: the pairs `RunStep` relates, spelled by its witness square. -/
def gensOver (n : ℕ) (d : List ℕ) : List (Wedge × Wedge) := dedup <|
  let A := allWedges n
  let runs := (comps n).map fun e =>
    (e, A.filter fun w => (wsrc w == List.replicate n 1) && (wtgt w == e))
  (A.filter fun z => wtgt z == d).flatMap fun z =>
    let R := (runs.lookup (wsrc z)).getD []
    (R.filter fun t => invCount (flatWedge t) == 1).flatMap fun t =>
      (R.filter isMono).map fun m => (wcomp z t, wcomp z m)

/-- The 0-cells: the runs a copy reaches. -/
def zeroCells (n : ℕ) : List Chart :=
  let S := maximalCharts n
  let R := ((S.map dimsOf).eraseDups).map fun d => (d, runOver n d)
  dedup <| S.flatMap fun s => ((R.lookup (dimsOf s)).getD []).map fun a => pullChart s a

/-- The 1-cells of the copies: a `RunStep` read inside a maximal chain, before the overlaps. -/
def copyCells (n : ℕ) : List (Chart × Wedge × Wedge) :=
  let S := maximalCharts n
  let G := ((S.map dimsOf).eraseDups).map fun d => (d, gensOver n d)
  S.flatMap fun s => ((G.lookup (dimsOf s)).getD []).map fun ab => (s, ab.1, ab.2)

/-- The two 0-cells a 1-cell joins. -/
def ends (g : Chart × Wedge × Wedge) : Chart × Chart :=
  (pullChart g.1 g.2.1, pullChart g.1 g.2.2)

/-- `GlueOnEq.span`: a span of maximal chains with agreeing charts identifies the two readings of
a 1-cell of the apex's slice. -/
def overlapPairs (n : ℕ) : List ((Chart × Wedge × Wedge) × (Chart × Wedge × Wedge)) :=
  let S := maximalCharts n
  let A := allWedges n
  (comps n).flatMap fun d =>
    let G := gensOver n d
    if G.isEmpty then [] else
      let legs := S.map fun s => (s, A.filter fun f => (wsrc f == d) && (wtgt f == dimsOf s))
      let feet := legs.flatMap fun sf => sf.2.map fun f => (sf.1, f, pullChart sf.1 f)
      feet.flatMap fun p₁ => (feet.filter fun p₂ => p₂.2.2 == p₁.2.2).flatMap fun p₂ =>
        G.map fun ab =>
          ((p₁.1, wcomp p₁.2.1 ab.1, wcomp p₁.2.1 ab.2),
            (p₂.1, wcomp p₂.2.1 ab.1, wcomp p₂.2.1 ab.2))

/-! ## Union-find over the 1-cells -/

/-- The root of `i`, with `f` steps of fuel. -/
def root (p : Array ℕ) : ℕ → ℕ → ℕ
  | 0, i => i
  | f + 1, i => if p[i]! == i then i else root p f p[i]!

/-- The 1-cells, each tagged by its overlap class. -/
def classOf (n : ℕ) : List ℕ :=
  let gs := copyCells n
  let k := gs.length
  let idx : Std.HashMap (Chart × Wedge × Wedge) ℕ :=
    ((List.range k).zip gs).foldl (fun m p => m.insert p.2 p.1) ∅
  let p := (overlapPairs n).foldl (fun p e =>
    match idx[e.1]?, idx[e.2]? with
    | some i, some j =>
      let ri := root p k i
      let rj := root p k j
      if ri == rj then p else p.set! ri rj
    | _, _ => p) ((List.range k).toArray)
  (List.range k).map (root p k)

/-- **The 1-cells of `glueOn`**: a copy's, modulo the overlaps, named by a representative. -/
def oneCells (n : ℕ) : List (Chart × Wedge × Wedge) :=
  let gs := copyCells n
  (dedup (classOf n)).filterMap fun i => gs[i]?

/-! ## The table -/

/-- `⟨copies, 0-cells, the copies' 1-cells, overlap identifications, 1-cells⟩`. -/
def table (n : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  ((maximalCharts n).length, (zeroCells n).length, (copyCells n).length,
    (overlapPairs n).length, (oneCells n).length)

/-- How many 1-cells join each `⟨source, target⟩` pair of 0-cells. -/
def endCounts (n : ℕ) : List ((Chart × Chart) × ℕ) :=
  (((copyCells n).map ends).foldl (fun m e => m.insert e (m.getD e 0 + 1))
    (∅ : Std.HashMap (Chart × Chart) ℕ)).toList

/-- The multiplicities: how many copies witness a `⟨source, target⟩` pair. -/
def multiplicities (n : ℕ) : List ℕ := dedup ((endCounts n).map Prod.snd)

/-- The distinct `⟨source, target⟩` pairs a 1-cell can join. -/
def endPairs (n : ℕ) : ℕ := (endCounts n).length

/-- Whether an overlap ever identifies 1-cells with different endpoints. -/
def overlapEndsAgree (n : ℕ) : Bool := (overlapPairs n).all fun e => ends e.1 == ends e.2

/-- The overlaps that identify two *distinct* 1-cells. -/
def properOverlaps (n : ℕ) : ℕ := (overlapPairs n).countP fun e => e.1 != e.2

/-- The index at which the two 0-cells of a 1-cell differ. -/
def swapPos (g : Chart × Wedge × Wedge) : ℕ :=
  let r := (pullChart g.1 g.2.1).flatten
  let r' := (pullChart g.1 g.2.2).flatten
  ((List.range r.length).filter fun i => r.getD i 0 != r'.getD i 0).getD 0 0

/-- **Which copies witness a crossing**: a 1-cell at `⟨r, k⟩` lives in the copy `w` exactly when
`w` performs the two crossed directions in the opposite order — half the chambers. -/
def witnessRule (n : ℕ) : Bool :=
  (copyCells n).all fun g =>
    let r := (pullChart g.1 g.2.1).flatten
    let k := swapPos g
    let w := g.1.flatten
    decide (w.idxOf (r.getD (k + 1) 0) < w.idxOf (r.getD k 0))

/-- The whole `n = 2` presentation: each 1-cell as `⟨copy, source run, target run⟩`. -/
def presentation2 : List (Chart × Chart × Chart) :=
  (oneCells 2).map fun g => (g.1, pullChart g.1 g.2.1, pullChart g.1 g.2.2)

/-! ## Validation against the enumerated `Ch⋆(□ⁿ)`

`charts` is `execs`, `pullChart` is the action of `hwedge` on chains, and `chArrows` is the arrow
count `HWedge`'s summary reports.  `allWedges`/`wcomp`/`isMono` are validated in `Merges`. -/

/-- `charts n` against `execs (SubCube.full n)`. -/
def chartsMatch (n : ℕ) : Bool :=
  setEq (charts n) ((execs (SubCube.full n)).map fun X => X.1.map fun b => b.map Fin.val)

/-- `pullChart` against `hwedge` on every arrow of `Ch⋆(□ⁿ)`. -/
def pullMatch (n : ℕ) : Bool :=
  (arrows (SubCube.full n)).all fun q =>
    pullChart (q.1.1.map fun b => b.map Fin.val) (hwedge q.1 q.2)
      == (q.2.1.map fun b => b.map Fin.val)

/-- `flatWedge` and `fpermList` have the same inversion count on every arrow. -/
def invMatch (n : ℕ) : Bool :=
  (arrows (SubCube.full n)).all fun q =>
    invCount (flatWedge (hwedge q.1 q.2)) == invCount (FExec.fpermList q.1 q.2)

/-! ## The measurement

`⟨copies, 0-cells, the copies' 1-cells, overlap identifications, 1-cells⟩` at `n = 2, 3, 4`: the
copies and the 0-cells are `n!`, the copies between them offer `(n-1)(n!)²/2` 1-cells with every
`⟨source, target⟩` pair witnessed `n!/2` times, and the overlaps coequalize them to the `n!(n-1)`
the fibration route names. -/

#eval (chartsMatch 2, chartsMatch 3, chartsMatch 4)                     -- (true, true, true)
#eval (pullMatch 2, pullMatch 3, pullMatch 4)                           -- (true, true, true)
#eval (invMatch 2, invMatch 3, invMatch 4)                              -- (true, true, true)
#eval ((chArrows 2).length, (chArrows 3).length, (chArrows 4).length)   -- (8, 120, 2880)

#eval (table 2, table 3, table 4)
                    -- ((2,2,2,2,2), (6,6,36,144,12), (24,24,864,19296,72))
#eval ((oneCells 2).length, (oneCells 3).length, (oneCells 4).length)   -- (2, 12, 72)
#eval (multiplicities 2, multiplicities 3, multiplicities 4)            -- ([1], [3], [12])
#eval (endPairs 2, endPairs 3, endPairs 4)                              -- (2, 12, 72)
#eval (overlapEndsAgree 2, overlapEndsAgree 3, overlapEndsAgree 4)      -- (true, true, true)
#eval (properOverlaps 2, properOverlaps 3, properOverlaps 4)            -- (0, 72, 15840)
#eval (witnessRule 2, witnessRule 3, witnessRule 4)                     -- (true, true, true)

/-! `n = 5`, without the overlaps: the same shape at `120` copies. -/

#eval ((maximalCharts 5).length, (zeroCells 5).length, (copyCells 5).length,
       endPairs 5, multiplicities 5)                          -- (120, 120, 28800, 480, [60])

/-! The whole presentation at `n = 2`: two 0-cells, and one 1-cell in each copy — the two atoms
of the wall, whose composite is the pure braid generator. -/

#eval zeroCells 2                                             -- [[[0], [1]], [[1], [0]]]
#eval presentation2
      -- [([[0,1]], [[1],[0]], [[0],[1]]), ([[1,0]], [[0],[1]], [[1],[0]])]

end GlueCount

end CubeChains
