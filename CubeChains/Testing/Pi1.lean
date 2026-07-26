import CubeChains.Testing.FastExec
import CubeChains.Testing.Presentation

/-!
# Testing/Pi1 — a sub-precubical set of `□n` to a presentation of its concurrency `π₁`

`FreeGroupoid` is the localization of a category, so the vertex group of `Conc K` is `π₁` of the
*nerve* of the execution poset — not the free group on its graph, which over-counts as soon as the
poset has a strict `3`-chain (i.e. as soon as a bead of dimension `≥ 3` survives in `K`).

Three composable pieces: `execs` enumerates the executions, `buildPoset` their refinement order,
`present` the Tietze-reduced presentation.  The arrow label is `fperm`, `ConcPos`'s crossing
permutation, so each generator carries the braid word `Conc` assigns its loop.

Not built by `lake build CubeChains`.
-/

namespace CubeChains

variable {n : ℕ}

/-- The execution poset of `K ⊆ □n`, each arrow carrying the signed Artin word of its crossing
permutation — the label `ConcPos` assigns it (`braidWordZ = permWordZ ∘ permOf`). -/
def concPoset (K : SubCube n) : PosetData :=
  let P := buildPoset K
  let ns := P.nodes
  { size := ns.size
    le := P.le
    label := fun a b =>
      match ns[a]?, ns[b]? with
      | some X, some Y => permWordZ (FExec.fperm X Y)
      | _, _ => [] }

/-- **The concurrency fundamental group of `K ⊆ □n`**, presented: generators from a spanning tree of
the execution poset's Hasse diagram, relations from its strict `3`-chains. -/
def concPi1 (K : SubCube n) : Presentation := present (concPoset K)

/-- The permutation underlying a signed Artin word, in one-line notation: letter `x` swaps the
strands at `|x| - 1` and `|x|`, and a sign does not change the transposition. -/
def braidPerm (n : ℕ) (w : List ℤ) : List ℕ :=
  w.foldl (fun l x =>
    let j := x.natAbs - 1
    l.mapIdx fun i v => if i = j then l.getD (j + 1) 0 else if i = j + 1 then l.getD j 0 else v)
    (List.range n)

/-- Linking numbers of a braid word, indexed by the pairs `i < j` — the image in `Pₙ^ab = ℤ^C(n,2)`.
Each letter crosses whichever two strands currently sit at its position. -/
def linkVec (n : ℕ) (w : List ℤ) : List ℤ :=
  let fin := w.foldl (fun (p : Array ℕ × Array ℤ) x =>
      let j := x.natAbs - 1
      let a := p.1.getD j 0
      let b := p.1.getD (j + 1) 0
      let k := min a b * n + max a b
      ((p.1.set! j b).set! (j + 1) a, p.2.set! k (p.2.getD k 0 + if x < 0 then -1 else 1)))
    ((List.range n).toArray, Array.replicate (n * n) (0 : ℤ))
  (List.range n).flatMap fun i =>
    ((List.range n).filter (i < ·)).map fun j => fin.2.getD (i * n + j) 0

/-- The linking-number vectors of every `π₁` generator — the abelianized braid content of `K`. -/
def concLinks (K : SubCube n) : List (List ℤ) := (concPi1 K).words.toList.map (linkVec n)

/-- Every generating loop maps to a *pure* braid.  For `□n` this is forced (Salvetti asphericity),
so it fails exactly when the enumeration, the arrow rule, the labels or the word order is wrong. -/
def concPure (K : SubCube n) : Bool :=
  ((concPi1 K).words.toList.map (braidPerm n)).all (· = List.range n)

/-- An execution with `k` beads is a Salvetti cell of dimension `n - k`, so the alternating sum is
the Euler characteristic of the complex whose `π₁` `concPi1` presents. -/
def concSummary (K : SubCube n) : ℕ × ℕ × List ℕ × ℤ :=
  let xs := execs K
  let cells : List ℕ := (List.range (n + 1)).map fun d => xs.countP fun X => X.1.length == n - d
  let arrows := ((buildPoset K).le.map fun r => r.count true).sum
  (xs.length, arrows - xs.length, cells,
    (List.range (n + 1)).foldl (fun acc d => acc + (-1 : ℤ) ^ d * (cells.getD d 0 : ℤ)) 0)

end CubeChains
