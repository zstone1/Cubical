import CubeChains.Testing.Graph

/-!
# Testing/Pi1 — the fundamental group of the concurrency graph `Ch⋆(∂□³)`

The graph of `Testing/Graph` (proven `= Ch⋆` in `ExecEquiv`, labels proven `= ConcPos`'s crossing map
in `LabelConcPos`) is a finite quiver.  Its fundamental group — the vertex group of the free groupoid
`FreeGroupoid (Ch⋆(∂□n))` that `Conc` grades — is, for a connected graph, free of rank `E − V + 1`.

Everything computes without `Multiset.toList` (noncomputable): executions are rendered to comparable
keys and the invariants are `Finset`/`Multiset` operations.

Not built by `lake build CubeChains`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain StdCube

/-! ## Rendering an execution to a comparable key -/

/-- A cell of `□n` as a nat-vector (`none↦0`, `some false↦1`, `some true↦2`). -/
def cellNats (n k : ℕ) (c : (cube n).cells k) : List ℕ :=
  (List.finRange n).map fun i =>
    match (cubeCellEquiv n k c).1 i with
    | none => 0
    | some false => 1
    | some true => 2

/-- A cube of a chain: its dimension, then its cell. -/
def cubeNats (n : ℕ) (c : Σ d : ℕ+, (cube n).cells (d : ℕ)) : List ℕ :=
  (c.1 : ℕ) :: cellNats n (c.1 : ℕ) c.2

/-- A cube chain as its list of cube-keys. -/
def chainNats (n : ℕ) (C : CubeChain (cube n)) : List (List ℕ) := C.cubes.map (cubeNats n)

/-- **A node key**: the chain, then each bead's linearization — a decidable-eq render of an execution. -/
abbrev NKey : Type := (List (List ℕ)) × List (List (List ℕ))

def nkey (n : ℕ) (e : Exec n) : NKey :=
  (chainNats n e.1,
   (List.finRange e.1.cubes.length).map fun i => chainNats ((e.1.cubes.get i).1 : ℕ) (e.2 i).1)

/-! ## The graph as keyed data -/

/-- The boundary graph's nodes, as a finite set of keys. -/
def nodeSet (n : ℕ) : Finset NKey := ((bdryNodes n).map (nkey n)).toFinset

/-- The non-identity directed edges as key-pairs (a source ≠ target refinement). -/
def edgeSet (n : ℕ) : Finset (NKey × NKey) :=
  (((bdryEdges n).map fun t => (nkey n t.1, nkey n t.2.1)).filter fun e => e.1 ≠ e.2).toFinset

/-- Edges made symmetric — the underlying undirected 1-skeleton of the groupoid. -/
def edgeSym (n : ℕ) : Finset (NKey × NKey) := edgeSet n ∪ (edgeSet n).image Prod.swap

/-! ## Connectivity and the free rank -/

/-- One step of reachability along the (symmetric) edges. -/
def stepReach (E : Finset (NKey × NKey)) (s : Finset NKey) : Finset NKey :=
  s ∪ (E.filter fun e => e.1 ∈ s).image Prod.snd

/-- Reachable closure after `k` steps. -/
def reachN (E : Finset (NKey × NKey)) (s : Finset NKey) : ℕ → Finset NKey
  | 0 => s
  | k + 1 => reachN E (stepReach E s) k

/-- **The fundamental-group data of the graph**, computed in one pass (graph enumerated once):
`⟨V, E, components, rank⟩` with `rank = E − V + components` — the free rank of the vertex group of the
free groupoid `Conc` grades.  Components are the distinct reachable closures. -/
def graphSummary (n : ℕ) : ℕ × ℕ × ℕ × ℤ :=
  let nodes : Finset NKey := ((bdryNodes n).map (nkey n)).toFinset
  let dir : Finset (NKey × NKey) :=
    (((bdryEdges n).map fun t => (nkey n t.1, nkey n t.2.1)).filter fun e => e.1 ≠ e.2).toFinset
  let sym : Finset (NKey × NKey) := dir ∪ dir.image Prod.swap
  let V := nodes.card
  let E := dir.card
  let comps := (nodes.image fun v => reachN sym {v} V).card
  (V, E, comps, (E : ℤ) - (V : ℤ) + (comps : ℤ))
