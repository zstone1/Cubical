import CubeChains.Testing.Enumerate.FastExec

/-!
# Testing/H/HWedge — is the crossing permutation a function of the `Ch (Hbp □n)` wedge map?

A `Ch (Hbp K)` arrow's wedge map is the `Ch K` refinement **twisted by the coarse object's run**
(`twist`, `Concurrency/Complexification/ChStarSym`): bead `j` of the coarse execution contributes
the ordered partition of its *run positions* cut out by the beads of the fine one — `hwedge`. 
Untwisted (`cwedge`, positions in the bead's sorted direction set) the datum is the plain `Ch (□n)`
refinement and forgets the run.

Not built by `lake build CubeChains`.
-/

namespace CubeChains

variable {n : ℕ}

/-! ## Regrouping a refinement -/

/-- Take beads off the front of `ys` until they account for `m` letters. -/
def takeLen {α : Type*} (m : ℕ) (ys : List (List α)) : List (List α) × List (List α) :=
  match m, ys with
  | 0, ys => ([], ys)
  | _ + 1, [] => ([], [])
  | k + 1, y :: ys =>
      let p := takeLen (k + 1 - y.length) ys
      (y :: p.1, p.2)
termination_by ys.length

/-- The beads of the finer list, grouped one consecutive run per bead of the coarser one. -/
def groupBeads {α : Type*} (bs ys : List (List α)) : List (List (List α)) :=
  match bs with
  | [] => []
  | b :: bs' =>
      let p := takeLen b.length ys
      p.1 :: groupBeads bs' p.2
termination_by bs.length

/-! ## The two wedge maps

A bead face of a wedge map is a *monotone* injection, so it is its image; `enum` is the canonical
increasing spelling. -/

/-- The increasing enumeration of `l ⊆ {0, …, m-1}`. -/
def enum (m : ℕ) (l : List ℕ) : List ℕ := (List.range m).filter (l.contains ·)

/-- **The `Ch (Hbp □n)` wedge map** of the refinement `X ⟶ Y`: per bead of the coarse `X`, the
ordered partition of its **run positions** cut out by the beads of the fine `Y`. -/
def hwedge (X Y : FExec n) : List (List (List ℕ)) :=
  (X.1.zip (groupBeads X.1 Y.1)).map fun bg =>
    bg.2.map fun p => enum bg.1.length (p.map fun d => bg.1.idxOf d)

/-- The run-free wedge map — the plain `Ch (□n)` refinement: positions in the bead's **sorted**
direction set, a function of the two chains alone. -/
def cwedge (X Y : FExec n) : List (List (List ℕ)) :=
  (X.1.zip (groupBeads X.1 Y.1)).map fun bg =>
    bg.2.map fun p => enum bg.1.length (p.map fun d => bg.1.countP fun e => decide (e < d))

/-- The opposite twist — `σ` where the `sortPerm`/`sortFace` factorization gives `σ⁻¹`.  It agrees
with `hwedge` at `n = 2`, where every bead run is an involution. -/
def vwedge (X Y : FExec n) : List (List (List ℕ)) :=
  (X.1.zip (groupBeads X.1 Y.1)).map fun bg =>
    let srt := (List.finRange n).filter (bg.1.contains ·)
    bg.2.map fun p => enum bg.1.length (p.map fun d => srt.idxOf (bg.1.getD (srt.idxOf d) d))

/-! ## The arrows of `Ch⋆(K)` -/

/-- Every arrow of `Ch⋆(K)` for `K ⊆ □n`, as a `(coarse, fine)` pair — identities included. -/
def arrows (K : SubCube n) : List (FExec n × FExec n) :=
  let xs := execs K
  xs.flatMap fun X => (xs.filter fun Y => refinesB X.1 Y.1).map fun Y => (X, Y)

/-- One arrow, with its wedge map and its crossing permutation in one-line notation. -/
structure Row (n : ℕ) where
  /-- The coarse execution. -/
  src : List (List (Fin n))
  /-- The fine execution. -/
  tgt : List (List (Fin n))
  /-- The wedge map under test. -/
  w : List (List (List ℕ))
  /-- `ConcPos`'s crossing permutation. -/
  p : List ℕ
deriving Repr

/-- The arrows of `K` tabulated against the wedge map `wf` assigns them. -/
def rows (K : SubCube n) (wf : FExec n → FExec n → List (List (List ℕ))) : List (Row n) :=
  (arrows K).map fun q => ⟨q.1.1, q.2.1, wf q.1 q.2, FExec.fpermList q.1 q.2⟩

/-- Arrows sharing a wedge map but disagreeing on the crossing permutation. -/
def wedgeConflicts (rs : List (Row n)) : List (Row n × Row n) :=
  rs.flatMap fun r => (rs.filter fun s => (s.w == r.w) && !(s.p == r.p)).map fun s => (r, s)

/-- `⟨executions, arrows, distinct wedge maps, distinct permutations, conflicting pairs⟩`. -/
def wedgeSummary (K : SubCube n) (wf : FExec n → FExec n → List (List (List ℕ))) :
    ℕ × ℕ × ℕ × ℕ × ℕ :=
  let rs := rows K wf
  ((execs K).length, rs.length, (rs.map Row.w).eraseDups.length,
    (rs.map Row.p).eraseDups.length, (wedgeConflicts rs).length)

/-- The same, hashed: `⟨arrows, distinct wedge maps, distinct permutations, a conflict⟩`.  The
quadratic scan is hopeless past `n = 4`. -/
def wedgeSummary' (K : SubCube n) (wf : FExec n → FExec n → List (List (List ℕ))) :
    ℕ × ℕ × ℕ × Option (Row n × Row n) :=
  let rs := rows K wf
  let st := rs.foldl
    (fun (s : Std.HashMap (List (List (List ℕ))) (Row n) × Std.HashSet (List ℕ) ×
          Option (Row n × Row n)) r =>
      match s.1[r.w]? with
      | some t =>
          (s.1, s.2.1.insert r.p,
            if s.2.2.isSome || t.p == r.p then s.2.2 else some (t, r))
      | none => (s.1.insert r.w r, s.2.1.insert r.p, s.2.2))
    (∅, ∅, none)
  (rs.length, st.1.size, st.2.1.size, st.2.2)

/-! ## `pos ∘ coordMap` -/

/-- Running prefix sums, excluding the total. -/
def prefixSums (l : List ℕ) : List ℕ :=
  (l.foldl (fun p x => (p.1 ++ [p.2], p.2 + x)) (([] : List ℕ), 0)).1

/-- `pos ∘ coordMap` of a wedge map, listed in the source's own `pos` order — monotone exactly when
it is `List.range n`. -/
def flatWedge (w : List (List (List ℕ))) : List ℕ :=
  let offs := prefixSums (w.map fun g => (g.map List.length).sum)
  (w.zip offs).flatMap fun go => go.1.flatMap fun u => u.map (go.2 + ·)

/-- Arrows where "`pos ∘ coordMap` is monotone" and "the crossing permutation is trivial"
disagree. -/
def monoConflicts (K : SubCube n) : List (Row n) :=
  (rows K hwedge).filter fun r =>
    (flatWedge r.w == List.range n) != (r.p == List.range n)

/-! ## Functoriality of the model

`coordMap` is a functor (`coordMap_comp`), so the model is testable against composition without
leaving `Testing/`. -/

/-- `coordMap` of a wedge map, as the images of the source events in `pos` order. -/
def evList (w : List (List (List ℕ))) : List (ℕ × ℕ) :=
  w.zipIdx.flatMap fun gj => gj.1.flatMap fun u => u.map fun c => (gj.2, c)

/-- `coordMap (w₁ ≫ w₂)` predicted from the factors. -/
def compEv (w₁ w₂ : List (List (List ℕ))) : List (ℕ × ℕ) :=
  let offs := prefixSums (w₂.flatten.map List.length)
  let e₂ := evList w₂
  (evList w₁).map fun jc => e₂.getD (offs.getD jc.1 0 + jc.2) (0, 0)

/-- Composable triples on which `hwedge` fails `coordMap_comp`. -/
def funcConflicts (K : SubCube n) : List (List (List (List (Fin n)))) :=
  let xs := execs K
  xs.flatMap fun X => xs.flatMap fun Y => xs.flatMap fun Z =>
    if refinesB X.1 Y.1 && refinesB Y.1 Z.1 &&
        (compEv (hwedge Y Z) (hwedge X Y) != evList (hwedge X Z))
      then [[X.1, Y.1, Z.1]] else []

/-! ## The verdict

`⟨executions, arrows, distinct wedge maps, distinct permutations, conflicting pairs⟩`.  The wedge
count is `∑` over the compositions `d` of `n` of `∏ⱼ Fub(dⱼ)` (`1, 3, 13, 75, 541`) — every wedge
map of the serial-wedge category is realised, so the enumeration is not a sub-family. -/

#eval wedgeSummary (SubCube.full 2) hwedge      -- ⟨4, 8, 4, 2, 0⟩
#eval wedgeSummary (SubCube.full 3) hwedge      -- ⟨24, 120, 20, 6, 0⟩
#eval wedgeSummary (SubCube.full 4) hwedge      -- ⟨192, 2880, 120, 24, 0⟩
#eval wedgeSummary (SubCube.boundary 3) hwedge  -- ⟨18, 42, 7, 3, 0⟩
#eval wedgeSummary (SubCube.boundary 4) hwedge  -- ⟨168, 1080, 45, 11, 0⟩
#eval let s := wedgeSummary' (SubCube.full 5) hwedge
      (s.1, s.2.1, s.2.2.1, s.2.2.2.isSome)     -- ⟨101760, 848, 120, false⟩

/-! Neither control determines the crossing permutation, and neither is separated at `n = 2`. -/

#eval wedgeSummary (SubCube.full 3) cwedge      -- ⟨24, 120, 20, 6, 396⟩
#eval (wedgeSummary (SubCube.full 2) vwedge, wedgeSummary (SubCube.full 3) vwedge)
                                                -- ⟨…, 0⟩ and ⟨24, 120, 20, 6, 216⟩

-- The smallest witness: the same two chains, run `[1,2]` versus `[2,1]` in the second bead.
#eval ((wedgeConflicts (rows (SubCube.full 3) cwedge)).take 1).map fun c =>
  ((c.1.src, c.1.tgt, c.1.p), (c.2.src, c.2.tgt, c.2.p), c.1.w)

/-! ### Triviality, and functoriality of the model -/

#eval ((monoConflicts (SubCube.full 3)).length, (monoConflicts (SubCube.full 4)).length)  -- (0, 0)
#eval ((funcConflicts (SubCube.full 3)).length, (funcConflicts (SubCube.full 4)).length)  -- (0, 0)


end CubeChains
