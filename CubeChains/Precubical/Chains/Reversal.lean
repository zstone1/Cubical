import CubeChains.Precubical.Chains.CubeVtx
import CubeChains.Machinery.Cube.Reversal

/-!
# Precubical/Chains/Reversal — running a chain backwards

The cubes in reverse order, each one flipped by `Box.rev`.  Reversal exchanges a cube's two
extremal vertices, so the reversed list is again a chain, and it permutes the dimension list, so
an all-edges chain stays all-edges.

This is the geometry `Run.rev` reaches through (`Concurrency/Executions/RunPerm`).
-/

open CategoryTheory Opposite BPSet StdCube

namespace CubeChains

variable {n : ℕ}

/-! ### One cube -/

/-- A cube of `□n`, run backwards: flip every fixed sign. -/
def revCube (c : Σ d : ℕ+, (□n).cells (d : ℕ)) : Σ d : ℕ+, (□n).cells (d : ℕ) :=
  ⟨c.1, Box.rev.map c.2⟩

@[simp] theorem revCube_revCube (c : Σ d : ℕ+, (□n).cells (d : ℕ)) : revCube (revCube c) = c :=
  congrArg (Sigma.mk c.1) (Box.rev_rev_map c.2)

/-- `Box.sign_rev` at the spelling a *cell* of `□n` carries.  `(□n).cells m` is the hom-type only up
to unfolding, and `rw` will not reach through it. -/
theorem sign_rev_cell {m : ℕ} (c : (□n).cells m) :
    Box.sign (Box.rev.map c) = flipCell (Box.sign c) := Box.sign_rev c

/-- **Reversal negates an extremal vertex inclusion** — `endVertexMap ε` is a constant sign
vector, and flipping a constant negates it.  Everything else about reversal and endpoints is
this, whiskered (`vertexEnd` on a representable *is* precomposition, `vertexEnd_cube`). -/
@[simp] theorem rev_endVertexMap (ε : Bool) (m : ℕ) :
    Box.rev.map (PrecubicalSet.endVertexMap ε m) = PrecubicalSet.endVertexMap (!ε) m :=
  (Box.rev_ofSign _).trans (congrArg Box.ofSign (flipCell_constVertex m ε))

/-- **Reversal exchanges a cube's two extremal vertices.** -/
theorem vertexEnd_rev (ε : Bool) {m : ℕ} (c : (□n).cells m) :
    (□n).toPsh.vertexEnd ε (Box.rev.map c) = Box.rev.map ((□n).toPsh.vertexEnd (!ε) c) := by
  rw [vertexEnd_cube, vertexEnd_cube, Box.rev.map_comp, rev_endVertexMap, Bool.not_not]
  rfl

@[simp] theorem rev_cube_init (n : ℕ) : Box.rev.map ((□n).init) = (□n).final :=
  rev_endVertexMap false n

@[simp] theorem rev_cube_final (n : ℕ) : Box.rev.map ((□n).final) = (□n).init :=
  rev_endVertexMap true n

/-! ### One cube list -/

/-- A cube list, run backwards. -/
def revCubes (cubes : List (Σ d : ℕ+, (□n).cells (d : ℕ))) :
    List (Σ d : ℕ+, (□n).cells (d : ℕ)) :=
  (cubes.map revCube).reverse

@[simp] theorem revCubes_revCubes (cubes : List (Σ d : ℕ+, (□n).cells (d : ℕ))) :
    revCubes (revCubes cubes) = cubes := by
  simp [revCubes, List.map_reverse, List.map_map, Function.comp_def]

/-- Reversal exchanges the endpoints, because it exchanges each cube's two extremal vertices. -/
theorem isCubeChain_revCubes {u v : (□n).cells 0} :
    ∀ cubes : List (Σ d : ℕ+, (□n).cells (d : ℕ)), IsCubeChain u cubes v →
      IsCubeChain (Box.rev.map v) (revCubes cubes) (Box.rev.map u)
  | [], h => congrArg Box.rev.map h.symm
  | ⟨m, c⟩ :: rest, h => by
      rw [show revCubes ((⟨m, c⟩ : Σ d : ℕ+, (□n).cells (d : ℕ)) :: rest)
            = revCubes rest ++ [revCube ⟨m, c⟩] by simp [revCubes]]
      exact IsCubeChain.append (isCubeChain_revCubes rest h.2)
        ⟨vertexEnd_rev false c, (vertexEnd_rev true c).trans (congrArg Box.rev.map h.1)⟩

/-- **A cube chain, run backwards.** -/
def revCubeChain (C : CubeChain (□n)) : CubeChain (□n) :=
  CubeChain.ofIsCubeChain (revCubes C.cubes) (by
    have h := isCubeChain_revCubes C.cubes (isCubeChain C)
    rwa [rev_cube_final, rev_cube_init] at h)

@[simp] theorem revCubeChain_revCubeChain (C : CubeChain (□n)) :
    revCubeChain (revCubeChain C) = C :=
  CubeChain.eq_of_cubes (revCubes_revCubes C.cubes)

/-! ### All-edges chains are closed under reversal

Reversal only permutes the cube list, so it preserves "every bead is an edge". -/

/-- An all-edges chain, run backwards. -/
def EdgeChain.rev (r : EdgeChain (□n)) : EdgeChain (□n) :=
  ⟨revCubeChain r.1, fun c hc => by
    obtain ⟨c', hc', rfl⟩ := List.exists_of_mem_map (List.mem_reverse.mp hc)
    exact r.2 c' hc'⟩

@[simp] theorem EdgeChain.rev_rev (r : EdgeChain (□n)) : r.rev.rev = r :=
  Subtype.ext (revCubeChain_revCubeChain r.1)

end CubeChains
