import CubeChains.Precubical.Bipointed
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Cube chains (ClaudeSetup.md §4)

For a bi-pointed precubical set `K`, a *cube chain* is a sequence of cubes of
positive dimension running from `K.init` to `K.final`, each cube's target vertex
being the next cube's source vertex.

We use the *junction-vertex* representation: alongside the cubes we store the
`l + 1` junction vertices `vtx : Fin (dims.length + 1) → cells 0`, with
`vtx 0 = init`, `vtx last = final`, and `cube i` running from `vtx i.castSucc`
to `vtx i.succ`.  This handles the empty chain uniformly (it forces
`init = final`) and makes the link condition `vertex₁ (cube i) = vertex₀
(cube (i+1))` a theorem rather than a field.
-/

universe u

open CategoryTheory

/-- A cube chain in a bi-pointed precubical set `K`: a dimension sequence of
positive naturals, a cube of each dimension, and the junction vertices tying
them together from `init` to `final`. -/
structure CubeChain (K : BPSet.{u}) where
  /-- The dimension sequence, all entries `> 0`. -/
  dims : List ℕ+
  /-- The `i`-th cube, of dimension `dims.get i`. -/
  cube : ∀ i : Fin dims.length, K.cells (dims.get i : ℕ)
  /-- The `l + 1` junction vertices. -/
  vtx : Fin (dims.length + 1) → K.cells 0
  /-- The first junction vertex is the initial cell. -/
  vtx_zero : vtx 0 = K.init
  /-- The last junction vertex is the final cell. -/
  vtx_last : vtx (Fin.last dims.length) = K.final
  /-- The source vertex of cube `i` is junction `i`. -/
  cube_src : ∀ i : Fin dims.length, K.vertex₀ (cube i) = vtx i.castSucc
  /-- The target vertex of cube `i` is junction `i + 1`. -/
  cube_tgt : ∀ i : Fin dims.length, K.vertex₁ (cube i) = vtx i.succ

namespace CubeChain

variable {K : BPSet.{u}}

/-- The total length of a chain: the sum of its dimensions. -/
def length (c : CubeChain K) : ℕ := (c.dims.map (·.val)).sum

/-- The dimension sequence of a chain. -/
def dimSeq (c : CubeChain K) : List ℕ+ := c.dims

@[simp] theorem dimSeq_eq (c : CubeChain K) : c.dimSeq = c.dims := rfl

/-- The link condition: the target vertex of consecutive cubes matches the source
vertex of the next.  This is automatic in the junction-vertex representation. -/
theorem link (c : CubeChain K) (i : Fin c.dims.length) (h : i.val + 1 < c.dims.length) :
    K.vertex₁ (c.cube i) = K.vertex₀ (c.cube ⟨i.val + 1, h⟩) := by
  have hfin : Fin.succ i = Fin.castSucc (⟨i.val + 1, h⟩ : Fin c.dims.length) := by
    apply Fin.ext; simp
  rw [c.cube_tgt i, c.cube_src ⟨i.val + 1, h⟩, hfin]

/-- An empty dimension sequence forces `init = final` (the trivial point chain). -/
theorem init_eq_final_of_nil (c : CubeChain K) (h : c.dims.length = 0) :
    K.init = K.final := by
  have hfin : (0 : Fin (c.dims.length + 1)) = Fin.last c.dims.length := by
    apply Fin.ext; simp [h]
  rw [← c.vtx_zero, ← c.vtx_last, hfin]

end CubeChain
