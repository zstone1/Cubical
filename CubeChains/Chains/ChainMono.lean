import CubeChains.Chains.CubeVtx
import CubeChains.Chains.ChainRestrictions

/-!
# Chains/ChainMono — the junctions of a cube chain ascend; each coordinate flips once

The junction vertices of a cube chain of `□n` form a **monotone** chain of `0`-cells
`⊥ = vtx 0 ≤ vtx 1 ≤ … ≤ vtx L = ⊤`, because each bead's `⊥`-vertex sits below its `⊤`-vertex —
the cube-vertex extension `cubeVtxOfCell` is an `→o`, so the orientation `cubeVtxOfCell_bot_le_top`
is free.  A monotone `Bool` chain has one ascent, so **each coordinate is free in exactly one bead**
(`cube_none_unique` / `cube_none_exists`).  This "flips once" fact is the count-free primitive the
coordinate partition — and the braid combinatorics downstream — rests on.
-/

open CategoryTheory CubeChain StdCube

namespace CubeChains

variable {n : ℕ}

/-- The value of a `0`-cell (vertex) of `□n` at coordinate `q`. -/
def vertexCoord (v : (□n).cells 0) (q : Fin n) : Bool := ((Box.sign v).val q).getD false

/-! ### Endpoints through `cubeVtx` -/

/-- A bead's `⊥`-vertex is `cubeVtx` of the bead cell at the constant `false` input. -/
theorem vertexCoord_vertex₀_eq {k : ℕ} (c : (□n).cells k) (q : Fin n) :
    vertexCoord ((□n).toPsh.vertex₀ c) q = cubeVtxOfCell (Box.sign c) (fun _ => false) q := by
  simp only [vertexCoord, sign_vertex₀, StdCube.subst_val, cubeVtxOfCell_const, StdCube.act_eq_subst]

/-- A bead's `⊤`-vertex is `cubeVtx` of the bead cell at the constant `true` input. -/
theorem vertexCoord_vertex₁_eq {k : ℕ} (c : (□n).cells k) (q : Fin n) :
    vertexCoord ((□n).toPsh.vertex₁ c) q = cubeVtxOfCell (Box.sign c) (fun _ => true) q := by
  simp only [vertexCoord, sign_vertex₁, StdCube.subst_val, cubeVtxOfCell_const, StdCube.act_eq_subst]

/-- Reading a cube's `⊥`-vertex at `q`: `false` on the free coordinates, the fixed value elsewhere. -/
theorem vertexCoord_vertex₀ {k : ℕ} (c : (□n).cells k) (q : Fin n) :
    vertexCoord ((□n).toPsh.vertex₀ c) q
      = if (Box.sign c).val q = none then false else ((Box.sign c).val q).getD false := by
  rw [vertexCoord_vertex₀_eq, cubeVtxOfCell_apply]
  by_cases h : q ∈ StdCube.noneSet (Box.sign c).val
  · rw [dif_pos h, if_pos (StdCube.mem_noneSet.mp h)]
  · rw [dif_neg h, if_neg fun hn => h (StdCube.mem_noneSet.mpr hn)]

/-- Reading a cube's `⊤`-vertex at `q`: `true` on the free coordinates, the fixed value elsewhere. -/
theorem vertexCoord_vertex₁ {k : ℕ} (c : (□n).cells k) (q : Fin n) :
    vertexCoord ((□n).toPsh.vertex₁ c) q
      = if (Box.sign c).val q = none then true else ((Box.sign c).val q).getD false := by
  rw [vertexCoord_vertex₁_eq, cubeVtxOfCell_apply]
  by_cases h : q ∈ StdCube.noneSet (Box.sign c).val
  · rw [dif_pos h, if_pos (StdCube.mem_noneSet.mp h)]
  · rw [dif_neg h, if_neg fun hn => h (StdCube.mem_noneSet.mpr hn)]

/-- A coordinate is free in a cube iff the cube's two endpoints differ there. -/
theorem sign_eq_none_iff_vertexCoord_ne {k : ℕ} (c : (□n).cells k) (q : Fin n) :
    (Box.sign c).val q = none
      ↔ vertexCoord ((□n).toPsh.vertex₀ c) q ≠ vertexCoord ((□n).toPsh.vertex₁ c) q := by
  rw [vertexCoord_vertex₀, vertexCoord_vertex₁]
  by_cases h : (Box.sign c).val q = none <;> simp [h]

/-! ### The junctions ascend (from `cubeVtx`'s orientation) -/

/-- **Consecutive junctions ascend, for free.**  `vtx i ≤ vtx (i+1)` at every coordinate — the bead's
own orientation `cubeVtxOfCell_bot_le_top`, no case analysis. -/
theorem vertexCoord_vtx_mono_step (C : CubeChain (□n)) (i : Fin C.cubes.length) (q : Fin n) :
    vertexCoord (C.vtx i.castSucc) q ≤ vertexCoord (C.vtx i.succ) q := by
  rw [← C.cube_src i, ← C.cube_tgt i, vertexCoord_vertex₀_eq, vertexCoord_vertex₁_eq]
  exact cubeVtxOfCell_bot_le_top (Box.sign (C.cubes.get i).2) q

/-- The junction vertices are monotone in the bead index. -/
theorem vertexCoord_vtx_monotone (C : CubeChain (□n)) (q : Fin n) :
    Monotone (fun k : Fin (C.cubes.length + 1) => vertexCoord (C.vtx k) q) :=
  Fin.monotone_iff_le_succ.mpr fun i => vertexCoord_vtx_mono_step C i q

/-- **A coordinate free in bead `i` flips there** (`false` before, `true` after) — a monotone `Bool`
sequence has one ascent. -/
theorem vertexCoord_flip (C : CubeChain (□n)) (i : Fin C.cubes.length) (q : Fin n)
    (hf : vertexCoord (C.vtx i.castSucc) q ≠ vertexCoord (C.vtx i.succ) q) :
    vertexCoord (C.vtx i.castSucc) q = false ∧ vertexCoord (C.vtx i.succ) q = true := by
  have hle := vertexCoord_vtx_monotone C q
    (show i.castSucc ≤ i.succ by rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
  refine ⟨?_, ?_⟩
  · by_contra h; rw [Bool.not_eq_false] at h
    exact hf (le_antisymm hle (h.symm ▸ Bool.le_true _))
  · by_contra h; rw [Bool.not_eq_true] at h
    exact hf (le_antisymm hle (h.symm ▸ Bool.false_le _))

/-- The first junction is the initial vertex: every coordinate is `false`. -/
theorem vertexCoord_vtx_zero (C : CubeChain (□n)) (q : Fin n) : vertexCoord (C.vtx 0) q = false := by
  simp only [vertexCoord, C.vtx_zero,
    show Box.sign ((□n).init) = StdCube.constVertex n false from StdCube.ev_canonicalMap _]
  rfl

/-- The last junction is the final vertex: every coordinate is `true`. -/
theorem vertexCoord_vtx_last (C : CubeChain (□n)) (q : Fin n) :
    vertexCoord (C.vtx (Fin.last C.cubes.length)) q = true := by
  simp only [vertexCoord, C.vtx_last,
    show Box.sign ((□n).final) = StdCube.constVertex n true from StdCube.ev_canonicalMap _]
  rfl

/-! ### Flips once -/

/-- Rephrase freeness in terms of the *junction* endpoints of bead `i`. -/
theorem free_iff_vtx_ne (C : CubeChain (□n)) (i : Fin C.cubes.length) (q : Fin n) :
    (Box.sign (C.cubes.get i).2).val q = none
      ↔ vertexCoord (C.vtx i.castSucc) q ≠ vertexCoord (C.vtx i.succ) q := by
  rw [sign_eq_none_iff_vertexCoord_ne, C.cube_src i, C.cube_tgt i]

/-- **A coordinate is free in at most one bead** — the monotone junction chain ascends past a
coordinate exactly once. -/
theorem cube_none_unique (C : CubeChain (□n)) {j j' : Fin C.cubes.length} (q : Fin n)
    (hj : (Box.sign (C.cubes.get j).2).val q = none)
    (hj' : (Box.sign (C.cubes.get j').2).val q = none) : j = j' := by
  have flip : ∀ a : Fin C.cubes.length, (Box.sign (C.cubes.get a).2).val q = none →
      vertexCoord (C.vtx a.castSucc) q = false ∧ vertexCoord (C.vtx a.succ) q = true :=
    fun a ha => vertexCoord_flip C a q ((free_iff_vtx_ne C a q).mp ha)
  rcases lt_trichotomy (j : ℕ) (j' : ℕ) with hlt | heq | hlt
  · have hmono : vertexCoord (C.vtx j.succ) q ≤ vertexCoord (C.vtx j'.castSucc) q :=
      vertexCoord_vtx_monotone C q (by rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega)
    rw [(flip j hj).2, (flip j' hj').1] at hmono; exact absurd hmono (by decide)
  · exact Fin.ext heq
  · have hmono : vertexCoord (C.vtx j'.succ) q ≤ vertexCoord (C.vtx j.castSucc) q :=
      vertexCoord_vtx_monotone C q (by rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega)
    rw [(flip j' hj').2, (flip j hj).1] at hmono; exact absurd hmono (by decide)

/-- **A coordinate is free in at least one bead** — the junctions rise from `false` to `true`. -/
theorem cube_none_exists (C : CubeChain (□n)) (q : Fin n) :
    ∃ i : Fin C.cubes.length, (Box.sign (C.cubes.get i).2).val q = none := by
  by_contra hnone
  push_neg at hnone
  have hconst : ∀ k : Fin (C.cubes.length + 1), vertexCoord (C.vtx k) q = false := by
    intro k
    induction k using Fin.induction with
    | zero => exact vertexCoord_vtx_zero C q
    | succ i ih =>
        by_contra hne
        exact hnone i ((free_iff_vtx_ne C i q).mpr fun hc => hne (hc ▸ ih))
  have := hconst (Fin.last _)
  rw [vertexCoord_vtx_last] at this
  exact absurd this (by decide)

end CubeChains
