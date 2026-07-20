import CubeChains.Salvetti.SalLines

/-!
# Salvetti/RunOrderFace — restriction along a face preserves the order of a run

Restricting a chain of `□ᵇ` along `face : ▫a ⟶ ▫b` is `List.filterMap`, which drops cubes but
never reorders them.  So the bead carrying a surviving coordinate keeps its relative position, and
the block index of the restricted chain is the `filterMap` position of the original block index
(`blockIndex_restrict`).  Coordinates travel along `faceEmb face`.

The consumer is the bead-local half of the Salvetti wall-crossing law, which needs a height
comparison to survive `runRestrictFace` — `runHeight_runRestrictFace_lt_iff`.
-/

open CategoryTheory Opposite CubeChain StdCube BPSet SignType ChainCat

namespace CubeChains

/-! ## Part 0 — `List.filterMap` never reorders

`fmIdx f l i` is the output position of input index `i`: the number of survivors strictly before
it.  Monotone always, strictly monotone across a surviving index. -/

/-- The output position, under `filterMap f`, of the input index `i`. -/
def fmIdx {α β : Type*} (f : α → Option β) (l : List α) (i : ℕ) : ℕ :=
  ((l.take i).filterMap f).length

/-- `filterMap` split at a surviving index. -/
theorem filterMap_split {α β : Type*} (f : α → Option β) (l : List α) {i : ℕ}
    (hi : i < l.length) {b : β} (hb : f l[i] = some b) :
    l.filterMap f = (l.take i).filterMap f ++ b :: ((l.drop (i + 1)).filterMap f) := by
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.filterMap_append, List.drop_eq_getElem_cons hi, List.filterMap_cons_some hb]

theorem fmIdx_mono {α β : Type*} (f : α → Option β) (l : List α) {i j : ℕ} (h : i ≤ j) :
    fmIdx f l i ≤ fmIdx f l j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [fmIdx, fmIdx, List.take_add, List.filterMap_append, List.length_append]
  exact Nat.le_add_right _ _

theorem fmIdx_succ {α β : Type*} {f : α → Option β} {l : List α} {i : ℕ} (hi : i < l.length)
    {b : β} (hb : f l[i] = some b) : fmIdx f l (i + 1) = fmIdx f l i + 1 := by
  have hone : ((l[i]?).toList).filterMap f = [b] := by
    rw [List.getElem?_eq_getElem hi]
    exact List.filterMap_cons_some hb
  rw [fmIdx, fmIdx, List.take_add_one, List.filterMap_append, List.length_append, hone]
  rfl

theorem fmIdx_lt {α β : Type*} {f : α → Option β} {l : List α} {i j : ℕ} (hij : i < j)
    (hi : i < l.length) {b : β} (hb : f l[i] = some b) : fmIdx f l i < fmIdx f l j :=
  calc fmIdx f l i < fmIdx f l i + 1 := Nat.lt_succ_self _
    _ = fmIdx f l (i + 1) := (fmIdx_succ hi hb).symm
    _ ≤ fmIdx f l j := fmIdx_mono f l hij

/-- The survivor of input index `i` sits at output position `fmIdx f l i`. -/
theorem fmIdx_getElem? {α β : Type*} {f : α → Option β} {l : List α} {i : ℕ} (hi : i < l.length)
    {b : β} (hb : f l[i] = some b) : (l.filterMap f)[fmIdx f l i]? = some b := by
  rw [filterMap_split f l hi hb,
    List.getElem?_append_right (Nat.le_of_eq (by rw [fmIdx])), fmIdx, Nat.sub_self]
  rfl

/-! ## Part 1 — restricting a chain of `□ᵇ` -/

/-- The projected chain, as an object of the refinement category. -/
def restrictRefineObj {n b : ℕ} (face : ▫n ⟶ ▫b) (x : RefineObj (□b).init (□b).final) :
    RefineObj (□n).init (□n).final where
  cubes := restrictChain face x.cubes
  isChain := by
    have h := restrict_isCubeChain face x.cubes _ _ x.isChain
    rwa [restrictVertex_init, restrictVertex_final] at h

/-- `toStar` and `Box.sign` are the same reading of a cube cell. -/
theorem toStar_eq_sign {m k : ℕ} (f : (□m).cells k) : toStar f = Box.sign f := rfl

/-- A surviving cube's sign vector is the projected sign vector. -/
theorem sign_restrictCube {n b : ℕ} (face : ▫n ⟶ ▫b) (c : Σ d : ℕ+, (cube b).cells (d : ℕ))
    (d : Σ d : ℕ+, (cube n).cells (d : ℕ)) (h : restrictCube face c = some d) :
    (Box.sign d.2).val = restrictCoord face (Box.sign c.2) := by
  by_cases hpos : 0 < (noneSet (restrictCoord face (Box.sign c.2))).card
  · rw [restrictCube, dif_pos hpos] at h
    obtain rfl := (Option.some_inj.mp h).symm
    exact congrArg Subtype.val (Box.sign_ofSign _)
  · rw [restrictCube, dif_neg hpos] at h; cases h

/-- **Coordinates travel along `faceEmb`.**  A coordinate is free in the projected cube exactly
when its image is free in the original. -/
theorem mem_noneSet_restrictCube {n b : ℕ} (face : ▫n ⟶ ▫b)
    (c : Σ d : ℕ+, (cube b).cells (d : ℕ)) (d : Σ d : ℕ+, (cube n).cells (d : ℕ))
    (h : restrictCube face c = some d) (q : Fin n) :
    q ∈ noneSet (Box.sign d.2).val ↔ faceEmb face q ∈ noneSet (Box.sign c.2).val := by
  rw [mem_noneSet, mem_noneSet, sign_restrictCube face c d h]
  rfl

/-- A cube with a free coordinate in the image of `faceEmb` survives the projection. -/
theorem restrictCube_isSome_of_free {n b : ℕ} (face : ▫n ⟶ ▫b)
    (c : Σ d : ℕ+, (cube b).cells (d : ℕ)) {p : Fin n}
    (hp : faceEmb face p ∈ noneSet (Box.sign c.2).val) :
    ∃ d, restrictCube face c = some d := by
  have h0 : (Box.sign c.2).val (faceEmb face p) = none := mem_noneSet.mp hp
  have hmem : p ∈ noneSet (restrictCoord face (Box.sign c.2)) := mem_noneSet.mpr h0
  exact ⟨_, by rw [restrictCube]; exact dif_pos (Finset.card_pos.mpr ⟨p, hmem⟩)⟩

/-! ## Part 2 — the block index of the projected chain -/

variable {n b : ℕ} (face : ▫n ⟶ ▫b) (x : RefineObj (□b).init (□b).final)

/-- The bead that flips `faceEmb face p` survives the projection. -/
theorem restrictCube_blockIndex (p : Fin n) :
    ∃ d, restrictCube face x.cubes[((blockIndex x (faceEmb face p)) : ℕ)] = some d :=
  restrictCube_isSome_of_free face _ (blockIndex_mem x (faceEmb face p))

/-- **The projected block index is the `filterMap` position of the original one.** -/
theorem blockIndex_restrict (p : Fin n) :
    ((blockIndex (restrictRefineObj face x) p) : ℕ)
      = fmIdx (restrictCube face) x.cubes ((blockIndex x (faceEmb face p)) : ℕ) := by
  obtain ⟨d, hd⟩ := restrictCube_blockIndex face x p
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp
    (fmIdx_getElem? (blockIndex x (faceEmb face p)).isLt hd)
  have hpd : p ∈ blockOf (restrictRefineObj face x)
      ⟨fmIdx (restrictCube face) x.cubes ((blockIndex x (faceEmb face p)) : ℕ), hj⟩ := by
    change p ∈ noneSet (toStar ((restrictRefineObj face x).cubes.get ⟨_, hj⟩).2).val
    rw [toStar_eq_sign, show (restrictRefineObj face x).cubes.get ⟨_, hj⟩ = d from hgj]
    exact (mem_noneSet_restrictCube face _ d hd p).mpr (blockIndex_mem x (faceEmb face p))
  exact congrArg Fin.val (blockIndex_unique _ hpd)

/-- **Restriction preserves the order in which the chain visits its coordinates.** -/
theorem blockIndex_restrict_lt_iff (p q : Fin n) :
    blockIndex (restrictRefineObj face x) p < blockIndex (restrictRefineObj face x) q
      ↔ blockIndex x (faceEmb face p) < blockIndex x (faceEmb face q) := by
  rw [Fin.lt_def, Fin.lt_def, blockIndex_restrict face x p, blockIndex_restrict face x q]
  constructor
  · intro h
    by_contra hle
    exact absurd (fmIdx_mono (restrictCube face) x.cubes (Nat.le_of_not_lt hle)) (Nat.not_le.mpr h)
  · intro h
    obtain ⟨d, hd⟩ := restrictCube_blockIndex face x p
    exact fmIdx_lt h (blockIndex x (faceEmb face p)).isLt hd

/-! ## Part 3 — the same law for `runRestrictFace`

A one-bead run is a chain of `□ᵇ` classified by the trivial one-bead chain `beadCh b`; under that
identification `runRestrictFace` *is* `restrictRefineObj`. -/

/-- The one-bead chain of `□ᵇ`: the cube itself, `⋁[b] ≅ □ᵇ`. -/
def beadCh (b : ℕ+) : Ch (□(b : ℕ)) := ⟨[b], (serialWedge1 b).hom⟩

/-- **`runRestrictFace` is `restrictRefineObj`.** -/
theorem wedgeToRefineObj_runChain_runRestrictFace {a b : ℕ+}
    (f : (cube (a : ℕ)).toPsh ⟶ (cube (b : ℕ)).toPsh) (r : Run [b]) :
    wedgeToRefineObj (runChain (beadCh a) (runRestrictFace f r))
      = restrictRefineObj (yonedaEquiv f) (wedgeToRefineObj (runChain (beadCh b) r)) :=
  RefineObj.ext' (congrArg (fun e : EdgeChain (cube (a : ℕ)) => e.1.cubes)
    (toEdgeChain_toRun (EdgeChain.restrict (yonedaEquiv f) r.toEdgeChain)))

/-- **Restriction along a face preserves the order in which a run visits its edges.**  The
bead-local half of the Salvetti wall-crossing law. -/
theorem runHeight_runRestrictFace_lt_iff {a b : ℕ+}
    (f : (cube (a : ℕ)).toPsh ⟶ (cube (b : ℕ)).toPsh) (r : Run [b]) (p q : Fin (a : ℕ)) :
    runHeight (beadCh a) (runRestrictFace f r) p < runHeight (beadCh a) (runRestrictFace f r) q
      ↔ runHeight (beadCh b) r (faceEmb (yonedaEquiv f) p)
          < runHeight (beadCh b) r (faceEmb (yonedaEquiv f) q) := by
  have hobj := wedgeToRefineObj_runChain_runRestrictFace f r
  change covectorHeight (wedgeToRefineObj (runChain (beadCh a) (runRestrictFace f r))) p
      < covectorHeight (wedgeToRefineObj (runChain (beadCh a) (runRestrictFace f r))) q
    ↔ covectorHeight (wedgeToRefineObj (runChain (beadCh b) r)) (faceEmb (yonedaEquiv f) p)
      < covectorHeight (wedgeToRefineObj (runChain (beadCh b) r)) (faceEmb (yonedaEquiv f) q)
  rw [hobj, covectorHeight_lt_iff, covectorHeight_lt_iff]
  exact blockIndex_restrict_lt_iff (yonedaEquiv f) _ p q

end CubeChains
