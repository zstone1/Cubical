import CubeChains.Concurrency.Salvetti.CrossCompare

/-!
# Concurrency/Complexification/HPresentation — crossing a wall in `Ch(Hbp □ⁿ)[W⁻¹]`

    cell of codimension one
        ↑ crosses                  ↑ merges
    run a                          run b

Both legs go *up* — a codimension-one chain lies **below** both runs it separates — so a generator
is a span, and inverting the merge leg makes it an arrow (`Wall.loc`).
`topeCross_wallCross`/`topeCross_wallCross_flip` label the two legs `adjT k` and `1` in the
arrangement's order, `crossPerm_eq_topeCross` carries those labels to the flattening order `W` is
defined by, and `chamberWall` reads the resulting `(w, k)`-indexed span as a `Wall`.
-/

open CategoryTheory Equiv Opposite BPSet ChainCat

namespace CubeChains

variable {n : ℕ}

/-! ## The generator, intrinsically

A codimension-one chain is entered from two runs: along one leg it crosses, along the other it
merges.  Inverting the merge leg turns the span into an arrow of runs — the generator, named by a
cell of the category itself rather than by an index. -/

/-- **A wall between two runs**: a codimension-one chain above both, crossed from `a` and merged
from `b`. -/
structure Wall {K : BPSet} (a b : Run K) where
  /-- The codimension-one chain the two runs meet in. -/
  cell : Ch K
  /-- The leg out of `a`, which crosses. -/
  cross : a.chain ⟶ cell
  /-- The leg out of `b`, which merges. -/
  merge : b.chain ⟶ cell
  /-- One junction removed. -/
  codim_cross : ChainCat.codim cross = 1
  /-- …but not by a merge. -/
  not_mem : ¬ W K cross
  /-- The far leg is a merge, so it inverts. -/
  merge_mem : W K merge

/-- **Crossing a wall**: the crossing leg, then the merge leg inverted. -/
noncomputable def Wall.loc {K : BPSet} {a b : Run K} (u : Wall a b) :
    (W K).Q.obj a.chain ⟶ (W K).Q.obj b.chain :=
  letI hiso : IsIso ((W K).Q.map u.merge) := (W K).Q_inverts u.merge u.merge_mem
  (W K).Q.map u.cross ≫ @inv _ _ _ _ _ hiso

/-- A chamber cell is a run: its degree is its codimension in the arrangement, namely zero. -/
theorem isRun_cellObj_topeCell (T : Tope n) : IsRun (Hbp.obj (□n)) (cellObj (topeCell T)) := by
  refine (isRun_iff_degree_eq_zero _).mpr ?_
  rw [← cellCodim_hbpBraidSalEquiv, functor_cellObj]
  exact cellCodim_topeCell T

/-- The chamber `w`, as a run of the decorated cube. -/
def chamberRun (w : Perm (Fin n)) : Run (Hbp.obj (□n)) :=
  ⟨cellObj (topeCell ⟨wordTope w, isTope_wordTope w⟩),
    isRun_cellObj_topeCell ⟨wordTope w, isTope_wordTope w⟩⟩

/-- **The `k`-th wall of the chamber `w`, as a wall of runs** — `wallCross w k` is the cell,
`wallLeg` the crossing leg and `wallLegFlip` the merge. -/
noncomputable def chamberWall (w : Perm (Fin n)) (k : Fin (n - 1)) :
    Wall (chamberRun w) (chamberRun (w * adjT k)) where
  cell := cellObj (wallCross w k)
  cross := wallLeg w k
  merge := wallLegFlip w k
  codim_cross := codim_wallLeg w k
  not_mem h := adjT_ne_one k
    ((crossPerm_wallLeg w k).symm.trans
      ((W_iff_crossPerm_eq_one
        (dimSum_of_hbpCubeHom (cellObj (topeCell ⟨wordTope w, isTope_wordTope w⟩)).map)
        (wallLeg w k)).mp h))
  merge_mem := W_wallLegFlip w k

/-- The chamber `w`, as an object of the localized decorated chains. -/
noncomputable def chamberLoc (w : Perm (Fin n)) : (W (Hbp.obj (□n))).Localization :=
  (W (Hbp.obj (□n))).Q.obj (cellObj (topeCell ⟨wordTope w, isTope_wordTope w⟩))

/-- **Crossing the `k`-th wall of the chamber `w`**: the atom leg, then the merge leg inverted. -/
noncomputable def wallCrossLoc (w : Perm (Fin n)) (k : Fin (n - 1)) :
    chamberLoc w ⟶ chamberLoc (w * adjT k) :=
  letI hiso : IsIso ((W (Hbp.obj (□n))).Q.map (wallLegFlip w k)) :=
    (W (Hbp.obj (□n))).Q_inverts (wallLegFlip w k) (W_wallLegFlip w k)
  (W (Hbp.obj (□n))).Q.map (wallLeg w k) ≫ @inv _ _ _ _ _ hiso

/-- **The indexed wall crossing is the intrinsic one** — `wallCrossLoc` names by `(w, k)` what
`Wall.loc` names by the cell. -/
theorem chamberWall_loc (w : Perm (Fin n)) (k : Fin (n - 1)) :
    (chamberWall w k).loc = wallCrossLoc w k := rfl

end CubeChains
