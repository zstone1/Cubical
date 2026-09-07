import CubeChains.Concurrency.Salvetti.CrossCompare

/-!
# Concurrency/Complexification/HPresentation — crossing a wall in `Ch(Hbp □ⁿ)[W⁻¹]`

A wall of the braid arrangement separates two chambers; on the chain side it is a codimension-one
cell entered from both, along one leg crossing and along the other merging.  `wallCrossLoc` is that
cell read in the localization: the crossing leg, then the merging leg inverted.

`topeCross_wallCross`/`topeCross_wallCross_flip` label the two legs `adjT k` and `1` in the
arrangement's order, and `crossPerm_eq_topeCross` carries those labels to the flattening order `W`
is defined by.
-/

open CategoryTheory Equiv Opposite BPSet ChainCat

namespace CubeChains

variable {n : ℕ}

/-- **The leg that crosses is not a merge** — it crosses the `k`-th adjacent pair. -/
theorem not_W_wallLeg (w : Perm (Fin n)) (k : Fin (n - 1)) :
    ¬ W (Hbp.obj (□n)) (wallLeg w k) := fun h =>
  adjT_ne_one k
    ((crossPerm_wallLeg w k).symm.trans
      ((W_iff_crossPerm_eq_one
        (dimSum_of_hbpCubeHom (cellObj (topeCell ⟨wordTope w, isTope_wordTope w⟩)).map)
        (wallLeg w k)).mp h))

/-- The chamber `w`, as an object of the localized decorated chains. -/
noncomputable def chamberLoc (w : Perm (Fin n)) : (W (Hbp.obj (□n))).Localization :=
  (W (Hbp.obj (□n))).Q.obj (cellObj (topeCell ⟨wordTope w, isTope_wordTope w⟩))

/-- **Crossing the `k`-th wall of the chamber `w`**: the crossing leg, then the merging leg
inverted.  The `(w, k)` indexing is the arrangement's own, which is what the comparison is about. -/
noncomputable def wallCrossLoc (w : Perm (Fin n)) (k : Fin (n - 1)) :
    chamberLoc w ⟶ chamberLoc (w * adjT k) :=
  letI hiso : IsIso ((W (Hbp.obj (□n))).Q.map (wallLegFlip w k)) :=
    (W (Hbp.obj (□n))).Q_inverts (wallLegFlip w k) (W_wallLegFlip w k)
  (W (Hbp.obj (□n))).Q.map (wallLeg w k) ≫ @inv _ _ _ _ _ hiso

end CubeChains
