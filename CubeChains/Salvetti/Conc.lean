import CubeChains.Salvetti.Flips
import CubeChains.Foundations.FreeGroupoidLift
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory

/-!
# Salvetti/Conc — the positive-braid functor of a complexified chain

`Conc K : FreeGroupoid (Ch⋆ K) ⥤ Braids` is the free-groupoid lift of `ConcPos K = proj K ⋙ Flips`:
the braid a refinement performs depends only on its wedge map and the runs it intertwines, so it
factors through `proj K : Ch⋆ K ⥤ RunWedge` and the `K`-free `Flips` (`Salvetti/Flips`).  This file
is just that pullback, plus the thin `Ch⋆ K`-level names the tope layer reads off `RunWedge`.
-/

open CategoryTheory Opposite BPSet ChainCat CubeChain Equiv

namespace CubeChains

variable {K : BPSet}

/-! ## The refinement's wedge map and its descent triangle

The one piece of genuinely `Ch⋆ K`-level data: the triangle over `K`, which `proj` forgets and
`RunWedge` never sees. -/

/-- The refinement's underlying wedge map (`y → x`, from the `op`). -/
def wedgeOf {x y : Ch⋆ K} (f : x ⟶ y) : ⋁y.chain.dims ⟶ ⋁x.chain.dims := (f.val.unop).φ

/-- The refinement triangle: `y`'s descent factors through `x`'s. -/
theorem wedgeOf_w {x y : Ch⋆ K} (f : x ⟶ y) : wedgeOf f ≫ x.chain.map = y.chain.map :=
  f.val.unop.w

/-! ## The braid data, pulled back from `RunWedge` along `proj`

Everything below is `RunWedge`'s, read at `proj K`; the generic braid bookkeeping (`permCast`,
`braidTransport`, …) is re-exported straight from `Salvetti/Flips`. -/

export RunWedge (permCast permLen_permCast braidTransport braidTransport_ofPerm eqToHom_comp_braidHom)

/-- The atomic events of a complexified chain. -/
def Nev (x : Ch⋆ K) : ℕ := RunWedge.Nev ((proj K).obj x)

/-- Refinement preserves the event count. -/
theorem Nev_eq {x y : Ch⋆ K} (f : x ⟶ y) : Nev x = Nev y := RunWedge.Nev_eq ((proj K).map f)

/-- The recoordinatization `beadEvent y ≃ beadEvent x` induced by the refinement. -/
def eventEquiv {x y : Ch⋆ K} (f : x ⟶ y) :
    beadEvent y.chain.dims ≃ beadEvent x.chain.dims :=
  RunWedge.eventEquiv ((proj K).map f)

theorem eventEquiv_apply {x y : Ch⋆ K} (f : x ⟶ y) (e : beadEvent y.chain.dims) :
    eventEquiv f e = coordMap (wedgeOf f) e :=
  RunWedge.eventEquiv_apply ((proj K).map f) e

theorem runProj_dims_length (x : Ch⋆ K) (i : Fin x.chain.dims.length) :
    (runProj x.run i).chain.dims.length = (x.chain.dims.get i : ℕ) :=
  RunWedge.runProj_dims_length ((proj K).obj x) i

/-- The run's rank: events ordered bead-by-bead, then within each bead by its local run. -/
def rankEquiv (x : Ch⋆ K) : beadEvent x.chain.dims ≃ Fin (Nev x) :=
  RunWedge.rankEquiv ((proj K).obj x)

theorem rankEquiv_val (x : Ch⋆ K) (i : Fin x.chain.dims.length) (k : Fin (x.chain.dims.get i : ℕ)) :
    (rankEquiv x ⟨i, k⟩ : ℕ)
      = (∑ j : Fin (i : ℕ), (x.chain.dims.get (Fin.castLE i.2.le j) : ℕ))
        + (beadOf (runProj x.run i).chain k : ℕ) :=
  RunWedge.rankEquiv_val ((proj K).obj x) i k

/-- The reordering from `x`'s run order to `y`'s, before regrading. -/
def rawPerm {x y : Ch⋆ K} (f : x ⟶ y) : Fin (Nev x) ≃ Fin (Nev y) :=
  RunWedge.rawPerm ((proj K).map f)

theorem rawPerm_rankEquiv {x y : Ch⋆ K} (f : x ⟶ y) (e : beadEvent x.chain.dims) :
    rawPerm f (rankEquiv x e) = rankEquiv y ((eventEquiv f).symm e) :=
  RunWedge.rawPerm_rankEquiv ((proj K).map f) e

/-- The crossing permutation of a refinement.  Spelled in its `.trans` form (defeq to
`RunWedge.permOf (proj f)`) so the tope layer can unfold it directly. -/
def permOf {x y : Ch⋆ K} (f : x ⟶ y) : Equiv.Perm (Fin (Nev x)) :=
  (rawPerm f).trans (finCongr (Nev_eq f)).symm

/-- Length-additivity: each pair of events crosses at most once. -/
theorem permOf_noDoubleCross {x y z : Ch⋆ K} (f : x ⟶ y) (g : y ⟶ z) :
    permLen (permOf (f ≫ g)) = permLen (permOf f) + permLen (permOf g) := by
  have h := RunWedge.permOf_noDoubleCross ((proj K).map f) ((proj K).map g)
  rwa [← (proj K).map_comp] at h

/-! ## The braid functor -/

/-- The graded braid functor: `proj` into the `K`-free braid, then `Flips`. -/
def ConcPos (K : BPSet) : Ch⋆ K ⥤ Braids := proj K ⋙ Flips

/-- The concurrency braid functor: the free-groupoid lift of `ConcPos`. -/
noncomputable def Conc (K : BPSet) : FreeGroupoid (Ch⋆ K) ⥤ Braids :=
  FreeGroupoid.lift (ConcPos K)

end CubeChains
