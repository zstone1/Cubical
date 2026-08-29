import CubeChains.Foundations.SymRepresentable
import CubeChains.Salvetti.ChStarSym

/-!
# Salvetti/SymOverRun — `H K` lies over the runs, and over nothing else

`H` applied to the terminal map `K ⟶ Z`, followed by `HZIsoRun`, is a natural `H K ⟶ runBp`: an
`H`-cell's order *is* a run.  There is no companion `H K ⟶ K` — at `K = □ⁿ` with `n ≥ 2` there is
no such map at all (`isEmpty_cubeHom`).  So `H (□ⁿ)` lies over `runBp` only, whereas
`(□ⁿ).prod runBp` lies over both factors, via `prodFst` and `prodSnd`; that missing `prodFst` is
what leaves `H` room for a reorientation the product cannot carry.
-/

open CategoryTheory Opposite BPSet

namespace CubeChains

/-- **`H` lies over the run presheaf** — an `H`-cell's order is a run of its axes. -/
def HOverRun : H ⟶ (Functor.const PrecubicalSet).obj runPresheaf where
  app K := H.map (toZ K) ≫ HZIsoRun.hom
  naturality K L f := by
    rw [Functor.const_obj_map, ← Category.assoc, ← H.map_comp,
      isTerminalZ.hom_ext (f ≫ toZ L) (toZ K)]
    exact (Category.comp_id _).symm

/-- …bi-pointedly too: `runBp` has a single vertex, so the pointing is forced. -/
def HbpOverRun : Hbp ⟶ (Functor.const BPSet).obj runBp where
  app K := (homEquivPsh (Hbp.obj K) runBp).symm (HOverRun.app K.toPsh)
  naturality _ _ f := hom_ext (HOverRun.naturality f.hom)

/-- **No cell projection off `H (□²)`, even into the product** — a map into `K.prod runBp` has a
`K`-component, and that one does not exist. -/
instance isEmpty_cubeProdHom : IsEmpty (H.obj (□2).toPsh ⟶ ((□2).prod runBp).toPsh) :=
  ⟨fun ψ => IsEmpty.false (ψ ≫ (prodFst (□2) runBp).hom)⟩

instance : IsEmpty (Hbp.obj (□2) ⟶ (□2).prod runBp) :=
  ⟨fun f => isEmpty_cubeProdHom.false f.hom⟩

end CubeChains
