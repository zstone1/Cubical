import CubeChains.Concurrency.Executions.Runs
import CubeChains.Precubical.Basic.Terminal

/-!
# Concurrency/Executions/RunWedgeZ — `RunWedge` is the executions of the terminal precubical set

`Zbp` (`Precubical/Basic/Terminal`) is terminal in `BPSet`: a wedge maps into it uniquely, so a
chain of `Zbp` *is* just its wedge and a run of `Zbp` is just a run.  Hence `proj Zbp : Ch⋆ Zbp ⥤
RunWedge` is an equivalence — the coordinate labelling that makes `proj □n` non-full collapses
precisely because `Hom(-, Zbp)` is a singleton.  So `RunWedge = Ch⋆ Zbp` and the braid on
`RunWedge` is `Conc` at the terminal object: the full braid group, not just the pure part.

The inverse `chStarZbpFunctor` is built by hand (`Equivalence.mk`) rather than through the
choice-based `Functor.asEquivalence`, so the equivalence computes: `chStarZbp` is a definitional
section (`proj ∘ chStarZbp = id` on the nose, counit `Iso.refl`) and terminality supplies the unit
`chStarZbp ∘ proj ≅ id`.
-/

open CategoryTheory Opposite Limits CategoryOfElements

namespace CubeChains

/-- The execution of `Zbp` over a `RunWedge`: the wedge with its (forced) map to `Zbp`, same run. -/
def chStarZbp (W : RunWedge) : Ch⋆ Zbp := ⟨op ⟨W.dims, default⟩, W.cls⟩

@[simp] theorem proj_chStarZbp (W : RunWedge) : (proj Zbp).obj (chStarZbp W) = W := rfl

/-- **Inverse to `proj Zbp`**: read a run-wedge back as a chain of the terminal object.  The map to
`Zbp` is forced (`Subsingleton.elim`), the wedge and run kept. -/
def chStarZbpFunctor : RunWedge ⥤ Ch⋆ Zbp where
  obj := chStarZbp
  map {W W'} g := homMk _ _ (Quiver.Hom.op ⟨g.1, Subsingleton.elim _ _⟩) g.2
  map_id _ := CategoryOfElements.ext _ _ _ (Quiver.Hom.unop_inj (ChainCat.hom_ext' rfl))
  map_comp _ _ := CategoryOfElements.ext _ _ _ (Quiver.Hom.unop_inj (ChainCat.hom_ext' rfl))

/-- `proj Zbp` keeps a morphism's wedge map and drops only propositions, so it is faithful. -/
instance : (proj Zbp).Faithful where
  map_injective {x y} {f g} h :=
    CategoryOfElements.ext _ f g
      (Quiver.Hom.unop_inj (ChainCat.hom_ext' (congrArg Subtype.val h)))

/-- The round trip `chStarZbp ∘ proj = id`: same wedge and run, and the two maps to the terminal
`Zbp` agree (`Subsingleton.elim`). -/
theorem chStarZbp_proj (X : Ch⋆ Zbp) : chStarZbp ((proj Zbp).obj X) = X :=
  congrArg (fun m : ⋁X.chain.dims ⟶ Zbp => (⟨op ⟨X.chain.dims, m⟩, X.2⟩ : Ch⋆ Zbp))
    (Subsingleton.elim default X.chain.map)

/-- **`RunWedge` is the concurrency-braid domain of the terminal precubical set**, `Ch⋆ Zbp`. -/
def runWedgeEquivChStarZbp : Ch⋆ Zbp ≌ RunWedge :=
  .mk (proj Zbp) chStarZbpFunctor
    (NatIso.ofComponents (fun X => eqToIso (chStarZbp_proj X).symm))
    (Iso.refl _)

/-! ## Decomplexification `Ch⋆ K ⥤ (Ch Zbp)ᵒᵖ` -/

/-- **Decomplexification**: forget the run (`CategoryOfElements.π`) and push the chain to the
terminal object.  A refinement keeps its wedge map; only the run and the map to `K` are dropped. -/
def toChainZ (K : BPSet) : Ch⋆ K ⥤ (Ch Zbp)ᵒᵖ :=
  CategoryOfElements.π (Lines K) ⋙ (ChainCat.pushforward (isTerminalZbp.from K)).op

/-- A refinement is determined by its wedge map over `Z`: dropping the run and the map to `K` loses
no *morphism* data (both are propositions). -/
instance (K : BPSet) : (toChainZ K).Faithful where
  map_injective {x y} {f g} h :=
    CategoryOfElements.ext _ f g
      (Quiver.Hom.unop_inj (ChainCat.hom_ext' (congrArg (fun t => (Opposite.unop t).φ) h)))

end CubeChains
