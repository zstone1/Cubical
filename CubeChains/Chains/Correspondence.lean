import CubeChains.Chains.Basic
import CubeChains.Chains.WedgeMap
import CubeChains.Chains.Refine
import CubeChains.Chains.Category

/-!
# The chain ↔ wedge-map correspondence (ClaudeSetup.md §3)

The two constructions of `Chains/WedgeMap.lean` (`wedgeDesc`/`wedgeToCubes`) and
the chain bridge of `Chains/Basic.lean` (`isCubeChain`/`ofIsCubeChain`) assemble
into an equivalence

`equivWedgeHom : CubeChain K ≃ Σ dims, (□^∨(dims) ⟶ K)`.

`left_inv` is direct (reading the cubes back off the descent map recovers them,
and a chain is pinned by its cubes).  `right_inv` then comes for free from
`left_inv` together with injectivity of the inverse map (the wedge's colimit
universal property, `wedgeToCubes_inj`).
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace CubeChain

variable {K : BPSet}

/-- The wedge map classifying a chain (forward map of the §3 correspondence). -/
noncomputable def wedgeOfChain (C : CubeChain K) :
    Σ dims : List ℕ+, (BPSet.serialWedge dims ⟶ K) :=
  ⟨C.dims, wedgeDescHom _ (wedgeDesc _ _ _ (isCubeChain C))⟩

/-- The chain read off a wedge map (inverse map). -/
noncomputable def chainOfWedge (φ : Σ dims : List ℕ+, (BPSet.serialWedge dims ⟶ K)) :
    CubeChain K :=
  ofIsCubeChain (wedgeToCubes ⟨φ.1, φ.2.hom⟩) <| by
    have h := wedgeToCubes_isCubeChain φ.1 φ.2.hom
    rwa [φ.2.app_init, φ.2.app_final] at h

theorem chainOfWedge_wedgeOfChain (C : CubeChain K) : chainOfWedge (wedgeOfChain C) = C := by
  apply eq_of_cubes
  change wedgeToCubes ⟨C.cubes.map (·.1), (wedgeDesc K.init K.final C.cubes (isCubeChain C)).map⟩
    = C.cubes
  exact wedgeToCubes_wedgeDesc K.init K.final C.cubes (isCubeChain C)

theorem chainOfWedge_injective : Function.Injective (chainOfWedge (K := K)) := by
  rintro ⟨dims₁, ψ₁⟩ ⟨dims₂, ψ₂⟩ heq
  have hcubes : wedgeToCubes ⟨dims₁, ψ₁.hom⟩ = wedgeToCubes ⟨dims₂, ψ₂.hom⟩ := by
    have := congrArg CubeChain.cubes heq
    simpa only [chainOfWedge, ofIsCubeChain] using this
  obtain rfl : dims₁ = dims₂ := by
    rw [← wedgeToCubes_dims dims₁ ψ₁.hom, ← wedgeToCubes_dims dims₂ ψ₂.hom, hcubes]
  refine (Sigma.mk.injEq ..).mpr ⟨rfl, heq_of_eq (BPSet.hom_ext ?_)⟩
  exact wedgeToCubes_inj dims₁ ψ₁.hom ψ₂.hom hcubes (by rw [ψ₁.app_init, ψ₂.app_init])

/-- **The map↔chain correspondence (ClaudeSetup.md §3).**  Cube chains in `K` are
exactly bi-pointed maps out of a serial wedge: forward is the descent map
(`wedgeOfChain`), inverse reads the cubes off (`chainOfWedge`). -/
noncomputable def equivWedgeHom (K : BPSet) :
    CubeChain K ≃ Σ dims : List ℕ+, (BPSet.serialWedge dims ⟶ K) where
  toFun := wedgeOfChain
  invFun := chainOfWedge
  left_inv := chainOfWedge_wedgeOfChain
  right_inv φ := chainOfWedge_injective (chainOfWedge_wedgeOfChain (chainOfWedge φ))

/-! ### Lifting `equivWedgeHom` to the categories  [IN PROGRESS, top-down]

We assemble the intended equivalence

`RefineObj K.init K.final ≌ ChainCat.Obj K`

out of two functors.  The **object** maps are exactly the object equivalence
(`wedgeOfChain`/`chainOfWedge`), with no obstruction.  Every obstruction lives in
the **morphism** maps, surfaced below as named `sorry`s with the precise wall. -/

/-- Object part of the forward functor `refine ⥤ wedge`: a chain `↦` its dimension
sequence together with its descent map (this is `wedgeOfChain`, repackaged). -/
noncomputable def refineToWedgeObj (x : RefineObj K.init K.final) : ChainCat.Obj K where
  dims := x.cubes.map (·.1)
  map := wedgeDescHom x.cubes (wedgeDesc K.init K.final x.cubes x.isChain)

/-- The wedge map `□^∨(x.dims) ⟶ □^∨(y.dims)` induced by a refinement `f : x ⟶ y`.

*(Former Obstruction A, now resolved.)*  `ChainRefine` carries the face inclusions
as **data** (`f.incl i : □^{x.dimᵢ} ↪ □^{y.dim_{f i}}`), so this is definable with no
rigidity assumption on `K`: block `i` of `x` includes into block `f i` of `y` by
`yoneda.map (f.incl i)` followed by the `y`-block wedge inclusion, and these assemble
through the wedge's descent — the junctions matching because `f.refinement` is
monotone.  [TODO: assemble it.] -/
noncomputable def refineWedgeMap {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    BPSet.serialWedge (x.cubes.map (·.1)) ⟶ BPSet.serialWedge (y.cubes.map (·.1)) :=
  sorry

/-- The induced wedge map commutes over `K` (the triangle of `ChainCat.Hom`). -/
theorem refineWedgeMap_w {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    refineWedgeMap f ≫ (refineToWedgeObj y).map = (refineToWedgeObj x).map :=
  sorry

/-- The forward functor `refine ⥤ wedge`. -/
noncomputable def refineToWedge (K : BPSet) : RefineObj K.init K.final ⥤ ChainCat.Obj K where
  obj := refineToWedgeObj
  map f := ⟨refineWedgeMap f, refineWedgeMap_w f⟩
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Object part of the backward functor `wedge ⥤ refine`: a wedge map `↦` the cubes
read off it (this is `chainOfWedge`, repackaged). -/
noncomputable def wedgeToRefineObj (a : ChainCat.Obj K) : RefineObj K.init K.final where
  cubes := wedgeToCubes ⟨a.dims, a.map.hom⟩
  isChain := by
    have h := wedgeToCubes_isCubeChain a.dims a.map.hom
    rwa [a.map.app_init, a.map.app_final] at h

/-- **Obstruction B (reindexing).**  The refinement read off a wedge-map morphism
`g : a ⟶ b`.  From `g.φ : □^∨(a.dims) ⟶ □^∨(b.dims)` we must extract *which*
`b`-block each `a`-block lands in (the monotone reindexing) — `g.φ` a priori sends
an `a`-block to an arbitrary cell of `□^∨(b.dims)`, so isolating a single block
index again leans on how `b.map` separates the blocks. -/
noncomputable def wedgeToRefineMap {a b : ChainCat.Obj K} (g : a ⟶ b) :
    wedgeToRefineObj a ⟶ wedgeToRefineObj b :=
  sorry

/-- The backward functor `wedge ⥤ refine`. -/
noncomputable def wedgeToRefine (K : BPSet) : ChainCat.Obj K ⥤ RefineObj K.init K.final where
  obj := wedgeToRefineObj
  map g := wedgeToRefineMap g
  map_id _ := sorry
  map_comp _ _ := sorry

/-- **[IN PROGRESS]** `equivWedgeHom` lifts to an equivalence of categories.  With
`ChainRefine` now carrying the inclusion data, both functors are constructible (no
rigidity assumption needed: distinct wedge maps give distinct inclusions, hence
distinct refinements, so the correspondence is faithful).  Once the two morphism maps
are built, the unit/counit are the object round-trips (`chainOfWedge_wedgeOfChain` and
its inverse), which hold *strictly* — so this is even an isomorphism of categories. -/
noncomputable def equivWedgeCat (K : BPSet) :
    RefineObj K.init K.final ≌ ChainCat.Obj K :=
  sorry

end CubeChain
