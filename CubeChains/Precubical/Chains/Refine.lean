import CubeChains.Precubical.Chains.Basic

/-!
# Precubical/Chains/Refine

A *refinement* of a cube chain replaces each cube `cᵢ` by a sub-chain `p₁, …, p_j`
of its faces — so the finer chain `x` has each cube a face of a cube of the coarser
chain `y`, the two sharing endpoints `a`, `b`.  This is Ziemiański's subdivision
relation on `Ch(K)`.

`ChainRefine a b x y`: a monotone reindexing `x`-cubes ↦ `y`-cubes, **together with the
inclusion data** realising each `x`-cube as a face of its `y`-cube — an explicit `Box`
morphism `□^{x.dimᵢ} ↪ □^{y.dim_{f i}}` (every `Box` morphism *is* a cube face) pulling
the `y`-cube back to the `x`-cube.  Carrying the inclusion as *data* (rather than the mere
`Prop` that a face relation holds) is what makes the forward functor to wedge maps
definable without rigidity assumptions on `K`; see `Precubical/Chains/Correspondence.lean`.

`ChainRefine` organises chains into a `Category` (`refineCategory`): identity is the
trivial refinement (every cube included into itself by `𝟙`), composition composes
the reindexings and the inclusions.
-/

open CategoryTheory Opposite

namespace CubeChain

variable {K : BPSet}

/-- An object of the refinement category: a cube chain from `a` to `b`, carrying its shape. -/
structure RefineObj (a b : K.cells 0) where
  /-- The dimension sequence. -/
  dims : List ℕ+
  /-- The cubes of the chain, indexed by the shape. -/
  cubes : Beads K.toPsh dims
  /-- The proof that they form a chain from `a` to `b`. -/
  isChain : IsCubeChain a cubes.toList b

/-- A *refinement* `x ⟶ y`: a monotone reindexing of `x`'s beads into `y`'s beads, with, for
each `x`-bead, an explicit standard-cube inclusion `□^{x.dimᵢ} ↪ □^{y.dim_{f i}}` pulling the
`y`-cube back to it (`inclSpec`).  (`x` is a subdivision of `y`.) -/
structure ChainRefine {a b : K.cells 0} (x y : RefineObj a b) where
  /-- The reindexing of `x`-beads into `y`-beads. -/
  refinement : Fin x.dims.length → Fin y.dims.length
  /-- The reindexing is monotone (refinements preserve the order along the chain). -/
  refinementMono : Monotone refinement
  /-- The face inclusion `□^{x.dimᵢ} ↪ □^{y.dim_{f i}}` of standard cubes. -/
  incl : ∀ i : Fin x.dims.length, ▫((x.dims.get i : ℕ)) ⟶ ▫((y.dims.get (refinement i) : ℕ))
  /-- Pulling the `y`-cube back along the inclusion gives the `x`-cube. -/
  inclSpec : ∀ i : Fin x.dims.length, x.cubes i = K.toPsh.map (incl i).op (y.cubes (refinement i))

/-- A refinement is determined by its reindexing map together with its inclusion
data (the conditions are `Prop`s). -/
theorem ChainRefine.ext {a b : K.cells 0} {x y : RefineObj a b} {f g : ChainRefine x y}
    (hr : f.refinement = g.refinement) (hi : HEq f.incl g.incl) : f = g := by
  obtain ⟨rf, _, incf, _⟩ := f
  obtain ⟨rg, _, incg, _⟩ := g
  obtain rfl : rf = rg := hr
  obtain rfl : incf = incg := eq_of_heq hi
  rfl

/-- **The refinement category** of chains from `a` to `b`: objects are chains,
morphisms are refinements (subdivisions).  Identity includes every cube into itself
by `𝟙`; composition composes both the reindexings and the cube inclusions, the
`inclSpec` following from functoriality of `K.toPsh`. -/
instance refineCategory (a b : K.cells 0) : Category (RefineObj a b) where
  Hom x y := ChainRefine x y
  id x :=
    { refinement := id
      refinementMono := fun _ _ h => h
      incl := fun _ => 𝟙 _
      inclSpec := fun _ => (K.toPsh.map_id_apply _ _).symm }
  comp f g :=
    { refinement := g.refinement ∘ f.refinement
      refinementMono := g.refinementMono.comp f.refinementMono
      incl := fun i => f.incl i ≫ g.incl (f.refinement i)
      inclSpec := fun i => by
        rw [f.inclSpec i, g.inclSpec (f.refinement i), op_comp, Functor.map_comp,
          types_comp_apply]
        rfl }
  id_comp _ := ChainRefine.ext rfl (heq_of_eq (funext fun _ => Category.id_comp _))
  comp_id _ := ChainRefine.ext rfl (heq_of_eq (funext fun _ => Category.comp_id _))
  assoc _ _ _ := ChainRefine.ext rfl (heq_of_eq (funext fun _ => Category.assoc _ _ _))

end CubeChain
