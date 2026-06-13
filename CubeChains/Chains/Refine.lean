import CubeChains.Chains.Basic

/-!
# The refinement (subdivision) category of cube chains

A *refinement* of a cube chain replaces each cube `cᵢ` by a sub-chain `p₁, …, p_j`
of its faces — so the finer chain `x` has each cube a face of a cube of the coarser
chain `y`, the two sharing endpoints `a`, `b`.  This is Ziemiański's subdivision
relation on `Ch(K)`.

We record it as `ChainRefine a b x y`: a monotone reindexing `x`-cubes ↦ `y`-cubes,
**together with the inclusion data** realising each `x`-cube as a face of its
`y`-cube — an explicit `Box` morphism `□^{x.dimᵢ} ↪ □^{y.dim_{f i}}` (every `Box`
morphism *is* a cube face) pulling the `y`-cube back to the `x`-cube.  Carrying the
inclusion as *data* (rather than the mere `Prop` that a face relation holds) is what
makes the forward functor to wedge maps definable without rigidity assumptions on
`K`; see `Chains/Correspondence.lean`.

`ChainRefine` organises chains into a `Category` (`refineCategory`): identity is the
trivial refinement (every cube included into itself by `𝟙`), composition composes
the reindexings and the inclusions.
-/

open CategoryTheory Opposite

namespace CubeChain

variable {K : BPSet}

/-- A *refinement* of chains from `a` to `b`: a monotone reindexing of `x`'s cubes
into `y`'s cubes, with, for each `x`-cube, an explicit standard-cube inclusion
`□^{x.dimᵢ} ↪ □^{y.dim_{f i}}` pulling the `y`-cube back to it (`inclSpec`).  (`x` is
a subdivision of `y`.) -/
structure ChainRefine (a b : K.toPsh.cells 0)
    (x y : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))) where
  /-- `x` is a chain from `a` to `b`. -/
  chainx : IsCubeChain a x b
  /-- `y` is a chain from `a` to `b`. -/
  chainy : IsCubeChain a y b
  /-- The reindexing of `x`-cubes into `y`-cubes. -/
  refinement : Fin x.length → Fin y.length
  /-- The reindexing is monotone (refinements preserve the order along the chain). -/
  refinementMono : ∀ i j : Fin x.length, i ≤ j → refinement i ≤ refinement j
  /-- The face inclusion `□^{x.dimᵢ} ↪ □^{y.dim_{f i}}` of standard cubes. -/
  incl : ∀ i : Fin x.length,
    Box.ob ((x.get i).1 : ℕ) ⟶ Box.ob ((y.get (refinement i)).1 : ℕ)
  /-- Pulling the `y`-cube back along the inclusion gives the `x`-cube. -/
  inclSpec : ∀ i : Fin x.length,
    (x.get i).2 = K.toPsh.map (incl i).op (y.get (refinement i)).2

/-- A refinement is determined by its reindexing map together with its inclusion
data (the chain proofs and the conditions are `Prop`s). -/
theorem ChainRefine.ext {a b : K.toPsh.cells 0}
    {x y : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))} {f g : ChainRefine a b x y}
    (hr : f.refinement = g.refinement) (hi : HEq f.incl g.incl) : f = g := by
  obtain ⟨_, _, rf, _, incf, _⟩ := f
  obtain ⟨_, _, rg, _, incg, _⟩ := g
  obtain rfl : rf = rg := hr
  obtain rfl : incf = incg := eq_of_heq hi
  rfl

/-- An object of the refinement category: a cube chain from `a` to `b`. -/
structure RefineObj (a b : K.toPsh.cells 0) where
  /-- The cubes of the chain. -/
  cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))
  /-- The proof that they form a chain from `a` to `b`. -/
  isChain : IsCubeChain a cubes b

/-- **The refinement category** of chains from `a` to `b`: objects are chains,
morphisms are refinements (subdivisions).  Identity includes every cube into itself
by `𝟙`; composition composes both the reindexings and the cube inclusions, the
`inclSpec` following from functoriality of `K.toPsh`. -/
instance refineCategory (a b : K.toPsh.cells 0) : Category (RefineObj a b) where
  Hom x y := ChainRefine a b x.cubes y.cubes
  id x :=
    { chainx := x.isChain
      chainy := x.isChain
      refinement := id
      refinementMono := fun _ _ h => h
      incl := fun _ => 𝟙 _
      inclSpec := fun _ => (K.toPsh.map_id_apply _ _).symm }
  comp f g :=
    { chainx := f.chainx
      chainy := g.chainy
      refinement := g.refinement ∘ f.refinement
      refinementMono := fun i j h => g.refinementMono _ _ (f.refinementMono i j h)
      incl := fun i => f.incl i ≫ g.incl (f.refinement i)
      inclSpec := fun i => by
        rw [f.inclSpec i, g.inclSpec (f.refinement i), op_comp, Functor.map_comp,
          types_comp_apply]
        rfl }
  id_comp _ := ChainRefine.ext rfl (heq_of_eq (funext fun _ => Category.id_comp _))
  comp_id _ := ChainRefine.ext rfl (heq_of_eq (funext fun _ => Category.comp_id _))
  assoc _ _ _ := ChainRefine.ext rfl (heq_of_eq (funext fun _ => Category.assoc _ _ _))

end CubeChain
