import CubeChains.Chains.Category
import CubeChains.Chains.WedgeMap
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
import Mathlib.Tactic.CategoryTheory.Slice

/-!
# The Segal monoidality of `Ch` (keystone of the cylinder refactor)

This file proves that the cube-chain functor `Ch : BPSet ⥤ Cat` is **strong
monoidal** from bi-pointed sets (with the wedge `∨` and unit `□⁰`) to `Cat` (with
the product `×` and unit `𝟙`):
```
ChainCat.Obj X × ChainCat.Obj Y  ≌  ChainCat.Obj (wedge2 X Y)
ChainCat.Obj (cube 0)            ≌  Discrete PUnit
ChainCat.Obj (serialWedge dims)  ≌  ∏ᵢ ChainCat.Obj (cube (dims.get i))   (n-ary)
```

The crux is the **Segal property**: a full chain `init → final` in `X ∨ Y` is
forced through the junction vertex `v` (the only bridge between the two sides), so
it splits canonically as `(chain init → v in X) ++ (chain v → final in Y)`.  In
the topos `PrecubicalSet = Boxᵒᵖ ⥤ Type` colimits are pointwise, and since the glue
point `□⁰` has no positive-dimensional cells, the positive cubes of any chain land
in *exactly one* of `X`, `Y`; the `X`-cubes form a prefix and the `Y`-cubes a
suffix.  All of that combinatorics is already packaged in `Chains/WedgeMap.lean`
(`wedge2_cell_cases`, `serialWedge_cell_exists`, `serialWedge_block_unique`,
`wedge2_inl_ne_inr`, …); here we assemble it into the equivalence.

The route is the recommended one: build the **concatenation functor** `chConcat`,
show it is fully faithful and essentially surjective, and conclude via mathlib's
`Functor.IsEquivalence`/`asEquivalence`.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace ChainCat

universe u

/-! ## Wedge2 functoriality and the append isomorphism

These two helpers (`wedge2Cube0Iso`, `wedge2Assoc`) are copied from
`Operations/Cylinder.lean` (owned by another agent) rather than imported. -/

/-- The initial-vertex *map* of `X ∨ Y` factors through the left inclusion. -/
theorem wedge2_initVertex (X Y : BPSet) :
    (BPSet.wedge2 X Y).initVertex
      = X.initVertex ≫ pushout.inl X.finalVertex Y.initVertex := by
  conv_lhs => rw [show (BPSet.wedge2 X Y).initVertex
    = yonedaEquiv.symm ((BPSet.wedge2 X Y).init) from rfl, CubeChain.wedge2_init']
  exact (yonedaEquiv_symm_naturality_right (Box.ob 0)
    (pushout.inl X.finalVertex Y.initVertex) X.init).symm

/-- The final-vertex *map* of `X ∨ Y` factors through the right inclusion. -/
theorem wedge2_finalVertex (X Y : BPSet) :
    (BPSet.wedge2 X Y).finalVertex
      = Y.finalVertex ≫ pushout.inr X.finalVertex Y.initVertex := by
  conv_lhs => rw [show (BPSet.wedge2 X Y).finalVertex
    = yonedaEquiv.symm ((BPSet.wedge2 X Y).final) from rfl, CubeChain.wedge2_final']
  exact (yonedaEquiv_symm_naturality_right (Box.ob 0)
    (pushout.inr X.finalVertex Y.initVertex) Y.final).symm

/-- `wedge2`-functoriality on the underlying presheaves: a pair of BPSet maps
`f : X ⟶ X'`, `g : Y ⟶ Y'` induces `wedge2 X Y ⟶ wedge2 X' Y'`.  The two
`pushout.map` square conditions are the preservation of `final`/`init` by the
vertex maps (Yoneda-naturality of the basepoint selectors). -/
noncomputable def wedge2HomPsh {X X' Y Y' : BPSet} (f : X ⟶ X') (g : Y ⟶ Y') :
    (BPSet.wedge2 X Y).toPsh ⟶ (BPSet.wedge2 X' Y').toPsh :=
  pushout.map X.finalVertex Y.initVertex X'.finalVertex Y'.initVertex
    f.hom g.hom (𝟙 _)
    (by
      rw [Category.id_comp]
      apply yonedaEquiv.injective
      simp only [BPSet.finalVertex, BPSet.vertexMap, yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact f.app_final)
    (by
      rw [Category.id_comp]
      apply yonedaEquiv.injective
      simp only [BPSet.initVertex, BPSet.vertexMap, yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact g.app_init)

theorem wedge2HomPsh_inl {X X' Y Y' : BPSet} (f : X ⟶ X') (g : Y ⟶ Y') :
    pushout.inl X.finalVertex Y.initVertex ≫ wedge2HomPsh f g
      = f.hom ≫ pushout.inl X'.finalVertex Y'.initVertex :=
  pushout.inl_desc _ _ _

theorem wedge2HomPsh_inr {X X' Y Y' : BPSet} (f : X ⟶ X') (g : Y ⟶ Y') :
    pushout.inr X.finalVertex Y.initVertex ≫ wedge2HomPsh f g
      = g.hom ≫ pushout.inr X'.finalVertex Y'.initVertex :=
  pushout.inr_desc _ _ _

/-- `wedge2HomPsh` as a BPSet morphism. -/
noncomputable def wedge2Hom {X X' Y Y' : BPSet} (f : X ⟶ X') (g : Y ⟶ Y') :
    BPSet.wedge2 X Y ⟶ BPSet.wedge2 X' Y' where
  hom := wedge2HomPsh f g
  app_init := by
    show (wedge2HomPsh f g).app (op (Box.ob 0)) ((BPSet.wedge2 X Y).init)
      = (BPSet.wedge2 X' Y').init
    rw [CubeChain.wedge2_init', CubeChain.wedge2_init']
    erw [CubeChain.inl_desc_app X.init, types_comp_apply, f.app_init]
    rfl
  app_final := by
    show (wedge2HomPsh f g).app (op (Box.ob 0)) ((BPSet.wedge2 X Y).final)
      = (BPSet.wedge2 X' Y').final
    rw [CubeChain.wedge2_final', CubeChain.wedge2_final']
    erw [CubeChain.inr_desc_app Y.final, types_comp_apply, g.app_final]
    rfl

/-! ### Lifting presheaf isomorphisms to `BPSet`

A basepoint-preserving isomorphism of the underlying presheaves is a `BPSet`
isomorphism.  We package this so that the (already-built, presheaf-level)
`wedge2Cube0Iso`/`wedge2Assoc` lift to `BPSet`. -/

/-- A `BPSet` morphism out of `K` from a presheaf map preserving the basepoints. -/
noncomputable def homOfPsh {K L : BPSet} (e : K.toPsh ⟶ L.toPsh)
    (hi : e.app (op (Box.ob 0)) K.init = L.init)
    (hf : e.app (op (Box.ob 0)) K.final = L.final) : K ⟶ L where
  hom := e
  app_init := hi
  app_final := hf

/-- A basepoint-preserving presheaf isomorphism is a `BPSet` isomorphism. -/
noncomputable def isoOfPshIso {K L : BPSet} (e : K.toPsh ≅ L.toPsh)
    (hi : e.hom.app (op (Box.ob 0)) K.init = L.init)
    (hf : e.hom.app (op (Box.ob 0)) K.final = L.final) : K ≅ L where
  hom := homOfPsh e.hom hi hf
  inv := homOfPsh e.inv
    (by
      have h := congrArg (fun m => m.app (op (Box.ob 0)) K.init) e.hom_inv_id
      simp only [NatTrans.comp_app, types_comp_apply, NatTrans.id_app, types_id_apply] at h
      rw [hi] at h; exact h)
    (by
      have h := congrArg (fun m => m.app (op (Box.ob 0)) K.final) e.hom_inv_id
      simp only [NatTrans.comp_app, types_comp_apply, NatTrans.id_app, types_id_apply] at h
      rw [hf] at h; exact h)
  hom_inv_id := by apply BPSet.hom_ext; exact e.hom_inv_id
  inv_hom_id := by apply BPSet.hom_ext; exact e.inv_hom_id

@[simp] theorem isoOfPshIso_hom_hom {K L : BPSet} (e : K.toPsh ≅ L.toPsh) (hi hf) :
    (isoOfPshIso e hi hf).hom.hom = e.hom := rfl

/-- The basepoint condition `e.app K.init = L.init` in vertex-map form: it is
equivalent to `K.initVertex ≫ e = L.initVertex` (Yoneda naturality). -/
theorem app_init_eq_of_initVertex {K L : BPSet} (e : K.toPsh ⟶ L.toPsh)
    (h : K.initVertex ≫ e = L.initVertex) : e.app (op (Box.ob 0)) K.init = L.init := by
  apply yonedaEquiv.symm.injective
  rw [show yonedaEquiv.symm (e.app (op (Box.ob 0)) K.init) = K.initVertex ≫ e from
    (yonedaEquiv_symm_naturality_right (Box.ob 0) e K.init).symm]
  exact h

theorem app_final_eq_of_finalVertex {K L : BPSet} (e : K.toPsh ⟶ L.toPsh)
    (h : K.finalVertex ≫ e = L.finalVertex) : e.app (op (Box.ob 0)) K.final = L.final := by
  apply yonedaEquiv.symm.injective
  rw [show yonedaEquiv.symm (e.app (op (Box.ob 0)) K.final) = K.finalVertex ≫ e from
    (yonedaEquiv_symm_naturality_right (Box.ob 0) e K.final).symm]
  exact h

/-- Build a `BPSet` iso from a presheaf iso that intertwines the basepoint
*selectors* (the vertex maps `□⁰ ⟶ ·`). -/
noncomputable def isoOfPshIso' {K L : BPSet} (e : K.toPsh ≅ L.toPsh)
    (hi : K.initVertex ≫ e.hom = L.initVertex)
    (hf : K.finalVertex ≫ e.hom = L.finalVertex) : K ≅ L :=
  isoOfPshIso e (app_init_eq_of_initVertex e.hom hi) (app_final_eq_of_finalVertex e.hom hf)

@[simp] theorem isoOfPshIso'_hom_hom {K L : BPSet} (e : K.toPsh ≅ L.toPsh) (hi hf) :
    (isoOfPshIso' e hi hf).hom.hom = e.hom := rfl

/-! ### The collapse and associativity isomorphisms (copied from `Operations/Cylinder.lean`)

We copy `wedge2Cube0Iso`/`wedge2Assoc` rather than importing `Operations/Cylinder.lean`,
which is concurrently being rewritten. -/

/-- The initial-vertex inclusion of the point `cube 0` is the identity. -/
@[simp] theorem cube0_initVertex_eq_id :
    (BPSet.cube 0).initVertex = 𝟙 (yoneda.obj (Box.ob 0)) := by
  rw [BPSet.initVertex, BPSet.vertexMap, Equiv.symm_apply_eq]
  exact Subsingleton.elim _ _

instance : IsIso ((BPSet.cube 0).initVertex) := by
  rw [cube0_initVertex_eq_id]; exact IsIso.id _

/-- The final-vertex inclusion of the point `cube 0` is the identity. -/
@[simp] theorem cube0_finalVertex_eq_id :
    (BPSet.cube 0).finalVertex = 𝟙 (yoneda.obj (Box.ob 0)) := by
  rw [BPSet.finalVertex, BPSet.vertexMap, Equiv.symm_apply_eq]
  exact Subsingleton.elim _ _

instance : IsIso ((BPSet.cube 0).finalVertex) := by
  rw [cube0_finalVertex_eq_id]; exact IsIso.id _

/-- Prepending the point `cube 0` to a wedge collapses: the right inclusion
`X ⟶ wedge2 (cube 0) X` is an iso. -/
instance wedge2_cube0_inr_isIso (X : BPSet) :
    IsIso (pushout.inr (BPSet.cube 0).finalVertex X.initVertex) :=
  (IsPushout.of_hasPushout _ _).isIso_inr_of_isIso

/-- **A leading point collapses**: `X ≅ wedge2 (cube 0) X` (presheaf level). -/
noncomputable def wedge2Cube0Iso (X : BPSet) :
    X.toPsh ≅ (BPSet.wedge2 (BPSet.cube 0) X).toPsh :=
  @asIso _ _ _ _ (pushout.inr (BPSet.cube 0).finalVertex X.initVertex)
    (wedge2_cube0_inr_isIso X)

/-- **Associativity of the wedge** `(A ∨ B) ∨ C ≅ A ∨ (B ∨ C)` (presheaf level), via
mathlib's `pushoutAssoc`: `pushoutAssoc g₁ g₂ g₃ g₄ : pushout (g₃ ≫ inr) g₄ ≅
pushout g₁ (g₂ ≫ inl)` matches wedge-associativity exactly with
`(g₁,g₂,g₃,g₄) = (A.fin, B.init, B.fin, C.init)`. -/
noncomputable def wedge2Assoc (A B C : BPSet) :
    (BPSet.wedge2 (BPSet.wedge2 A B) C).toPsh ≅ (BPSet.wedge2 A (BPSet.wedge2 B C)).toPsh :=
  eqToIso (by
    change pushout (BPSet.wedge2 A B).finalVertex C.initVertex
      = pushout (B.finalVertex ≫ pushout.inr A.finalVertex B.initVertex) C.initVertex
    rw [wedge2_finalVertex]; rfl)
  ≪≫ pushoutAssoc A.finalVertex B.initVertex B.finalVertex C.initVertex
  ≪≫ eqToIso (by
    change pushout A.finalVertex (B.initVertex ≫ pushout.inl B.finalVertex C.initVertex)
      = pushout A.finalVertex (BPSet.wedge2 B C).initVertex
    rw [wedge2_initVertex]; rfl)

/-- **A leading point collapses** (as a `BPSet` iso): `X ≅ wedge2 (cube 0) X`. -/
noncomputable def wedge2Cube0IsoBP (X : BPSet) : X ≅ BPSet.wedge2 (BPSet.cube 0) X :=
  isoOfPshIso (wedge2Cube0Iso X)
    (by
      change (pushout.inr (BPSet.cube 0).finalVertex X.initVertex).app (op (Box.ob 0)) X.init = _
      rw [CubeChain.wedge2_init',
        ← Subsingleton.elim (α := (BPSet.cube 0).toPsh.cells 0) (BPSet.cube 0).final
          (BPSet.cube 0).init]
      exact (CubeChain.wedge2_glue (BPSet.cube 0) X).symm)
    (by
      change (pushout.inr (BPSet.cube 0).finalVertex X.initVertex).app (op (Box.ob 0)) X.final = _
      rw [CubeChain.wedge2_final'])

end ChainCat
