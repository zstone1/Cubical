import CubeChains.Flow.ChainConcat
import CubeChains.Foundations.FreeGroupoidLift
import Mathlib.CategoryTheory.Bicategory.CatEnriched

/-!
# Flow/Fund — the fundamental 2-category of `K`, as a `Cat`-enriched category

    0-cells  vertices of `K`
    1-cells  cube chains
    2-cells  zigzags of refinements

This is `CFund` with the **line deleted**.  Everything that made `CFund` hard lived in the lines
(`linesRestrict_chConcMor`); the chain half is `Flow/ChainConcat`, which already has
`chConc_assoc`, `chConc_id_left`/`_right` and their morphism counterparts.

The hom-object is a groupoid on `(Ch (K;u,v))ᵒᵖ` — the *opposite*, because `ConcCat` is the category
of elements of a presheaf on `Ch`, so `Fund`'s hom-groupoid is what `CFund`'s projects onto
(`concProj`, `Braid/Purity`).  Composition is concatenation, and it is strict for the same reason:
`List.append` is.
-/

open CategoryTheory Opposite BPSet

namespace CubeChains

variable {K : BPSet}

/-! ## Concatenation of chains, read on the opposite category -/

/-- **Concatenation of chains** on `(Ch)ᵒᵖ` — the hom-object's composition law before
groupoidification. -/
noncomputable def chConcatOp (K : BPSet) (u v w : K.cells 0) :
    (Ch (K.repoint u v))ᵒᵖ × (Ch (K.repoint v w))ᵒᵖ ⥤ (Ch (K.repoint u w))ᵒᵖ where
  obj p := op (chConc p.1.unop p.2.unop)
  map {p q} fg := (chConcMor fg.1.unop fg.2.unop).op
  map_id p := congrArg Quiver.Hom.op (chConcMor_id p.1.unop p.2.unop)
  map_comp {p q r} fg gh :=
    congrArg Quiver.Hom.op
      (chConcMor_comp (gh.1.unop) (fg.1.unop) (gh.2.unop) (fg.2.unop))

/-! ## The three laws, on objects and on morphisms -/

theorem chConcatOp_obj_assoc (K : BPSet) (u v w x : K.cells 0)
    (a : (Ch (K.repoint u v))ᵒᵖ) (b : (Ch (K.repoint v w))ᵒᵖ) (c : (Ch (K.repoint w x))ᵒᵖ) :
    (chConcatOp K u w x).obj ((chConcatOp K u v w).obj (a, b), c)
      = (chConcatOp K u v x).obj (a, (chConcatOp K v w x).obj (b, c)) :=
  congrArg op (chConc_assoc a.unop b.unop c.unop)

theorem chConcatOp_obj_id_left (K : BPSet) (u v : K.cells 0) (b : (Ch (K.repoint u v))ᵒᵖ) :
    (chConcatOp K u u v).obj (op (chId K u), b) = b :=
  congrArg op (chConc_id_left b.unop)

theorem chConcatOp_obj_id_right (K : BPSet) (u v : K.cells 0) (a : (Ch (K.repoint u v))ᵒᵖ) :
    (chConcatOp K u v v).obj (a, op (chId K v)) = a :=
  congrArg op (chConc_id_right a.unop)

theorem chConcatOp_map_assoc (K : BPSet) (u v w x : K.cells 0)
    {a a' : (Ch (K.repoint u v))ᵒᵖ} {b b' : (Ch (K.repoint v w))ᵒᵖ}
    {c c' : (Ch (K.repoint w x))ᵒᵖ} (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
    (chConcatOp K u w x).map ((chConcatOp K u v w).map (f, g), h)
      = eqToHom (chConcatOp_obj_assoc K u v w x a b c)
        ≫ (chConcatOp K u v x).map (f, (chConcatOp K v w x).map (g, h))
        ≫ eqToHom (chConcatOp_obj_assoc K u v w x a' b' c').symm := by
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, eqToHom_unop]
  exact chConcMor_assoc f.unop g.unop h.unop

theorem chConcatOp_map_id_left (K : BPSet) (u v : K.cells 0)
    {b b' : (Ch (K.repoint u v))ᵒᵖ} (g : b ⟶ b') :
    (chConcatOp K u u v).map ((𝟙 (op (chId K u)), g) : (op (chId K u), b) ⟶ (op (chId K u), b'))
      = eqToHom (chConcatOp_obj_id_left K u v b) ≫ g
        ≫ eqToHom (chConcatOp_obj_id_left K u v b').symm := by
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, eqToHom_unop]
  exact chConcMor_id_left g.unop

theorem chConcatOp_map_id_right (K : BPSet) (u v : K.cells 0)
    {a a' : (Ch (K.repoint u v))ᵒᵖ} (f : a ⟶ a') :
    (chConcatOp K u v v).map ((f, 𝟙 (op (chId K v))) : (a, op (chId K v)) ⟶ (a', op (chId K v)))
      = eqToHom (chConcatOp_obj_id_right K u v a) ≫ f
        ≫ eqToHom (chConcatOp_obj_id_right K u v a').symm := by
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, eqToHom_unop]
  exact chConcMor_id_right f.unop

/-! ## The hom-groupoid, and its composition -/

/-- The hom-groupoid of `Fund`: zigzags of refinements of the chains `u ⟶ v`. -/
abbrev fundHom (K : BPSet) (u v : K.cells 0) : Type _ :=
  FreeGroupoid ((Ch (K.repoint u v))ᵒᵖ)

/-- The identity 1-cell: the empty chain. -/
noncomputable def fundId (K : BPSet) (v : K.cells 0) : fundHom K v v :=
  FreeGroupoid.mk (op (chId K v))

/-- Composition of chains, groupoidified — built with `lift₂`, so its universal property is an
*equality* and the enrichment can be strict. -/
noncomputable def fundConc (K : BPSet) (u v w : K.cells 0) :
    fundHom K u v × fundHom K v w ⥤ fundHom K u w :=
  FreeGroupoid.lift₂ (chConcatOp K u v w ⋙ FreeGroupoid.of _)

theorem fundConc_map_homMk (K : BPSet) (u v w : K.cells 0)
    {a a' : (Ch (K.repoint u v))ᵒᵖ} {b b' : (Ch (K.repoint v w))ᵒᵖ} (f : a ⟶ a') (g : b ⟶ b') :
    (fundConc K u v w).map
        ((FreeGroupoid.homMk f, FreeGroupoid.homMk g) :
          (FreeGroupoid.mk a, FreeGroupoid.mk b) ⟶ (FreeGroupoid.mk a', FreeGroupoid.mk b'))
      = FreeGroupoid.homMk ((chConcatOp K u v w).map ((f, g) : (a, b) ⟶ (a', b'))) :=
  FreeGroupoid.lift₂_map_homMk _ f g

theorem fundConc_map_id_homMk (K : BPSet) (u v w : K.cells 0)
    (a : (Ch (K.repoint u v))ᵒᵖ) {b b' : (Ch (K.repoint v w))ᵒᵖ} (g : b ⟶ b') :
    (fundConc K u v w).map
        ((𝟙 (FreeGroupoid.mk a), FreeGroupoid.homMk g) :
          (FreeGroupoid.mk a, FreeGroupoid.mk b) ⟶ (FreeGroupoid.mk a, FreeGroupoid.mk b'))
      = FreeGroupoid.homMk ((chConcatOp K u v w).map ((𝟙 a, g) : (a, b) ⟶ (a, b'))) :=
  FreeGroupoid.lift₂_map_id_homMk _ a g

theorem fundConc_map_homMk_id (K : BPSet) (u v w : K.cells 0)
    {a a' : (Ch (K.repoint u v))ᵒᵖ} (f : a ⟶ a') (b : (Ch (K.repoint v w))ᵒᵖ) :
    (fundConc K u v w).map
        ((FreeGroupoid.homMk f, 𝟙 (FreeGroupoid.mk b)) :
          (FreeGroupoid.mk a, FreeGroupoid.mk b) ⟶ (FreeGroupoid.mk a', FreeGroupoid.mk b))
      = FreeGroupoid.homMk ((chConcatOp K u v w).map ((f, 𝟙 b) : (a, b) ⟶ (a', b))) :=
  FreeGroupoid.lift₂_map_homMk_id _ f b

/-! ## The fundamental 2-category -/

/-- The 0-cells: the vertices of `K`, as a type synonym so the enrichment does not leak onto
`K.cells 0`. -/
def Fund (K : BPSet) : Type _ := K.cells 0

/-- **The fundamental 2-category of `K`**: vertices, chains, refinement zigzags.
`CatEnriched (Fund K)` is the associated `Bicategory.Strict`.

Same two gotchas as `CFund`: inside `namespace CubeChains`, `Functor.ext` and `Functor.map_id`
resolve to *core* Lean's `Functor`, and `Cat`'s monoidal `rfl`-lemmas need `erw`. -/
noncomputable instance : EnrichedCategory Cat (Fund K) where
  Hom u v := Cat.of (fundHom K u v)
  id v := Cat.Hom.ofFunctor (Cat.fromChosenTerminalEquiv.symm (fundId K v))
  comp u v w := Cat.Hom.ofFunctor (fundConc K u v w)
  id_comp u v := by
    ext
    refine FreeGroupoid.lift_ext (C := (Ch (K.repoint u v))ᵒᵖ) (G := fundHom K u v) ?_
    refine CategoryTheory.Functor.ext (fun b => ?_) (fun b b' g => ?_)
    · exact congrArg FreeGroupoid.mk (chConcatOp_obj_id_left K u v b)
    · simp only [Monoidal.leftUnitor_inv, Monoidal.whiskerRight, fundId,
        Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor, Functor.toCatHom_toFunctor,
        Functor.comp_map, Functor.prod_map, Functor.id_map, Prod.sectR_map, Prod.mkHom]
      erw [CategoryTheory.Functor.map_id, fundConc_map_id_homMk K u u v (op (chId K u)) g,
        chConcatOp_map_id_left K u v g]
      simp only [CategoryTheory.Functor.map_comp, eqToHom_map]
      rfl
  comp_id u v := by
    ext
    refine FreeGroupoid.lift_ext (C := (Ch (K.repoint u v))ᵒᵖ) (G := fundHom K u v) ?_
    refine CategoryTheory.Functor.ext (fun a => ?_) (fun a a' f => ?_)
    · exact congrArg FreeGroupoid.mk (chConcatOp_obj_id_right K u v a)
    · simp only [Monoidal.rightUnitor_inv, Monoidal.whiskerLeft, fundId,
        Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor, Functor.toCatHom_toFunctor,
        Functor.comp_map, Functor.prod_map, Functor.id_map, Prod.sectL_map, Prod.mkHom]
      erw [CategoryTheory.Functor.map_id, fundConc_map_homMk_id K u v v f (op (chId K v)),
        chConcatOp_map_id_right K u v f]
      simp only [CategoryTheory.Functor.map_comp, eqToHom_map]
      rfl
  assoc u v w x := by
    ext
    refine FreeGroupoid.lift₃_ext (C := (Ch (K.repoint u v))ᵒᵖ) (D := (Ch (K.repoint v w))ᵒᵖ)
      (E' := (Ch (K.repoint w x))ᵒᵖ) (G := fundHom K u x) ?_
    refine CategoryTheory.Functor.ext (fun p => ?_) (fun p q fgh => ?_)
    · exact congrArg FreeGroupoid.mk (chConcatOp_obj_assoc K u v w x p.1 p.2.1 p.2.2)
    · obtain ⟨a, b, c⟩ := p
      obtain ⟨a', b', c'⟩ := q
      obtain ⟨f, g, h⟩ := fgh
      simp only [Monoidal.associator_inv, Monoidal.whiskerLeft, Monoidal.whiskerRight,
        Cat.Hom.comp_toFunctor, Functor.toCatHom_toFunctor, Functor.comp_map,
        Functor.prod_map, Functor.id_map, Prod.mkHom, Functor.prod'_map, Prod.fst_map,
        Prod.snd_map]
      erw [fundConc_map_homMk K u v w f g, fundConc_map_homMk K v w x g h,
        fundConc_map_homMk K u w x ((chConcatOp K u v w).map ((f, g) : (a, b) ⟶ (a', b'))) h,
        fundConc_map_homMk K u v x f ((chConcatOp K v w x).map ((g, h) : (b, c) ⟶ (b', c'))),
        chConcatOp_map_assoc K u v w x f g h]
      simp only [CategoryTheory.Functor.map_comp, eqToHom_map]
      rfl

/-- The payoff: `Fund K` is a strict 2-category, with no coherence left to prove. -/
example : Bicategory.Strict (CatEnriched (Fund K)) := inferInstance

end CubeChains
