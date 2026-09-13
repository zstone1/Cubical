import CubeChains.Machinery.Presentation.Basic

/-!
# Machinery/Presentation/Adjunction — `⟨generators | relations⟩ ⊣ arrows`, on hom-sets

`catPoly C` reads a category as a polygraph: every arrow a 1-cell, and a 2-cell for each parallel
pair of words that compose alike.  `catHomEquiv` is the hom-bijection with `presented`, and
`Polygraph.desc` is its forward direction — the `φ : GenObj P.Gen ⥤q C` of a `desc` is exactly a
morphism `P ⟶ catPoly C`, whose action on 2-cells is exactly `desc`'s `sound`.
-/

universe w u' u v w₂

namespace CategoryTheory

namespace Polygraph

/-! ## A category, read as a polygraph

Its 0-cells are the objects, its 1-cells *all* the arrows, and its 2-cells the parallel pairs of
words that compose alike.  Nothing is free here: `catPre` is the tautological interpretation. -/

variable (C : Type u) [Category.{v} C]

/-- The 2-cells of a category read as a polygraph: the parallel pairs of words composing alike. -/
def CatRel (x y : GenObj (catGen C)) : Type (max u v) :=
  {p : Quiver.Path x y × Quiver.Path x y //
    (Paths.lift (catPre C)).map p.1 = (Paths.lift (catPre C)).map p.2}

/-- **A category, as a polygraph.** -/
def catPoly : Polygraph.{v, u, max u v} where
  V := C
  Gen := catGen C
  Rel := CatRel C
  src α := α.1.1
  tgt α := α.1.2

/-! ## The transpose

`Polygraph.desc` is the forward direction of the hom-set bijection: its interpretation of the
cells is exactly a morphism into `catPoly C`, and `sound` is exactly the action on 2-cells. -/

section Transpose

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C]

/-- **A morphism into `catPoly C` is determined by its 1-cells**: a 2-cell there is a pair of
words, and both are pinned by the boundary conditions. -/
theorem catHom_ext {f g : Hom P (catPoly C)} (h : f.pre = g.pre) : f = g :=
  hom_ext_of_boundaryDetermined (fun _ _ hs ht => Subtype.ext (Prod.ext hs ht)) h

/-- The cells of `P`, interpreted in `C` by a morphism into `catPoly C`. -/
def cellEval (f : Hom P (catPoly C)) : GenObj P.Gen ⥤q C := f.pre ⋙q catPre C

/-- **The action on 2-cells *is* `desc`'s `sound`** — a 2-cell of `catPoly C` says exactly that the
two words compose alike. -/
theorem cellEval_sound (f : Hom P (catPoly C)) {x y : GenObj P.Gen} (α : P.Rel x y) :
    (Paths.lift (cellEval f)).map (P.src α) = (Paths.lift (cellEval f)).map (P.tgt α) := by
  have h := (f.two α).2
  rw [show (f.two α).1.1 = f.pre.mapPath (P.src α) from f.src_two α,
    show (f.two α).1.2 = f.pre.mapPath (P.tgt α) from f.tgt_two α] at h
  exact (Paths.lift_mapPath f.pre (catPre C) _).symm.trans
    (h.trans (Paths.lift_mapPath f.pre (catPre C) _))

/-- **The transpose**, forwards: `Polygraph.desc` at a morphism into `catPoly C`. -/
def homToFun (f : Hom P (catPoly C)) : P.presented ⥤ C :=
  P.desc (cellEval f) (cellEval_sound f)

theorem quot_comp_homToFun (f : Hom P (catPoly C)) :
    P.quot ⋙ homToFun f = Paths.lift (cellEval f) :=
  P.quot_comp_desc _ _

/-- The cells of `P` named by a functor out of `presented`. -/
def homInvPre (F : P.presented ⥤ C) : GenObj P.Gen ⥤q GenObj (catGen C) where
  obj x := ⟨F.obj (P.quot.obj x)⟩
  map e := F.map (P.quot.map e.toPath)

/-- **A word, read through a functor out of `presented`, is that functor on the word.** -/
theorem lift_homInvPre (F : P.presented ⥤ C) {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (Paths.lift (catPre C)).map ((homInvPre F).mapPath u) = F.map (P.quot.map u) :=
  (Paths.lift_mapPath (homInvPre F) (catPre C) u).trans
    ((Paths.lift_comp_map (Paths.of (GenObj P.Gen)) (P.quot ⋙ F) u).symm.trans
      (congrArg (P.quot ⋙ F).map (Paths.lift_of_map u)))

/-- **The transpose**, backwards. -/
def homInvFun (F : P.presented ⥤ C) : Hom P (catPoly C) where
  pre := show GenObj P.Gen ⥤q GenObj (catGen C) from homInvPre F
  two α := ⟨((homInvPre F).mapPath (P.src α), (homInvPre F).mapPath (P.tgt α)), by
    rw [lift_homInvPre, lift_homInvPre]
    exact congrArg F.map (P.quot_src_tgt α)⟩
  src_two _ := rfl
  tgt_two _ := rfl

/-- **`⟨generators | relations⟩ ⊣ arrows`, on hom-sets**: a morphism into the polygraph of a
category's own arrows is a functor out of the presented category. -/
def catHomEquiv (P : Polygraph.{w, u', w₂}) (C : Type u) [Category.{v} C] :
    Hom P (catPoly C) ≃ (P.presented ⥤ C) where
  toFun := homToFun
  invFun := homInvFun
  left_inv f := by
    refine catHom_ext (Prefunctor.ext (fun _ => rfl) fun _ _ e => ?_)
    exact Paths.lift_toPath (cellEval f) e
  right_inv F := by
    refine Quotient.lift_unique' P.homRel _ F ?_
    rw [quot_comp_homToFun]
    exact (Paths.lift_unique (cellEval (homInvFun F)) (P.quot ⋙ F) rfl).symm

end Transpose

end Polygraph

end CategoryTheory
