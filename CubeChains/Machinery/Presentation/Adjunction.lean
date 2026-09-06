import CubeChains.Machinery.Presentation.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Machinery/Presentation/Adjunction — `presented` is a left adjoint

`catPoly C` reads a category as a polygraph: every arrow a 1-cell, and a 2-cell for each parallel
pair of words that compose alike.  It is right adjoint to `presented`, so `presented` preserves
every colimit: a colimit of polygraphs presents the colimit of what they present.

`Polygraph.desc` is the transpose — its `φ : GenObj P.Gen ⥤q C` is exactly a morphism
`P ⟶ catPoly C`, whose action on 2-cells is exactly `desc`'s `sound`.

The colimits preserved are the **strict** ones of `Cat`, and those do not see levelwise
equivalence: the coequalizer of `1 ⇉ (walking iso)` is `SingleObj ℤ` while the coequalizer of the
levelwise-equivalent `1 ⇉ 1` is `1`.  So `presentsColimit` asks for the colimit of the *presented*
categories themselves, not of a diagram merely equivalent to them.
-/

universe w' w u''' u'' u' u v w₂

namespace CategoryTheory

/-- **Substituting a map of quivers into a lift.** -/
theorem Paths.pathsFunctor_comp_lift {V : Type u'} [Quiver.{w} V] {W : Type u''} [Quiver.{w'} W]
    {D : Type u} [Category.{v} D] (π : V ⥤q W) (φ : W ⥤q D) :
    π.pathsFunctor ⋙ Paths.lift φ = Paths.lift (π ⋙q φ) :=
  Paths.lift_unique _ _ (Prefunctor.ext (fun _ => rfl) (fun _ _ _ => by simp))

namespace Polygraph

/-! ## A category, read as a polygraph

Its 0-cells are the objects, its 1-cells *all* the arrows, and its 2-cells the parallel pairs of
words that compose alike.  Nothing is free here: `catPre` is the tautological interpretation. -/

variable (C : Type u) [Category.{v} C]

/-- The generating quiver of a category: its own arrows. -/
def catGen : C → C → Type v := fun X Y => X ⟶ Y

/-- The tautological interpretation of a category's own arrows. -/
def catPre : GenObj (catGen C) ⥤q C where
  obj x := x.as
  map f := f

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

section Map

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]

/-- A functor, read on the generating quivers. -/
def catPreMap (F : C ⥤ D) : GenObj (catGen C) ⥤q GenObj (catGen D) where
  obj x := ⟨F.obj x.as⟩
  map f := F.map f

/-- **A word of arrows, pushed forward, composes to the pushforward of the composite.** -/
theorem lift_catPreMap (F : C ⥤ D) {x y : GenObj (catGen C)} (u : Quiver.Path x y) :
    (Paths.lift (catPre D)).map ((catPreMap F).mapPath u)
      = F.map ((Paths.lift (catPre C)).map u) :=
  (Paths.lift_mapPath (catPreMap F) (catPre D) u).trans (Paths.lift_comp_map (catPre C) F u).symm

/-- A functor is a morphism of the polygraphs it and its target are. -/
def catCell (F : C ⥤ D) : Hom (catPoly C) (catPoly D) where
  pre := show GenObj (catGen C) ⥤q GenObj (catGen D) from catPreMap F
  two α := ⟨((catPreMap F).mapPath α.1.1, (catPreMap F).mapPath α.1.2), by
    rw [lift_catPreMap, lift_catPreMap, α.2]⟩
  src_two _ := rfl
  tgt_two _ := rfl

end Map

/-! ## The transpose

`Polygraph.desc` is the forward direction of the hom-set bijection: its interpretation of the
cells is exactly a morphism into `catPoly C`, and `sound` is exactly the action on 2-cells. -/

section Transpose

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C]

/-- **A morphism into `catPoly C` is determined by its 1-cells**: a 2-cell there is a pair of
words, and both are pinned by the boundary conditions. -/
theorem catHom_ext {f g : Hom P (catPoly C)} (h : f.pre = g.pre) : f = g := by
  obtain ⟨p, t, hs, ht⟩ := f
  obtain ⟨p', t', hs', ht'⟩ := g
  cases h
  refine Hom.ext' rfl (fun α => heq_of_eq (Subtype.ext (Prod.ext ?_ ?_)))
  · exact (hs α).trans (hs' α).symm
  · exact (ht α).trans (ht' α).symm

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

/-! ## The adjunction -/

section Adj

/-- `presented`, as a functor. -/
def presentedFunctor : Polygraph.{max u v, u, max u v} ⥤ Cat.{max u v, u} where
  obj P := Cat.of P.presented
  map f := Functor.toCatHom f.functor
  map_id _ := Cat.ext functor_id
  map_comp f g := Cat.ext (functor_comp f g)

/-- A category, as a polygraph, functorially. -/
def catPolyFunctor : Cat.{max u v, u} ⥤ Polygraph.{max u v, u, max u v} where
  obj C := catPoly C
  map G := catCell G.toFunctor
  map_id _ := by exact catHom_ext rfl
  map_comp _ _ := by exact catHom_ext rfl

/-- **`⟨generators | relations⟩ ⊣ arrows`.**  Hence `presented` preserves all colimits: the
colimit of a family of presentations presents the colimit of what they present. -/
def presentedAdj : presentedFunctor.{u, v} ⊣ catPolyFunctor.{u, v} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P C => by exact (Cat.Hom.equivFunctor _ C).trans (catHomEquiv P C).symm
      homEquiv_naturality_left_symm := fun {P' P C} f g => by
        refine Cat.ext (Quotient.lift_unique' P'.homRel (homToFun (f ≫ g))
          (Hom.functor f ⋙ homToFun g) ?_)
        rw [quot_comp_homToFun, ← Functor.assoc, Hom.quot_comp_functor, Functor.assoc,
          quot_comp_homToFun, Paths.pathsFunctor_comp_lift]
        rfl
      homEquiv_naturality_right := fun _ _ => by exact catHom_ext rfl }

/-- `presented` preserves every colimit. -/
instance : Limits.PreservesColimitsOfSize.{w, u'''} presentedFunctor.{u, v} :=
  presentedAdj.leftAdjoint_preservesColimits

/-! ## What the adjunction gives

The counit is a presentation, a tautological one: every arrow a generator.  So a presentation
always exists and the content is in replacing it by a *compact* polygraph.  What transports for
free is `presentsColimit`: a colimit of polygraphs presents the colimit of what they present. -/

/-- **A category presents itself**, by all its arrows.  The counit of the adjunction. -/
def presentsCatPoly (C : Type u) [Category.{v} C] : Presents (catPoly C) C :=
  Presents.ofDesc (catPre C) (fun α => α.2) (fun h => Quotient.sound _ ⟨⟨(_, _), h⟩, rfl, rfl⟩)
    { map_surjective := fun {x y} f =>
        ⟨@Quiver.Hom.toPath (GenObj (catGen C)) _ x y f, Paths.lift_toPath (catPre C) f⟩ }
    { mem_essImage := fun X => ⟨⟨X⟩, ⟨Iso.refl _⟩⟩ }

/-- **A colimit of polygraphs presents the colimit of what they present** — the whole content of
`presented ⊣ catPoly`, in the form a presentation of a glued category needs. -/
noncomputable def presentsColimit {J : Type u''} [Category.{w} J]
    (D : J ⥤ Polygraph.{max u v, u, max u v}) [Limits.HasColimit D]
    [Limits.HasColimit (D ⋙ presentedFunctor.{u, v})] :
    Presents (Limits.colimit D) ↥(Limits.colimit (D ⋙ presentedFunctor.{u, v})) where
  E := (preservesColimitIso presentedFunctor.{u, v} D).hom.toFunctor
  isEquiv := (Cat.equivOfIso (preservesColimitIso presentedFunctor.{u, v} D)).isEquivalence_functor

end Adj

end Polygraph

end CategoryTheory
