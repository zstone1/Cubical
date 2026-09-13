import CubeChains.Machinery.Presentation.Elements

/-!
# Machinery/Presentation/Bijective — a cell-for-cell morphism carries a presentation

A morphism of polygraphs bijective in **every** dimension is an isomorphism (`isoOfBijective`), so
whatever the target presents the source presents too (`Presents.ofBijective`, which is then
`ofPolyIso`).  Nothing is chosen: the inverse is read back along the three bijections, and its two
boundary laws are the morphism's own, seen through faithfulness on words.
-/

universe v w u u' w₂

namespace CategoryTheory.Polygraph

variable {P Q : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C]
  (F : Hom P Q) (hobj : Function.Bijective F.pre.obj)
  (hmap : ∀ x y : GenObj P.Gen, Function.Bijective (F.pre.map : (x ⟶ y) → _))

include hobj hmap in
/-- **A cell-for-cell morphism is a bijection on the stars** — fullness and faithfulness of
`mapPath` at once. -/
theorem star_bijective (x : GenObj P.Gen) : Function.Bijective (F.pre.star x) := by
  constructor
  · rintro ⟨y₁, e₁⟩ ⟨y₂, e₂⟩ h
    obtain ⟨hy, he⟩ := Sigma.mk.inj_iff.mp h
    obtain rfl : y₁ = y₂ := hobj.1 hy
    exact Sigma.ext rfl (heq_of_eq ((hmap x y₁).1 (eq_of_heq he)))
  · rintro ⟨b, g⟩
    obtain ⟨y, rfl⟩ := hobj.2 b
    obtain ⟨e, rfl⟩ := (hmap x y).2 g
    exact ⟨⟨y, e⟩, rfl⟩

include hobj hmap in
theorem pathsFunctor_faithful' : F.pre.pathsFunctor.Faithful :=
  Prefunctor.pathsFunctor_faithful F.pre fun x => (star_bijective F hobj hmap x).1

variable (htwo : ∀ x y : GenObj P.Gen, Function.Bijective (F.two : P.Rel x y → _))

/-! ## The morphism, read back

Everything the inverse has to do is read back along the three bijections; its two boundary laws are
the morphism's own, read through faithfulness on words (`pathsFunctor_faithful'`). -/

/-- The 0-cell a 0-cell of the target is the image of. -/
private noncomputable def backObj (x : GenObj Q.Gen) : GenObj P.Gen :=
  (Equiv.ofBijective _ hobj).symm x

private theorem obj_backObj (x : GenObj Q.Gen) : F.pre.obj (backObj F hobj x) = x :=
  (Equiv.ofBijective _ hobj).apply_symm_apply x

private theorem backObj_obj (x : GenObj P.Gen) : backObj F hobj (F.pre.obj x) = x :=
  (Equiv.ofBijective _ hobj).symm_apply_apply x

/-- …and the 1-cell a 1-cell is. -/
private noncomputable def backMap {x y : GenObj Q.Gen} (e : x ⟶ y) :
    backObj F hobj x ⟶ backObj F hobj y :=
  (Equiv.ofBijective _ (hmap (backObj F hobj x) (backObj F hobj y))).symm
    (Quiver.homOfEq e (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm)

private theorem map_backMap {x y : GenObj Q.Gen} (e : x ⟶ y) :
    F.pre.map (backMap F hobj hmap e)
      = Quiver.homOfEq e (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm :=
  (Equiv.ofBijective _ (hmap _ _)).apply_symm_apply _

/-- The generating quiver, read back. -/
private noncomputable def backPre : GenObj Q.Gen ⥤q GenObj P.Gen where
  obj := backObj F hobj
  map := backMap F hobj hmap

private theorem backPre_comp_pre : backPre F hobj hmap ⋙q F.pre = 𝟭q _ :=
  Prefunctor.ext_homOfEq (obj_backObj F hobj) fun _ _ e => map_backMap F hobj hmap e

private theorem pre_comp_backPre : F.pre ⋙q backPre F hobj hmap = 𝟭q _ := by
  refine Prefunctor.ext_homOfEq (backObj_obj F hobj) fun x y e => ?_
  exact (hmap _ _).1 ((map_backMap F hobj hmap (F.pre.map e)).trans
    (Prefunctor.homOfEq_map F.pre e
      (backObj_obj F hobj x).symm (backObj_obj F hobj y).symm).symm)

/-- …and the 2-cell a 2-cell is. -/
private noncomputable def backTwo {x y : GenObj Q.Gen} (β : Q.Rel x y) :
    P.Rel (backObj F hobj x) (backObj F hobj y) :=
  (Equiv.ofBijective _ (htwo (backObj F hobj x) (backObj F hobj y))).symm
    (cellCongr Q.Rel (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm β)

private theorem two_backTwo {x y : GenObj Q.Gen} (β : Q.Rel x y) :
    F.two (backTwo F hobj htwo β)
      = cellCongr Q.Rel (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm β :=
  (Equiv.ofBijective _ (htwo _ _)).apply_symm_apply _

/-- **Either boundary of a read-back 2-cell is the boundary, read back** — faithfulness on words
sees it through `F`. -/
private theorem back_bdry (bdP : ∀ {x y : GenObj P.Gen}, P.Rel x y → Quiver.Path x y)
    (bdQ : ∀ {x y : GenObj Q.Gen}, Q.Rel x y → Quiver.Path x y)
    (hbd : ∀ {x y : GenObj P.Gen} (α : P.Rel x y), bdQ (F.two α) = F.pre.mapPath (bdP α))
    {x y : GenObj Q.Gen} (β : Q.Rel x y) :
    bdP (backTwo F hobj htwo β) = (backPre F hobj hmap).mapPath (bdQ β) := by
  haveI := pathsFunctor_faithful' F hobj hmap
  have h1 : F.pre.mapPath (bdP (backTwo F hobj htwo β))
      = cellCongr Quiver.Path (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm (bdQ β) :=
    (hbd (backTwo F hobj htwo β)).symm.trans
      ((congrArg bdQ (two_backTwo F hobj htwo β)).trans
        (cellCongr_natural (F := Q.Rel) (G := Quiver.Path) bdQ _ _ β))
  have h2 : F.pre.mapPath ((backPre F hobj hmap).mapPath (bdQ β))
      = cellCongr Quiver.Path (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm (bdQ β) :=
    (Prefunctor.mapPath_comp_apply (backPre F hobj hmap) F.pre (bdQ β)).symm.trans
      ((Prefunctor.mapPath_cellCongr_of_eq (backPre_comp_pre F hobj hmap) (bdQ β)).trans
        (congrArg (cellCongr Quiver.Path _ _) (Prefunctor.mapPath_id (bdQ β))))
  exact F.pre.pathsFunctor.map_injective (h1.trans h2.symm)

/-- The morphism, read back. -/
private noncomputable def back : Hom Q P where
  pre := backPre F hobj hmap
  two := backTwo F hobj htwo
  src_two := back_bdry F hobj hmap htwo P.src Q.src F.src_two
  tgt_two := back_bdry F hobj hmap htwo P.tgt Q.tgt F.tgt_two

private theorem backTwo_two {x y : GenObj P.Gen} (α : P.Rel x y) :
    cellCongr P.Rel (backObj_obj F hobj x) (backObj_obj F hobj y)
      (backTwo F hobj htwo (F.two α)) = α := by
  refine (htwo x y).1 ?_
  rw [cellCongr_map (F := P.Rel) (G := Q.Rel) F.pre.obj F.two, two_backTwo, cellCongr_trans]
  exact cellCongr_self Q.Rel _ _ (F.two α)

/-- **A morphism bijective in every dimension is an isomorphism.** -/
noncomputable def isoOfBijective : P ≅ Q where
  hom := F
  inv := back F hobj hmap htwo
  hom_inv_id := Hom.ext' (pre_comp_backPre F hobj hmap) fun α =>
    (cellCongr_heq P.Rel (backObj_obj F hobj _) (backObj_obj F hobj _) _).symm.trans
      (heq_of_eq (backTwo_two F hobj htwo α))
  inv_hom_id := Hom.ext' (backPre_comp_pre F hobj hmap) fun β =>
    (heq_of_eq (two_backTwo F hobj htwo β)).trans (cellCongr_heq Q.Rel _ _ β)

/-- **A cell-for-cell morphism carries a presentation back along itself** — the same category, read
on `P`'s cells. -/
noncomputable def Presents.ofBijective (q : Presents Q C) : Presents P C :=
  q.ofPolyIso (isoOfBijective F hobj hmap htwo).symm

end CategoryTheory.Polygraph
