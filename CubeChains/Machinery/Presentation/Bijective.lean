import CubeChains.Machinery.Presentation.Elements

/-!
# Machinery/Presentation/Bijective — a cell-for-cell morphism carries a presentation

A morphism of polygraphs bijective in **every** dimension is a change of names, so whatever the
target presents the source presents too (`Presents.ofBijective`), and it is an isomorphism of
polygraphs (`isoOfBijective`).  Nothing is chosen: the interpretation is the target's, read through
the morphism, and the four obligations of `Presents.ofDesc` are the bijections — soundness needs
none of them, fullness and essential surjectivity the 0- and 1-cells, and completeness the 2-cells,
through `gen_pullbackRel`.  The inverse's two boundary laws are the morphism's own, read through
faithfulness on words.
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
theorem pathsFunctor_full' : F.pre.pathsFunctor.Full :=
  Prefunctor.pathsFunctor_full F.pre (fun x => (star_bijective F hobj hmap x).2) hobj.1

include hobj hmap in
theorem pathsFunctor_faithful' : F.pre.pathsFunctor.Faithful :=
  Prefunctor.pathsFunctor_faithful F.pre fun x => (star_bijective F hobj hmap x).1

variable (htwo : ∀ x y : GenObj P.Gen, Function.Bijective (F.two : P.Rel x y → _))

include hobj hmap htwo in
/-- **A 2-cell of the target between images is an image**, so the relation pulls back. -/
theorem homRel_of_mapPath {x y : GenObj P.Gen} {u v : Quiver.Path x y}
    (h : Q.homRel (F.pre.mapPath u) (F.pre.mapPath v)) : P.homRel u v := by
  haveI := pathsFunctor_faithful' F hobj hmap
  obtain ⟨β, hs, ht⟩ := h
  obtain ⟨α, rfl⟩ := (htwo x y).2 β
  exact ⟨α, F.pre.pathsFunctor.map_injective ((F.src_two α).symm.trans hs),
    F.pre.pathsFunctor.map_injective ((F.tgt_two α).symm.trans ht)⟩

/-- **A word equal to another in `P.presented` once their `F`-images are related** — the congruence
is a congruence, so a related pair inside a composite carries the whole composite. -/
theorem quot_map_eq_of_gen_pullback
    (hback : ∀ {x y : GenObj P.Gen} {u v : Quiver.Path x y},
      Q.homRel (F.pre.mapPath u) (F.pre.mapPath v) → P.quot.map u = P.quot.map v)
    {x y : GenObj P.Gen} {u v : Quiver.Path x y}
    (h : HomRel.Gen (F.pre.pathsFunctor.pullbackRel Q.homRel) u v) :
    P.quot.map u = P.quot.map v :=
  HomRel.map_eq_of_gen _ P.quot (fun hm => hback hm) h

/-- **The target's interpretation, read through `F`, kills `P`'s 2-cells** — `F`'s two boundary laws
and `Q`'s soundness. -/
theorem Presents.sound_pre (q : Presents Q C) {x y : GenObj P.Gen} (α : P.Rel x y) :
    (Paths.lift (F.pre ⋙q q.evalPre)).map (P.src α)
      = (Paths.lift (F.pre ⋙q q.evalPre)).map (P.tgt α) := by
  refine ((q.eval_mapPath F.pre (P.src α)).symm.trans ?_).trans (q.eval_mapPath F.pre (P.tgt α))
  rw [← F.src_two α, ← F.tgt_two α]
  exact q.sound (F.two α)

include hobj hmap in
/-- **A morphism bijective on the 0- and 1-cells carries a presentation back along itself**, given
that the target's 2-cells hold in the source (`hback`).  The 2-cells themselves need not biject:
what a presentation sees of them is only the congruence they generate. -/
noncomputable def Presents.ofCells (q : Presents Q C)
    (hback : ∀ {x y : GenObj P.Gen} {u v : Quiver.Path x y},
      Q.homRel (F.pre.mapPath u) (F.pre.mapPath v) → P.quot.map u = P.quot.map v) :
    Presents P C := by
  haveI := pathsFunctor_full' F hobj hmap
  haveI := pathsFunctor_faithful' F hobj hmap
  refine Presents.ofDesc (F.pre ⋙q q.evalPre) (fun {_ _} α => Presents.sound_pre F q α)
    (fun {x y u v} h => ?_) ?_ ?_
  · refine quot_map_eq_of_gen_pullback F hback
      (gen_pullbackRel F.pre.pathsFunctor Q.homRel ?_ (q.gen_of_eval_eq ?_))
    · intro a b X _ _
      exact ⟨(Equiv.ofBijective _ hobj).symm X, (Equiv.ofBijective _ hobj).apply_symm_apply X⟩
    · exact ((q.eval_mapPath F.pre u).trans h).trans (q.eval_mapPath F.pre v).symm
  · refine ⟨fun {x y} f => ?_⟩
    obtain ⟨w, hw⟩ : ∃ w : Quiver.Path (F.pre.obj x) (F.pre.obj y), q.eval.map w = f :=
      q.eval.map_surjective f
    obtain ⟨u, rfl⟩ := F.pre.pathsFunctor.map_surjective (X := x) (Y := y) w
    exact ⟨u, (q.eval_mapPath F.pre u).symm.trans hw⟩
  · refine ⟨fun c => ?_⟩
    obtain ⟨⟨w⟩, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := q.E) c
    exact ⟨(Equiv.ofBijective _ hobj).symm w,
      ⟨eqToIso (congrArg q.at' ((Equiv.ofBijective _ hobj).apply_symm_apply w)) ≪≫ i⟩⟩

/-- **The comparison is the target's, read through the morphism** — what a naturality square for
`ofCells` is conjugated by. -/
theorem Presents.ofCells_E (q : Presents Q C)
    (hback : ∀ {x y : GenObj P.Gen} {u v : Quiver.Path x y},
      Q.homRel (F.pre.mapPath u) (F.pre.mapPath v) → P.quot.map u = P.quot.map v) :
    (Presents.ofCells F hobj hmap q hback).E = F.functor ⋙ q.E :=
  descWords_comp (h' := fun {_ _} α => Presents.sound_pre F q α) q.E (q.lift_comp_evalPre F.pre)

include hobj hmap htwo in
/-- **A cell-for-cell morphism carries a presentation back along itself** — the same category, read
on `P`'s cells. -/
noncomputable def Presents.ofBijective (q : Presents Q C) : Presents P C :=
  Presents.ofCells F hobj hmap q fun hr =>
    (HomRel.gen_iff_functor_map_eq P.homRel _ _).mp
      (Relation.EqvGen.rel _ _ (HomRel.CompClosure.of
        (homRel_of_mapPath F hobj hmap htwo hr)))

/-! ## …and is an isomorphism

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

private theorem map_homOfEq {x y x' y' : GenObj P.Gen} (hx : x = x') (hy : y = y') (e : x ⟶ y) :
    F.pre.map (Quiver.homOfEq e hx hy)
      = Quiver.homOfEq (F.pre.map e) (congrArg F.pre.obj hx) (congrArg F.pre.obj hy) := by
  subst hx; subst hy; rfl

private theorem pre_comp_backPre : F.pre ⋙q backPre F hobj hmap = 𝟭q _ := by
  refine Prefunctor.ext_homOfEq (backObj_obj F hobj) fun x y e => ?_
  exact (hmap _ _).1 ((map_backMap F hobj hmap (F.pre.map e)).trans
    (map_homOfEq F (backObj_obj F hobj x).symm (backObj_obj F hobj y).symm e).symm)

/-- …and the 2-cell a 2-cell is. -/
private noncomputable def backTwo {x y : GenObj Q.Gen} (β : Q.Rel x y) :
    P.Rel (backObj F hobj x) (backObj F hobj y) :=
  (Equiv.ofBijective _ (htwo (backObj F hobj x) (backObj F hobj y))).symm
    (cellCongr Q.Rel (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm β)

private theorem two_backTwo {x y : GenObj Q.Gen} (β : Q.Rel x y) :
    F.two (backTwo F hobj htwo β)
      = cellCongr Q.Rel (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm β :=
  (Equiv.ofBijective _ (htwo _ _)).apply_symm_apply _

private theorem bdry_cellCongr (bd : ∀ {x y : GenObj Q.Gen}, Q.Rel x y → Quiver.Path x y)
    {x y x' y' : GenObj Q.Gen} (hx : x = x') (hy : y = y') (β : Q.Rel x y) :
    bd (cellCongr Q.Rel hx hy β) = cellCongr Quiver.Path hx hy (bd β) := by
  subst hx; subst hy; rfl

private theorem mapPath_of_eq {V : Type*} [Quiver V] {W : Type*} [Quiver W] {φ ψ : V ⥤q W}
    (h : φ = ψ) {x y : V} (w : Quiver.Path x y) :
    φ.mapPath w = cellCongr Quiver.Path (congrArg (fun π : V ⥤q W => π.obj x) h).symm
      (congrArg (fun π : V ⥤q W => π.obj y) h).symm (ψ.mapPath w) := by
  subst h; rfl

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
      ((congrArg bdQ (two_backTwo F hobj htwo β)).trans (bdry_cellCongr bdQ _ _ β))
  have h2 : F.pre.mapPath ((backPre F hobj hmap).mapPath (bdQ β))
      = cellCongr Quiver.Path (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm (bdQ β) :=
    (Prefunctor.mapPath_comp_apply (backPre F hobj hmap) F.pre (bdQ β)).symm.trans
      ((mapPath_of_eq (backPre_comp_pre F hobj hmap) (bdQ β)).trans
        (congrArg (cellCongr Quiver.Path _ _) (Prefunctor.mapPath_id (bdQ β))))
  exact F.pre.pathsFunctor.map_injective (h1.trans h2.symm)

/-- The morphism, read back. -/
private noncomputable def back : Hom Q P where
  pre := backPre F hobj hmap
  two := backTwo F hobj htwo
  src_two := back_bdry F hobj hmap htwo P.src Q.src F.src_two
  tgt_two := back_bdry F hobj hmap htwo P.tgt Q.tgt F.tgt_two

private theorem two_cellCongr {x y x' y' : GenObj P.Gen} (hx : x = x') (hy : y = y')
    (γ : P.Rel x y) : F.two (cellCongr P.Rel hx hy γ)
      = cellCongr Q.Rel (congrArg F.pre.obj hx) (congrArg F.pre.obj hy) (F.two γ) := by
  subst hx; subst hy; rfl

private theorem backTwo_two {x y : GenObj P.Gen} (α : P.Rel x y) :
    cellCongr P.Rel (backObj_obj F hobj x) (backObj_obj F hobj y)
      (backTwo F hobj htwo (F.two α)) = α := by
  refine (htwo x y).1 ?_
  rw [two_cellCongr, two_backTwo, cellCongr_trans]
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

end CategoryTheory.Polygraph
