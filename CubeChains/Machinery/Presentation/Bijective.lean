import CubeChains.Machinery.Presentation.Elements

/-!
# Machinery/Presentation/Bijective — a cell-for-cell morphism carries a presentation

A morphism of polygraphs bijective in **every** dimension is a change of names, so whatever the
target presents the source presents too.  Nothing is chosen: the interpretation is the target's,
read through the morphism, and the four obligations of `Presents.ofDesc` are the bijections —
soundness needs none of them, fullness and essential surjectivity the 0- and 1-cells, and
completeness the 2-cells, through `gen_pullbackRel`.
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

include hobj hmap htwo in
/-- **…and so does the congruence it generates.** -/
theorem gen_of_gen_mapPath {x y : GenObj P.Gen} {u v : Quiver.Path x y}
    (h : HomRel.Gen Q.homRel (F.pre.mapPath u) (F.pre.mapPath v)) :
    HomRel.Gen P.homRel u v := by
  haveI := pathsFunctor_full' F hobj hmap
  haveI := pathsFunctor_faithful' F hobj hmap
  refine HomRel.Gen.mono (fun hr => homRel_of_mapPath F hobj hmap htwo hr)
    (gen_pullbackRel F.pre.pathsFunctor Q.homRel ?_ h)
  intro a b X _ _
  exact ⟨(Equiv.ofBijective _ hobj).symm X, (Equiv.ofBijective _ hobj).apply_symm_apply X⟩

/-- **A word equal to another in `P.presented` once their `F`-images are related** — the congruence
is a congruence, so a related pair inside a composite carries the whole composite. -/
theorem quot_map_eq_of_gen_pullback
    (hback : ∀ {x y : GenObj P.Gen} {u v : Quiver.Path x y},
      Q.homRel (F.pre.mapPath u) (F.pre.mapPath v) → P.quot.map u = P.quot.map v)
    {x y : GenObj P.Gen} {u v : Quiver.Path x y}
    (h : HomRel.Gen (F.pre.pathsFunctor.pullbackRel Q.homRel) u v) :
    P.quot.map u = P.quot.map v := by
  induction h with
  | rel _ _ hab =>
      obtain ⟨X, Y, w, m₁, m₂, w', hm⟩ := hab
      rw [P.quot.map_comp, P.quot.map_comp, P.quot.map_comp, P.quot.map_comp, hback hm]
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

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
  refine Presents.ofDesc (F.pre ⋙q q.evalPre) (fun {x y} α => ?_) (fun {x y u v} h => ?_) ?_ ?_
  · refine ((q.eval_mapPath F.pre (P.src α)).symm.trans ?_).trans (q.eval_mapPath F.pre (P.tgt α))
    rw [← F.src_two α, ← F.tgt_two α]
    exact q.sound (F.two α)
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

include hobj hmap htwo in
/-- **A cell-for-cell morphism carries a presentation back along itself** — the same category, read
on `P`'s cells. -/
noncomputable def Presents.ofBijective (q : Presents Q C) : Presents P C :=
  Presents.ofCells F hobj hmap q fun hr =>
    (HomRel.gen_iff_functor_map_eq P.homRel _ _).mp
      (Relation.EqvGen.rel _ _ (HomRel.CompClosure.of
        (homRel_of_mapPath F hobj hmap htwo hr)))

end CategoryTheory.Polygraph
