import CubeChains.Machinery.Presentation.Glue

/-!
# Machinery/Presentation/GlueOn — copies over a generating set only

The redundancy that makes `Glue`'s bijectivity hypothesis unattainable is exactly what makes this
version work: a localization keeps one object per object of `Over d` while a compact presentation
names one per *iso-class*, so `Glue`'s `L.ob d` cannot be surjective — but for the same reason
every object is *isomorphic* to a named one, which is all `Presents` ever asks.

So the change from `Glue` is **fewer 0-cells, not fewer copies at the same 0-cells**: the 0-cells
here are the objects a copy over `S` actually reaches (`Covered`), and the comparison is asked to
be essentially surjective rather than bijective on objects.

The overlap 2-cells are indexed by *spans* `s₁ ← e → s₂` rather than by single arrows, because the
apex of a span need carry no copy of its own.
-/

universe w w' v₁ u₁ u'

namespace CategoryTheory

namespace Polygraph

open Opposite

variable {D : Type u₁} [Category.{v₁} D] (X : Dᵒᵖ ⥤ Type w) {P : D ⥤ Polygraph.{w', u'}}
  (L : SliceLabels P) (S : Set (GlueV X))

/-! ## The 0-cells a generating set reaches -/

/-- A 0-cell of `Glue`, read as the object of `∫X` it is.  `GlueV` is `Σ d, X d` and the elements
category spells the same data with two `op`s; this is the one place that translation lives. -/
@[reducible] def elt (v : GlueV X) : (X.Elements)ᵒᵖ := op ⟨op v.1, v.2⟩

/-- The objects of `∫X` named by some copy over `S`. -/
def Covered : GlueV X → Prop :=
  fun v => ∃ s ∈ S, ∃ a : (P.obj s.1).V, gluePt X L s.1 s.2 a = v

/-- The 0-cells of the glued polygraph: only the covered objects. -/
abbrev GlueOnV : Type (max u₁ w) := {v : GlueV X // Covered X L S v}

/-- The 0-cell of the copy at `s` that a 0-cell `a` of `P s.1` names. -/
def glueOnPt (s : GlueV X) (hs : s ∈ S) (a : (P.obj s.1).V) : GlueOnV X L S :=
  ⟨gluePt X L s.1 s.2 a, s, hs, a, rfl⟩

@[simp] theorem glueOnPt_val (s : GlueV X) (hs : s ∈ S) (a : (P.obj s.1).V) :
    (glueOnPt X L S s hs a).1 = gluePt X L s.1 s.2 a := rfl

/-- **The copy at `s` read through `P.map f` lands where the copy at the span's apex would.**
`Glue`'s `gluePt_map`, restricted to the 0-cells that exist here. -/
theorem glueOnPt_map {s : GlueV X} (hs : s ∈ S) {d' : D} (f : d' ⟶ s.1)
    (a : GenObj (P.obj d').Gen) :
    (glueOnPt X L S s hs ((P.map f).cells.obj a).as).1 = gluePt X L d' (X.map f.op s.2) a.as :=
  gluePt_map X L f s.2 a

/-- **`S` generates**: every object of `∫X` maps into an object *of `S`* — not merely into a
covered one, since it is the copies that spell arrows and those sit at `S`.  This is what makes an
arrow lie in a single slice, hence be spelled by a single copy's word; it is `Full`'s hypothesis,
and the diamond condition wants the same thing one level down (`Cubical-xsm4`). -/
def Generating : Prop := ∀ c : (X.Elements)ᵒᵖ, ∃ s ∈ S, Nonempty (c ⟶ elt X s)

/-! ## The cells

A 1-cell is a 1-cell of some `P s.1` with `s ∈ S`; a 2-cell is either one of a copy's own, or an
**overlap**: a span `s₁ ← e → s₂` with both feet in `S` makes the two readings of a generator of
`P e` agree.  Taking `s₁ = s₂` gives the self-spans. -/

/-- 1-cells: a 1-cell of `P s.1`, in the copy at `s ∈ S`. -/
inductive GlueOnGen : GlueOnV X L S → GlueOnV X L S → Type (max u₁ w u' w')
  | mk (s : GlueV X) (hs : s ∈ S) {a b : (P.obj s.1).V} (g : (P.obj s.1).Gen a b) :
      GlueOnGen (glueOnPt X L S s hs a) (glueOnPt X L S s hs b)

/-- The copy of `P s.1` sitting over `s ∈ S`. -/
def glueOnPre (s : GlueV X) (hs : s ∈ S) :
    GenObj (P.obj s.1).Gen ⥤q GenObj (GlueOnGen X L S) where
  obj a := ⟨glueOnPt X L S s hs a.as⟩
  map g := GlueOnGen.mk s hs g

/-- The two feet of a span name the same 0-cell. -/
theorem glueOnPre_obj_span {s₁ s₂ : GlueV X} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S) {d' : D}
    (f₁ : d' ⟶ s₁.1) (f₂ : d' ⟶ s₂.1) (hx : X.map f₁.op s₁.2 = X.map f₂.op s₂.2)
    (a : GenObj (P.obj d').Gen) :
    (glueOnPre X L S s₁ h₁).obj ((P.map f₁).cells.obj a)
      = (glueOnPre X L S s₂ h₂).obj ((P.map f₂).cells.obj a) :=
  congrArg (fun v => (⟨v⟩ : GenObj (GlueOnGen X L S)))
    (Subtype.ext ((glueOnPt_map X L S h₁ f₁ a).trans
      (hx ▸ (glueOnPt_map X L S h₂ f₂ a).symm)))

/-- 2-cells: each copy's own, plus one per span with both feet in `S`. -/
inductive GlueOnRel : ∀ {s t : Paths (GenObj (GlueOnGen X L S))}, (s ⟶ t) → (s ⟶ t) → Prop
  | copy (s : GlueV X) (hs : s ∈ S) {a b : GenObj (P.obj s.1).Gen} {u v : Quiver.Path a b} :
      (P.obj s.1).rel u v →
      GlueOnRel ((glueOnPre X L S s hs).mapPath u) ((glueOnPre X L S s hs).mapPath v)
  | overlap {s₁ s₂ : GlueV X} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S) {d' : D}
      (f₁ : d' ⟶ s₁.1) (f₂ : d' ⟶ s₂.1) (hx : X.map f₁.op s₁.2 = X.map f₂.op s₂.2)
      {a b : GenObj (P.obj d').Gen} (g : a ⟶ b) :
      GlueOnRel ((glueOnPre X L S s₁ h₁).mapPath ((P.map f₁).cells.map g))
        (eqToHom (glueOnPre_obj_span X L S h₁ h₂ f₁ f₂ hx a) ≫
          (glueOnPre X L S s₂ h₂).mapPath ((P.map f₂).cells.map g) ≫
          eqToHom (glueOnPre_obj_span X L S h₁ h₂ f₁ f₂ hx b).symm)

/-- **The glued polygraph over a generating set.** -/
def glueOn : Polygraph.{max u₁ w u' w', max u₁ w} where
  V := GlueOnV X L S
  Gen := GlueOnGen X L S
  rel := fun _ _ => GlueOnRel X L S

/-- A copy's 2-cells hold in the glued polygraph. -/
theorem glueOnRel_copy_sound (s : GlueV X) (hs : s ∈ S) {a b : GenObj (P.obj s.1).Gen}
    {u v : Quiver.Path a b} (h : (P.obj s.1).rel u v) :
    (glueOn X L S).quot.map ((glueOnPre X L S s hs).mapPath u)
      = (glueOn X L S).quot.map ((glueOnPre X L S s hs).mapPath v) :=
  Quotient.sound _ (GlueOnRel.copy s hs h)

/-- The inclusion of the copy of `P s.1` at `s ∈ S`. -/
def glueOnIncl (s : GlueV X) (hs : s ∈ S) : Hom (P.obj s.1) (glueOn X L S) :=
  Hom.ofPre (glueOnPre X L S s hs) (glueOnRel_copy_sound X L S s hs)

/-! ## The comparison functor

Identical to `Glue`'s, except at the overlap: there the two readings are compared *through the
apex's slice*, which exists as a category even though it carries no copy.  That is what lets the
copies sit over `S` alone. -/

section Compare

variable (W : MorphismProperty D)
  (p : ∀ d : D, Presents (P.obj d) ((W.over (X := d)).Localization))
  (hL : ∀ (d : D) (a : (P.obj d).V),
    (p d).at' ⟨a⟩ = Localization.Construction.objEquiv (W.over (X := d)) (L.ob d a))

/-- The object of `(∫X)[W⁻¹]` a 0-cell names. -/
@[reducible] def glueOnAt (v : GenObj (GlueOnGen X L S)) :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization :=
  (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj (elt X v.as.1)

include hL in
theorem glueOnAt_glueOnPt (s : GlueV X) (hs : s ∈ S) (a : (P.obj s.1).V) :
    (glueSliceEval X W s.1 s.2).obj ((p s.1).at' ⟨a⟩)
      = glueOnAt X L S W ⟨glueOnPt X L S s hs a⟩ := by
  rw [hL s.1 a]
  exact glueSliceEval_obj X W s.1 s.2 (L.ob s.1 a)

include hL in
/-- The arrow a 1-cell names: the copy's own arrow, pushed along the cartesian lift. -/
noncomputable def glueOnArrow :
    ∀ {v t : GenObj (GlueOnGen X L S)}, (v ⟶ t) → (glueOnAt X L S W v ⟶ glueOnAt X L S W t)
  | ⟨_⟩, ⟨_⟩, GlueOnGen.mk s hs g =>
      eqToHom (glueOnAt_glueOnPt X L S W p hL s hs _).symm ≫
        (glueSliceEval X W s.1 s.2).map ((p s.1).arrow g) ≫
        eqToHom (glueOnAt_glueOnPt X L S W p hL s hs _)

include hL in
/-- The cells of the glued polygraph, interpreted. -/
noncomputable def glueOnEval : GenObj (GlueOnGen X L S) ⥤q
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization where
  obj := glueOnAt X L S W
  map := glueOnArrow X L S W p hL

include hL in
theorem glueOnEval_map_glueOnPre (s : GlueV X) (hs : s ∈ S)
    {a b : GenObj (P.obj s.1).Gen} (e : a ⟶ b) :
    (glueOnEval X L S W p hL).map ((glueOnPre X L S s hs).map e) =
      eqToHom (glueOnAt_glueOnPt X L S W p hL s hs a.as).symm ≫
        (glueSliceEval X W s.1 s.2).map ((p s.1).arrow e) ≫
        eqToHom (glueOnAt_glueOnPt X L S W p hL s hs b.as) :=
  rfl

include hL in
/-- **A copy's word, evaluated**: the copy's own evaluation, pushed along the cartesian lift. -/
theorem glueOnEval_mapPath (s : GlueV X) (hs : s ∈ S) {a b : GenObj (P.obj s.1).Gen}
    (u : Quiver.Path a b) :
    (Paths.lift (glueOnEval X L S W p hL)).map ((glueOnPre X L S s hs).mapPath u) =
      eqToHom (glueOnAt_glueOnPt X L S W p hL s hs a.as).symm ≫
        (glueSliceEval X W s.1 s.2).map ((p s.1).eval.map u) ≫
        eqToHom (glueOnAt_glueOnPt X L S W p hL s hs b.as) := by
  induction u with
  | nil =>
      rw [show (Paths.lift (glueOnEval X L S W p hL)).map
            ((glueOnPre X L S s hs).mapPath (Quiver.Path.nil : Quiver.Path a a)) = 𝟙 _ from
          (Paths.lift (glueOnEval X L S W p hL)).map_id _,
        show (p s.1).eval.map (Quiver.Path.nil : Quiver.Path a a) = 𝟙 _ from (p s.1).eval.map_id _,
        Functor.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
      rfl
  | cons u e ih =>
      rw [Prefunctor.mapPath_cons, Paths.lift_cons, ih, glueOnEval_map_glueOnPre,
        (p s.1).eval_cons, Functor.map_comp]
      exact (eqToHom_conj_comp _ _ _ _ _ _).trans (by simp; rfl)

variable (hP : ∀ {d' d : D} (f : d' ⟶ d),
  (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc W f)

include hP in
/-- **The span identification, as an equality of functors.**  Both feet are compared *through the
apex's slice* — `glueSliceEval X W d' _`, a category that exists whether or not `d'` carries a
copy.  That is the whole reason the copies may sit over `S` alone. -/
theorem glueOnSliceEval_span {s₁ s₂ : GlueV X} {d' : D}
    (f₁ : d' ⟶ s₁.1) (f₂ : d' ⟶ s₂.1) (hx : X.map f₁.op s₁.2 = X.map f₂.op s₂.2) :
    (P.map f₁).words ⋙ (p s₁.1).eval ⋙ glueSliceEval X W s₁.1 s₁.2
      = (P.map f₂).words ⋙ (p s₂.1).eval ⋙ glueSliceEval X W s₂.1 s₂.2 :=
  (glueSliceEval_bridge X W p hP f₁ s₁.2).symm.trans
    (hx ▸ glueSliceEval_bridge X W p hP f₂ s₂.2)

include hL in
/-- The copy 2-cells are sound: they are `p s.1`'s own, pushed forward. -/
theorem glueOn_sound_copy (s : GlueV X) (hs : s ∈ S) {a b : GenObj (P.obj s.1).Gen}
    {u v : Quiver.Path a b} (h : (P.obj s.1).rel u v) :
    (Paths.lift (glueOnEval X L S W p hL)).map ((glueOnPre X L S s hs).mapPath u) =
      (Paths.lift (glueOnEval X L S W p hL)).map ((glueOnPre X L S s hs).mapPath v) := by
  rw [glueOnEval_mapPath, glueOnEval_mapPath, (p s.1).sound h]

include hL hP in
/-- **The overlap 2-cells are sound**: the two feet of a span read the same generator the same
way, because both readings factor through the apex's slice (`glueOnSliceEval_span`). -/
theorem glueOn_sound_overlap {s₁ s₂ : GlueV X} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S) {d' : D}
    (f₁ : d' ⟶ s₁.1) (f₂ : d' ⟶ s₂.1) (hx : X.map f₁.op s₁.2 = X.map f₂.op s₂.2)
    {a b : GenObj (P.obj d').Gen} (g : a ⟶ b) :
    (Paths.lift (glueOnEval X L S W p hL)).map
        ((glueOnPre X L S s₁ h₁).mapPath ((P.map f₁).cells.map g))
      = (Paths.lift (glueOnEval X L S W p hL)).map
          (eqToHom (glueOnPre_obj_span X L S h₁ h₂ f₁ f₂ hx a) ≫
            (glueOnPre X L S s₂ h₂).mapPath ((P.map f₂).cells.map g) ≫
            eqToHom (glueOnPre_obj_span X L S h₁ h₂ f₁ f₂ hx b).symm) := by
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, glueOnEval_mapPath,
    glueOnEval_mapPath]
  have key := Functor.congr_hom (glueOnSliceEval_span X W p hP f₁ f₂ hx) (Quiver.Hom.toPath g)
  simp only [Functor.comp_map, Paths.lift_toPath] at key
  refine (eqToHom_conj_congr _ _ key).trans ?_
  refine (eqToHom_conj_conj _ _ _ _ _).trans ?_
  exact (eqToHom_conj_conj _ _ _ _ _).symm

include hL hP in
/-- **The 2-cells of the glued polygraph are sound.** -/
theorem glueOn_sound {v t : GenObj (GlueOnGen X L S)} {u u' : Quiver.Path v t}
    (h : GlueOnRel X L S u u') :
    (Paths.lift (glueOnEval X L S W p hL)).map u
      = (Paths.lift (glueOnEval X L S W p hL)).map u' := by
  cases h with
  | copy s hs hr => exact glueOn_sound_copy X L S W p hL s hs hr
  | overlap h₁ h₂ f₁ f₂ hx g => exact glueOn_sound_overlap X L S W p hL hP h₁ h₂ f₁ f₂ hx g

include hL hP in
/-- **The comparison functor**: a word of the glued polygraph, read in `(∫X)[W⁻¹]`. -/
noncomputable def glueOnDesc : (glueOn X L S).presented ⥤
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization :=
  (glueOn X L S).desc (glueOnEval X L S W p hL) (glueOn_sound X L S W p hL hP)

include hL hP in
/-- **A copy, read by Φ**: the copy's own interpretation, pushed along the cartesian lift.  This is
the bridge every spelling argument runs through — it turns "a word of `P s.1`" into "an arrow of
`(∫X)[W⁻¹]`" with no bookkeeping at the call site. -/
theorem glueOnIncl_desc (s : GlueV X) (hs : s ∈ S) :
    (glueOnIncl X L S s hs).functor ⋙ glueOnDesc X L S W p hL hP
      = (p s.1).E ⋙ glueSliceEval X W s.1 s.2 := by
  refine Quotient.lift_unique' _ _ _ ?_
  rw [← Functor.assoc, Hom.quot_comp_functor, Functor.assoc,
    show (glueOn X L S).quot ⋙ glueOnDesc X L S W p hL hP
        = Paths.lift (glueOnEval X L S W p hL) from
      Quotient.lift_spec _ _ fun _ _ _ _ h => glueOn_sound X L S W p hL hP h, ← Functor.assoc]
  refine Functor.ext (fun a => (glueOnAt_glueOnPt X L S W p hL s hs a.as).symm) ?_
  intro a b u
  change (Paths.lift (glueOnEval X L S W p hL)).map ((glueOnIncl X L S s hs).words.map u) = _
  rw [show (glueOnIncl X L S s hs).words.map u = (glueOnPre X L S s hs).mapPath u from
      Paths.lift_comp_of_map _ u]
  exact glueOnEval_mapPath X L S W p hL s hs u

include hL hP in
@[simp] theorem glueOnDesc_obj (v : GlueOnV X L S) :
    (glueOnDesc X L S W p hL hP).obj ((presentedVEquiv (glueOn X L S)) v)
      = glueOnAt X L S W ⟨v⟩ := rfl

/-! ## The base 0-cell of an object

`Glue`'s bijective labels named the terminal object of each slice on the nose; here it is named
only up to isomorphism, and that isomorphism is the one every spelling argument conjugates by.
Fixing it once, for every object at once, is what keeps the argument from being circular. -/

/-- The 0-cell of `P d` naming the terminal object of the slice over `d`. -/
noncomputable def sliceBase (d : D) : (P.obj d).V :=
  ((p d).E.objPreimage ((W.over (X := d)).Q.obj (Over.mk (𝟙 d)))).as.as

/-- …and the isomorphism naming it. -/
noncomputable def sliceBaseIso (d : D) :
    (p d).at' ⟨sliceBase W p d⟩ ≅ (W.over (X := d)).Q.obj (Over.mk (𝟙 d)) :=
  (p d).E.objObjPreimageIso _

/-- The 0-cell of `∫X` that `c`'s own slice contributes at its base. -/
noncomputable def glueOnBase (c : (X.Elements)ᵒᵖ) : GlueV X :=
  gluePt X L ((CategoryOfElements.π X).leftOp.obj c) c.unop.2
    (sliceBase W p ((CategoryOfElements.π X).leftOp.obj c))

/-- **The base 0-cell is a 0-cell of every copy `c` maps into** — the span with apex `c`, read on
0-cells, which is why the base does not depend on the copy. -/
theorem gluePt_sliceBase {s : GlueV X} {c : (X.Elements)ᵒᵖ} (k : c ⟶ elt X s) :
    gluePt X L s.1 s.2 ((P.map ((CategoryOfElements.π X).leftOp.map k)).cells.obj
        ⟨sliceBase W p ((CategoryOfElements.π X).leftOp.obj c)⟩).as
      = glueOnBase X L W p c :=
  (gluePt_map X L _ s.2 _).trans
    (congrArg (fun z => gluePt X L ((CategoryOfElements.π X).leftOp.obj c) z _)
      (elements_snd_map X k))

/-- …so `Generating` is all it takes for the base 0-cell to exist. -/
theorem glueOnBase_covered (hgen : Generating X S) (c : (X.Elements)ᵒᵖ) :
    Covered X L S (glueOnBase X L W p c) := by
  obtain ⟨s, hs, ⟨k⟩⟩ := hgen c
  exact ⟨s, hs, _, gluePt_sliceBase X L W p k⟩

include hL in
/-- The base cell of `c`'s own slice, read in `(∫X)[W⁻¹]`, is the base 0-cell. -/
theorem glueOnBase_at (c : (X.Elements)ᵒᵖ) :
    (glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).obj
        ((p _).at' ⟨sliceBase W p ((CategoryOfElements.π X).leftOp.obj c)⟩)
      = (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj (elt X (glueOnBase X L W p c)) :=
  glueAt_gluePt X L W p hL _ _ _

/-- …and the terminal object of that slice reads as `c` itself. -/
theorem glueOnBase_obj (c : (X.Elements)ᵒᵖ) :
    (glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).obj
        ((W.over (X := (CategoryOfElements.π X).leftOp.obj c)).Q.obj
          (Over.mk (𝟙 ((CategoryOfElements.π X).leftOp.obj c))))
      = (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj c :=
  (glueSliceEval_obj X W _ _ _).trans
    (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj (elementsLift_id X c))

include hL in
/-- **The base 0-cell at `c` names `c`** — up to an isomorphism, which is all `Presents` asks. -/
noncomputable def glueOnBaseIso (c : (X.Elements)ᵒᵖ) :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj (elt X (glueOnBase X L W p c))
      ≅ (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj c :=
  eqToIso (glueOnBase_at X L W p hL c).symm ≪≫
    (glueSliceEval X W _ _).mapIso (sliceBaseIso W p _) ≪≫ eqToIso (glueOnBase_obj X W c)

/-- The base 0-cell at `c`, as a 0-cell of the glued polygraph. -/
noncomputable def glueOnBaseV (hgen : Generating X S) (c : (X.Elements)ᵒᵖ) : GlueOnV X L S :=
  ⟨glueOnBase X L W p c, glueOnBase_covered X L S W p hgen c⟩

include hL hP in
/-- **The comparison is essentially surjective**: every object has a base 0-cell naming it. -/
theorem glueOnDesc_essSurj (hgen : Generating X S) :
    (glueOnDesc X L S W p hL hP).EssSurj where
  mem_essImage c := by
    obtain ⟨d, rfl⟩ := (Localization.Construction.objEquiv
      (W.inverseImage (CategoryOfElements.π X).leftOp)).surjective c
    exact ⟨presentedVEquiv (glueOn X L S) (glueOnBaseV X L S W p hgen d),
      ⟨glueOnBaseIso X L W p hL d⟩⟩

/-! ## Fullness

Every arrow of `(∫X)[W⁻¹]` is a `Q`-image or a formal inverse, conjugated onto the base 0-cells;
`Generating` puts both of its endpoints and the arrow itself into a single slice, where `p s.1`
being an equivalence spells them. -/

include hL hP in
/-- **Fullness, one copy at a time.** -/
theorem exists_word_of_slice (s : GlueV X) (hs : s ∈ S) {b₁ b₂ : (P.obj s.1).V}
    (n : (p s.1).at' ⟨b₁⟩ ⟶ (p s.1).at' ⟨b₂⟩) :
    ∃ u : presentedVEquiv (glueOn X L S) (glueOnPt X L S s hs b₁) ⟶
        presentedVEquiv (glueOn X L S) (glueOnPt X L S s hs b₂),
      (glueOnDesc X L S W p hL hP).map u
        = eqToHom (glueOnAt_glueOnPt X L S W p hL s hs b₁).symm ≫
          (glueSliceEval X W s.1 s.2).map n ≫
          eqToHom (glueOnAt_glueOnPt X L S W p hL s hs b₂) := by
  obtain ⟨h, rfl⟩ := (p s.1).E.map_surjective n
  exact ⟨(glueOnIncl X L S s hs).functor.map h,
    Functor.congr_hom (glueOnIncl_desc X L S W p hL hP s hs) h⟩

include hP in
/-- The base cell of `c`'s own slice, read in the slice under an arrow out of `c`. -/
noncomputable def sliceBaseOver {s : GlueV X} {c : (X.Elements)ᵒᵖ} (k : c ⟶ elt X s) :
    (p s.1).at' ⟨((P.map ((CategoryOfElements.π X).leftOp.map k)).cells.obj
        ⟨sliceBase W p ((CategoryOfElements.π X).leftOp.obj c)⟩).as⟩
      ≅ (W.over (X := s.1)).Q.obj
          ((Over.post (CategoryOfElements.π X).leftOp).obj (Over.mk k)) :=
  eqToIso (Functor.congr_obj (hP ((CategoryOfElements.π X).leftOp.map k)) _) ≪≫
    (overMapLoc W _).mapIso (sliceBaseIso W p _) ≪≫
    eqToIso ((overMapLoc_obj W _ _).trans
      (congrArg (Localization.Construction.objEquiv (W.over (X := s.1)))
        (OverCocone.map_obj_top _)))

include hL in
/-- The source of `sliceBaseOver`, read in `(∫X)[W⁻¹]`: `c`'s base 0-cell. -/
theorem sliceBaseOver_src {s : GlueV X} {c : (X.Elements)ᵒᵖ} (k : c ⟶ elt X s) :
    (glueSliceEval X W s.1 s.2).obj
        ((p s.1).at' ⟨((P.map ((CategoryOfElements.π X).leftOp.map k)).cells.obj
          ⟨sliceBase W p ((CategoryOfElements.π X).leftOp.obj c)⟩).as⟩)
      = (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj (elt X (glueOnBase X L W p c)) :=
  (glueAt_gluePt X L W p hL s.1 s.2 _).trans
    (congrArg (fun v : GlueV X =>
      (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj (elt X v))
      (gluePt_sliceBase X L W p k))

/-- …and its target: `c` itself, since the cartesian lift is a section of the projection. -/
theorem sliceBaseOver_tgt {s : GlueV X} {c : (X.Elements)ᵒᵖ} (k : c ⟶ elt X s) :
    (glueSliceEval X W s.1 s.2).obj ((W.over (X := s.1)).Q.obj
        ((Over.post (CategoryOfElements.π X).leftOp).obj (Over.mk k)))
      = (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj c :=
  (glueSliceEval_obj X W s.1 s.2 _).trans
    (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
      (Functor.congr_obj (elementsLift_post X (elt X s)) (Over.mk k)))

include hL hP in
/-- **The comparison of base cells is the base isomorphism itself**, read in the slice under `k`;
in particular it does not depend on `k`, which is what makes the copies agree. -/
theorem glueSliceEval_sliceBaseOver {s : GlueV X} {c : (X.Elements)ᵒᵖ} (k : c ⟶ elt X s) :
    (glueSliceEval X W s.1 s.2).mapIso (sliceBaseOver X W p hP k)
      = eqToIso (sliceBaseOver_src X L W p hL k) ≪≫ glueOnBaseIso X L W p hL c ≪≫
        eqToIso (sliceBaseOver_tgt X W k).symm := by
  have hE : overMapLoc W ((CategoryOfElements.π X).leftOp.map k) ⋙ glueSliceEval X W s.1 s.2
      = glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c) c.unop.2 :=
    (overMapLoc_comp_glueSliceEval X W _ s.2).trans
      (congrArg (glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c))
        (elements_snd_map X k))
  ext
  simp only [Functor.mapIso_hom, sliceBaseOver, glueOnBaseIso, Iso.trans_hom, eqToIso.hom]
  refine (eqToHom_conj_map (glueSliceEval X W s.1 s.2) _ _ _).trans ?_
  refine (eqToHom_conj_congr _ _ (Functor.congr_hom hE
    (sliceBaseIso W p ((CategoryOfElements.π X).leftOp.obj c)).hom)).trans ?_
  refine (eqToHom_conj_conj _ _ _ _ _).trans ?_
  exact (eqToHom_conj_conj _ _ _ _ _).symm

include hL hP in
/-- **An arrow that factors through one copy is a word.**  Both endpoints are compared with their
base 0-cells inside the *same* slice, so the two comparisons are the ones `glueOnBaseIso` names and
nothing else is left to choose. -/
theorem exists_word_of_arrow (hgen : Generating X S) {s : GlueV X} (hs : s ∈ S)
    {a b : (X.Elements)ᵒᵖ} (kA : a ⟶ elt X s) (kB : b ⟶ elt X s)
    (g : (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj a ⟶
      (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj b)
    {m : (W.over (X := s.1)).Q.obj ((Over.post (CategoryOfElements.π X).leftOp).obj (Over.mk kA))
      ⟶ (W.over (X := s.1)).Q.obj
        ((Over.post (CategoryOfElements.π X).leftOp).obj (Over.mk kB))}
    (hm : (glueSliceEval X W s.1 s.2).map m
      = eqToHom (sliceBaseOver_tgt X W kA) ≫ g ≫ eqToHom (sliceBaseOver_tgt X W kB).symm) :
    ∃ u : presentedVEquiv (glueOn X L S) (glueOnBaseV X L S W p hgen a) ⟶
        presentedVEquiv (glueOn X L S) (glueOnBaseV X L S W p hgen b),
      (glueOnDesc X L S W p hL hP).map u
        = (glueOnBaseIso X L W p hL a).hom ≫ g ≫ (glueOnBaseIso X L W p hL b).inv := by
  obtain ⟨u₀, hu₀⟩ := exists_word_of_slice X L S W p hL hP s hs
    ((sliceBaseOver X W p hP kA).hom ≫ m ≫ (sliceBaseOver X W p hP kB).inv)
  have hA : glueOnPt X L S s hs _ = glueOnBaseV X L S W p hgen a :=
    Subtype.ext (gluePt_sliceBase X L W p kA)
  have hB : glueOnPt X L S s hs _ = glueOnBaseV X L S W p hgen b :=
    Subtype.ext (gluePt_sliceBase X L W p kB)
  have hia := congrArg Iso.hom (glueSliceEval_sliceBaseOver X L W p hL hP kA)
  have hib := congrArg Iso.inv (glueSliceEval_sliceBaseOver X L W p hL hP kB)
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
    eqToIso.inv] at hia hib
  have hcore : (glueSliceEval X W s.1 s.2).map
        ((sliceBaseOver X W p hP kA).hom ≫ m ≫ (sliceBaseOver X W p hP kB).inv)
      = eqToHom (sliceBaseOver_src X L W p hL kA) ≫
        ((glueOnBaseIso X L W p hL a).hom ≫ g ≫ (glueOnBaseIso X L W p hL b).inv) ≫
        eqToHom (sliceBaseOver_src X L W p hL kB).symm := by
    rw [Functor.map_comp, Functor.map_comp, hia, hib, hm]
    simp
  refine ⟨eqToHom (congrArg (presentedVEquiv (glueOn X L S)) hA.symm) ≫ u₀ ≫
    eqToHom (congrArg (presentedVEquiv (glueOn X L S)) hB), ?_⟩
  refine (eqToHom_conj_map (glueOnDesc X L S W p hL hP) _ _ _).trans ?_
  refine (eqToHom_conj_congr _ _ hu₀).trans ?_
  refine (eqToHom_conj_conj _ _ _ _ _).trans ?_
  refine (eqToHom_conj_congr _ _ hcore).trans ?_
  refine (eqToHom_conj_conj _ _ _ _ _).trans ?_
  exact eqToHom_conj_id _ _ _

/-- **An arrow of `∫X`, read in the slice under a chosen arrow out of its target.** -/
theorem glueSliceEval_post_map {s : GlueV X} {a b : (X.Elements)ᵒᵖ} (f : a ⟶ b)
    (k : b ⟶ elt X s) :
    (glueSliceEval X W s.1 s.2).map ((W.over (X := s.1)).Q.map
        ((Over.post (CategoryOfElements.π X).leftOp).map
          (Over.homMk f rfl : Over.mk (f ≫ k) ⟶ Over.mk k)))
      = eqToHom (sliceBaseOver_tgt X W (f ≫ k)) ≫
        (W.inverseImage (CategoryOfElements.π X).leftOp).Q.map f ≫
        eqToHom (sliceBaseOver_tgt X W k).symm := by
  refine (Functor.congr_hom (glueSliceEval_fac X W s.1 s.2)
    ((Over.post (CategoryOfElements.π X).leftOp).map
      (Over.homMk f rfl : Over.mk (f ≫ k) ⟶ Over.mk k))).trans ?_
  refine (eqToHom_conj_congr _ _ (congrArg
    (W.inverseImage (CategoryOfElements.π X).leftOp).Q.map
    (Functor.congr_hom (elementsLift_post X (elt X s))
      (Over.homMk f rfl : Over.mk (f ≫ k) ⟶ Over.mk k)))).trans ?_
  refine (eqToHom_conj_congr _ _
    (eqToHom_conj_map (W.inverseImage (CategoryOfElements.π X).leftOp).Q _ _ _)).trans ?_
  exact eqToHom_conj_conj _ _ _ _ _

include hL hP in
/-- **A 0-cell is spelled onto the base 0-cell of its own object**, invertibly: the comparison
lives in one copy, where `(p s.1).E` is fully faithful. -/
theorem exists_wordIso_glueOnBase (hgen : Generating X S) (v : GlueOnV X L S) :
    ∃ e : presentedVEquiv (glueOn X L S) (glueOnBaseV X L S W p hgen (elt X v.1)) ≅
        presentedVEquiv (glueOn X L S) v,
      (glueOnDesc X L S W p hL hP).mapIso e = glueOnBaseIso X L W p hL (elt X v.1) := by
  obtain ⟨w, hw⟩ := v
  obtain ⟨s, hs, a, rfl⟩ := hw
  set kA : elt X (gluePt X L s.1 s.2 a) ⟶ elt X s :=
    ((elementsLiftOver X (elt X s)).obj (L.ob s.1 a)).hom with hkA
  have hkey : (W.over (X := s.1)).Q.obj
      ((Over.post (CategoryOfElements.π X).leftOp).obj (Over.mk kA)) = (p s.1).at' ⟨a⟩ :=
    (hL s.1 a).symm
  set ι : (p s.1).at' ⟨((P.map ((CategoryOfElements.π X).leftOp.map kA)).cells.obj
      ⟨sliceBase W p ((CategoryOfElements.π X).leftOp.obj
        (elt X (gluePt X L s.1 s.2 a)))⟩).as⟩ ≅ (p s.1).at' ⟨a⟩ :=
    sliceBaseOver X W p hP kA ≪≫ eqToIso hkey with hι
  refine ⟨eqToIso (congrArg (presentedVEquiv (glueOn X L S))
      (Subtype.ext (gluePt_sliceBase X L W p kA)).symm) ≪≫
    (glueOnIncl X L S s hs).functor.mapIso ((p s.1).E.preimageIso ι) ≪≫ eqToIso rfl, ?_⟩
  have hia := congrArg Iso.hom (glueSliceEval_sliceBaseOver X L W p hL hP kA)
  simp only [Functor.mapIso_hom, Iso.trans_hom, eqToIso.hom] at hia
  ext
  simp only [Functor.mapIso_hom, Iso.trans_hom, eqToIso.hom]
  refine (eqToHom_conj_map (glueOnDesc X L S W p hL hP) _ _ _).trans ?_
  refine (eqToHom_conj_congr _ _ (Functor.congr_hom
    (glueOnIncl_desc X L S W p hL hP s hs) ((p s.1).E.preimageIso ι).hom)).trans ?_
  refine (eqToHom_conj_conj _ _ _ _ _).trans ?_
  refine (eqToHom_conj_congr _ _ (congrArg (glueSliceEval X W s.1 s.2).map
    ((p s.1).E.map_preimage ι.hom))).trans ?_
  have hmid : (glueSliceEval X W s.1 s.2).map ι.hom
      = eqToHom (sliceBaseOver_src X L W p hL kA) ≫
        (glueOnBaseIso X L W p hL (elt X (gluePt X L s.1 s.2 a))).hom ≫
        eqToHom ((sliceBaseOver_tgt X W kA).symm.trans
          (congrArg (glueSliceEval X W s.1 s.2).obj hkey)) := by
    rw [hι, Iso.trans_hom, eqToIso.hom, Functor.map_comp, hia, eqToHom_map]
    simp
  refine (eqToHom_conj_congr _ _ hmid).trans ?_
  refine (eqToHom_conj_conj _ _ _ _ _).trans ?_
  exact eqToHom_conj_id _ _ _

include hL hP in
/-- **An arrow of `∫X` is a word**, conjugated onto the base 0-cells. -/
theorem exists_word_of_Q (hgen : Generating X S) {a b : (X.Elements)ᵒᵖ} (f : a ⟶ b) :
    ∃ u : presentedVEquiv (glueOn X L S) (glueOnBaseV X L S W p hgen a) ⟶
        presentedVEquiv (glueOn X L S) (glueOnBaseV X L S W p hgen b),
      (glueOnDesc X L S W p hL hP).map u
        = (glueOnBaseIso X L W p hL a).hom ≫
          (W.inverseImage (CategoryOfElements.π X).leftOp).Q.map f ≫
          (glueOnBaseIso X L W p hL b).inv := by
  obtain ⟨s, hs, ⟨k⟩⟩ := hgen b
  exact exists_word_of_arrow X L S W p hL hP hgen hs (f ≫ k) k _
    (glueSliceEval_post_map X W f k)

include hL hP in
/-- **…and so is the formal inverse of a `W`-arrow**: it is an arrow of the same slice, already
inverted there. -/
theorem exists_word_of_wInv (hgen : Generating X S) {a b : (X.Elements)ᵒᵖ} (f : a ⟶ b)
    (hf : W.inverseImage (CategoryOfElements.π X).leftOp f) :
    ∃ u : presentedVEquiv (glueOn X L S) (glueOnBaseV X L S W p hgen b) ⟶
        presentedVEquiv (glueOn X L S) (glueOnBaseV X L S W p hgen a),
      (glueOnDesc X L S W p hL hP).map u
        = (glueOnBaseIso X L W p hL b).hom ≫ Localization.Construction.wInv f hf ≫
          (glueOnBaseIso X L W p hL a).inv := by
  obtain ⟨s, hs, ⟨k⟩⟩ := hgen b
  haveI : IsIso ((W.over (X := s.1)).Q.map ((Over.post (CategoryOfElements.π X).leftOp).map
      (Over.homMk f rfl : Over.mk (f ≫ k) ⟶ Over.mk k))) :=
    Localization.inverts (W.over (X := s.1)).Q (W.over (X := s.1)) _ hf
  refine exists_word_of_arrow X L S W p hL hP hgen hs k (f ≫ k) _
    (m := inv ((W.over (X := s.1)).Q.map ((Over.post (CategoryOfElements.π X).leftOp).map
      (Over.homMk f rfl : Over.mk (f ≫ k) ⟶ Over.mk k)))) ?_
  have hhi : ∀ {Z : (W.inverseImage (CategoryOfElements.π X).leftOp).Localization}
      (x : (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj a ⟶ Z),
      (W.inverseImage (CategoryOfElements.π X).leftOp).Q.map f ≫
        Localization.Construction.wInv f hf ≫ x = x :=
    fun x => (Localization.Construction.wIso f hf).hom_inv_id_assoc x
  rw [Functor.map_inv]
  refine IsIso.inv_eq_of_hom_inv_id ?_
  rw [glueSliceEval_post_map X W f k]
  simp [hhi]

include hL in
/-- The comparison of an object of the localization with the base 0-cell of a name for it. -/
private noncomputable def glueOnBaseIsoAt (hgen : Generating X S)
    {A : (W.inverseImage (CategoryOfElements.π X).leftOp).Localization} (a : (X.Elements)ᵒᵖ)
    (hA : (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj a = A) :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
        (elt X (glueOnBaseV X L S W p hgen a).1) ≅ A :=
  glueOnBaseIso X L W p hL a ≪≫ eqToIso hA

/-- Everything is a word, once conjugated onto the base 0-cells — the property the induction over
`Q`-images and formal inverses establishes. -/
private def spelled (hgen : Generating X S) :
    MorphismProperty ((W.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  fun A B g => ∀ (a b : (X.Elements)ᵒᵖ)
    (hA : (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj a = A)
    (hB : (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj b = B),
    ∃ u : presentedVEquiv (glueOn X L S) (glueOnBaseV X L S W p hgen a) ⟶
        presentedVEquiv (glueOn X L S) (glueOnBaseV X L S W p hgen b),
      (glueOnDesc X L S W p hL hP).map u
        = (glueOnBaseIsoAt X L S W p hL hgen a hA).hom ≫ g ≫
          (glueOnBaseIsoAt X L S W p hL hgen b hB).inv

private instance spelled_comp (hgen : Generating X S) :
    (spelled X L S W p hL hP hgen).IsStableUnderComposition where
  comp_mem {_ B _} g g' hg hg' := by
    intro a c hA hC
    obtain ⟨b, hb⟩ : ∃ b : (X.Elements)ᵒᵖ,
        (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj b = B :=
      ⟨(Localization.Construction.objEquiv _).symm B,
        (Localization.Construction.objEquiv _).apply_symm_apply B⟩
    obtain ⟨u₁, hu₁⟩ := hg a b hA hb
    obtain ⟨u₂, hu₂⟩ := hg' b c hb hC
    refine ⟨u₁ ≫ u₂, ?_⟩
    rw [Functor.map_comp, hu₁, hu₂]
    exact conj_comp_conj _ _ _ g g'

private theorem spelled_Q (hgen : Generating X S) :
    ∀ ⦃a b : (X.Elements)ᵒᵖ⦄ (f : a ⟶ b),
      spelled X L S W p hL hP hgen
        ((W.inverseImage (CategoryOfElements.π X).leftOp).Q.map f) := by
  intro a₀ b₀ f a b hA hB
  obtain rfl := (Localization.Construction.objEquiv
    (W := W.inverseImage (CategoryOfElements.π X).leftOp)).injective hA
  obtain rfl := (Localization.Construction.objEquiv
    (W := W.inverseImage (CategoryOfElements.π X).leftOp)).injective hB
  simpa [glueOnBaseIsoAt] using exists_word_of_Q X L S W p hL hP hgen f

private theorem spelled_wInv (hgen : Generating X S) :
    ∀ ⦃a b : (X.Elements)ᵒᵖ⦄ (f : a ⟶ b)
      (hf : W.inverseImage (CategoryOfElements.π X).leftOp f),
      spelled X L S W p hL hP hgen (Localization.Construction.wInv f hf) := by
  intro a₀ b₀ f hf a b hA hB
  obtain rfl := (Localization.Construction.objEquiv
    (W := W.inverseImage (CategoryOfElements.π X).leftOp)).injective hA
  obtain rfl := (Localization.Construction.objEquiv
    (W := W.inverseImage (CategoryOfElements.π X).leftOp)).injective hB
  simpa [glueOnBaseIsoAt] using exists_word_of_wInv X L S W p hL hP hgen f hf

include hL hP in
/-- **The comparison is full**: every arrow is a word between base 0-cells, and every 0-cell is
spelled onto its own base. -/
theorem glueOnDesc_full (hgen : Generating X S) : (glueOnDesc X L S W p hL hP).Full where
  map_surjective {A B} g := by
    obtain ⟨vA, rfl⟩ : ∃ v, presentedVEquiv (glueOn X L S) v = A :=
      ⟨(presentedVEquiv (glueOn X L S)).symm A, rfl⟩
    obtain ⟨vB, rfl⟩ : ∃ v, presentedVEquiv (glueOn X L S) v = B :=
      ⟨(presentedVEquiv (glueOn X L S)).symm B, rfl⟩
    obtain ⟨eA, hEA⟩ := exists_wordIso_glueOnBase X L S W p hL hP hgen vA
    obtain ⟨eB, hEB⟩ := exists_wordIso_glueOnBase X L S W p hL hP hgen vB
    have h : spelled X L S W p hL hP hgen g := by
      rw [Localization.Construction.morphismProperty_eq_top (spelled X L S W p hL hP hgen)
        (spelled_Q X L S W p hL hP hgen) (spelled_wInv X L S W p hL hP hgen)]
      trivial
    obtain ⟨u₀, hu₀⟩ := h (elt X vA.1) (elt X vB.1) rfl rfl
    have hA' : (glueOnDesc X L S W p hL hP).map eA.inv
        = (glueOnBaseIso X L W p hL (elt X vA.1)).inv := by rw [← Functor.mapIso_inv, hEA]
    have hB' : (glueOnDesc X L S W p hL hP).map eB.hom
        = (glueOnBaseIso X L W p hL (elt X vB.1)).hom := by rw [← Functor.mapIso_hom, hEB]
    refine ⟨eA.inv ≫ u₀ ≫ eB.hom, ?_⟩
    rw [Functor.map_comp, Functor.map_comp, hu₀, hA', hB']
    simp [glueOnBaseIsoAt]

include hL hP in
/-- **`glueOn X L S` presents `(∫X)[W⁻¹]`.**  The 0-cells cover because every object has a base
0-cell, the 1-cells span because every arrow factors through one copy, and what is left over is
the word problem. -/
noncomputable def presentsGlueOn (hgen : Generating X S)
    (hcomplete : ∀ {v t : GenObj (GlueOnGen X L S)} (u u' : Quiver.Path v t),
      (Paths.lift (glueOnEval X L S W p hL)).map u
          = (Paths.lift (glueOnEval X L S W p hL)).map u' →
        (glueOn X L S).quot.map u = (glueOn X L S).quot.map u') :
    Presents (glueOn X L S)
      ((W.inverseImage (CategoryOfElements.π X).leftOp).Localization) := by
  haveI := glueOnDesc_full X L S W p hL hP hgen
  haveI := glueOnDesc_essSurj X L S W p hL hP hgen
  haveI : (glueOnDesc X L S W p hL hP).Faithful := ⟨by
    intro A B f g h
    obtain ⟨u, rfl⟩ := (glueOn X L S).quot.map_surjective f
    obtain ⟨v, rfl⟩ := (glueOn X L S).quot.map_surjective g
    exact hcomplete u v h⟩
  exact ⟨glueOnDesc X L S W p hL hP, { }⟩

end Compare

end Polygraph


end CategoryTheory
