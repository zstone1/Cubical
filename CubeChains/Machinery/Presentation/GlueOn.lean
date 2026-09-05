import CubeChains.Machinery.Presentation.Glue

/-!
# Machinery/Presentation/GlueOn — copies over a generating set only

The redundancy that makes `Glue`'s bijectivity hypothesis unattainable is exactly what makes this
version work: a localization keeps one object per object of `Over d` while a compact presentation
names one per *iso-class*, so `L.ob d` cannot be surjective — but for the same reason every object
is *isomorphic* to a named one, which is all `Presents` ever asks.

So the 0-cells are the objects a copy over `S` reaches (`Covered`), the 1-cells are the copies'
modulo the *spans* `s₁ ← e → s₂` — a span's apex need carry no copy — and what inverts the slice
presentations is `SliceRetract` in place of bijective labels: the localized slices are posets, the
labels are injective, and every slice object is entered from a canonical labelled one.

The span identification is taken on the 1-cells, not imposed on them by a 2-cell, which is what
makes the copies' redundancy invisible downstream and `spanIncl_eq` a statement about 1-cells.
That needs `Cellular P`: a `Polygraph` morphism spells a 1-cell by a *word*, so the two readings
of a span are comparable as 1-cells only when each word has length one.
-/

universe w w' v₁ u₁ u'

namespace CategoryTheory

namespace Polygraph

open Opposite

variable {D : Type u₁} [Category.{v₁} D]

/-- **A diagram of polygraphs whose maps spell a 1-cell by a single 1-cell.**  A morphism of
polygraphs sends a 1-cell to a *word*, so the two readings of a span are parallel words and can
only be identified by a 2-cell; along a cellular map they are 1-cells, and the gluing takes the
coequalizer in dimension 1 as well as in dimension 0.  `Hom.ofPre` is always cellular. -/
structure Cellular (P : D ⥤ Polygraph.{w', u'}) where
  /-- the 1-cell that `P.map f` spells a 1-cell by -/
  cell {d' d : D} {a b : GenObj (P.obj d').Gen} (f : d' ⟶ d) (g : a ⟶ b) :
    (P.obj d).Gen ((P.map f).cells.obj a).as ((P.map f).cells.obj b).as
  /-- …and it is the whole word -/
  spec {d' d : D} {a b : GenObj (P.obj d').Gen} (f : d' ⟶ d) (g : a ⟶ b) :
    (P.map f).cells.map g = Quiver.Hom.toPath (cell f g)

variable (X : Dᵒᵖ ⥤ Type w) {P : D ⥤ Polygraph.{w', u'}}
  (L : SliceLabels P) (S : Set (GlueV X)) (C : Cellular P)

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

A 0-cell is the object of `∫X` a copy's 0-cell *names*, so two copies naming the same object give
literally the same 0-cell: the coequalizer, already taken.  A 1-cell is the same in dimension one —
a 1-cell of some `P s.1` with `s ∈ S`, modulo the **overlap**: a span `s₁ ← e → s₂` with both feet
in `S` identifies the two readings of a 1-cell of `P e`.  Naming the endpoints in the raw datum is
what makes that a relation at fixed 0-cells: the two readings land on the same 0-cell
(`glueOnPt_span`) and the proof of that is irrelevant, so nothing is transported.

The only 2-cells left are then each copy's own. -/

/-- **The two feet of a span name the same 0-cell.** -/
theorem glueOnPt_span {s₁ s₂ : GlueV X} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S) {d' : D}
    (f₁ : d' ⟶ s₁.1) (f₂ : d' ⟶ s₂.1) (hx : X.map f₁.op s₁.2 = X.map f₂.op s₂.2)
    (a : GenObj (P.obj d').Gen) :
    glueOnPt X L S s₁ h₁ ((P.map f₁).cells.obj a).as
      = glueOnPt X L S s₂ h₂ ((P.map f₂).cells.obj a).as :=
  Subtype.ext ((glueOnPt_map X L S h₁ f₁ a).trans (hx ▸ (glueOnPt_map X L S h₂ f₂ a).symm))

/-- A 1-cell of a copy, together with the two 0-cells it joins. -/
structure GlueOnRaw (A B : GlueOnV X L S) : Type (max u₁ w u' w') where
  /-- the copy it sits in -/
  s : GlueV X
  /-- …which is one of the copies -/
  hs : s ∈ S
  /-- its source there -/
  a : (P.obj s.1).V
  /-- its target there -/
  b : (P.obj s.1).V
  /-- the 1-cell itself -/
  g : (P.obj s.1).Gen a b
  /-- the 0-cell its source names -/
  src : glueOnPt X L S s hs a = A
  /-- the 0-cell its target names -/
  tgt : glueOnPt X L S s hs b = B

/-- **The overlap, on 1-cells**: the two feet of a span read a 1-cell of the apex the same way. -/
inductive GlueOnEq (X : Dᵒᵖ ⥤ Type w) {P : D ⥤ Polygraph.{w', u'}} (L : SliceLabels P)
    (S : Set (GlueV X)) (C : Cellular P) :
    ∀ {A B : GlueOnV X L S}, GlueOnRaw X L S A B → GlueOnRaw X L S A B → Prop
  | span {s₁ s₂ : GlueV X} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S) {d' : D}
      (f₁ : d' ⟶ s₁.1) (f₂ : d' ⟶ s₂.1) (hx : X.map f₁.op s₁.2 = X.map f₂.op s₂.2)
      {a b : GenObj (P.obj d').Gen} (g : a ⟶ b) {A B : GlueOnV X L S}
      (hA : glueOnPt X L S s₁ h₁ ((P.map f₁).cells.obj a).as = A)
      (hB : glueOnPt X L S s₁ h₁ ((P.map f₁).cells.obj b).as = B) :
      GlueOnEq X L S C ⟨s₁, h₁, _, _, C.cell f₁ g, hA, hB⟩
        ⟨s₂, h₂, _, _, C.cell f₂ g,
          (glueOnPt_span X L S h₁ h₂ f₁ f₂ hx a).symm.trans hA,
          (glueOnPt_span X L S h₁ h₂ f₁ f₂ hx b).symm.trans hB⟩

/-- 1-cells: a 1-cell of `P s.1` in the copy at `s ∈ S`, modulo the overlap. -/
def GlueOnGen (A B : GlueOnV X L S) : Type (max u₁ w u' w') :=
  Quot (@GlueOnEq _ _ X _ L S C A B)

/-- The copy of `P s.1` sitting over `s ∈ S`. -/
def glueOnPre (s : GlueV X) (hs : s ∈ S) :
    GenObj (P.obj s.1).Gen ⥤q GenObj (GlueOnGen X L S C) where
  obj a := ⟨glueOnPt X L S s hs a.as⟩
  map g := Quot.mk _ ⟨s, hs, _, _, g, rfl, rfl⟩

/-- …read as a vertex of the generating quiver. -/
theorem glueOnPre_obj_span {s₁ s₂ : GlueV X} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S) {d' : D}
    (f₁ : d' ⟶ s₁.1) (f₂ : d' ⟶ s₂.1) (hx : X.map f₁.op s₁.2 = X.map f₂.op s₂.2)
    (a : GenObj (P.obj d').Gen) :
    (glueOnPre X L S C s₁ h₁).obj ((P.map f₁).cells.obj a)
      = (glueOnPre X L S C s₂ h₂).obj ((P.map f₂).cells.obj a) :=
  congrArg (fun v => (⟨v⟩ : GenObj (GlueOnGen X L S C)))
    (glueOnPt_span X L S h₁ h₂ f₁ f₂ hx a)

/-- **…and they are the same 1-cell**: `Quot.sound`, with the 0-cells substituted away, so the
identification carries no transport at all. -/
theorem glueOnPre_span_heq {s₁ s₂ : GlueV X} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S) {d' : D}
    (f₁ : d' ⟶ s₁.1) (f₂ : d' ⟶ s₂.1) (hx : X.map f₁.op s₁.2 = X.map f₂.op s₂.2)
    {a b : GenObj (P.obj d').Gen} (g : a ⟶ b) :
    (glueOnPre X L S C s₁ h₁).map (C.cell f₁ g)
      ≍ (glueOnPre X L S C s₂ h₂).map (C.cell f₂ g) := by
  have key : ∀ {A B A' B' : GlueOnV X L S} (hA : A' = A) (hB : B' = B)
      (r₁ : GlueOnRaw X L S A B) (r₂ : GlueOnRaw X L S A' B'),
      GlueOnEq X L S C r₁ ⟨r₂.s, r₂.hs, r₂.a, r₂.b, r₂.g, r₂.src.trans hA, r₂.tgt.trans hB⟩ →
      (Quot.mk _ r₁ : GlueOnGen X L S C A B) ≍ (Quot.mk _ r₂ : GlueOnGen X L S C A' B') := by
    rintro A B A' B' rfl rfl r₁ r₂ h
    exact heq_of_eq (Quot.sound h)
  exact key (glueOnPt_span X L S h₁ h₂ f₁ f₂ hx a).symm
    (glueOnPt_span X L S h₁ h₂ f₁ f₂ hx b).symm _ _
    (GlueOnEq.span (C := C) h₁ h₂ f₁ f₂ hx g rfl rfl)

/-- 2-cells: each copy's own; the overlaps are already taken on the 1-cells. -/
inductive GlueOnRel : ∀ {s t : Paths (GenObj (GlueOnGen X L S C))}, (s ⟶ t) → (s ⟶ t) → Prop
  | copy (s : GlueV X) (hs : s ∈ S) {a b : GenObj (P.obj s.1).Gen} {u v : Quiver.Path a b} :
      (P.obj s.1).rel u v →
      GlueOnRel ((glueOnPre X L S C s hs).mapPath u) ((glueOnPre X L S C s hs).mapPath v)

/-- **The glued polygraph over a generating set.** -/
def glueOn : Polygraph.{max u₁ w u' w', max u₁ w} where
  V := GlueOnV X L S
  Gen := GlueOnGen X L S C
  rel := fun _ _ => GlueOnRel X L S C

/-- A copy's 2-cells hold in the glued polygraph. -/
theorem glueOnRel_copy_sound (s : GlueV X) (hs : s ∈ S) {a b : GenObj (P.obj s.1).Gen}
    {u v : Quiver.Path a b} (h : (P.obj s.1).rel u v) :
    (glueOn X L S C).quot.map ((glueOnPre X L S C s hs).mapPath u)
      = (glueOn X L S C).quot.map ((glueOnPre X L S C s hs).mapPath v) :=
  Quotient.sound _ (GlueOnRel.copy s hs h)

/-- The inclusion of the copy of `P s.1` at `s ∈ S`. -/
def glueOnIncl (s : GlueV X) (hs : s ∈ S) : Hom (P.obj s.1) (glueOn X L S C) :=
  Hom.ofPre (glueOnPre X L S C s hs) (glueOnRel_copy_sound X L S C s hs)

/-- **The span identification, as an equation between words** — `glueOnPre_span_heq`, conjugated
onto the 0-cells the two readings share.  The only transports here are the ones the 0-cells
already carry. -/
theorem glueOnPre_span {s₁ s₂ : GlueV X} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S) {d' : D}
    (f₁ : d' ⟶ s₁.1) (f₂ : d' ⟶ s₂.1) (hx : X.map f₁.op s₁.2 = X.map f₂.op s₂.2)
    {a b : GenObj (P.obj d').Gen} (g : a ⟶ b) :
    (glueOn X L S C).quot.map ((glueOnPre X L S C s₁ h₁).mapPath ((P.map f₁).cells.map g))
      = eqToHom (congrArg (glueOn X L S C).quot.obj
            (glueOnPre_obj_span X L S C h₁ h₂ f₁ f₂ hx a)) ≫
        (glueOn X L S C).quot.map ((glueOnPre X L S C s₂ h₂).mapPath ((P.map f₂).cells.map g)) ≫
        eqToHom (congrArg (glueOn X L S C).quot.obj
            (glueOnPre_obj_span X L S C h₁ h₂ f₁ f₂ hx b)).symm := by
  rw [C.spec f₁ g, C.spec f₂ g, Prefunctor.mapPath_toPath, Prefunctor.mapPath_toPath]
  exact (conj_eqToHom_iff_heq' _ _ _ _).2
    (quot_map_heq (glueOnPre_obj_span X L S C h₁ h₂ f₁ f₂ hx a)
      (glueOnPre_obj_span X L S C h₁ h₂ f₁ f₂ hx b)
      (glueOnPre_span_heq X L S C h₁ h₂ f₁ f₂ hx g))

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
@[reducible] def glueOnAt (v : GenObj (GlueOnGen X L S C)) :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization :=
  (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj (elt X v.as.1)

include hL in
theorem glueOnAt_glueOnPt (s : GlueV X) (hs : s ∈ S) (a : (P.obj s.1).V) :
    (glueSliceEval X W s.1 s.2).obj ((p s.1).at' ⟨a⟩)
      = glueOnAt X L S C W ⟨glueOnPt X L S s hs a⟩ := by
  rw [hL s.1 a]
  exact glueSliceEval_obj X W s.1 s.2 (L.ob s.1 a)

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
/-- The 0-cell a raw 1-cell's endpoint names, read in `(∫X)[W⁻¹]`. -/
theorem glueOnAt_of_eq {A : GlueOnV X L S} {s : GlueV X} {hs : s ∈ S} {a : (P.obj s.1).V}
    (h : glueOnPt X L S s hs a = A) :
    (glueSliceEval X W s.1 s.2).obj ((p s.1).at' ⟨a⟩) = glueOnAt X L S C W ⟨A⟩ :=
  (glueOnAt_glueOnPt X L S C W p hL s hs a).trans
    (congrArg (fun v => glueOnAt X L S C W ⟨v⟩) h)

include hL in
/-- The arrow a 1-cell of a copy names: the copy's own arrow, pushed along the cartesian lift. -/
noncomputable def glueOnRawArrow {A B : GlueOnV X L S} (r : GlueOnRaw X L S A B) :
    glueOnAt X L S C W ⟨A⟩ ⟶ glueOnAt X L S C W ⟨B⟩ :=
  eqToHom (glueOnAt_of_eq X L S C W p hL r.src).symm ≫
    (glueSliceEval X W r.s.1 r.s.2).map ((p r.s.1).arrow r.g) ≫
    eqToHom (glueOnAt_of_eq X L S C W p hL r.tgt)

include hL hP in
/-- **The two readings of a span name the same arrow**: both factor through the apex's slice
(`glueOnSliceEval_span`), which is what makes the arrow well defined on the coequalized 1-cells. -/
theorem glueOnRawArrow_span {A B : GlueOnV X L S} {r r' : GlueOnRaw X L S A B}
    (h : GlueOnEq X L S C r r') :
    glueOnRawArrow X L S C W p hL r = glueOnRawArrow X L S C W p hL r' := by
  cases h with
  | span h₁ h₂ f₁ f₂ hx g hA hB =>
      have key := Functor.congr_hom (glueOnSliceEval_span X W p hP f₁ f₂ hx) (Quiver.Hom.toPath g)
      simp only [Functor.comp_map, Paths.lift_toPath, C.spec] at key
      exact (eqToHom_conj_congr _ _ key).trans (eqToHom_conj_conj _ _ _ _ _)

include hL hP in
/-- The arrow a 1-cell names. -/
noncomputable def glueOnArrow :
    ∀ {v t : GenObj (GlueOnGen X L S C)}, (v ⟶ t) →
      (glueOnAt X L S C W v ⟶ glueOnAt X L S C W t) :=
  fun {v t} e => Quot.liftOn (e : GlueOnGen X L S C v.as t.as)
    (glueOnRawArrow X L S C W p hL) fun _ _ h => glueOnRawArrow_span X L S C W p hL hP h

include hL in
/-- The cells of the glued polygraph, interpreted. -/
noncomputable def glueOnEval : GenObj (GlueOnGen X L S C) ⥤q
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization where
  obj := glueOnAt X L S C W
  map := glueOnArrow X L S C W p hL hP

include hL in
theorem glueOnEval_map_glueOnPre (s : GlueV X) (hs : s ∈ S)
    {a b : GenObj (P.obj s.1).Gen} (e : a ⟶ b) :
    (glueOnEval X L S C W p hL hP).map ((glueOnPre X L S C s hs).map e) =
      eqToHom (glueOnAt_glueOnPt X L S C W p hL s hs a.as).symm ≫
        (glueSliceEval X W s.1 s.2).map ((p s.1).arrow e) ≫
        eqToHom (glueOnAt_glueOnPt X L S C W p hL s hs b.as) :=
  rfl

include hL in
/-- **A copy's word, evaluated**: the copy's own evaluation, pushed along the cartesian lift. -/
theorem glueOnEval_mapPath (s : GlueV X) (hs : s ∈ S) {a b : GenObj (P.obj s.1).Gen}
    (u : Quiver.Path a b) :
    (Paths.lift (glueOnEval X L S C W p hL hP)).map ((glueOnPre X L S C s hs).mapPath u) =
      eqToHom (glueOnAt_glueOnPt X L S C W p hL s hs a.as).symm ≫
        (glueSliceEval X W s.1 s.2).map ((p s.1).eval.map u) ≫
        eqToHom (glueOnAt_glueOnPt X L S C W p hL s hs b.as) := by
  induction u with
  | nil =>
      rw [show (Paths.lift (glueOnEval X L S C W p hL hP)).map
            ((glueOnPre X L S C s hs).mapPath (Quiver.Path.nil : Quiver.Path a a)) = 𝟙 _ from
          (Paths.lift (glueOnEval X L S C W p hL hP)).map_id _,
        show (p s.1).eval.map (Quiver.Path.nil : Quiver.Path a a) = 𝟙 _ from (p s.1).eval.map_id _,
        Functor.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
      rfl
  | cons u e ih =>
      rw [Prefunctor.mapPath_cons, Paths.lift_cons, ih, glueOnEval_map_glueOnPre,
        (p s.1).eval_cons, Functor.map_comp]
      exact (eqToHom_conj_comp _ _ _ _ _ _).trans (by simp; rfl)

include hL hP in
/-- **The 2-cells of the glued polygraph are sound**: they are a copy's own, pushed forward. -/
theorem glueOn_sound {v t : GenObj (GlueOnGen X L S C)} {u u' : Quiver.Path v t}
    (h : GlueOnRel X L S C u u') :
    (Paths.lift (glueOnEval X L S C W p hL hP)).map u
      = (Paths.lift (glueOnEval X L S C W p hL hP)).map u' := by
  cases h with
  | copy s hs hr =>
      rw [glueOnEval_mapPath, glueOnEval_mapPath, (p s.1).sound hr]

include hL hP in
/-- **The comparison functor**: a word of the glued polygraph, read in `(∫X)[W⁻¹]`. -/
noncomputable def glueOnDesc : (glueOn X L S C).presented ⥤
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization :=
  (glueOn X L S C).desc (glueOnEval X L S C W p hL hP) (glueOn_sound X L S C W p hL hP)

include hL hP in
/-- **A copy, read by Φ**: the copy's own interpretation, pushed along the cartesian lift.  This is
the bridge every spelling argument runs through — it turns "a word of `P s.1`" into "an arrow of
`(∫X)[W⁻¹]`" with no bookkeeping at the call site. -/
theorem glueOnIncl_desc (s : GlueV X) (hs : s ∈ S) :
    (glueOnIncl X L S C s hs).functor ⋙ glueOnDesc X L S C W p hL hP
      = (p s.1).E ⋙ glueSliceEval X W s.1 s.2 := by
  refine Quotient.lift_unique' _ _ _ ?_
  rw [← Functor.assoc, Hom.quot_comp_functor, Functor.assoc,
    show (glueOn X L S C).quot ⋙ glueOnDesc X L S C W p hL hP
        = Paths.lift (glueOnEval X L S C W p hL hP) from
      Quotient.lift_spec _ _ fun _ _ _ _ h => glueOn_sound X L S C W p hL hP h, ← Functor.assoc]
  refine Functor.ext (fun a => (glueOnAt_glueOnPt X L S C W p hL s hs a.as).symm) ?_
  intro a b u
  change (Paths.lift (glueOnEval X L S C W p hL hP)).map ((glueOnIncl X L S C s hs).words.map u) = _
  rw [show (glueOnIncl X L S C s hs).words.map u = (glueOnPre X L S C s hs).mapPath u from
      Paths.lift_comp_of_map _ u]
  exact glueOnEval_mapPath X L S C W p hL hP s hs u

include hL hP in
@[simp] theorem glueOnDesc_obj (v : GlueOnV X L S) :
    (glueOnDesc X L S C W p hL hP).obj ((presentedVEquiv (glueOn X L S C)) v)
      = glueOnAt X L S C W ⟨v⟩ := rfl

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
    (glueOnDesc X L S C W p hL hP).EssSurj where
  mem_essImage c := by
    obtain ⟨d, rfl⟩ := (Localization.Construction.objEquiv
      (W.inverseImage (CategoryOfElements.π X).leftOp)).surjective c
    exact ⟨presentedVEquiv (glueOn X L S C) (glueOnBaseV X L S W p hgen d),
      ⟨glueOnBaseIso X L W p hL d⟩⟩

/-! ## Fullness

Every arrow of `(∫X)[W⁻¹]` is a `Q`-image or a formal inverse, conjugated onto the base 0-cells;
`Generating` puts both of its endpoints and the arrow itself into a single slice, where `p s.1`
being an equivalence spells them. -/

include hL hP in
/-- **Fullness, one copy at a time.** -/
theorem exists_word_of_slice (s : GlueV X) (hs : s ∈ S) {b₁ b₂ : (P.obj s.1).V}
    (n : (p s.1).at' ⟨b₁⟩ ⟶ (p s.1).at' ⟨b₂⟩) :
    ∃ u : presentedVEquiv (glueOn X L S C) (glueOnPt X L S s hs b₁) ⟶
        presentedVEquiv (glueOn X L S C) (glueOnPt X L S s hs b₂),
      (glueOnDesc X L S C W p hL hP).map u
        = eqToHom (glueOnAt_glueOnPt X L S C W p hL s hs b₁).symm ≫
          (glueSliceEval X W s.1 s.2).map n ≫
          eqToHom (glueOnAt_glueOnPt X L S C W p hL s hs b₂) := by
  obtain ⟨h, rfl⟩ := (p s.1).E.map_surjective n
  exact ⟨(glueOnIncl X L S C s hs).functor.map h,
    Functor.congr_hom (glueOnIncl_desc X L S C W p hL hP s hs) h⟩

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
    ∃ u : presentedVEquiv (glueOn X L S C) (glueOnBaseV X L S W p hgen a) ⟶
        presentedVEquiv (glueOn X L S C) (glueOnBaseV X L S W p hgen b),
      (glueOnDesc X L S C W p hL hP).map u
        = (glueOnBaseIso X L W p hL a).hom ≫ g ≫ (glueOnBaseIso X L W p hL b).inv := by
  obtain ⟨u₀, hu₀⟩ := exists_word_of_slice X L S C W p hL hP s hs
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
  refine ⟨eqToHom (congrArg (presentedVEquiv (glueOn X L S C)) hA.symm) ≫ u₀ ≫
    eqToHom (congrArg (presentedVEquiv (glueOn X L S C)) hB), ?_⟩
  refine (eqToHom_conj_map (glueOnDesc X L S C W p hL hP) _ _ _).trans ?_
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
    ∃ e : presentedVEquiv (glueOn X L S C) (glueOnBaseV X L S W p hgen (elt X v.1)) ≅
        presentedVEquiv (glueOn X L S C) v,
      (glueOnDesc X L S C W p hL hP).mapIso e = glueOnBaseIso X L W p hL (elt X v.1) := by
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
  refine ⟨eqToIso (congrArg (presentedVEquiv (glueOn X L S C))
      (Subtype.ext (gluePt_sliceBase X L W p kA)).symm) ≪≫
    (glueOnIncl X L S C s hs).functor.mapIso ((p s.1).E.preimageIso ι) ≪≫ eqToIso rfl, ?_⟩
  have hia := congrArg Iso.hom (glueSliceEval_sliceBaseOver X L W p hL hP kA)
  simp only [Functor.mapIso_hom, Iso.trans_hom, eqToIso.hom] at hia
  ext
  simp only [Functor.mapIso_hom, Iso.trans_hom, eqToIso.hom]
  refine (eqToHom_conj_map (glueOnDesc X L S C W p hL hP) _ _ _).trans ?_
  refine (eqToHom_conj_congr _ _ (Functor.congr_hom
    (glueOnIncl_desc X L S C W p hL hP s hs) ((p s.1).E.preimageIso ι).hom)).trans ?_
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
    ∃ u : presentedVEquiv (glueOn X L S C) (glueOnBaseV X L S W p hgen a) ⟶
        presentedVEquiv (glueOn X L S C) (glueOnBaseV X L S W p hgen b),
      (glueOnDesc X L S C W p hL hP).map u
        = (glueOnBaseIso X L W p hL a).hom ≫
          (W.inverseImage (CategoryOfElements.π X).leftOp).Q.map f ≫
          (glueOnBaseIso X L W p hL b).inv := by
  obtain ⟨s, hs, ⟨k⟩⟩ := hgen b
  exact exists_word_of_arrow X L S C W p hL hP hgen hs (f ≫ k) k _
    (glueSliceEval_post_map X W f k)

include hL hP in
/-- **…and so is the formal inverse of a `W`-arrow**: it is an arrow of the same slice, already
inverted there. -/
theorem exists_word_of_wInv (hgen : Generating X S) {a b : (X.Elements)ᵒᵖ} (f : a ⟶ b)
    (hf : W.inverseImage (CategoryOfElements.π X).leftOp f) :
    ∃ u : presentedVEquiv (glueOn X L S C) (glueOnBaseV X L S W p hgen b) ⟶
        presentedVEquiv (glueOn X L S C) (glueOnBaseV X L S W p hgen a),
      (glueOnDesc X L S C W p hL hP).map u
        = (glueOnBaseIso X L W p hL b).hom ≫ Localization.Construction.wInv f hf ≫
          (glueOnBaseIso X L W p hL a).inv := by
  obtain ⟨s, hs, ⟨k⟩⟩ := hgen b
  haveI : IsIso ((W.over (X := s.1)).Q.map ((Over.post (CategoryOfElements.π X).leftOp).map
      (Over.homMk f rfl : Over.mk (f ≫ k) ⟶ Over.mk k))) :=
    Localization.inverts (W.over (X := s.1)).Q (W.over (X := s.1)) _ hf
  refine exists_word_of_arrow X L S C W p hL hP hgen hs k (f ≫ k) _
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
    ∃ u : presentedVEquiv (glueOn X L S C) (glueOnBaseV X L S W p hgen a) ⟶
        presentedVEquiv (glueOn X L S C) (glueOnBaseV X L S W p hgen b),
      (glueOnDesc X L S C W p hL hP).map u
        = (glueOnBaseIsoAt X L S W p hL hgen a hA).hom ≫ g ≫
          (glueOnBaseIsoAt X L S W p hL hgen b hB).inv

private instance spelled_comp (hgen : Generating X S) :
    (spelled X L S C W p hL hP hgen).IsStableUnderComposition where
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
      spelled X L S C W p hL hP hgen
        ((W.inverseImage (CategoryOfElements.π X).leftOp).Q.map f) := by
  intro a₀ b₀ f a b hA hB
  obtain rfl := (Localization.Construction.objEquiv
    (W := W.inverseImage (CategoryOfElements.π X).leftOp)).injective hA
  obtain rfl := (Localization.Construction.objEquiv
    (W := W.inverseImage (CategoryOfElements.π X).leftOp)).injective hB
  simpa [glueOnBaseIsoAt] using exists_word_of_Q X L S C W p hL hP hgen f

private theorem spelled_wInv (hgen : Generating X S) :
    ∀ ⦃a b : (X.Elements)ᵒᵖ⦄ (f : a ⟶ b)
      (hf : W.inverseImage (CategoryOfElements.π X).leftOp f),
      spelled X L S C W p hL hP hgen (Localization.Construction.wInv f hf) := by
  intro a₀ b₀ f hf a b hA hB
  obtain rfl := (Localization.Construction.objEquiv
    (W := W.inverseImage (CategoryOfElements.π X).leftOp)).injective hA
  obtain rfl := (Localization.Construction.objEquiv
    (W := W.inverseImage (CategoryOfElements.π X).leftOp)).injective hB
  simpa [glueOnBaseIsoAt] using exists_word_of_wInv X L S C W p hL hP hgen f hf

include hL hP in
/-- **The comparison is full**: every arrow is a word between base 0-cells, and every 0-cell is
spelled onto its own base. -/
theorem glueOnDesc_full (hgen : Generating X S) : (glueOnDesc X L S C W p hL hP).Full where
  map_surjective {A B} g := by
    obtain ⟨vA, rfl⟩ : ∃ v, presentedVEquiv (glueOn X L S C) v = A :=
      ⟨(presentedVEquiv (glueOn X L S C)).symm A, rfl⟩
    obtain ⟨vB, rfl⟩ : ∃ v, presentedVEquiv (glueOn X L S C) v = B :=
      ⟨(presentedVEquiv (glueOn X L S C)).symm B, rfl⟩
    obtain ⟨eA, hEA⟩ := exists_wordIso_glueOnBase X L S C W p hL hP hgen vA
    obtain ⟨eB, hEB⟩ := exists_wordIso_glueOnBase X L S C W p hL hP hgen vB
    have h : spelled X L S C W p hL hP hgen g := by
      rw [Localization.Construction.morphismProperty_eq_top (spelled X L S C W p hL hP hgen)
        (spelled_Q X L S C W p hL hP hgen) (spelled_wInv X L S C W p hL hP hgen)]
      trivial
    obtain ⟨u₀, hu₀⟩ := h (elt X vA.1) (elt X vB.1) rfl rfl
    have hA' : (glueOnDesc X L S C W p hL hP).map eA.inv
        = (glueOnBaseIso X L W p hL (elt X vA.1)).inv := by rw [← Functor.mapIso_inv, hEA]
    have hB' : (glueOnDesc X L S C W p hL hP).map eB.hom
        = (glueOnBaseIso X L W p hL (elt X vB.1)).hom := by rw [← Functor.mapIso_hom, hEB]
    refine ⟨eA.inv ≫ u₀ ≫ eB.hom, ?_⟩
    rw [Functor.map_comp, Functor.map_comp, hu₀, hA', hB']
    simp [glueOnBaseIsoAt]

/-! ## The copy an object carries

An object outside `S` carries no copy of its own, but each leg of a span reads `P d'` inside a copy
that exists, and the coequalized 1-cells say the reading does not depend on the leg.  So `P (π c)`
sits inside the glued polygraph however `c` is covered, and nothing downstream has to choose. -/

/-- `P d'`, read inside the copy at `s` along a leg `d' ⟶ s.1`. -/
def spanIncl {d' : D} {s : GlueV X} (hs : s ∈ S) (f : d' ⟶ s.1) :
    (P.obj d').presented ⥤ (glueOn X L S C).presented :=
  (P.map f).functor ⋙ (glueOnIncl X L S C s hs).functor

/-- The reading, on words: `P d'`'s words spelled in the copy at `s`. -/
theorem quot_comp_spanIncl {d' : D} {s : GlueV X} (hs : s ∈ S) (f : d' ⟶ s.1) :
    (P.obj d').quot ⋙ spanIncl X L S C hs f
      = (P.map f).words ⋙ (glueOnIncl X L S C s hs).words ⋙ (glueOn X L S C).quot := by
  rw [spanIncl, ← Functor.assoc, Hom.quot_comp_functor, Functor.assoc]
  exact congrArg ((P.map f).words ⋙ ·) (Hom.quot_comp_functor (glueOnIncl X L S C s hs))

/-- **The reading does not depend on the leg** — this is `glueOnPre_span` and nothing else, and it
is a strict equality of functors, so the retraction below is a cocone rather than a
pseudo-cocone. -/
theorem spanIncl_eq {d' : D} {s₁ s₂ : GlueV X} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S)
    (f₁ : d' ⟶ s₁.1) (f₂ : d' ⟶ s₂.1) (hx : X.map f₁.op s₁.2 = X.map f₂.op s₂.2) :
    spanIncl X L S C h₁ f₁ = spanIncl X L S C h₂ f₂ := by
  have hword : ∀ {s : GlueV X} (hs : s ∈ S) (f : d' ⟶ s.1)
      {a b : GenObj (P.obj d').Gen} (e : a ⟶ b),
      ((P.map f).words ⋙ (glueOnIncl X L S C s hs).words ⋙ (glueOn X L S C).quot).map
          (Quiver.Hom.toPath e)
        = (glueOn X L S C).quot.map ((glueOnPre X L S C s hs).mapPath ((P.map f).cells.map e)) := by
    intro s hs f a b e
    change (glueOn X L S C).quot.map
      ((glueOnIncl X L S C s hs).words.map ((P.map f).words.map (Quiver.Hom.toPath e))) = _
    rw [show (P.map f).words.map (Quiver.Hom.toPath e) = (P.map f).cells.map e from
      Paths.lift_toPath _ e]
    exact congrArg (glueOn X L S C).quot.map (Paths.lift_comp_of_map (glueOnPre X L S C s hs) _)
  refine Quotient.lift_unique' _ _ _ ?_
  rw [quot_comp_spanIncl, quot_comp_spanIncl]
  refine Paths.ext_functor
    (funext fun a => congrArg (glueOn X L S C).quot.obj
      (glueOnPre_obj_span X L S C h₁ h₂ f₁ f₂ hx a)) ?_
  intro a b e
  rw [hword h₁ f₁, hword h₂ f₂]
  exact glueOnPre_span X L S C h₁ h₂ f₁ f₂ hx e

/-- The reading along a longer leg. -/
theorem spanIncl_comp {d'' d' : D} (g : d'' ⟶ d') {s : GlueV X} (hs : s ∈ S) (f : d' ⟶ s.1) :
    (P.map g).functor ⋙ spanIncl X L S C hs f = spanIncl X L S C hs (g ≫ f) := by
  rw [spanIncl, spanIncl, ← Functor.assoc, ← Polygraph.functor_comp, ← P.map_comp]

/-- …and at a copy of `S` itself it is that copy. -/
theorem spanIncl_id {s : GlueV X} (hs : s ∈ S) :
    spanIncl X L S C hs (𝟙 s.1) = (glueOnIncl X L S C s hs).functor := by
  change (P.map (𝟙 s.1)).functor ⋙ (glueOnIncl X L S C s hs).functor = _
  rw [P.map_id, Polygraph.functor_id, Functor.id_comp]

/-- The copy `Generating` picks for `c`. -/
noncomputable def genPt (hgen : Generating X S) (c : (X.Elements)ᵒᵖ) : GlueV X :=
  (hgen c).choose

theorem genPt_mem (hgen : Generating X S) (c : (X.Elements)ᵒᵖ) : genPt X S hgen c ∈ S :=
  (hgen c).choose_spec.1

/-- …and the leg into it. -/
noncomputable def genLeg (hgen : Generating X S) (c : (X.Elements)ᵒᵖ) :
    c ⟶ elt X (genPt X S hgen c) :=
  (hgen c).choose_spec.2.some

/-- **The copy `c` carries.**  Which copy of `S` it is read in is a choice; `spanIncl_eq` says the
functor is not. -/
noncomputable def carriedIncl (hgen : Generating X S) (c : (X.Elements)ᵒᵖ) :
    (P.obj ((CategoryOfElements.π X).leftOp.obj c)).presented ⥤ (glueOn X L S C).presented :=
  spanIncl X L S C (genPt_mem X S hgen c)
    ((CategoryOfElements.π X).leftOp.map (genLeg X S hgen c))

theorem carriedIncl_eq (hgen : Generating X S) {c : (X.Elements)ᵒᵖ} {s : GlueV X} (hs : s ∈ S)
    (k : c ⟶ elt X s) :
    carriedIncl X L S C hgen c = spanIncl X L S C hs ((CategoryOfElements.π X).leftOp.map k) :=
  spanIncl_eq X L S C _ _ _ _
    ((elements_snd_map X (genLeg X S hgen c)).trans (elements_snd_map X k).symm)

/-- **The copies an object and its target carry agree along an arrow** — the strict naturality that
makes the retraction a cocone. -/
theorem carriedIncl_naturality (hgen : Generating X S) {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙ carriedIncl X L S C hgen c
      = carriedIncl X L S C hgen c' := by
  rw [carriedIncl_eq X L S C hgen (genPt_mem X S hgen c) (genLeg X S hgen c), spanIncl_comp,
    carriedIncl_eq X L S C hgen (genPt_mem X S hgen c) (u ≫ genLeg X S hgen c)]
  rfl

theorem carriedIncl_at (hgen : Generating X S) {s : GlueV X} (hs : s ∈ S) :
    carriedIncl X L S C hgen (elt X s) = (glueOnIncl X L S C s hs).functor :=
  -- `π.leftOp` preserves the identity strictly, but only up to a spelling `rw` will not unfold
  (carriedIncl_eq X L S C hgen hs (𝟙 (elt X s))).trans (spanIncl_id X L S C hs)

/-! ## Inverting a slice presentation

`Glue`'s retraction needs each slice presentation to be an *isomorphism* of categories; a compact
presentation is only an equivalence, and inverting one is a choice.  What restores strictness is
geometry: the localized slices are posets, distinct 0-cells name distinct slice objects, and every
slice object is entered from a canonical labelled one. -/

/-- **Every slice object is entered from a canonical labelled one.**  The data a compact family of
slice presentations needs in place of bijective labels; `Glue`'s `hb` is the special case where
`ret` is the inverse of `L.ob`. -/
structure SliceRetract (L : SliceLabels P) (W : MorphismProperty D) where
  /-- the labelled object a slice object is entered from -/
  ret {d : D} : Over d → (P.obj d).V
  /-- distinct 0-cells name distinct slice objects -/
  inj (d : D) : Function.Injective (L.ob d)
  /-- the entry is a `W`-arrow, so the localized slice inverts it -/
  merge {d : D} (y : Over d) : ∃ w : L.ob d (ret y) ⟶ y, (W.over (X := d)) w
  /-- a labelled object is entered from itself -/
  fix {d : D} (a : (P.obj d).V) : ret (L.ob d a) = a
  /-- and the entry is stable under pushing the base -/
  push {d' d : D} (f : d' ⟶ d) (y : Over d') :
    L.ob d (ret ((Over.map f).obj y)) = (Over.map f).obj (L.ob d' (ret y))
  /-- the source of a labelled object carries its own identity as a label -/
  top {d : D} (a : (P.obj d).V) :
    ∃ b : (P.obj (L.ob d a).left).V, L.ob (L.ob d a).left b = Over.mk (𝟙 (L.ob d a).left)

variable (hthin : ∀ d : D, Quiver.IsThin ((W.over (X := d)).Localization))
  (R : SliceRetract L W)

include p hthin in
/-- A poset is presented by a poset. -/
theorem presented_isThin (d : D) : Quiver.IsThin ((P.obj d).presented) :=
  haveI := hthin d
  isThin_of_equiv (p d).equiv.symm

include hL in
/-- **The entry, read in the localized slice** — an iso, since the entry is a `W`-arrow. -/
noncomputable def retIso (d : D) (y : Over d) :
    (p d).at' ⟨R.ret y⟩ ≅ (W.over (X := d)).Q.obj y :=
  eqToIso (hL d (R.ret y)) ≪≫
    @asIso _ _ _ _ ((W.over (X := d)).Q.map (R.merge y).choose)
      (Localization.inverts (W.over (X := d)).Q (W.over (X := d)) _ (R.merge y).choose_spec)

include hL hthin in
/-- **The slice presentation, inverted on the nose.**  Objects go to the labelled object they are
entered from; morphisms are forced, the slice being a poset. -/
noncomputable def slInv (d : D) :
    (W.over (X := d)).Localization ⥤ (P.obj d).presented :=
  haveI := presented_isThin W p hthin d
  { obj := fun Y => ⟨⟨R.ret ((Localization.Construction.objEquiv (W.over (X := d))).symm Y)⟩⟩
    map := fun {Y Y'} g => (p d).E.preimage
      ((retIso L W p hL R d ((Localization.Construction.objEquiv (W.over (X := d))).symm Y)).hom
        ≫ g ≫
        (retIso L W p hL R d
          ((Localization.Construction.objEquiv (W.over (X := d))).symm Y')).inv)
    map_id := fun _ => Subsingleton.elim _ _
    map_comp := fun _ _ => Subsingleton.elim _ _ }

/-- **The entry is stable under pushing the base** — `push`, read on 0-cells. -/
theorem ret_push {d' d : D} (f : d' ⟶ d) (y : Over d') :
    R.ret ((Over.map f).obj y) = ((P.map f).cells.obj ⟨R.ret y⟩).as :=
  R.inj d ((R.push f y).trans (L.map_ob f ⟨R.ret y⟩).symm)

include hL hthin in
/-- **The inversion is a strict retraction of the presentation**: a labelled object is entered from
itself, and a poset leaves the morphisms nothing to disagree about. -/
theorem comp_slInv (d : D) : (p d).E ⋙ slInv L W p hL hthin R d = 𝟭 _ := by
  haveI := presented_isThin W p hthin d
  refine CategoryTheory.Functor.ext (fun Z => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  change (⟨⟨R.ret ((Localization.Construction.objEquiv (W.over (X := d))).symm
    ((p d).at' ⟨Z.as.as⟩))⟩⟩ : (P.obj d).presented) = Z
  rw [hL d Z.as.as, Equiv.symm_apply_apply, R.fix]
  rfl

include hL hthin in
/-- **A commuting square inverts to a commuting square** — `Glue`'s `strictInv_square`, with the
labels' injectivity and the poset in place of bijectivity on objects. -/
theorem slInv_square {d' d : D} (f : d' ⟶ d) :
    overMapLoc W f ⋙ slInv L W p hL hthin R d
      = slInv L W p hL hthin R d' ⋙ (P.map f).functor := by
  haveI := presented_isThin W p hthin d
  refine CategoryTheory.Functor.ext (fun Y => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  have hy : (Localization.Construction.objEquiv (W.over (X := d))).symm ((overMapLoc W f).obj Y)
      = (Over.map f).obj ((Localization.Construction.objEquiv (W.over (X := d'))).symm Y) := by
    refine (Localization.Construction.objEquiv (W.over (X := d))).symm_apply_eq.mpr ?_
    rw [← overMapLoc_obj W f, Equiv.apply_symm_apply]
  change (⟨⟨R.ret ((Localization.Construction.objEquiv (W.over (X := d))).symm
      ((overMapLoc W f).obj Y))⟩⟩ : (P.obj d).presented)
    = ⟨(P.map f).cells.obj ⟨R.ret
        ((Localization.Construction.objEquiv (W.over (X := d'))).symm Y)⟩⟩
  rw [hy]
  exact congrArg (fun a => (⟨⟨a⟩⟩ : (P.obj d).presented)) (ret_push L W R f _)

/-! ## The retraction

`Glue`'s retraction, with the copy `c` carries in place of the copy at `c` and `slInv` in place of
the strict inverse.  Both replacements are strict, so this is an honest `OverCocone`. -/

include hL hthin in
/-- The comparison on the base slice: `slInv_square` followed by `carriedIncl_naturality`. -/
theorem glueOnStep (hgen : Generating X S) {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    overMapLoc W ((CategoryOfElements.π X).leftOp.map u) ⋙
        slInv L W p hL hthin R ((CategoryOfElements.π X).leftOp.obj c) ⋙
        carriedIncl X L S C hgen c
      = slInv L W p hL hthin R ((CategoryOfElements.π X).leftOp.obj c') ⋙
        carriedIncl X L S C hgen c' := by
  rw [← Functor.assoc, slInv_square, Functor.assoc, carriedIncl_naturality]

include hL hthin in
/-- The retraction, before localizing: down to the base slice, the slice presentation inverted, and
the copy `c` carries. -/
noncomputable def glueOnRetractPre (hgen : Generating X S) (c : (X.Elements)ᵒᵖ) :
    Over c ⥤ (glueOn X L S C).presented :=
  Over.post (CategoryOfElements.π X).leftOp ⋙
    (W.over (X := (CategoryOfElements.π X).leftOp.obj c)).Q ⋙
    slInv L W p hL hthin R ((CategoryOfElements.π X).leftOp.obj c) ⋙
    carriedIncl X L S C hgen c

include hL hthin in
/-- …and it is natural in `c` on the nose. -/
theorem glueOnRetractPre_map (hgen : Generating X S) {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    Over.map u ⋙ glueOnRetractPre X L S C W p hL hthin R hgen c
      = glueOnRetractPre X L S C W p hL hthin R hgen c' := by
  unfold glueOnRetractPre
  rw [← Functor.assoc, elementsPost_map, Functor.assoc, ← Functor.assoc (Over.map _),
    ← overMapLocFac, Functor.assoc, glueOnStep X L S C W p hL hthin R hgen u]

include hL hthin in
theorem glueOnRetractPre_inverts (hgen : Generating X S) (c : (X.Elements)ᵒᵖ) :
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).IsInvertedBy
      (glueOnRetractPre X L S C W p hL hthin R hgen c) := by
  intro Y Z φ hφ
  haveI : IsIso ((W.over (X := (CategoryOfElements.π X).leftOp.obj c)).Q.map
      ((Over.post (CategoryOfElements.π X).leftOp).map φ)) :=
    Localization.inverts _ (W.over (X := (CategoryOfElements.π X).leftOp.obj c)) _ hφ
  exact inferInstanceAs (IsIso
    ((slInv L W p hL hthin R ((CategoryOfElements.π X).leftOp.obj c) ⋙
        carriedIncl X L S C hgen c).map
      ((W.over (X := (CategoryOfElements.π X).leftOp.obj c)).Q.map
        ((Over.post (CategoryOfElements.π X).leftOp).map φ))))

include hL hthin in
/-- The retraction, as a **strict** cocone on the slices. -/
noncomputable def glueOnRetractCocone (hgen : Generating X S) :
    OverCocone ((X.Elements)ᵒᵖ) ((glueOn X L S C).presented) where
  obj c := glueOnRetractPre X L S C W p hL hthin R hgen c
  w u := glueOnRetractPre_map X L S C W p hL hthin R hgen u

include hL hthin in
theorem glueOnRetractCocone_inverts (hgen : Generating X S) :
    (W.inverseImage (CategoryOfElements.π X).leftOp).IsInvertedBy
      (glueOnRetractCocone X L S C W p hL hthin R hgen).desc := by
  rw [isInvertedBy_iff_over, OverCocone.ofFunctor_desc]
  exact glueOnRetractPre_inverts X L S C W p hL hthin R hgen

include hL hthin in
/-- **The retraction** `Ψ : (∫X)[W⁻¹] ⥤ GlueOn`, descended from the slices. -/
noncomputable def glueOnRetractDesc (hgen : Generating X S) :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization ⥤ (glueOn X L S C).presented :=
  Localization.Construction.lift _ (glueOnRetractCocone_inverts X L S C W p hL hthin R hgen)

include hL hthin in
theorem glueOnRetractDesc_fac (hgen : Generating X S) :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Q ⋙
        glueOnRetractDesc X L S C W p hL hthin R hgen
      = (glueOnRetractCocone X L S C W p hL hthin R hgen).desc :=
  Localization.Construction.fac _ _

include hL hthin in
theorem glueOnRetract_forget (hgen : Generating X S) (c : (X.Elements)ᵒᵖ) :
    Over.forget c ⋙ (glueOnRetractCocone X L S C W p hL hthin R hgen).desc
      = glueOnRetractPre X L S C W p hL hthin R hgen c :=
  congrArg (fun G => OverCocone.obj G c) (OverCocone.ofFunctor_desc _)

include hL hthin in
/-- **A slice, read through the retraction, is the copy its object carries** — the mirror of
`glueOnIncl_desc`, and what makes the unit computable on generators. -/
theorem glueOnSliceEval_retract (hgen : Generating X S) (c : (X.Elements)ᵒᵖ) :
    glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c) c.unop.2 ⋙
        glueOnRetractDesc X L S C W p hL hthin R hgen
      = slInv L W p hL hthin R ((CategoryOfElements.π X).leftOp.obj c) ⋙
        carriedIncl X L S C hgen c := by
  refine Localization.Construction.uniq _ _ ?_
  rw [← Functor.assoc, glueSliceEval_fac, Functor.assoc, glueOnRetractDesc_fac,
    ← elementsLiftOver_forget X c, Functor.assoc, glueOnRetract_forget]
  unfold glueOnRetractPre
  simp only [← Functor.assoc]
  rw [elementsLiftOver_post, Functor.id_comp]

/-! ## The unit

A covered object is the base of its own slice: its base carries the identity as a label, so the
retraction lands back on the 0-cell it came from — on the nose, which is what lets the unit be an
equality of functors rather than an isomorphism. -/

/-- **The identity is entered from itself** where it is a label. -/
theorem ret_ob_top {d : D} (h : ∃ a : (P.obj d).V, L.ob d a = Over.mk (𝟙 d)) :
    L.ob d (R.ret (Over.mk (𝟙 d))) = Over.mk (𝟙 d) := by
  obtain ⟨a, ha⟩ := h
  rw [← ha, R.fix]

/-- **Every 0-cell of a copy is read along its own label from the base of that label's source** —
so the copies' 0-cells are already identified by the spans that identify their 1-cells, and the
0-cells of `glueOn` are the coequalizer of the copies', not merely their image.  It takes
`SliceRetract`, which is not available where `glueOn` is defined; that is why the construction can
only take the image there, and is a colimit by this theorem rather than by construction. -/
theorem cells_obj_ret_top {s : GlueV X} (a : (P.obj s.1).V) :
    ((P.map (L.ob s.1 a).hom).cells.obj
        ⟨R.ret (Over.mk (𝟙 (L.ob s.1 a).left))⟩).as = a := by
  refine R.inj s.1 ((L.map_ob _ _).trans ?_)
  rw [ret_ob_top L W R (R.top a)]
  exact congrArg Over.mk (Category.id_comp _)

include R in
/-- **The base of a covered 0-cell carries the identity as a label** — `top`, read at a copy. -/
theorem top_of_covered {v : GlueV X} (hv : Covered X L S v) :
    ∃ a : (P.obj v.1).V, L.ob v.1 a = Over.mk (𝟙 v.1) := by
  obtain ⟨s, hs, a, rfl⟩ := hv
  exact R.top a

/-- **A covered 0-cell is the base of its own slice** — `Glue`'s `gluePt_base`, with `top` in place
of surjective labels. -/
theorem gluePt_ret {d : D} (x : X.obj (op d))
    (h : ∃ a : (P.obj d).V, L.ob d a = Over.mk (𝟙 d)) :
    gluePt X L d x (R.ret (Over.mk (𝟙 d))) = ⟨d, x⟩ :=
  Eq.trans
    (congrArg (fun Y : Over d => (⟨Y.left, X.map Y.hom.op x⟩ : GlueV X)) (ret_ob_top L W R h))
    (congrArg (fun z => (⟨d, z⟩ : GlueV X)) (by simp; rfl))

include hL hthin in
/-- The retraction, read at a slice's terminal object. -/
theorem glueOnRetractPre_top (hgen : Generating X S) (c : (X.Elements)ᵒᵖ) :
    (glueOnRetractPre X L S C W p hL hthin R hgen c).obj (Over.mk (𝟙 c))
      = (glueOn X L S C).quot.obj
          ⟨glueOnPt X L S (genPt X S hgen c) (genPt_mem X S hgen c)
            (((P.map ((CategoryOfElements.π X).leftOp.map (genLeg X S hgen c))).cells.obj
              ⟨R.ret (Over.mk (𝟙 ((CategoryOfElements.π X).leftOp.obj c)))⟩).as)⟩ := rfl

include hL hthin in
/-- **The retraction sends a 0-cell's object back to that 0-cell**, on the nose. -/
theorem glueOnRetract_glueOnAt (hgen : Generating X S) (v : GenObj (GlueOnGen X L S C)) :
    (glueOnRetractDesc X L S C W p hL hthin R hgen).obj (glueOnAt X L S C W v)
      = (glueOn X L S C).quot.obj v := by
  refine (Functor.congr_obj (glueOnRetractDesc_fac X L S C W p hL hthin R hgen)
    (elt X v.as.1)).trans ?_
  refine (glueOnRetractPre_top X L S C W p hL hthin R hgen (elt X v.as.1)).trans ?_
  refine congrArg (glueOn X L S C).quot.obj
    (congrArg (fun z => (⟨z⟩ : GenObj (GlueOnGen X L S C))) (Subtype.ext ?_))
  refine (glueOnPt_map X L S (genPt_mem X S hgen (elt X v.as.1)) _ _).trans ?_
  refine Eq.trans (congrArg (fun z => gluePt X L v.as.1.1 z
    (R.ret (Over.mk (𝟙 v.as.1.1)))) (elements_snd_map X (genLeg X S hgen (elt X v.as.1)))) ?_
  exact gluePt_ret X L W R v.as.1.2 (top_of_covered X L S W R v.as.2)

include hL hthin in
/-- A copy, read through the retraction, is that copy's own inversion. -/
theorem glueOnSliceEval_retract_at (hgen : Generating X S) {s : GlueV X} (hs : s ∈ S) :
    glueSliceEval X W s.1 s.2 ⋙ glueOnRetractDesc X L S C W p hL hthin R hgen
      = slInv L W p hL hthin R s.1 ⋙ (glueOnIncl X L S C s hs).functor :=
  (glueOnSliceEval_retract X L S C W p hL hthin R hgen (elt X s)).trans
    (congrArg (fun G => slInv L W p hL hthin R s.1 ⋙ G) (carriedIncl_at X L S C hgen hs))

include hL hP hthin in
/-- **The unit**: the comparison, read through the retraction, is the identity.  Checked on
generators, where `slInv` cancels `(p s.1).E` and the copy inclusion is `glueOnIncl_desc`. -/
theorem glueOnUnit (hgen : Generating X S) :
    glueOnDesc X L S C W p hL hP ⋙ glueOnRetractDesc X L S C W p hL hthin R hgen = 𝟭 _ := by
  refine Quotient.lift_unique' _ _ _ ?_
  rw [← Functor.assoc, show (glueOn X L S C).quot ⋙ glueOnDesc X L S C W p hL hP
      = Paths.lift (glueOnEval X L S C W p hL hP) from
    Quotient.lift_spec _ _ fun _ _ _ _ h => glueOn_sound X L S C W p hL hP h, Functor.comp_id]
  refine Paths.ext_functor ?_ ?_
  · exact funext fun v => glueOnRetract_glueOnAt X L S C W p hL hthin R hgen v
  · rintro ⟨a⟩ ⟨b⟩ ⟨s, hs, a', b', g, hsrc, htgt⟩
    -- the goal mentions the endpoint proofs, so `cases` (which abstracts them) not `subst`
    cases hsrc
    cases htgt
    refine Eq.trans (congrArg (glueOnRetractDesc X L S C W p hL hthin R hgen).map
      ((Paths.lift_toPath _ _).trans (glueOnEval_map_glueOnPre X L S C W p hL hP s hs g))) ?_
    -- no rewrite reaches under a `Quotient` lift's `.map`, so the chain runs through `exact`
    have m1 := Functor.congr_hom
      (glueOnSliceEval_retract_at X L S C W p hL hthin R hgen hs) ((p s.1).arrow g)
    have m2 := Functor.congr_hom (comp_slInv L W p hL hthin R s.1)
      ((P.obj s.1).quot.map (Quiver.Hom.toPath g))
    have m3 := (Functor.congr_hom (Hom.quot_comp_functor (glueOnIncl X L S C s hs))
      (Quiver.Hom.toPath g)).trans (eqToHom_conj_congr _ _ (congrArg (glueOn X L S C).quot.map
        (Paths.lift_comp_of_map (glueOnPre X L S C s hs) (Quiver.Hom.toPath g))))
    have inner := (congrArg (glueOnIncl X L S C s hs).functor.map m2).trans
      ((eqToHom_conj_map (glueOnIncl X L S C s hs).functor _ _ _).trans
        ((eqToHom_conj_congr _ _ m3).trans (eqToHom_conj_conj _ _ _ _ _)))
    have mid := m1.trans ((eqToHom_conj_congr _ _ inner).trans (eqToHom_conj_conj _ _ _ _ _))
    exact (eqToHom_conj_map (glueOnRetractDesc X L S C W p hL hthin R hgen) _ _ _).trans
      ((eqToHom_conj_congr _ _ mid).trans (eqToHom_conj_conj _ _ _ _ _))

include hL hP hthin R in
/-- **The comparison is faithful**: the retraction undoes it, so two words with the same image are
the same word. -/
theorem glueOnDesc_faithful (hgen : Generating X S) :
    (glueOnDesc X L S C W p hL hP).Faithful := by
  haveI : (glueOnDesc X L S C W p hL hP ⋙
      glueOnRetractDesc X L S C W p hL hthin R hgen).Faithful := by
    rw [glueOnUnit X L S C W p hL hP hthin R hgen]
    infer_instance
  exact Functor.Faithful.of_comp _ (glueOnRetractDesc X L S C W p hL hthin R hgen)

include hL hP hthin R in
/-- **`glueOn X L S C` presents `(∫X)[W⁻¹]`.**  The 0-cells cover because every object has a base
0-cell, the 1-cells span because every arrow factors through one copy, and the word problem is the
retraction: a word is recovered from its image slice by slice. -/
noncomputable def presentsGlueOn (hgen : Generating X S) :
    Presents (glueOn X L S C)
      ((W.inverseImage (CategoryOfElements.π X).leftOp).Localization) := by
  haveI := glueOnDesc_full X L S C W p hL hP hgen
  haveI := glueOnDesc_essSurj X L S C W p hL hP hgen
  haveI := glueOnDesc_faithful X L S C W p hL hP hthin R hgen
  exact ⟨glueOnDesc X L S C W p hL hP, { }⟩

end Compare

end Polygraph


end CategoryTheory
