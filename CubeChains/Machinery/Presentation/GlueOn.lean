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
  (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj (op ⟨op v.as.1.1, v.as.1.2⟩)

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
@[simp] theorem glueOnDesc_obj (v : GlueOnV X L S) :
    (glueOnDesc X L S W p hL hP).obj ((presentedVEquiv (glueOn X L S)) v)
      = glueOnAt X L S W ⟨v⟩ := rfl

/-- **`S` covers up to `W`**: every object of `∫X` is reached by a `W`-arrow from a covered one.
This is what replaces `Glue`'s bijective labels — it asks the copies to meet every *iso-class*,
not every object, and it is exactly what a localization's own collapse supplies. -/
def CoversUpToW : Prop :=
  ∀ c : (X.Elements)ᵒᵖ, ∃ (v : GlueOnV X L S)
    (u : (op ⟨op v.1.1, v.1.2⟩ : (X.Elements)ᵒᵖ) ⟶ c),
      W.inverseImage (CategoryOfElements.π X).leftOp u

include hL hP in
/-- **The comparison is essentially surjective**, from covering alone.  This is the payoff of
"fewer 0-cells": `Glue` had to ask for bijectivity here and could not get it. -/
theorem glueOnDesc_essSurj (hcov : CoversUpToW X L S W) :
    (glueOnDesc X L S W p hL hP).EssSurj where
  mem_essImage c := by
    obtain ⟨d, rfl⟩ := Localization.Construction.objEquiv
      (W.inverseImage (CategoryOfElements.π X).leftOp) |>.surjective c
    obtain ⟨v, u, hu⟩ := hcov d
    have hiso : IsIso ((W.inverseImage (CategoryOfElements.π X).leftOp).Q.map u) :=
      Localization.inverts (W.inverseImage (CategoryOfElements.π X).leftOp).Q
        (W.inverseImage (CategoryOfElements.π X).leftOp) u hu
    exact ⟨(presentedVEquiv (glueOn X L S)) v,
      ⟨@asIso _ _ _ _ ((W.inverseImage (CategoryOfElements.π X).leftOp).Q.map u) hiso⟩⟩

end Compare

end Polygraph


end CategoryTheory
