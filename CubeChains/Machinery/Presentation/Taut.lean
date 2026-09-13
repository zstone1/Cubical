import CubeChains.Machinery.Presentation.LengthGraded
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Machinery/Presentation/Taut — a category presented by its own arrows

`taut C` takes `C`'s arrows as 1-cells and relates a word of **two** letters, or of none, to the one
letter it composes to: `f·g ↦ f ≫ g` and `ε ↦ 𝟙`.  Every word then collapses to its composite
(`taut_quot_map_eq_toPath`), so over a **thin** `C` nothing is left to present — soundness is
`Subsingleton.elim` and completeness is the collapse.

No relation preserves word length (`lengthGraded_taut`), which is what keeps the *tensor* of two
germs from receiving a merge.  The **product** is another matter: a 2-cell is a word, so a pair of
germ readings is one reading of the germ of the product category, and `taut (C × D)` **is** the
categorical product (`tautProdIso`) — the identity relation padding the shorter word.
-/

universe v u w u₀ w₂

namespace CategoryTheory

namespace Polygraph

open Limits

/-! ## The polygraph -/

/-- An arrow, as a 1-cell. -/
def tautCell {C : Type u} [Category.{v} C] {x y : C} (f : x ⟶ y) :
    (⟨x⟩ : GenObj (catGen C)) ⟶ ⟨y⟩ := f

/-- The arrow a word of the germ spells. -/
abbrev tautEval (C : Type u) [Category.{v} C] : Paths (GenObj (catGen C)) ⥤ C :=
  Paths.lift (catPre C)

/-- **The germ of `C`**: its arrows as 1-cells, and as 2-cells the words of two letters or of none,
each against the letter it composes to.  Reducible, so that instance search sees `C` through
`(taut C).V`. -/
@[reducible] def taut (C : Type u) [Category.{v} C] : Polygraph.{v, u, max u v} where
  V := C
  Gen := catGen C
  Rel x y := {w : Quiver.Path x y // w.length = 2 ∨ w.length = 0}
  src α := α.1
  tgt α := (tautCell ((tautEval C).map α.1)).toPath

variable {C : Type u} [Category.{v} C]

@[simp] theorem tautEval_toPath {x y : C} (f : x ⟶ y) :
    (tautEval C).map (tautCell f).toPath = f := Paths.lift_toPath (catPre C) f

/-- A word of two letters or none, as a 2-cell. -/
def tautRel {x y : GenObj (catGen C)} (w : Quiver.Path x y) (h : w.length = 2 ∨ w.length = 0) :
    (taut C).Rel x y := ⟨w, h⟩

/-- **A word of two letters or none is its composite.** -/
theorem taut_quot_rel {x y : GenObj (catGen C)} (w : Quiver.Path x y)
    (h : w.length = 2 ∨ w.length = 0) :
    (taut C).quot.map w = (taut C).quot.map (tautCell ((tautEval C).map w)).toPath :=
  (taut C).quot_src_tgt (tautRel w h)

/-- **A germ 2-cell is its source word** — the composite it is related to carries no choice. -/
theorem taut_boundaryDetermined : (taut C).BoundaryDetermined := fun _ _ hs _ => Subtype.ext hs

/-- **A germ relation changes the word length**: two letters become one, or none becomes one. -/
theorem lengthGraded_taut : LengthGraded (taut C) := by
  rintro x y ⟨w, h⟩ hα
  have h1 : w.length = 1 := hα
  rcases h with h | h <;> omega

/-! ## Every word is its composite -/

/-- **A word of the germ is the one letter its composite names** — the 2-cell at the empty word
starts the induction and the one at the last two letters continues it. -/
theorem taut_quot_map_eq_toPath {x y : GenObj (catGen C)} (w : Quiver.Path x y) :
    (taut C).quot.map w = (taut C).quot.map (tautCell ((tautEval C).map w)).toPath := by
  induction w with
  | nil => exact taut_quot_rel Quiver.Path.nil (Or.inr rfl)
  | @cons b c w e ih =>
      have hcons : (taut C).quot.map (w.cons e)
          = (taut C).quot.map w ≫ (taut C).quot.map (tautCell e).toPath :=
        (congrArg (taut C).quot.map (Quiver.Path.comp_toPath_eq_cons w e).symm).trans
          ((taut C).quot.map_comp w (tautCell e).toPath)
      have hsplit : (taut C).quot.map ((tautCell ((tautEval C).map w)).toPath.cons (tautCell e))
          = (taut C).quot.map (tautCell ((tautEval C).map w)).toPath
            ≫ (taut C).quot.map (tautCell e).toPath :=
        (congrArg (taut C).quot.map
            (Quiver.Path.comp_toPath_eq_cons
              (tautCell ((tautEval C).map w)).toPath (tautCell e)).symm).trans
          ((taut C).quot.map_comp _ _)
      have hval : (tautEval C).map ((tautCell ((tautEval C).map w)).toPath.cons (tautCell e))
          = (tautEval C).map (w.cons e) := by
        rw [Paths.lift_cons, Paths.lift_cons, tautEval_toPath]
        rfl
      refine hcons.trans ?_
      rw [ih]
      refine (hsplit.symm.trans (taut_quot_rel _ (Or.inl rfl))).trans ?_
      exact congrArg (fun f : x.as ⟶ c.as => (taut C).quot.map (tautCell f).toPath) hval

/-- **…so over a thin category every parallel pair of words is one arrow.** -/
theorem taut_quot_map_eq [Quiver.IsThin C] {x y : GenObj (catGen C)} (w w' : Quiver.Path x y) :
    (taut C).quot.map w = (taut C).quot.map w' :=
  ((taut_quot_map_eq_toPath w).trans
    (congrArg (fun f : x.as ⟶ y.as => (taut C).quot.map (tautCell f).toPath)
      (Subsingleton.elim _ _))).trans (taut_quot_map_eq_toPath w').symm

/-- **A one-letter word is its composite, on the nose** — the only surgery on words the germ
needs. -/
theorem taut_eq_toPath_of_length_eq_one {x y : GenObj (catGen C)} (w : Quiver.Path x y)
    (h : w.length = 1) : w = (tautCell ((tautEval C).map w)).toPath := by
  cases w with
  | nil => exact absurd h (by simp)
  | cons p e =>
      have h0 : p.length = 0 := by
        rw [Quiver.Path.length_cons] at h; omega
      cases Quiver.Path.eq_of_length_zero p h0
      cases Quiver.Path.eq_nil_of_length_zero p h0
      exact congrArg (fun f => (tautCell f).toPath)
        ((Paths.lift_toPath (catPre C) e).symm : e = (tautEval C).map _)

/-! ## What it presents -/

/-- **The germ of a thin category presents it** — the cells are its own, and the collapse of a word
to its composite is the whole word problem. -/
def tautPresents (C : Type u) [Category.{v} C] [Quiver.IsThin C] : Presents (taut C) C :=
  Presents.ofDesc (catPre C) (fun _ => Subsingleton.elim _ _)
    (fun {_ _ u v} _ => taut_quot_map_eq u v)
    ⟨fun {_ _} f => ⟨(tautCell f).toPath, Subsingleton.elim _ _⟩⟩
    ⟨fun c => ⟨⟨c⟩, ⟨Iso.refl c⟩⟩⟩

/-! ## …functorially -/

section Functorial

variable {D E : Type u} [Category.{v} D] [Category.{v} E]

/-- **A functor is a map of germs** — it pushes a relation's word forward, and the composite that
word is related to goes along. -/
def tautMap (F : C ⥤ D) : taut C ⟶ taut D where
  pre := catPreMap F
  two α := ⟨(catPreMap F).mapPath α.1, by rw [Prefunctor.length_mapPath]; exact α.2⟩
  src_two _ := rfl
  tgt_two α := by
    change (tautCell ((tautEval D).map ((catPreMap F).mapPath α.1))).toPath
      = (catPreMap F).mapPath (tautCell ((tautEval C).map α.1)).toPath
    rw [lift_catPreMap]
    exact (Prefunctor.mapPath_toPath (catPreMap F) _).symm

@[simp] theorem tautMap_id : tautMap (𝟭 C) = 𝟙 (taut C) :=
  hom_ext_of_boundaryDetermined taut_boundaryDetermined rfl

@[simp] theorem tautMap_comp (F : C ⥤ D) (G : D ⥤ E) :
    tautMap (F ⋙ G) = tautMap F ≫ tautMap G :=
  hom_ext_of_boundaryDetermined taut_boundaryDetermined rfl

/-- **An isomorphism of categories is an isomorphism of germs** — mutually inverse *on the nose*, an
equivalence being too weak to move the 0-cells. -/
def tautMapIso (F : C ⥤ D) (G : D ⥤ C) (hF : F ⋙ G = 𝟭 C) (hG : G ⋙ F = 𝟭 D) :
    taut C ≅ taut D where
  hom := tautMap F
  inv := tautMap G
  hom_inv_id := by rw [← tautMap_comp, hF, tautMap_id]
  inv_hom_id := by rw [← tautMap_comp, hG, tautMap_id]

end Functorial

/-! ## The germ of a product is the product of the germs

A 2-cell of `taut` is a word, so a pair of readings pushes a relation's word forward with nothing to
choose; what has to be checked is that the *composite* of the pushed word is again one letter, and
that is `taut_eq_toPath_of_length_eq_one` after reading the two projections. -/

section Prod

variable {D : Type u} [Category.{v} D] {R : Polygraph.{v, u, max u v}}

/-- **A word of the germ of a product spells the pair its two projections spell.** -/
theorem tautEval_prod {x y : GenObj (catGen (C × D))} (w : Quiver.Path x y) :
    (tautEval (C × D)).map w
      = ((tautEval C).map ((catPreMap (CategoryTheory.Prod.fst C D)).mapPath w),
          (tautEval D).map ((catPreMap (CategoryTheory.Prod.snd C D)).mapPath w)) :=
  Prod.ext (lift_catPreMap (CategoryTheory.Prod.fst C D) w).symm
    (lift_catPreMap (CategoryTheory.Prod.snd C D) w).symm

/-- A pair of germ readings, on the generating quivers. -/
def tautPairPre (u : R ⟶ taut C) (v : R ⟶ taut D) :
    GenObj R.Gen ⥤q GenObj (catGen (C × D)) where
  obj a := ⟨((u.pre.obj a).as, (v.pre.obj a).as)⟩
  map {_ _} e := (u.pre.map e, v.pre.map e)

/-- **The first projection of a paired word is the first reading's.**  An equation of *prefunctors*
would not rewrite under `mapPath` (the motive carries the endpoints), so it is stated on words. -/
theorem tautPairPre_mapPath_fst (u : R ⟶ taut C) (v : R ⟶ taut D) {a b : GenObj R.Gen}
    (w : Quiver.Path a b) :
    (catPreMap (CategoryTheory.Prod.fst C D)).mapPath ((tautPairPre u v).mapPath w)
      = u.pre.mapPath w :=
  (Prefunctor.mapPath_comp_apply (tautPairPre u v)
    (catPreMap (CategoryTheory.Prod.fst C D)) w).symm

/-- …and the second's. -/
theorem tautPairPre_mapPath_snd (u : R ⟶ taut C) (v : R ⟶ taut D) {a b : GenObj R.Gen}
    (w : Quiver.Path a b) :
    (catPreMap (CategoryTheory.Prod.snd C D)).mapPath ((tautPairPre u v).mapPath w)
      = v.pre.mapPath w :=
  (Prefunctor.mapPath_comp_apply (tautPairPre u v)
    (catPreMap (CategoryTheory.Prod.snd C D)) w).symm

/-- **A pair of germ readings is one reading of the germ of the product** — the relation's word goes
to the paired word, whose composite is one letter because each projection's is. -/
def tautPair (u : R ⟶ taut C) (v : R ⟶ taut D) : R ⟶ taut (C × D) where
  pre := tautPairPre u v
  two α := ⟨(tautPairPre u v).mapPath (R.src α), by
    have h : (u.pre.mapPath (R.src α)).length = 2 ∨ (u.pre.mapPath (R.src α)).length = 0 := by
      rw [← u.src_two α]; exact (u.two α).2
    have key : ((tautPairPre u v).mapPath (R.src α)).length
        = (u.pre.mapPath (R.src α)).length :=
      (Prefunctor.length_mapPath (catPreMap (CategoryTheory.Prod.fst C D)) _).symm.trans
        (congrArg Quiver.Path.length (tautPairPre_mapPath_fst u v (R.src α)))
    rw [key]; exact h⟩
  src_two _ := rfl
  tgt_two α := by
    have hone : ((tautPairPre u v).mapPath (R.tgt α)).length = 1 :=
      ((Prefunctor.length_mapPath (catPreMap (CategoryTheory.Prod.fst C D)) _).symm.trans
        (congrArg Quiver.Path.length (tautPairPre_mapPath_fst u v (R.tgt α)))).trans
        (by rw [← u.tgt_two α]; rfl)
    have hcomp : (tautEval (C × D)).map ((tautPairPre u v).mapPath (R.src α))
        = (tautEval (C × D)).map ((tautPairPre u v).mapPath (R.tgt α)) := by
      rw [tautEval_prod, tautEval_prod, tautPairPre_mapPath_fst, tautPairPre_mapPath_fst,
        tautPairPre_mapPath_snd, tautPairPre_mapPath_snd]
      refine Prod.ext ?_ ?_
      · rw [show u.pre.mapPath (R.src α) = (taut C).src (u.two α) from (u.src_two α).symm,
          show u.pre.mapPath (R.tgt α) = (taut C).tgt (u.two α) from (u.tgt_two α).symm]
        exact (tautEval_toPath _).symm
      · rw [show v.pre.mapPath (R.src α) = (taut D).src (v.two α) from (v.src_two α).symm,
          show v.pre.mapPath (R.tgt α) = (taut D).tgt (v.two α) from (v.tgt_two α).symm]
        exact (tautEval_toPath _).symm
    change (tautCell ((tautEval (C × D)).map ((tautPairPre u v).mapPath (R.src α)))).toPath
      = (tautPairPre u v).mapPath (R.tgt α)
    rw [hcomp]
    exact (taut_eq_toPath_of_length_eq_one _ hone).symm

/-- **The two projections exhibit the germ of a product as the product of the germs.**  A 2-cell is
a word and a word of the product is a pair of words, so nothing has to be matched up by hand. -/
def tautProd (C : Type u) [Category.{v} C] (D : Type u) [Category.{v} D] :
    IsLimit (BinaryFan.mk (tautMap (CategoryTheory.Prod.fst C D))
      (tautMap (CategoryTheory.Prod.snd C D))) :=
  BinaryFan.isLimitMk (fun s => tautPair s.fst s.snd)
    (fun _ => hom_ext_of_boundaryDetermined taut_boundaryDetermined rfl)
    (fun _ => hom_ext_of_boundaryDetermined taut_boundaryDetermined rfl)
    fun s m h₁ h₂ => by
      change m = tautPair s.fst s.snd
      rw [← h₁, ← h₂]
      exact hom_ext_of_boundaryDetermined taut_boundaryDetermined rfl

end Prod

/-! ## …in the universe where `Polygraph` has products -/

section ProdIso

variable (C : Type u) [Category.{u} C] (D : Type u) [Category.{u} D]

/-- **…so the germ of a product *is* the categorical product of the germs.** -/
noncomputable def tautProdIso : taut (C × D) ≅ taut C ⨯ taut D :=
  (tautProd C D).conePointUniqueUpToIso (limit.isLimit (pair _ _))

/-- **Two germs present the product of what they present** — the identity relation pads the shorter
word, which is what a cellwise product asks for and a length-preserving presentation cannot
give. -/
noncomputable def tautPresentsProd [Quiver.IsThin C] [Quiver.IsThin D] :
    Presents (taut C ⨯ taut D) (C × D) :=
  (tautPresents (C × D)).ofPolyIso (tautProdIso C D)

end ProdIso

end Polygraph

end CategoryTheory
