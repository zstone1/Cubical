import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Quotient

/-!
# Machinery/Presentation/Basic — `C ≌ ⟨generators | relations⟩`

A presentation of `C` is a 2-polygraph over `C`: 0-cells a type `V` with `ob : V → C`, 1-cells a
family `Gen` with `arrow` naming an arrow of `C`, 2-cells a relation on the words they spell.  The
cells are *indices*, not the objects and arrows themselves — that is what lets a presentation
transport along an equivalence (`transport`), so one presentation is read on every category
equivalent to `C` instead of a second being built there and compared.

Three obligations, one per way `functor` can fail: `spans` (full), `complete` (faithful),
`covers` (essentially surjective).

`GenObj` re-quivers `V` by the generators — without it `Paths` would pick up whatever quiver `V`
already carries — and it is indexed by `Gen` alone, so `transport` leaves the 2-cells untouched.
-/

universe w u' v u

namespace CategoryTheory

/-- A 0-cell: an index for an object, carrying the generating quiver rather than any quiver its
index type already has. -/
structure GenObj {V : Type u'} (Gen : V → V → Type w) where
  /-- the index it names -/
  as : V

instance genObjQuiver {V : Type u'} (Gen : V → V → Type w) : Quiver.{w} (GenObj Gen) :=
  ⟨fun x y => Gen x.as y.as⟩

/-- The 0- and 1-cells of a presentation of `C`: a quiver, and a prefunctor from it to `C`. -/
structure Gens (C : Type u) [Category.{v} C] where
  /-- the 0-cells -/
  V : Type u'
  /-- the object a 0-cell names -/
  ob : V → C
  /-- the 1-cells -/
  Gen : V → V → Type w
  /-- the arrow a 1-cell names -/
  arrow {x y : V} : Gen x y → (ob x ⟶ ob y)

namespace Gens

variable {C : Type u} [Category.{v} C] (G : Gens C)

/-- An index, as a 0-cell. -/
abbrev pt (a : G.V) : GenObj G.Gen := ⟨a⟩

/-- The object a 0-cell names. -/
abbrev at' (x : GenObj G.Gen) : C := G.ob x.as

/-- The arrow a generating word spells. -/
def eval : Paths (GenObj G.Gen) ⥤ C := Paths.lift ⟨fun x => G.ob x.as, G.arrow⟩

@[simp] theorem eval_obj (x : GenObj G.Gen) : G.eval.obj x = G.at' x := rfl

@[simp] theorem eval_toPath {x y : GenObj G.Gen} (e : x ⟶ y) : G.eval.map e.toPath = G.arrow e :=
  Paths.lift_toPath _ _

@[simp] theorem eval_nil (x : GenObj G.Gen) :
    G.eval.map (Quiver.Path.nil : Quiver.Path x x) = 𝟙 (G.at' x) :=
  Paths.lift_nil _ _

@[simp] theorem eval_cons {x y z : GenObj G.Gen} (P : Quiver.Path x y) (e : y ⟶ z) :
    G.eval.map (P.cons e) = G.eval.map P ≫ G.arrow e :=
  Paths.lift_cons _ _ _

/-! ### Reading the cells in another category -/

variable {D : Type*} [Category D]

/-- The cells of `C`, read along a functor.  `Gen` is unchanged, so `GenObj` — and hence any
relation on words — is the *same type*. -/
@[simps] def pushforward (F : C ⥤ D) : Gens D where
  V := G.V
  ob a := F.obj (G.ob a)
  Gen := G.Gen
  arrow g := F.map (G.arrow g)

theorem eval_pushforward (F : C ⥤ D) {x y : GenObj G.Gen} (P : Quiver.Path x y) :
    (G.pushforward F).eval.map P = F.map (G.eval.map P) := by
  induction P with
  | nil => exact (F.map_id _).symm
  | cons P g ih =>
      change (G.pushforward F).eval.map P ≫ F.map (G.arrow g) = _
      rw [ih]
      exact (F.map_comp _ _).symm

end Gens

/-- **A presentation of `C`**: cells indexing arrows of `C`, and relations between the words they
spell, presenting `C` — see `Presentation.equiv`. -/
structure Presentation (C : Type u) [Category.{v} C] extends Gens.{w, u'} C where
  /-- the 2-cells: parallel pairs of generating words -/
  rel : HomRel (Paths (GenObj toGens.Gen))
  /-- each relation holds in `C` -/
  sound {x y : GenObj toGens.Gen} {P Q : Quiver.Path x y} :
    rel P Q → toGens.eval.map P = toGens.eval.map Q
  /-- the generators span: every arrow between named objects is a word -/
  spans {x y : GenObj toGens.Gen} (f : toGens.at' x ⟶ toGens.at' y) :
    ∃ P : Quiver.Path x y, toGens.eval.map P = f
  /-- the relations are complete: words agreeing in `C` already agree in the quotient -/
  complete {x y : GenObj toGens.Gen} {P Q : Quiver.Path x y} :
    toGens.eval.map P = toGens.eval.map Q →
      (Quotient.functor rel).map P = (Quotient.functor rel).map Q
  /-- the 0-cells cover: every object of `C` is named, up to isomorphism -/
  covers (c : C) : ∃ x : GenObj toGens.Gen, Nonempty (toGens.at' x ≅ c)

namespace Presentation

variable {C : Type u} [Category.{v} C] (p : Presentation C)

/-- The presented category: generating words modulo the relations. -/
abbrev Quot : Type u' := Quotient p.rel

/-- The object of `p.Quot` a 0-cell names. -/
abbrev obj (x : GenObj p.Gen) : p.Quot := ⟨x⟩

/-- **Evaluation, on the quotient** — the comparison functor. -/
def functor : p.Quot ⥤ C := Quotient.lift p.rel p.toGens.eval fun _ _ _ _ h => p.sound h

@[simp] theorem functor_obj (x : GenObj p.Gen) : p.functor.obj (p.obj x) = p.toGens.at' x := rfl

@[simp] theorem functor_map {x y : GenObj p.Gen} (P : Quiver.Path x y) :
    p.functor.map ((Quotient.functor p.rel).map P) = p.toGens.eval.map P := rfl

instance : p.functor.Full where
  map_surjective {_ _} f := by
    obtain ⟨P, hP⟩ := p.spans f
    exact ⟨(Quotient.functor p.rel).map P, hP⟩

instance : p.functor.Faithful where
  map_injective {_ _} f g h := by
    obtain ⟨P, rfl⟩ := (Quotient.functor p.rel).map_surjective f
    obtain ⟨Q, rfl⟩ := (Quotient.functor p.rel).map_surjective g
    exact p.complete h

instance : p.functor.EssSurj where
  mem_essImage c := by
    obtain ⟨x, ⟨e⟩⟩ := p.covers c
    exact ⟨p.obj x, ⟨e⟩⟩

instance : p.functor.IsEquivalence where

/-- **`C ≌ ⟨generators | relations⟩`.** -/
noncomputable def equiv : p.Quot ≌ C := p.functor.asEquivalence

/-- A word for an arrow, chosen. -/
noncomputable def word {x y : GenObj p.Gen} (f : p.toGens.at' x ⟶ p.toGens.at' y) :
    Quiver.Path x y := (p.spans f).choose

@[simp] theorem eval_word {x y : GenObj p.Gen} (f : p.toGens.at' x ⟶ p.toGens.at' y) :
    p.toGens.eval.map (p.word f) = f := (p.spans f).choose_spec

/-! ## Transport

The cells index; they are not themselves the objects and arrows.  So the same presentation reads
on every category equivalent to `C`, with the same 2-cells — no second presentation is built, and
none has to be compared. -/

/-- **A presentation transports along an equivalence**, cells and relations unchanged. -/
def transport {D : Type*} [Category D] (e : C ≌ D) : Presentation D where
  toGens := p.toGens.pushforward e.functor
  rel := p.rel
  sound h := by rw [Gens.eval_pushforward, Gens.eval_pushforward, p.sound h]
  spans f := by
    obtain ⟨P, hP⟩ := p.spans (e.functor.preimage f)
    exact ⟨P, by rw [Gens.eval_pushforward, hP]; exact e.functor.map_preimage f⟩
  complete h := p.complete (e.functor.map_injective
    (by rw [← Gens.eval_pushforward, ← Gens.eval_pushforward]; exact h))
  covers d := by
    obtain ⟨x, ⟨i⟩⟩ := p.covers (e.inverse.obj d)
    exact ⟨x, ⟨e.functor.mapIso i ≪≫ e.counitIso.app d⟩⟩

end Presentation

end CategoryTheory
