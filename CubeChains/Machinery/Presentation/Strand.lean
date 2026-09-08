import CubeChains.Machinery.Presentation.Basic
import Mathlib.CategoryTheory.Sigma.Basic

/-!
# Machinery/Presentation/Strand — the coproduct of one-object polygraphs, indexed by its 0-cells

`strandPoly` is `Polygraph.coproduct` of a family of *one-object* polygraphs, with the redundant
vertex dropped: its 0-cells **are** the index, so there is no `Unique` to impose and no
`Σ i, Unit` to project.  A 1-cell lives at one index and a 2-cell is one index's own, both carried
by indexed inductives so that `cases` reads the index off a cell.

The fibre inclusion `strandPre` is star-bijective and injective on 0-cells, so a word between two
0-cells is one index's word; that, plus the absence of cross-index words, is the whole content of
`Presents.strand`.
-/

universe v u

namespace CategoryTheory

namespace Polygraph

/-! ## One-object fibres -/

variable {ι : Type} (G : ι → Type)

/-- The 0-cell of a one-object fibre. -/
abbrev loopPt (A : Type) : GenObj (fun _ _ : Unit => A) := ⟨()⟩

/-- **The one-object polygraph** of a set of generators and a set of relations between words in
them. -/
def loopPoly (A R : Type) (src tgt : R → Quiver.Path (loopPt A) (loopPt A)) :
    Polygraph.{0, 0, 0} where
  V := Unit
  Gen := fun _ _ => A
  Rel := fun _ _ => R
  src := fun α => src α
  tgt := fun α => tgt α

/-! ## The graded polygraph -/

/-- **1-cells graded by the index**: a generator at one index, and none across indices. -/
inductive StrandGen (G : ι → Type) : ι → ι → Type
  | mk {i : ι} : G i → StrandGen G i i

variable {G}

/-- The index a 1-cell lies at is preserved. -/
theorem StrandGen.index_eq {a b : ι} (e : StrandGen G a b) : a = b := by cases e; rfl

/-- The generator a 1-cell is. -/
def StrandGen.gen : ∀ {a b : ι}, StrandGen G a b → G a
  | _, _, .mk s => s

variable (G)

/-- The inclusion of one index's generating quiver. -/
def strandPre (i : ι) : GenObj (fun _ _ : Unit => G i) ⥤q GenObj (StrandGen G) where
  obj _ := ⟨i⟩
  map e := StrandGen.mk e

/-- **2-cells graded by the index**: one index's own. -/
inductive StrandRel (G : ι → Type) (R : ι → Type) :
    GenObj (StrandGen G) → GenObj (StrandGen G) → Type
  | mk {i : ι} : R i → StrandRel G R ((strandPre G i).obj (loopPt (G i)))
      ((strandPre G i).obj (loopPt (G i)))

variable (R : ι → Type)
  (sr tr : ∀ i : ι, R i → Quiver.Path (loopPt (G i)) (loopPt (G i)))

/-- The source of a graded 2-cell: its index's, included. -/
def StrandRel.src : ∀ {a b : GenObj (StrandGen G)}, StrandRel G R a b → Quiver.Path a b
  | _, _, .mk (i := i) α => (strandPre G i).mapPath (sr i α)

/-- The target of a graded 2-cell: its index's, included. -/
def StrandRel.tgt : ∀ {a b : GenObj (StrandGen G)}, StrandRel G R a b → Quiver.Path a b
  | _, _, .mk (i := i) α => (strandPre G i).mapPath (tr i α)

/-- **The coproduct of a family of one-object polygraphs, its 0-cells the index.** -/
def strandPoly : Polygraph.{0, 0, 0} where
  V := ι
  Gen := StrandGen G
  Rel := StrandRel G R
  src := StrandRel.src G R sr
  tgt := StrandRel.tgt G R tr

/-- The fibre at one index, as a polygraph in its own right. -/
abbrev strandFibre (i : ι) : Polygraph.{0, 0, 0} := loopPoly (G i) (R i) (sr i) (tr i)

/-- The index's inclusion. -/
def strandIncl (i : ι) : Hom (strandFibre G R sr tr i) (strandPoly G R sr tr) where
  pre := strandPre G i
  two α := StrandRel.mk α
  src_two _ := rfl
  tgt_two _ := rfl

variable {G R sr tr}

/-- A word stays at the index it starts at. -/
theorem strand_path_index {a b : GenObj (StrandGen G)} (u : Quiver.Path a b) : a.as = b.as := by
  induction u with
  | nil => rfl
  | cons _ e ih => exact ih.trans (StrandGen.index_eq e)

theorem strandPre_obj_injective (i : ι) : Function.Injective (strandPre G i).obj := by
  rintro ⟨⟩ ⟨⟩ _; rfl

theorem strandPre_star_surjective (i : ι) (x : GenObj (fun _ _ : Unit => G i)) :
    Function.Surjective ((strandPre G i).star x) := by
  rintro ⟨⟨j⟩, e⟩
  cases e with
  | mk g => exact ⟨⟨⟨()⟩, g⟩, rfl⟩

theorem strandPre_pathsFunctor_full (i : ι) : (strandPre G i).pathsFunctor.Full :=
  Prefunctor.pathsFunctor_full _ (strandPre_star_surjective i) (strandPre_obj_injective i)

theorem strandPre_star_injective (i : ι) (x : GenObj (fun _ _ : Unit => G i)) :
    Function.Injective ((strandPre G i).star x) := by
  rintro ⟨y₁, e₁⟩ ⟨y₂, e₂⟩ h
  obtain ⟨hy, he⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : y₁ = y₂ := strandPre_obj_injective i hy
  have h2 : (StrandGen.mk (G := G) (i := i) e₁) = StrandGen.mk (G := G) (i := i) e₂ :=
    eq_of_heq he
  exact Sigma.ext rfl (heq_of_eq (congrArg StrandGen.gen h2))

instance strandPre_pathsFunctor_faithful (i : ι) : (strandPre G i).pathsFunctor.Faithful :=
  Prefunctor.pathsFunctor_faithful _ (strandPre_star_injective i)

/-- **A word between 0-cells of one index is that index's word.** -/
theorem strand_exists_mapPath (i : ι) (u : Quiver.Path (⟨i⟩ : GenObj (StrandGen G)) ⟨i⟩) :
    ∃ u' : Quiver.Path (loopPt (G i)) (loopPt (G i)), (strandPre G i).mapPath u' = u :=
  (strandPre_pathsFunctor_full i).map_surjective (X := loopPt (G i)) (Y := loopPt (G i)) u

/-- **A 2-cell over one index's 0-cells is that index's.** -/
theorem strandRel_mk_of_eq :
    ∀ {a b : GenObj (StrandGen G)} (β : StrandRel G R a b) {i : ι},
      (⟨i⟩ : GenObj (StrandGen G)) = a → (⟨i⟩ : GenObj (StrandGen G)) = b →
      ∃ α : R i, β ≍ StrandRel.mk (G := G) α := by
  rintro _ _ ⟨β⟩ i ha _
  obtain rfl : i = _ := congrArg GenObj.as ha
  exact ⟨β, HEq.rfl⟩

/-- **A 2-cell is its index's boundary**: the inclusion is a covering, so words determine
themselves, and one index's 2-cells are pinned by theirs. -/
theorem boundaryDetermined_strandPoly
    (hQ : ∀ i, (strandFibre G R sr tr i).BoundaryDetermined) :
    (strandPoly G R sr tr).BoundaryDetermined := by
  rintro _ _ ⟨α⟩ β hs ht
  obtain ⟨β', hβ⟩ := strandRel_mk_of_eq β rfl rfl
  obtain rfl : β = StrandRel.mk β' := eq_of_heq hβ
  refine congrArg StrandRel.mk
    (hQ _ (x := loopPt (G _)) (y := loopPt (G _)) α β' ?_ ?_)
  · exact (strandPre_pathsFunctor_faithful _).map_injective hs
  · exact (strandPre_pathsFunctor_faithful _).map_injective ht

end Polygraph

/-! ## What it presents

Each index presents a category; the graded polygraph presents their disjoint union, its 0-cells
already the index. -/

namespace Presents

open Polygraph

variable {ι : Type} {G R : ι → Type}
  {sr tr : ∀ i : ι, R i → Quiver.Path (loopPt (G i)) (loopPt (G i))}
  {C : ι → Type u} [∀ i, Category.{v} (C i)]
  (q : ∀ i : ι, Presents (strandFibre G R sr tr i) (C i))

/-- The arrow a graded 1-cell names. -/
def strandArrow : ∀ {a b : ι}, StrandGen G a b →
    ((⟨a, (q a).at' (loopPt (G a))⟩ : Σ i, C i) ⟶ ⟨b, (q b).at' (loopPt (G b))⟩)
  | _, _, .mk g => Sigma.SigmaHom.mk ((q _).arrow g)

/-- The cells, interpreted in the disjoint union of the categories. -/
def strandEval : GenObj (StrandGen G) ⥤q (Σ i, C i) where
  obj x := ⟨x.as, (q x.as).at' (loopPt (G x.as))⟩
  map e := strandArrow q e

/-- **One index's word, evaluated** — that index's own evaluation, included. -/
theorem strandEval_mapPath (i : ι) {x y : GenObj (fun _ _ : Unit => G i)}
    (u : Quiver.Path x y) :
    (Paths.lift (strandEval q)).map ((strandPre G i).mapPath u)
      = (Sigma.incl i).map ((q i).eval.map u) := by
  rw [Paths.lift_mapPath]
  exact (q i).lift_evalPre_comp (Sigma.incl i) u

theorem strand_sound {a b : GenObj (StrandGen G)} (α : (strandPoly G R sr tr).Rel a b) :
    (Paths.lift (strandEval q)).map ((strandPoly G R sr tr).src α)
      = (Paths.lift (strandEval q)).map ((strandPoly G R sr tr).tgt α) := by
  cases α with
  | @mk i hr =>
      change (Paths.lift (strandEval q)).map ((strandPre G i).mapPath (sr i hr))
        = (Paths.lift (strandEval q)).map ((strandPre G i).mapPath (tr i hr))
      rw [strandEval_mapPath, strandEval_mapPath]
      exact congrArg _ ((q i).sound hr)

theorem strand_complete {a b : GenObj (StrandGen G)} {u v : Quiver.Path a b}
    (h : (Paths.lift (strandEval q)).map u = (Paths.lift (strandEval q)).map v) :
    (strandPoly G R sr tr).quot.map u = (strandPoly G R sr tr).quot.map v := by
  obtain ⟨i⟩ := a
  obtain ⟨j⟩ := b
  obtain rfl : i = j := strand_path_index u
  obtain ⟨u', rfl⟩ := strand_exists_mapPath i u
  obtain ⟨v', rfl⟩ := strand_exists_mapPath i v
  have h' : (q i).E.map ((strandFibre G R sr tr i).quot.map u')
      = (q i).E.map ((strandFibre G R sr tr i).quot.map v') :=
    (Sigma.incl i).map_injective
      ((strandEval_mapPath q i u').symm.trans (h.trans (strandEval_mapPath q i v')))
  exact (strandIncl G R sr tr i).quot_map_congr ((q i).E.map_injective h')

theorem strand_full : (Paths.lift (strandEval q)).Full where
  map_surjective := by
    rintro ⟨i⟩ ⟨j⟩ f
    cases f with
    | mk g =>
        obtain ⟨w, hw⟩ := (q i).eval.map_surjective (X := ⟨()⟩) (Y := ⟨()⟩) g
        exact ⟨(strandPre G i).mapPath w,
          (strandEval_mapPath q i w).trans (congrArg (Sigma.incl i).map hw)⟩

theorem strand_essSurj : (Paths.lift (strandEval q)).EssSurj where
  mem_essImage := by
    rintro ⟨i, c⟩
    obtain ⟨_, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := (q i).eval) c
    exact ⟨⟨i⟩, ⟨(Sigma.incl i).mapIso e⟩⟩

/-- **A family of one-object presentations presents the graded polygraph**, whose 0-cells are the
index itself. -/
def strand : Presents (strandPoly G R sr tr) (Σ i, C i) :=
  Presents.ofDesc (strandEval q) (strand_sound q) (strand_complete q) (strand_full q)
    (strand_essSurj q)

@[simp] theorem strand_at' (i : ι) :
    (strand q).at' (⟨i⟩ : GenObj (StrandGen G)) = ⟨i, (q i).at' (loopPt (G i))⟩ := rfl

/-- **One index's 1-cell names its own arrow, included.** -/
@[simp] theorem strand_arrow (i : ι) (g : G i) :
    (strand q).arrow (StrandGen.mk (G := G) g) = (Sigma.incl i).map ((q i).arrow g) :=
  Presents.ofDesc_arrow _ (strand_sound q) _

end Presents

end CategoryTheory
