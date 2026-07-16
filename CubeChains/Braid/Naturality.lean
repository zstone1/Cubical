import CubeChains.Braid.Grading
import CubeChains.Foundations.Terminal

/-!
# Braid/Naturality — `braidGrading` is natural in `K`, hence factors through the terminal set

A `BPSet` map `f : K ⟶ L` relabels every execution's chain by post-composition (`concMap f`),
keeping its dimension sequence, block data, and chamber tuple.  `braidGrading` reads only the event
count (`nEvents`) and the event permutation (`evPerm'`) of an execution, and both are blind to that
relabelling — so `braidGrading K = concMap f ⋙ braidGrading L`.

Specializing to the unique map `K ⟶ Zbp` (terminal), every braid of `K` is the image of a braid of
the terminal set: `Zbp` is universal for braids.
-/

open CategoryTheory Opposite

namespace CubeChains

variable {K L : BPSet}

/-! ## The functor on executions induced by a `BPSet` map -/

/-- Push an execution of `K` forward along `f : K ⟶ L`: relabel its chain by `f`
(`ChainCat.pushforward`), keeping the chamber tuple.  The chain's dimensions and block data are
untouched, so the chamber tuple retypes verbatim (`LinesObj` depends only on `dims`). -/
def concMap (f : K ⟶ L) : ConcCat K ⥤ ConcCat L where
  obj x := ⟨op ((ChainCat.pushforward f).obj x.1.unop), x.2⟩
  map {x y} g := ⟨(ChainCat.pushforward f).op.map g.val, g.property⟩
  map_id x := by apply CategoryOfElements.ext; simp
  map_comp g h := by apply CategoryOfElements.ext; simp

@[simp] theorem concMap_obj_chain (f : K ⟶ L) (x : ConcCat K) :
    (concMap f |>.obj x).chain = (ChainCat.pushforward f).obj x.chain := rfl

@[simp] theorem concMap_obj_line (f : K ⟶ L) (x : ConcCat K) :
    (concMap f |>.obj x).line = x.line := rfl

/-! ## Naturality: the frame is preserved -/

/-- The relabelling neither creates nor destroys events. -/
theorem nEvents_concMap (f : K ⟶ L) (x : ConcCat K) :
    nEvents (concMap f |>.obj x) = nEvents x := rfl

/-- **`braidGrading` is natural in `K`.**  `concMap f` preserves the event count and the event
permutation definitionally (the chamber tuple and block data are carried verbatim), so it commutes
with the braid grading. -/
theorem braidGrading_natural (f : K ⟶ L) :
    braidGrading K = concMap f ⋙ braidGrading L :=
  rfl

/-! ## The terminal factorization -/

/-- The unique `BPSet` map into the terminal set `Zbp` (its target has one cell per dimension, so
`init`/`final` preservation is forced). -/
def toZbp (K : BPSet) : K ⟶ Zbp where
  hom := toZ K.toPsh
  app_init := rfl
  app_final := rfl

/-- Any two maps into `Zbp` agree: `Z` is terminal. -/
theorem toZbp_unique {K : BPSet} (f : K ⟶ Zbp) : f = toZbp K :=
  BPSet.hom_ext (isTerminalZ.hom_ext _ _)

/-- Push executions of `K` forward to the terminal set. -/
def concToZ (K : BPSet) : ConcCat K ⥤ ConcCat Zbp := concMap (toZbp K)

/-- **`braidGrading` factors through the terminal set.**  Every braid of `K` is the image, under the
push to `Zbp`, of a braid of the terminal set — so `Zbp` is universal for braids. -/
theorem braidGrading_factor (K : BPSet) :
    braidGrading K = concToZ K ⋙ braidGrading Zbp :=
  braidGrading_natural (toZbp K)

end CubeChains
