import CubeChains.Machinery.Presentation.Localize

/-!
# Machinery/Presentation/Contract — collapsing a family of generators onto representatives

A `Collapse` names one 0-cell per class; `poly` keeps those 0-cells and renames each non-`S`
generator onto them.  A 1-cell of `poly` is a 1-cell of `P` and a 2-cell of `poly` is a 2-cell of
`P` — the collapse moves no cell, only the names of its two ends:

                         g
                a ───────────────▸ b
             rep a               rep b

An `S`-letter makes `cell g` the empty word.  `Restrict` cannot do this: convexity forces closure
under isomorphism.
-/

universe w u' w₂ v u

namespace CategoryTheory

open Polygraph

/-- **Data collapsing `P` along a family `S`**: one 0-cell per class, which an `S`-letter does not
leave. -/
structure Collapse (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop) where
  /-- the representative of a 0-cell -/
  rep : P.V → P.V
  /-- …which is its own representative -/
  rep_idem : ∀ x, rep (rep x) = rep x
  /-- an `S`-letter does not change the representative -/
  rep_eq_of_S : ∀ {a b : P.V} {g : P.Gen a b}, S g → rep a = rep b

namespace Collapse

variable {P : Polygraph.{w, u', w₂}} {S : ∀ {a b : P.V}, P.Gen a b → Prop} (c : Collapse P S)

/-! ## The collapsed polygraph -/

/-- The 0-cells: those of `P` that are their own representative. -/
abbrev V : Type u' := {x : P.V // c.rep x = x}

/-- **A 1-cell**: a non-`S` generator of `P`, carrying the representatives of its endpoints. -/
structure Gen (x y : c.V) where
  /-- where the generator starts -/
  dom : P.V
  /-- …and where it ends -/
  cod : P.V
  /-- the generator -/
  gen : P.Gen dom cod
  /-- …not one of the collapsed ones -/
  not_mem : ¬ S gen
  /-- its source represents `x`… -/
  rep_dom : c.rep dom = x.1
  /-- …and its target represents `y` -/
  rep_cod : c.rep cod = y.1

/-- The 0-cell a 0-cell of `P` represents. -/
def repObj (u : GenObj P.Gen) : GenObj c.Gen := ⟨⟨c.rep u.as, c.rep_idem u.as⟩⟩

theorem repObj_eq_of_S {u v : GenObj P.Gen} (g : u ⟶ v) (h : S g) : c.repObj u = c.repObj v :=
  GenObj.ext (Subtype.ext (c.rep_eq_of_S h))

/-- **A 1-cell of the collapse is its generator** — the two representative equations are
propositions, so the endpoints it carries and that generator are all of it. -/
theorem Gen.ext {x y : c.V} :
    ∀ g g' : c.Gen x y, g.dom = g'.dom → g.cod = g'.cod → g.gen ≍ g'.gen → g = g'
  | ⟨dom, cod, gen, _, _, _⟩, ⟨dom', cod', gen', _, _, _⟩, hdom, hcod, hgen => by
      obtain rfl : dom = dom' := hdom
      obtain rfl : cod = cod' := hcod
      obtain rfl : gen = gen' := eq_of_heq hgen
      rfl

/-- The 1-cell a non-`S` generator becomes. -/
def genCell {u v : GenObj P.Gen} (g : u ⟶ v) (hg : ¬ S g) : c.repObj u ⟶ c.repObj v :=
  ⟨u.as, v.as, g, hg, rfl, rfl⟩

/-- **The conjugation, on a letter**: an `S`-letter becomes the empty word, any other itself. -/
noncomputable def cell {u v : GenObj P.Gen} (g : u ⟶ v) :
    Quiver.Path (c.repObj u) (c.repObj v) :=
  @dite _ (S g) (Classical.propDecidable _)
    (fun hg => cellCongr Quiver.Path rfl (c.repObj_eq_of_S g hg) Quiver.Path.nil)
    (fun hg => (c.genCell g hg).toPath)

theorem cell_of_S {u v : GenObj P.Gen} (g : u ⟶ v) (hg : S g) :
    c.cell g = cellCongr Quiver.Path rfl (c.repObj_eq_of_S g hg) Quiver.Path.nil :=
  dif_pos hg

theorem cell_of_not_S {u v : GenObj P.Gen} (g : u ⟶ v) (hg : ¬ S g) :
    c.cell g = (c.genCell g hg).toPath :=
  dif_neg hg

/-- The conjugation, as a spelling of `P`'s letters by words of the collapse. -/
noncomputable def pre : GenObj P.Gen ⥤q Paths (GenObj c.Gen) where
  obj := c.repObj
  map g := c.cell g

/-- …and on whole words. -/
noncomputable abbrev words : P.Word ⥤ Paths (GenObj c.Gen) := Paths.lift c.pre

/-- **A 2-cell**: a 2-cell of `P`, carrying the representatives of its endpoints. -/
structure Cell (X Y : GenObj c.Gen) where
  /-- where the 2-cell sits, upstairs -/
  dom : GenObj P.Gen
  /-- …and where it ends -/
  cod : GenObj P.Gen
  /-- the 2-cell -/
  cell : P.Rel dom cod
  /-- its source represents `X`… -/
  rep_dom : c.repObj dom = X
  /-- …and its target represents `Y` -/
  rep_cod : c.repObj cod = Y

/-- **The collapsed polygraph** — the representatives, the conjugated non-`S` generators, and the
conjugated 2-cells. -/
noncomputable def poly : Polygraph where
  V := c.V
  Gen := c.Gen
  Rel := c.Cell
  src α := cellCongr Quiver.Path α.rep_dom α.rep_cod (c.words.map (P.src α.cell))
  tgt α := cellCongr Quiver.Path α.rep_dom α.rep_cod (c.words.map (P.tgt α.cell))

end Collapse

end CategoryTheory
