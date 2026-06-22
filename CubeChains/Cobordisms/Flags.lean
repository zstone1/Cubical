import CubeChains.Cobordisms.Cospan
import CubeChains.Cobordisms.Loops
import Mathlib.Order.Preorder.Finite

/-!
# Cobordisms/Flags — cobordism flags + the M6(a) "∅-bottom" theorem

The **flag layer** of the directed-cobordism build (M4 prep / M6(a)).  Given a
cospan `C : Cospan X Y` (the backbone `X ⇒ Y`, apex `C.mid`), we cut out the
images of the two legs as predicates on `C.mid.TotalCell` and impose the
directedness/coverage conditions a *cobordism* must satisfy:

* `Cospan.srcImage` / `Cospan.sinkImage` — the image sub-cell-sets of the source
  leg `inl` and sink leg `inr`.
* `Cospan.SrcSieve` / `Cospan.SinkCosieve` (C2/C3) — the source image is past-closed
  (a `Precubical.Cobordism.IsSieve`) and the sink image is future-closed (a
  `Precubical.Cobordism.IsCosieve`).
* `IsMinimalVertex` / `IsMaximalVertex` — vertices nothing strictly reaches /
  nothing is strictly reached from, over the directed `Reaches` preorder.
* `Cospan.Closed` — every minimal vertex lies in the source image and every maximal
  vertex lies in the sink image (the boundary is *all* of the directed extremes).
* `Cospan.Spanning` — every cell lies on a dipath from the source to the sink.
  (The third intended flag, *loop confinement*, is already `Loops.LoopConfined`
  applied as `LoopConfined C.mid (srcImage C) (sinkImage C)`; see the note below.)

The headline is **M6(a)** (`no_closed_cobordism_from_empty`): there is **no
`Closed` cobordism out of the empty precubical set** `∅ ⇒ X` once `C.mid` has a
minimal vertex.  Conceptually this is *why the `Closed` flag must be carried*:
under the bare cospan conditions C1–C4 alone the cylinder `X ⊗ □¹` is already a
cobordism `∅ ⇒ X` (its source leg is the empty map), so the cobordism relation
only "carries information" once `Closed` is imposed — `Closed` forces the source
image to absorb every minimal vertex, which an empty source image cannot do.

## The empty precubical set

There is no `OrderBot`/`⊥` on `PrecubicalSet = Boxᵒᵖ ⥤ Type`, and the abstract
`Limits.initial` makes `cells n` an opaque colimit.  We therefore take the
**concrete** initial object: the constant `PEmpty`-valued presheaf
`emptyPsh := (Functor.const Boxᵒᵖ).obj PEmpty`, written `∅` in this file.  Its
cells at every level are `PEmpty`, so `IsEmpty (∅.cells n)` is definitional
(`instEmptyCellsEmptyPsh`) — exactly what M6(a) needs.

**Layer:** Cobordisms.  **Imports:** `Cobordisms/Cospan`, `Cobordisms/Loops`,
mathlib `Order.Preorder.Finite`.
-/

open CategoryTheory Opposite
open Precubical.Cobordism

namespace PrecubicalSet

universe u

variable {X Y : PrecubicalSet}

/-! ### Leg images -/

namespace Cospan

/-- The **source image** of a cospan: the cells of `C.mid` in the image of the
source leg `inl`. -/
def srcImage (C : Cospan X Y) : C.mid.TotalCell → Prop :=
  fun z => ∃ x, mapCell C.inl x = z

/-- The **sink image** of a cospan: the cells of `C.mid` in the image of the sink
leg `inr`. -/
def sinkImage (C : Cospan X Y) : C.mid.TotalCell → Prop :=
  fun z => ∃ y, mapCell C.inr y = z

/-! ### Sieve / cosieve conditions (C2 / C3) -/

/-- **C2.**  The source image is a *sieve* (past-closed): the source `iX` is
closed under going backwards along `Reaches`. -/
def SrcSieve (C : Cospan X Y) : Prop :=
  IsSieve C.mid (srcImage C)

/-- **C3.**  The sink image is a *cosieve* (future-closed): the sink `jY` is
closed under going forwards along `Reaches`. -/
def SinkCosieve (C : Cospan X Y) : Prop :=
  IsCosieve C.mid (sinkImage C)

end Cospan

/-! ### Minimal and maximal vertices -/

/-- A vertex `v` of `W` is **minimal** when nothing strictly reaches it: every
total cell `u` with `Reaches W u ⟨0, v⟩` is already `⟨0, v⟩`. -/
def IsMinimalVertex (W : PrecubicalSet) (v : W.cells 0) : Prop :=
  ∀ u : W.TotalCell, Reaches W u ⟨0, v⟩ → u = ⟨0, v⟩

/-- A vertex `v` of `W` is **maximal** when nothing is strictly reached from it:
every total cell `u` with `Reaches W ⟨0, v⟩ u` is already `⟨0, v⟩`. -/
def IsMaximalVertex (W : PrecubicalSet) (v : W.cells 0) : Prop :=
  ∀ u : W.TotalCell, Reaches W ⟨0, v⟩ u → u = ⟨0, v⟩

/-! ### The flags -/

namespace Cospan

/-- **The `Closed` flag.**  A cobordism is *closed* when its directed boundary is
*all* of the directed extremes of `C.mid`: every minimal vertex lies in the source
image and every maximal vertex lies in the sink image.  (This is the flag that
M6(a) shows must be carried — see the module docstring.) -/
def Closed (C : Cospan X Y) : Prop :=
  (∀ v : C.mid.cells 0, IsMinimalVertex C.mid v → srcImage C ⟨0, v⟩) ∧
    (∀ v : C.mid.cells 0, IsMaximalVertex C.mid v → sinkImage C ⟨0, v⟩)

/-- **The `Spanning` flag.**  A cobordism is *spanning* when every cell lies on a
dipath from the source to the sink: each `z` is reached from some source-image cell
and reaches some sink-image cell. -/
def Spanning (C : Cospan X Y) : Prop :=
  ∀ z : C.mid.TotalCell,
    (∃ a, srcImage C a ∧ Reaches C.mid a z) ∧
      (∃ b, sinkImage C b ∧ Reaches C.mid z b)

/-- **The (loop-)confinement flag** is *not a new definition*: it is precisely
`Precubical.Cobordism.LoopConfined C.mid (srcImage C) (sinkImage C)` (from
`Cobordisms/Loops.lean`) — every nontrivial directed loop of `C.mid` lies wholly
in the source image or wholly in the sink image.  We record it as an abbreviation
so the three flags read uniformly. -/
abbrev Confined (C : Cospan X Y) : Prop :=
  LoopConfined C.mid (srcImage C) (sinkImage C)

end Cospan

/-! ### The empty precubical set -/

/-- The **empty precubical set** `∅`: the constant `PEmpty`-valued presheaf, a
concrete initial object of `PrecubicalSet`.  Chosen over the abstract
`Limits.initial` so that `IsEmpty (∅.cells n)` is definitional. -/
def emptyPsh : PrecubicalSet := (Functor.const Boxᵒᵖ).obj PEmpty

@[inherit_doc] notation "∅ₚ" => emptyPsh

/-- Every cell type of the empty precubical set is empty (definitionally `PEmpty`). -/
instance instEmptyCellsEmptyPsh (n : ℕ) : IsEmpty (emptyPsh.cells n) :=
  inferInstanceAs (IsEmpty PEmpty)

/-! ### M6(a): no closed cobordism out of `∅` -/

namespace Cospan

/-- The source image of a cospan **out of `∅`** is empty: there is no cell of `∅`
to land in it. -/
theorem emptySource_srcImage_eq_bot (C : Cospan emptyPsh X) (z : C.mid.TotalCell) :
    ¬ srcImage C z := by
  rintro ⟨x, _⟩
  exact (instEmptyCellsEmptyPsh x.1).false x.2

/-- **M6(a) — the `∅`-bottom theorem (explicit-hypothesis form).**  There is no
`Closed` cobordism out of the empty precubical set, *as soon as `C.mid` has a
minimal vertex*.

`Closed` forces every minimal vertex into the source image, but the source image of
a cospan out of `∅` is empty (`emptySource_srcImage_eq_bot`); a single minimal
vertex therefore yields a contradiction.

The minimal-vertex hypothesis is carried explicitly here; it is discharged from
finiteness + loop-freeness by `exists_minimalVertex_of_finite_loopFree`, giving the
self-contained `no_closed_cobordism_from_empty'` below. -/
theorem no_closed_cobordism_from_empty (C : Cospan emptyPsh X) (hC : C.Closed)
    (hmin : ∃ v : C.mid.cells 0, IsMinimalVertex C.mid v) : False := by
  obtain ⟨v, hv⟩ := hmin
  exact emptySource_srcImage_eq_bot C _ (hC.1 v hv)

end Cospan

/-! ### Discharging the minimal-vertex hypothesis

A nonempty *finite* and *loop-free* precubical set has a minimal vertex.  Over the
finite vertex set `W.cells 0`, vertex-reachability `VertexReaches W` is a transitive
relation, so `Set.Finite.exists_minimal` produces a vertex `m` minimal for it; loop-
freeness upgrades "minimal among vertices" to the full `IsMinimalVertex` (which
quantifies over *all* total cells), because any total cell reaching `⟨0, m⟩` has a
source vertex `vertex₀` that vertex-reaches `m` and hence equals `m`. -/

/-- A nonempty, finite, loop-free precubical set has a **minimal vertex**.

This discharges the explicit hypothesis of `Cospan.no_closed_cobordism_from_empty`.
Hypotheses: a chosen vertex `v₀` (nonemptiness of `W.cells 0`), `Finite (W.cells 0)`,
and `IsLoopFree W`. -/
theorem exists_minimalVertex_of_finite_loopFree (W : PrecubicalSet)
    [Finite (W.cells 0)] (v₀ : W.cells 0)
    (hlf : Precubical.Cobordism.IsLoopFree W) :
    ∃ v : W.cells 0, IsMinimalVertex W v := by
  -- A local `≤` on vertices given by vertex-reachability; it is transitive, so
  -- `Set.Finite.exists_minimal` applies on the finite (`univ`) vertex set.
  letI : LE (W.cells 0) := ⟨fun a b => VertexReaches W a b⟩
  haveI : IsTrans (W.cells 0) (· ≤ ·) :=
    ⟨fun _ _ _ hab hbc =>
      Reaches.trans (hab : VertexReaches W _ _) (hbc : VertexReaches W _ _)⟩
  obtain ⟨m, _, hmmin⟩ :=
    (Set.finite_univ (α := W.cells 0)).exists_minimal ⟨v₀, Set.mem_univ v₀⟩
  -- `hmmin : ∀ j ∈ univ, j ≤ m → m ≤ j`, i.e. `VertexReaches W j m → VertexReaches W m j`.
  refine ⟨m, ?_⟩
  intro u hu
  -- The source vertex of `u` vertex-reaches `m`.
  obtain ⟨k, c⟩ := u
  have hvr : VertexReaches W (W.vertex₀ c) m :=
    (reaches_vertex₀ c).trans hu
  -- Minimality gives `m ≤ vertex₀ c`, i.e. `VertexReaches W m (vertex₀ c)`;
  -- with `hvr` this is a directed loop among vertices, so loop-freeness collapses
  -- it to `vertex₀ c = m`.
  have hback : VertexReaches W m (W.vertex₀ c) :=
    hmmin (Set.mem_univ _) hvr
  have hmv : (⟨0, m⟩ : W.TotalCell) = ⟨0, W.vertex₀ c⟩ :=
    hlf _ _ ⟨hback, hvr⟩
  -- `⟨0, m⟩` reaches `⟨k, c⟩` (through `vertex₀ c = m`), and `⟨k, c⟩` reaches
  -- `⟨0, m⟩` by assumption: a directed loop, collapsed by loop-freeness.
  have hfwd : Reaches W ⟨0, m⟩ ⟨k, c⟩ := by
    rw [hmv]; exact reaches_vertex₀ c
  exact hlf _ _ ⟨hu, hfwd⟩

/-- **M6(a) (self-contained form).**  No `Closed` cobordism out of `∅` exists, given
that `C.mid` is finite (on vertices) and loop-free with at least one vertex. -/
theorem Cospan.no_closed_cobordism_from_empty' (C : Cospan emptyPsh X)
    [Finite (C.mid.cells 0)] (v₀ : C.mid.cells 0)
    (hlf : Precubical.Cobordism.IsLoopFree C.mid) (hC : C.Closed) : False :=
  C.no_closed_cobordism_from_empty hC
    (exists_minimalVertex_of_finite_loopFree C.mid v₀ hlf)

end PrecubicalSet
