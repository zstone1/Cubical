import CubeChains.Cobordisms.Flags
import CubeChains.Cobordisms.Collar

/-!
# Cobordisms/Cobordism — the directed-cobordism object + identity = cylinder (M4a)

This file **bundles** the cobordism backbone into a single object, the *directed
cobordism* `X ⇒ Y`, and exhibits the cylinder as its identity.

A `DirectedCobordism X Y` carries:

* the **cospan** `X ⟶ mid ⟵ Y` with both legs monic (condition **C1**, inherited
  from `Cospan`), together with **leg-disjointness** (`LegsDisjoint`, also C1);
* the **source sieve** `SrcSieve` (condition **C2**): the source image is
  past-closed;
* the **sink cosieve** `SinkCosieve` (condition **C3**): the sink image is
  future-closed;
* the two **collars** `SourceCollar`/`SinkCollar` (condition **C4**): each boundary
  leg is thickened to a monic cylinder neighbourhood whose appropriate end recovers
  the leg.

**Flags are tracked separately.**  The directedness/coverage *flags*
`Cospan.Closed` / `Cospan.Spanning` / `Cospan.Confined` are *not* fields of the
bundle — M6(a) (`Flags.lean`) shows the bare conditions C1–C4 are already satisfied
by the cylinder `∅ ⇒ X`, so the flags only carry information when imposed
selectively.  We expose them as thin abbreviations on `DirectedCobordism` (via
`.toCospan`) for ergonomics, but they remain *predicates*, not data.

**The identity cobordism is the cylinder.**  `idCob X : X ⇒ X` has underlying cospan
the cylinder cospan `cylCospan X` (apex `Cyl X`, legs the two ends); its sieve /
cosieve are exactly `Cylinder.cylEnd_false_isSieve` / `cylEnd_true_isCosieve`, and
its collars are the canonical cylinder collars.  This is the unit of the (still to
come) pushout-composition of cobordisms.

**Next file:** the pushout-composition *closure* — that C1–C4 are preserved under
the cospan composition `Cospan.comp`, making `DirectedCobordism` the morphisms of a
category with `idCob` as identity.

**Layer:** Cobordisms.  **Imports:** `Cobordisms.Flags` (cospan + flags + the
sieve/cosieve conditions), `Cobordisms.Collar` (collars + the cylinder cospan +
canonical collars).
-/

set_option relaxedAutoImplicit false

open CategoryTheory

namespace PrecubicalSet

open Cylinder

variable {X Y : PrecubicalSet}

/-! ### The directed-cobordism bundle -/

/-- A **directed cobordism** `X ⇒ Y`: the full boundary datum of a directed
cobordism from `X` to `Y`.  It extends the bare cospan `X ⟶ mid ⟵ Y` (C1: legs
mono, inherited) with:

* `legsDisjoint` — the leg images never meet (C1);
* `srcSieve` — the source image is past-closed (C2);
* `sinkCosieve` — the sink image is future-closed (C3);
* `srcCollar` / `sinkCollar` — the source/sink legs are collared (C4).

The *flags* `Closed` / `Spanning` / `Confined` are **not** carried here; they are
separate predicates (see `DirectedCobordism.Closed` etc. below). -/
structure DirectedCobordism (X Y : PrecubicalSet) extends Cospan X Y where
  /-- C1: the two legs have disjoint images. -/
  legsDisjoint : toCospan.LegsDisjoint
  /-- C2: the source image is a sieve (past-closed). -/
  srcSieve : toCospan.SrcSieve
  /-- C3: the sink image is a cosieve (future-closed). -/
  sinkCosieve : toCospan.SinkCosieve
  /-- C4: the source leg is collared. -/
  srcCollar : SourceCollar toCospan.inl
  /-- C4: the sink leg is collared. -/
  sinkCollar : SinkCollar toCospan.inr

@[inherit_doc] infixr:25 " ⇒c " => DirectedCobordism

namespace DirectedCobordism

/-! ### Accessors

`extends Cospan X Y` already exposes the cospan projections `W.mid`, `W.inl`, `W.inr`
on a `DirectedCobordism W` (inherited through `toCospan`), so no extra accessors are
needed for them.

### Flags (predicates, not fields)

The directedness/coverage flags live on the underlying cospan; we lift them through
`.toCospan` so a `DirectedCobordism` reads them uniformly.  They stay *predicates*:
imposing them is a separate hypothesis, never part of the bundle. -/

/-- The `Closed` flag of a directed cobordism (lifted from the underlying cospan):
every minimal vertex lies in the source image and every maximal vertex in the sink
image. -/
abbrev Closed (W : DirectedCobordism X Y) : Prop := W.toCospan.Closed

/-- The `Spanning` flag of a directed cobordism (lifted from the underlying cospan):
every cell lies on a dipath from source to sink. -/
abbrev Spanning (W : DirectedCobordism X Y) : Prop := W.toCospan.Spanning

/-- The (loop-)`Confined` flag of a directed cobordism (lifted from the underlying
cospan): every nontrivial directed loop lies wholly in the source or wholly in the
sink image. -/
abbrev Confined (W : DirectedCobordism X Y) : Prop := W.toCospan.Confined

end DirectedCobordism

/-! ### The identity cobordism = the cylinder

The unit of cobordism composition.  Its backbone is the cylinder cospan
`cylCospan X` (apex `Cyl X`, legs the two ends `cylEnd false/true X`), and every
field is supplied by the cylinder's own structure:

* `legsDisjoint` — `cylCospan_legsDisjoint X`;
* `srcSieve` / `sinkCosieve` — the cylinder's directed-boundary theorems
  `Cylinder.cylEnd_false_isSieve X` / `cylEnd_true_isCosieve X` (these match the
  required `SrcSieve` / `SinkCosieve` *definitionally*, because
  `(cylCospan X).inl = cylEnd false X` and `(cylCospan X).mid = Cyl.obj X` are `rfl`,
  so `srcImage (cylCospan X)` reduces to the predicate
  `fun z => ∃ c, mapCell (cylEnd false X) c = z`);
* `srcCollar` / `sinkCollar` — the canonical cylinder collars `cylSourceCollar X` /
  `cylSinkCollar X` (their legs are `cylEnd false/true X`, which are
  `(cylCospan X).inl/inr` by `rfl`). -/

/-- **The identity cobordism `idCob X : X ⇒ X` is the cylinder.**  Its underlying
cospan is `cylCospan X`; the directedness conditions are the cylinder's own
sieve/cosieve theorems, and the collars are the canonical cylinder collars.  This is
the unit of cobordism composition. -/
noncomputable def idCob (X : PrecubicalSet) : DirectedCobordism X X where
  toCospan := cylCospan X
  legsDisjoint := cylCospan_legsDisjoint X
  srcSieve := Cylinder.cylEnd_false_isSieve X
  sinkCosieve := Cylinder.cylEnd_true_isCosieve X
  srcCollar := cylSourceCollar X
  sinkCollar := cylSinkCollar X

@[simp] theorem idCob_toCospan (X : PrecubicalSet) :
    (idCob X).toCospan = cylCospan X := rfl

@[simp] theorem idCob_mid (X : PrecubicalSet) : (idCob X).mid = Cyl.obj X := rfl

@[simp] theorem idCob_inl (X : PrecubicalSet) : (idCob X).inl = cylEnd false X := rfl

@[simp] theorem idCob_inr (X : PrecubicalSet) : (idCob X).inr = cylEnd true X := rfl

@[simp] theorem idCob_srcCollar (X : PrecubicalSet) :
    (idCob X).srcCollar = cylSourceCollar X := rfl

@[simp] theorem idCob_sinkCollar (X : PrecubicalSet) :
    (idCob X).sinkCollar = cylSinkCollar X := rfl

end PrecubicalSet
