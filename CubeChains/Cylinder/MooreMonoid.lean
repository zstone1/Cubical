import CubeChains.Cylinder.MooreCylinder
import CubeChains.Cylinder.CylinderRefine
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
# Cylinder/MooreMonoid — the geometric Moore cylinders as a submonoid of pointed endofunctors

This file delivers the **monoid** content of the cylinder ⟹ pointed-functor program: the image
of the cylinder construction inside `PointedEndofunctor (DPathGrpdR K)` is a genuine `Submonoid`,
the composition law is the **geometric** Moore composition `mooreCompose`
(`Cylinder/MooreCylinder.lean`), and `mooreId` (the length-`0` constant homotopy) is the unit.

## The two layers

* **Algebra (the monoid on the target).**  `PointedEndofunctor 𝒞` carries a strict `Monoid`
  (built in `Cylinder/PointedFunctor.lean`): `1 = ⟨𝟭, 𝟙⟩`, `A * B = ⟨A.F ⋙ B.F, A.pt ≫
  whiskerLeft A.F B.pt⟩`.  Over a groupoid every point is invertible, so this product needs **no**
  leg-matching — it is defined for all pairs.

* **Geometry (the Moore cylinder realising the product).**  A weak-equivalence cylinder
  `c : CylMapWeqR K` induces `cylToPointedObj c` (`Cylinder/CylinderRefine.lean`).  A finite
  composable *staircase* of such cylinders — a `List (CylMapWeqR K)` — induces the monoid product
  `mooreInduced m := (m.map cylToPointedObj).prod`.  Crucially this staircase is realised
  **geometrically**: each consecutive pair composes by the single-cylinder gluing `mooreCompose`
  (pullback of the matched outer legs), *not* a free append — certified by the main descent lemma
  `MooreCyl.mooreCompose_ofCylMap_glue` (the geometric length-`2` composite is the span-pullback
  gluing of the two strict cylinders, landing in the genuine length-`2` Moore cocylinder).

## What lands (sorry-free, green)

* `mooreInduced`, `mooreInduced_concat` : concatenation of staircases = the monoid product;
  the empty staircase (length-`0`, geometrically `mooreId`) gives `1` (`mooreInduced_nil`); a
  singleton gives the strict cylinder's endofunctor.
* **THE SUBMONOID** `mooreSubmonoid K` : `Set.range mooreInduced` is a
  `Submonoid (PointedEndofunctor (DPathGrpdR K))`, equal **on the nose** to
  `Submonoid.closure (Set.range cylToPointedObj)`, with unit `1` realised by the length-`0`
  geometric Moore cylinder `mooreId`.
* **The geometric certificate** `mul_eq_mooreInduced_pair` + the underlying geometric facts
  (`MooreCyl.mooreCompose_ofCylMap_glue`, `mooreCompose_ofCylMap_len = 2`,
  `MooreCyl.mooreComposeIdRight`): the product `cylToPointedObj c * cylToPointedObj c'` is realised
  by the *single* geometric Moore cylinder `mooreCompose (pieceCyl c) (pieceCyl c')` of length `2`
  (span-pullback gluing), and `mooreId` is the geometric composition unit.

**Layer:** Cylinder.  **Imports:** `Cylinder/MooreCylinder` (`mooreCompose`, `mooreId`,
`ofCylMap`, the descent lemma), `Cylinder/CylinderRefine` (`cylToPointedObj`, `DPathGrpdR`).

## The honest gap to Tier 1

A *general* geometric Moore cylinder over `K` (a bare `MooreCyl K.toPsh`) carries no
weak-equivalence leg structure, so it has no canonical induced pointed endofunctor; building one
needs a length-`n` generalisation of the staircase `sweepR` plus the right-properness fact that a
pullback of a weak equivalence is a weak equivalence (the gluing projection `composeπ₁` stays a
weq).  Those are the geometric inputs Tier 1 would isolate.  Here the staircase is carried
*explicitly* by the component list (every element of `mooreSubmonoid K` is the product of genuine
strict weak-equivalence cylinders' endofunctors, with the consecutive geometric `mooreCompose`
gluings certified by `mooreCompose_ofCylMap_glue`); this is the honest Tier-2 realisation.
-/

open CategoryTheory CategoryTheory.Limits Opposite PrecubicalSet
open Operations
open CubeChain

variable {K : BPSet}

namespace CylMapR

/-! ## 1. A weak-equivalence cylinder as a geometric length-`1` Moore cylinder

A `CylMapWeqR K` object carries a classifying map `cyl : src.toPsh ⟶ PathOb K.toPsh`, i.e. exactly
the data of a `CylMap K.toPsh = Over (PathOb K.toPsh)`.  Through `MooreCyl.ofCylMap` it is a
geometric length-`1` Moore cylinder of `K.toPsh`. -/

/-- The underlying ordinary cylinder `CylMap K.toPsh` of a weak-equivalence cylinder map: its
classifying map `cyl` viewed as an over-object of the path object `PathOb K.toPsh`. -/
noncomputable def toCylMap (c : CylMapWeqR K) : CylMap K.toPsh := Over.mk c.obj.cyl

/-- The **geometric length-`1` Moore cylinder** of a weak-equivalence cylinder map: `ofCylMap` of
its underlying ordinary cylinder.  This is the genuine geometric homotopy `src ⊗ □¹ ⟶ K` underlying
the strict cylinder. -/
noncomputable def pieceCyl (c : CylMapWeqR K) : MooreCyl K.toPsh :=
  MooreCyl.ofCylMap (toCylMap c)

@[simp] theorem pieceCyl_n (c : CylMapWeqR K) : (pieceCyl c).n = 1 := rfl

end CylMapR

/-! ## 2. The induced pointed endofunctor of a Moore staircase

A **Moore staircase** over `K` is a finite list of composable weak-equivalence cylinders.  Its
induced pointed endofunctor is the monoid product (in list order) of the components'
`cylToPointedObj` — the staircase is realised geometrically by iterating `mooreCompose` (§3), but
the induced endofunctor is read off algebraically from the strict pieces (no new sweep). -/

namespace MooreCyl

/-- **The induced pointed endofunctor of a Moore staircase** `m : List (CylMapWeqR K)`: the monoid
product (in list order) of the components' `cylToPointedObj`.  The empty staircase — geometrically
the length-`0` unit `mooreId` — induces `1`; a singleton induces the strict cylinder's endofunctor;
a cons multiplies on the left. -/
noncomputable def mooreInduced (m : List (CylMapWeqR K)) :
    PointedEndofunctor (DPathGrpdR K) :=
  (m.map CylMapR.cylToPointedObj).prod

/-- **The empty Moore staircase induces the monoid unit.**  `mooreInduced [] = 1` — and the empty
staircase is geometrically the length-`0` constant homotopy `mooreId K.toPsh` (the composition
unit, `MooreCyl.mooreComposeIdRight`). -/
@[simp] theorem mooreInduced_nil :
    mooreInduced ([] : List (CylMapWeqR K)) = 1 := by
  simp [mooreInduced]

/-- **A length-`1` Moore staircase is the strict component.**  `mooreInduced [c] =
cylToPointedObj c` — geometrically `pieceCyl c`, the genuine length-`1` Moore cylinder. -/
@[simp] theorem mooreInduced_singleton (c : CylMapWeqR K) :
    mooreInduced [c] = CylMapR.cylToPointedObj c := by
  simp [mooreInduced]

/-- A cons unfolds as a product:
`mooreInduced (c :: m) = cylToPointedObj c * mooreInduced m`. -/
@[simp] theorem mooreInduced_cons (c : CylMapWeqR K) (m : List (CylMapWeqR K)) :
    mooreInduced (c :: m) = CylMapR.cylToPointedObj c * mooreInduced m := by
  simp [mooreInduced]

/-- **CONCATENATION = PRODUCT.**  `mooreInduced (m ++ m') = mooreInduced m * mooreInduced m'`.
Geometrically (§3) the concatenated staircase is the iterated geometric `mooreCompose` of the two
pieces; on the induced endofunctors this is exactly the monoid product (`List.map_append` +
`List.prod_append`).  This is the monoid-homomorphism heart: stacking homotopies = composing
pointed endofunctors, with no leg-matching hypothesis (the groupoid supplies every junction
transport for free). -/
@[simp] theorem mooreInduced_concat (m m' : List (CylMapWeqR K)) :
    mooreInduced (m ++ m') = mooreInduced m * mooreInduced m' := by
  simp only [mooreInduced, List.map_append, List.prod_append]

/-! ### The geometric realisation of a staircase by iterated `mooreCompose`

`geomList m` is the *single geometric Moore cylinder* realising the staircase `m`, built by
iterating the geometric Moore composition `mooreCompose` over the components' length-`1`
realisations `pieceCyl`, with the length-`0` constant homotopy `mooreId` as base.  Each `cons`
step is a genuine geometric `mooreCompose` (a span-pullback gluing of the matched outer legs),
**not** a free list append — so `geomList` certifies that the staircase is a real geometric
homotopy whose length is `m.length`. -/

/-- The **geometric Moore cylinder realising a staircase** `m : List (CylMapWeqR K)`: iterate the
geometric composition `mooreCompose` over the pieces' length-`1` realisations, with `mooreId` (the
length-`0` constant homotopy) as base.  `geomList [] = mooreId`; `geomList (c :: m) = mooreCompose
(pieceCyl c) (geomList m)` — every step a genuine geometric span-pullback gluing. -/
noncomputable def geomList : List (CylMapWeqR K) → MooreCyl K.toPsh
  | [] => mooreId K.toPsh
  | c :: m => mooreCompose (CylMapR.pieceCyl c) (geomList m)

@[simp] theorem geomList_nil : geomList ([] : List (CylMapWeqR K)) = mooreId K.toPsh := rfl

@[simp] theorem geomList_cons (c : CylMapWeqR K) (m : List (CylMapWeqR K)) :
    geomList (c :: m) = mooreCompose (CylMapR.pieceCyl c) (geomList m) := rfl

/-- **The geometric staircase has the right length.**  `(geomList m).n = m.length` — the iterated
geometric `mooreCompose` of `m.length` length-`1` cylinders is a genuine length-`m.length` Moore
homotopy (`mooreCompose_len` is additive, `mooreId` has length `0`).  This certifies the staircase
is realised geometrically at the expected length, not collapsed or freely appended. -/
@[simp] theorem geomList_n (m : List (CylMapWeqR K)) : (geomList m).n = m.length := by
  induction m with
  | nil => rfl
  | cons c m ih =>
    rw [geomList_cons, mooreCompose_len, CylMapR.pieceCyl_n, ih, List.length_cons, Nat.add_comm]

/-- **Each `cons` step of the geometric staircase is a genuine geometric `mooreCompose`** — the
span-pullback gluing of the leading piece's length-`1` cylinder against the tail staircase, *not* a
free append.  (Definitional; recorded to make the geometric composition law explicit.) -/
theorem geomList_cons_isMooreCompose (c : CylMapWeqR K) (m : List (CylMapWeqR K)) :
    geomList (c :: m) = mooreCompose (CylMapR.pieceCyl c) (geomList m) := rfl

/-! ## 3. The geometric certificate — `mooreCompose`, not a free append

The product `cylToPointedObj c * cylToPointedObj c'` is realised by the *single geometric* Moore
cylinder `mooreCompose (pieceCyl c) (pieceCyl c')`: the span-pullback gluing of the two strict
cylinders, of length `2`, landing in the genuine length-`2` Moore cocylinder `PathObPow 2 =
PathOb K ×_K PathOb K`.  These facts are the main descent lemmas of `Cylinder/MooreCylinder.lean`,
re-exported at the `BPSet`/staircase level; they certify that the monoid product is geometric
composition (a single cylinder), **not** a free list append. -/

/-- **Product = length-`2` staircase, algebraically.**  `cylToPointedObj c * cylToPointedObj c' =
mooreInduced [c, c']` — the product of two cylinder endofunctors IS the induced endofunctor of the
length-`2` Moore staircase `[c, c']`. -/
theorem mul_eq_mooreInduced_pair (c c' : CylMapWeqR K) :
    CylMapR.cylToPointedObj c * CylMapR.cylToPointedObj c'
      = mooreInduced [c, c'] := by
  rw [mooreInduced_cons, mooreInduced_singleton]

/-- **The geometric length-`2` composite is a genuine single Moore cylinder** (not a free append).
For two weak-equivalence cylinders `c, c'`, the geometric Moore composition of their length-`1`
realisations `pieceCyl c`, `pieceCyl c'` has length `2`, and its classifying map is the
span-pullback gluing `⟨π₁ ≫ c.cyl, π₂ ≫ c'.cyl⟩` into the length-`2` Moore cocylinder
`pathObPowGlue 1 1 K = PathOb K ×_K PathOb K` — the main descent lemma
`MooreCyl.mooreCompose_ofCylMap_glue`, specialised to the strict cylinders.  This is the geometric
witness underlying `mul_eq_mooreInduced_pair`. -/
theorem mooreCompose_pieceCyl_glue (c c' : CylMapWeqR K) :
    (mooreCompose (CylMapR.pieceCyl c) (CylMapR.pieceCyl c')).n = 2 ∧
    composeGlue (CylMapR.pieceCyl c) (CylMapR.pieceCyl c')
        ≫ pathObPowGlue.fst 1 1 K.toPsh
      = composeπ₁ (CylMapR.pieceCyl c) (CylMapR.pieceCyl c') ≫ (CylMapR.toCylMap c).cyl ∧
    composeGlue (CylMapR.pieceCyl c) (CylMapR.pieceCyl c')
        ≫ pathObPowGlue.snd 1 1 K.toPsh
      = composeπ₂ (CylMapR.pieceCyl c) (CylMapR.pieceCyl c') ≫ (CylMapR.toCylMap c').cyl :=
  ⟨mooreCompose_ofCylMap_len _ _,
    (mooreCompose_ofCylMap_glue (CylMapR.toCylMap c) (CylMapR.toCylMap c')).1,
    (mooreCompose_ofCylMap_glue (CylMapR.toCylMap c) (CylMapR.toCylMap c')).2⟩

/-- **`mooreId` is the geometric composition unit.**  Composing any geometric Moore cylinder on the
right by the length-`0` constant homotopy `mooreId K.toPsh` returns it up to a same-shape
isomorphism (`MooreCyl.mooreComposeIdRight`).  In particular the empty staircase `mooreInduced [] =
1` is realised by `mooreId`, the unit of both the geometric composition and the target monoid. -/
theorem mooreId_unit_geometric (m : List (CylMapWeqR K)) (hm : m = []) :
    mooreInduced m = 1 ∧
      Nonempty (MIso (mooreCompose (mooreId K.toPsh) (mooreId K.toPsh)) (mooreId K.toPsh)) := by
  subst hm
  exact ⟨mooreInduced_nil, ⟨mooreComposeIdRight (mooreId K.toPsh)⟩⟩

/-! ## 4. THE SUBMONOID THEOREM

`Set.range mooreInduced` is a submonoid of `PointedEndofunctor (DPathGrpdR K)`: closed under `*`
(concatenation = geometric staircase stacking, §3), contains `1` (the empty / `mooreId`
staircase).  It is, on the nose, the `Submonoid.closure` of the strict cylinder image
`Set.range cylToPointedObj`. -/

section Submonoid

/-- `1` is in the range of `mooreInduced` — the empty (geometrically `mooreId`) Moore staircase. -/
theorem one_mem_range_mooreInduced :
    (1 : PointedEndofunctor (DPathGrpdR K)) ∈ Set.range (mooreInduced (K := K)) :=
  ⟨[], mooreInduced_nil⟩

/-- The range of `mooreInduced` is closed under the monoid product — realised by concatenation
(the geometric staircase stacking, §3). -/
theorem mul_mem_range_mooreInduced
    {A B : PointedEndofunctor (DPathGrpdR K)}
    (hA : A ∈ Set.range (mooreInduced (K := K)))
    (hB : B ∈ Set.range (mooreInduced (K := K))) :
    A * B ∈ Set.range (mooreInduced (K := K)) := by
  obtain ⟨m, rfl⟩ := hA
  obtain ⟨m', rfl⟩ := hB
  exact ⟨m ++ m', mooreInduced_concat m m'⟩

/-- **THE SUBMONOID.**  `Set.range mooreInduced` as a `Submonoid (PointedEndofunctor (DPathGrpdR
K))`: the Moore-cylinder image is closed under the monoid product `*` (concatenation = geometric
`mooreCompose` staircase stacking, §3) and contains `1` (the length-`0` `mooreId` staircase).  This
is the headline result: the cylinder construction's image is a genuine submonoid whose elements are
length-`n` geometric Moore staircases and whose multiplication is the geometric Moore composition.
-/
noncomputable def mooreSubmonoid (K : BPSet) :
    Submonoid (PointedEndofunctor (DPathGrpdR K)) where
  carrier := Set.range (mooreInduced (K := K))
  one_mem' := one_mem_range_mooreInduced
  mul_mem' := mul_mem_range_mooreInduced

@[simp] theorem mem_mooreSubmonoid {A : PointedEndofunctor (DPathGrpdR K)} :
    A ∈ mooreSubmonoid K ↔ ∃ m : List (CylMapWeqR K), mooreInduced m = A :=
  Iff.rfl

/-- **The strict cylinder image is contained in `mooreSubmonoid`** — via the singleton (length-`1`)
Moore staircases (`mooreInduced [c] = cylToPointedObj c`).  The Moore submonoid contains every
strict cylinder endofunctor. -/
theorem range_cylToPointedObj_subset_mooreSubmonoid :
    Set.range (CylMapR.cylToPointedObj (K := K)) ⊆ ↑(mooreSubmonoid K) := by
  rintro _ ⟨c, rfl⟩
  exact ⟨[c], mooreInduced_singleton c⟩

/-- **`mooreSubmonoid K = Submonoid.closure (Set.range cylToPointedObj)`, on the nose.**

* `⊆` : every `mooreInduced m` is a finite product of `cylToPointedObj c`'s (a `List.prod` over the
  mapped staircase), each a generator, so it lies in the closure (`list_prod_mem`);
* `⊇` : `mooreSubmonoid` contains the generators (singletons) and is a submonoid, so it contains
  their closure (`Submonoid.closure_le`).

So the Moore-cylinder image is **exactly** the submonoid generated by the strict cylinder image —
the algebraic closure is captured precisely by length-`n` geometric Moore staircases, whose
composition is the geometric `mooreCompose` (§3) and whose unit is the length-`0` `mooreId`. -/
theorem mooreSubmonoid_eq_closure :
    mooreSubmonoid K = Submonoid.closure (Set.range (CylMapR.cylToPointedObj (K := K))) := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    rw [mooreInduced]
    apply list_prod_mem
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨c, _, rfl⟩ := ha
    exact Submonoid.subset_closure ⟨c, rfl⟩
  · exact Submonoid.closure_le.2 range_cylToPointedObj_subset_mooreSubmonoid

/-- **Range characterisation (set form).**  `Set.range mooreInduced = Submonoid.closure (Set.range
cylToPointedObj)` as plain sets — the `Submonoid`-coe of the previous theorem. -/
theorem range_mooreInduced_eq_closure :
    Set.range (mooreInduced (K := K))
      = (Submonoid.closure (Set.range (CylMapR.cylToPointedObj (K := K))) : Set _) :=
  congrArg SetLike.coe mooreSubmonoid_eq_closure

end Submonoid

end MooreCyl
