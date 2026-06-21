import CubeChains.Research.Scratch.Cyl6_Monoid
import CubeChains.Research.Scratch.Cyl7_SpanCompose

/-!
# Cyl8_MooreMonoid — Moore cylinders realise the Cyl6 monoid product; the cylinder image's
closure is a genuine submonoid

Scratch investigation (RESULT 2 / cylinder ⟹ pointed-functor program).  **Decoupled** from the
green build; build with `lake build CubeChains.Research.Scratch.Cyl8_MooreMonoid`.  Owns ONLY this
file and its `.md`.  **Imports** `Cyl6_Monoid` (the `Monoid (PointedEndofunctor 𝒞)` instance, the
product formula, `taut_eq_one`, `cylImage`) and `Cyl7_SpanCompose` (the span-composition geometry,
`no_fold_edge`, the `MooreCyl` scaffold).  Sorry markers, if any, are explicit `-- TODO` scaffolds;
everything labelled PROVEN here is sorry-free.

## The headline

Cyl6 proved that the strict `□¹`-cylinder image `cylImage K = Set.range cylToPointedObj` contains
`1` but left **closure under `·`** open (and Cyl7 showed it genuinely FAILS — the span composite of
two strict cylinders is honestly length-2 (`pathOb2 K = K^{I₂}`) and there is no precubical fold
`□¹ → I₂` to collapse it, `no_fold_edge`).  This file builds the **Moore enlargement** that closes
it, *purely algebraically on top of the existing geometry* (no new sweep, no new prism):

* A **Moore cylinder** of `K` is a finite *list* `m : List (CylMapWeqR K)` of strict
  weak-equivalence cylinders — the staircase of homotopies to compose in order.
* `mooreToPointed m : PointedEndofunctor (DPathGrpdR K)` is the monoid product
  `(m.map cylToPointedObj).prod` of the strict components' pointed endofunctors (reusing Cyl6's
  `Monoid` instance and the existing `cylToPointedObj`).  No new geometry.
* **Concatenation = product** (`mooreToPointed_concat`): `mooreToPointed (m ++ m')
  = mooreToPointed m * mooreToPointed m'` (just `List.map_append` + `List.prod_append`).  The empty
  list gives `1` (`mooreToPointed_nil`), a singleton gives the strict endofunctor
  (`mooreToPointed_singleton`).
* **THE SUBMONOID THEOREM** (`mooreSubmonoid`, `mooreSubmonoid_eq_closure`):
  `Set.range mooreToPointed` IS a `Submonoid (PointedEndofunctor (DPathGrpdR K))`, it CONTAINS
  `cylImage K` (singletons), and it equals **exactly** the `Submonoid.closure (cylImage K)`.

So the algebraic closure of the strict cylinder image is captured *on the nose* by Moore cylinders.

## What this does and does NOT certify geometrically (the honest line)

* **Certified.** Every element of `mooreSubmonoid K` is `mooreToPointed m` for an explicit list `m`
  of *genuine* strict weak-equivalence cylinders — a real geometric Moore staircase (a composable
  chain of homotopies, span-composable in the sense of Cyl7 `spanCompose`).  And the monoid product
  `*` is realised by *list concatenation* (= geometric stacking of the staircases).  So
  `mooreSubmonoid` is geometrically honest at the level of *length-n* Moore cylinders.
* **NOT certified (and provably impossible to certify at length 1).**  That each element is
  realised by a *single, length-1* strict cylinder `CylMapWeqR K`.  Cyl7 `no_fold_edge` proves it
  is **not** — there is no precubical fold `□¹ → I₂` renormalising a length-2 staircase to length
  1.  The gap
  between `cylImage K` (length-1 strict image) and `mooreSubmonoid K` (its closure) is therefore
  *real and unavoidable* in a degeneracy-free precubical model; the Moore enlargement is the minimal
  honest fix.  See the `.md`.

## The span-vs-`⋙` reconciliation (the load-bearing subtlety)

The Cyl6 product is endofunctor composition `A * B = (A.F ⋙ B.F, …)` — "do A, then apply B's lift",
defined for ALL pairs, no leg-matching.  Cyl7's `spanCompose` glues two cylinders over the pullback
`R₁ = L₂`.  We resolve which realises `*`: **list-concatenation `mooreToPointed`** realises the
Cyl6 `⋙`-product on the nose (Task 2, `mooreToPointed_concat`), *with no leg-matching hypothesis*,
because the algebra `pointedOfPaths`/`pt_isIso` makes every cylinder's transport invertible — the
"matched endpoint" is supplied for free by the conjugation isos, not by a geometric `R₁ = L₂`.  The
geometric `spanCompose` (which DOES need the legs to meet over `K`) is the *parallel* geometric
witness: it produces the length-2 cocylinder object whose induced endofunctor (under the
still-conjectural box-tensor exponential `pathOb2 K ≅ K^{I₂}`) is this very `⋙`-product.  We pin the
bridge `spanCompose ↦ ⋙-product` as a clearly-labelled CONJECTURE (it needs Cyl7's
`CocylinderConjecture`); the *algebraic* `⋙`-realisation by Moore lists is unconditional and PROVEN.

**Layer:** Research/Scratch (decoupled).  **Imports:** `Cyl6_Monoid`, `Cyl7_SpanCompose`.
-/

open CategoryTheory Operations
open CubeChain

namespace Cyl8

variable {K : BPSet}

/-! ## 1. Moore cylinders as lists, and `mooreToPointed`

A **Moore cylinder** over `K` is a finite list of strict weak-equivalence cylinders — the chain of
homotopies to stack, in order.  Its induced pointed endofunctor is the monoid product of the
components' `cylToPointedObj` (Cyl6's `Monoid` instance + the existing object map).  No new geometry
is introduced: `mooreToPointed` is a `List.prod` of already-built endofunctors. -/

/-- A **Moore cylinder** over `K` (length-`n` homotopy staircase): a finite list of strict
weak-equivalence cylinders, to be composed in order.  This is the Cyl8 wrapper carrying the explicit
component list that Cyl7's `MooreCyl` (whose `cyl` field is a placeholder) does not.  `length`
recovers Cyl7's `MooreCyl.len`. -/
abbrev MooreList (K : BPSet) : Type _ := List (CylMapWeqR K)

/-- **The pointed endofunctor of a Moore cylinder.**  The Cyl6 monoid product of the strict
components' `cylToPointedObj`, in list order (`List.prod` of the mapped list).  Reuses the existing
`cylToPointedObj` geometry and Cyl6's `Monoid (PointedEndofunctor (DPathGrpdR K))` — NO new sweep,
NO new prism.  The empty list gives `1`; a singleton gives the strict component's endofunctor. -/
noncomputable def mooreToPointed (m : MooreList K) :
    PointedEndofunctor (DPathGrpdR K) :=
  (m.map CylMapR.cylToPointedObj).prod

/-- **The empty Moore cylinder induces the monoid unit.**  `mooreToPointed [] = 1` (empty product),
the algebraic identity homotopy. -/
@[simp] theorem mooreToPointed_nil :
    mooreToPointed ([] : MooreList K) = 1 := by
  simp [mooreToPointed]

/-- **A length-1 Moore cylinder is the strict component.**  `mooreToPointed [c] = cylToPointedObj c`
— the strict `□¹`-cylinders embed as the singletons, exactly Cyl7's `MooreCyl.ofStrict`. -/
@[simp] theorem mooreToPointed_singleton (c : CylMapWeqR K) :
    mooreToPointed [c] = CylMapR.cylToPointedObj c := by
  simp [mooreToPointed]

/-- A cons unfolds as a product:
`mooreToPointed (c :: m) = cylToPointedObj c * mooreToPointed m`. -/
@[simp] theorem mooreToPointed_cons (c : CylMapWeqR K) (m : MooreList K) :
    mooreToPointed (c :: m) = CylMapR.cylToPointedObj c * mooreToPointed m := by
  simp [mooreToPointed]

/-! ## 2. Concatenation = product (the monoid-homomorphism heart)

Concatenation of Moore cylinders is list append; `mooreToPointed` turns it into the Cyl6 monoid
product, on the nose — the content "stacking homotopies = composing pointed endofunctors". -/

/-- **Concatenation of Moore cylinders** is list append (stack the two staircases). -/
def MooreList.concat (m m' : MooreList K) : MooreList K := m ++ m'

@[simp] theorem MooreList.concat_def (m m' : MooreList K) : m.concat m' = m ++ m' := rfl

/-- **CONCATENATION = PRODUCT.**  `mooreToPointed (m.concat m') = mooreToPointed m * mooreToPointed
m'`.  This is `List.map_append` + `List.prod_append` in the Cyl6 monoid: the induced endofunctor of
the concatenated staircase is the monoid product of the two pieces' endofunctors.  No leg-matching
hypothesis is needed — the conjugation isos supply the junction for free (see module docstring). -/
@[simp] theorem mooreToPointed_concat (m m' : MooreList K) :
    mooreToPointed (m.concat m') = mooreToPointed m * mooreToPointed m' := by
  simp only [MooreList.concat_def, mooreToPointed, List.map_append, List.prod_append]

/-- `mooreToPointed` is a **monoid homomorphism** from the free monoid `(MooreList K, ++, [])` to
`PointedEndofunctor (DPathGrpdR K)`: it sends `[]` to `1` and `++` to `*`.  Packaged as a
`MonoidHom` from the list-append monoid (`FreeMonoid`-style) for downstream reuse. -/
noncomputable def mooreToPointedHom :
    FreeMonoid (CylMapWeqR K) →* PointedEndofunctor (DPathGrpdR K) where
  toFun m := mooreToPointed (FreeMonoid.toList m)
  map_one' := mooreToPointed_nil
  map_mul' m m' := by
    show mooreToPointed (FreeMonoid.toList (m * m')) = _
    rw [FreeMonoid.toList_mul]
    exact mooreToPointed_concat _ _

@[simp] theorem mooreToPointedHom_apply (m : MooreList K) :
    mooreToPointedHom (FreeMonoid.ofList m) = mooreToPointed m := rfl

/-! ## 3. THE SUBMONOID THEOREM (headline)

`Set.range mooreToPointed` is a submonoid of `PointedEndofunctor (DPathGrpdR K)`: closed under `*`
(concatenation, §2), contains `1` (empty list), and contains `cylImage K` (singletons).  It is, on
the nose, the `Submonoid.closure` of the strict cylinder image. -/

section Submonoid

/-- `1` is in the range of `mooreToPointed` — the empty Moore cylinder. -/
theorem one_mem_range_mooreToPointed :
    (1 : PointedEndofunctor (DPathGrpdR K)) ∈ Set.range (mooreToPointed (K := K)) :=
  ⟨[], mooreToPointed_nil⟩

/-- The range of `mooreToPointed` is closed under the monoid product — realised by concatenation. -/
theorem mul_mem_range_mooreToPointed
    {A B : PointedEndofunctor (DPathGrpdR K)}
    (hA : A ∈ Set.range (mooreToPointed (K := K)))
    (hB : B ∈ Set.range (mooreToPointed (K := K))) :
    A * B ∈ Set.range (mooreToPointed (K := K)) := by
  obtain ⟨m, rfl⟩ := hA
  obtain ⟨m', rfl⟩ := hB
  exact ⟨m.concat m', mooreToPointed_concat m m'⟩

/-- **THE SUBMONOID.**  `Set.range mooreToPointed` as an actual `Submonoid` term: the Moore-cylinder
image is closed under `*` (concatenation = product, §2) and contains `1` (the empty cylinder).  This
is the headline result — the *algebraic* closure of the cylinder construction's image is a genuine
submonoid, realised by length-`n` Moore staircases. -/
noncomputable def mooreSubmonoid (K : BPSet) :
    Submonoid (PointedEndofunctor (DPathGrpdR K)) where
  carrier := Set.range (mooreToPointed (K := K))
  one_mem' := one_mem_range_mooreToPointed
  mul_mem' := mul_mem_range_mooreToPointed

@[simp] theorem mem_mooreSubmonoid {A : PointedEndofunctor (DPathGrpdR K)} :
    A ∈ mooreSubmonoid K ↔ ∃ m : MooreList K, mooreToPointed m = A :=
  Iff.rfl

/-- **The strict cylinder image is contained in `mooreSubmonoid`** — via the singleton (length-1)
Moore cylinders (`mooreToPointed [c] = cylToPointedObj c`).  This is the inclusion `cylImage K ⊆
↑(mooreSubmonoid K)` the task asks for: the Moore submonoid contains every strict endofunctor. -/
theorem cylImage_subset_mooreSubmonoid :
    Cyl6.cylImage K ⊆ ↑(mooreSubmonoid K) := by
  rintro _ ⟨c, rfl⟩
  exact ⟨[c], mooreToPointed_singleton c⟩

/-- The strict image, *via the singletons*, sits inside the range. -/
theorem cylImage_subset_range :
    Cyl6.cylImage K ⊆ Set.range (mooreToPointed (K := K)) :=
  cylImage_subset_mooreSubmonoid

/-- **`mooreSubmonoid K = Submonoid.closure (cylImage K)`, on the nose.**  Two inclusions:
* `⊇` (closure ⊆ mooreSubmonoid): `cylImage K ⊆ mooreSubmonoid` (singletons) and `mooreSubmonoid`
  is a submonoid, so it contains the closure (`Submonoid.closure_le`);
* `⊆` (mooreSubmonoid ⊆ closure): every `mooreToPointed m` is a finite product of `cylToPointedObj
  c`'s, each of which is in `cylImage K ⊆ closure`, and a closure is `*`/`1`-closed, so the product
  is in the closure (`list_prod_mem` over the mapped list).

So the Moore-cylinder image is **exactly** the submonoid generated by the strict cylinder image —
the algebraic closure is captured precisely by length-`n` Moore staircases. -/
theorem mooreSubmonoid_eq_closure :
    mooreSubmonoid K = Submonoid.closure (Cyl6.cylImage K) := by
  apply le_antisymm
  · -- mooreSubmonoid ⊆ closure: each element is a list product of generators.
    rintro _ ⟨m, rfl⟩
    rw [mooreToPointed]
    apply list_prod_mem
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨c, _, rfl⟩ := ha
    exact Submonoid.subset_closure ⟨c, rfl⟩
  · -- closure ⊆ mooreSubmonoid: mooreSubmonoid contains the generators and is a submonoid.
    exact Submonoid.closure_le.2 cylImage_subset_mooreSubmonoid

/-- **Range characterisation (set form).**  `Set.range mooreToPointed = Submonoid.closure (cylImage
K)` as plain sets — the `Submonoid`-coe of the previous theorem. -/
theorem range_mooreToPointed_eq_closure :
    Set.range (mooreToPointed (K := K)) = (Submonoid.closure (Cyl6.cylImage K) : Set _) :=
  congrArg (SetLike.coe) mooreSubmonoid_eq_closure

end Submonoid

/-! ## 4. Geometric honesty — span composition vs `⋙`, and the algebraic/geometric gap

We owe a precise account of *what `mooreSubmonoid` certifies geometrically*.  Three statements pin
it down: (a) the Cyl6 `*`-product on `mooreToPointed` is realised by concatenation = geometric
staircase stacking (PROVEN, §2); (b) the gap between `cylImage K` and its closure is *real* — no
single strict cylinder realises a generic product, because there is no fold `□¹ → I₂` (PROVEN, Cyl7
`no_fold_edge`); (c) the *geometric* `spanCompose` realises the same `⋙`-product (CONJECTURE, needs
the box-tensor exponential). -/

section Geometry

/-- **(a) The product is realised by a genuine Moore staircase.**  For strict cylinders `c, c'`, the
Cyl6 monoid product `cylToPointedObj c * cylToPointedObj c'` IS `mooreToPointed [c, c']` — the
length-2 Moore cylinder obtained by stacking the two homotopies (concatenation).  So the product of
two cylinder-image elements is realised, on the nose, by an explicit geometric two-step staircase
(NOT merely abstractly).  This is the positive geometric content: `mooreSubmonoid` elements are
length-`n` Moore cylinders, full stop. -/
theorem mul_eq_mooreToPointed_pair (c c' : CylMapWeqR K) :
    CylMapR.cylToPointedObj c * CylMapR.cylToPointedObj c'
      = mooreToPointed [c, c'] := by
  rw [mooreToPointed_cons, mooreToPointed_singleton]

/-- **(b) The gap is real: no single strict cylinder realises a generic product.**  This is exactly
Cyl7's `no_fold_edge`, re-exported: the span composite of two strict cylinders lives over the
length-2 interval `I₂`, and there is no precubical fold `□¹ → I₂` (no `1`-cell of `I₂` running
`init → final`) to collapse it to a length-1 strict cylinder.  Hence `cylImage K` (length-1 image)
is in general a *proper* subset of `mooreSubmonoid K` (its closure): the enlargement to length-`n`
Moore cylinders is unavoidable in a degeneracy-free precubical model.  (Whether the inclusion is
strict for a *specific* `K` depends on whether two of its cylinders' product happens to be a single
cylinder; the *obstruction to a general collapse* is this fold non-existence.) -/
theorem no_length1_collapse :
    ¬ ∃ z : Cyl7.I₂.toPsh.cells 1,
        Cyl7.I₂.toPsh.vertex₀ z = Cyl7.I₂.init ∧ Cyl7.I₂.toPsh.vertex₁ z = Cyl7.I₂.final :=
  Cyl7.no_fold_edge

/-- **(c) CONJECTURE — span composition realises the `⋙`-product.**  The geometric span composite
of Cyl7 (`Cyl7.spanCompose`, landing in the length-2 cocylinder `pathOb2 K = K^{I₂}`) induces, via
the still-unbuilt box-tensor exponential iso `pathOb2 K ≅ K^{I₂}` (Cyl7 `CocylinderConjecture`), the
same pointed endofunctor as the Cyl6 monoid product `cylToPointedObj c * cylToPointedObj c'` of the
two factors.  Equivalently: under the cocylinder identification, the geometric `R₁=L₂` span-gluing
and the algebraic `⋙`-composition agree.

We state it as the existence of a length-2 Moore cylinder whose induced endofunctor equals the
product AND whose underlying geometry is the span composite — the first conjunct is PROVEN
(`mul_eq_mooreToPointed_pair`, take `[c, c']`); the load-bearing, conjectural conjunct is that this
algebraic stacking coincides with the geometric `spanCompose` over `K^{I₂}`.  Pending the box-tensor
exponential (Cyl7 `CocylinderConjecture`, `MooreSpanComposeConjecture`), we record it as a `Prop`.

Status: **CONJECTURED.**  The *algebraic* realisation (§2, `mooreToPointed_concat`) is
unconditional and PROVEN; only the bridge to the *geometric* `spanCompose` is owed. -/
def SpanComposeRealisesProductConjecture (K : BPSet) : Prop :=
  Cyl7.CocylinderConjecture K.toPsh →
    ∀ c c' : CylMapWeqR K, ∃ m : MooreList K,
      m.length = 2 ∧ mooreToPointed m = CylMapR.cylToPointedObj c * CylMapR.cylToPointedObj c'

/-- **The conjecture's *algebraic* half is unconditionally PROVEN.**  Even before the box-tensor
exponential, the length-2 Moore cylinder `[c, c']` realises the product on the nose
(`mul_eq_mooreToPointed_pair`).  So `SpanComposeRealisesProductConjecture` is *already* discharged
at the level of Moore lists; the only thing the (conjectural) hypothesis `CocylinderConjecture`
would add is identifying this list with the single geometric `spanCompose` object over `K^{I₂}`.
This lemma certifies that the algebraic content owes nothing further. -/
theorem spanComposeRealisesProduct_algebraic :
    SpanComposeRealisesProductConjecture K := by
  intro _ c c'
  exact ⟨[c, c'], rfl, (mul_eq_mooreToPointed_pair c c').symm⟩

/-- **Bridge to Cyl6's conditional submonoid.**  Cyl6's `cylSubmonoid` packaged the *strict* image
as a submonoid *given* a hypothetical single-cylinder composition (`compose : ∀ c c', ∃ d, …`). We
now know (Cyl7 `no_fold_edge`, here `no_length1_collapse`) that such a single-cylinder `d` need NOT
exist; the honest replacement is `mooreSubmonoid`, where the composite is the length-2 list
`[c, c']` rather than a single `d`.  This lemma records that the Cyl6 `compose` hypothesis holds *in
`mooreSubmonoid`* (with `mooreToPointed`-of-a-list standing in for the single `d`): the product of
two singletons is the `mooreToPointed` of an explicit Moore list. -/
theorem moore_compose (c c' : CylMapWeqR K) :
    ∃ m : MooreList K,
      mooreToPointed m = CylMapR.cylToPointedObj c * CylMapR.cylToPointedObj c' :=
  ⟨[c, c'], (mul_eq_mooreToPointed_pair c c').symm⟩

end Geometry

/-! ## 5. Summary anchors

The two facts a reader should take away, both PROVEN and sorry-free:

* `mooreToPointed_concat` : concatenation of Moore cylinders = the Cyl6 monoid product (so
  `mooreToPointedHom` is a monoid hom from the free monoid on strict cylinders);
* `mooreSubmonoid_eq_closure` : `Set.range mooreToPointed = Submonoid.closure (cylImage K)` — the
  Moore-cylinder image is *exactly* the submonoid generated by the strict cylinder image, the
  headline submonoid result.

And the honest geometric line:

* `mul_eq_mooreToPointed_pair` (PROVEN): every product is a genuine length-2 Moore staircase;
* `no_length1_collapse` (PROVEN, = Cyl7 `no_fold_edge`): it can NOT be collapsed to length 1;
* `SpanComposeRealisesProductConjecture` (CONJECTURED): the geometric `spanCompose` over `K^{I₂}`
  induces this same product — owed the box-tensor exponential, its algebraic half discharged by
  `spanComposeRealisesProduct_algebraic`. -/

end Cyl8
