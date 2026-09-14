# DESIGN.md — conventions and decisions

This file records every non-obvious design choice. Each
entry gives a one-line justification and, where relevant, the paper equation it
matches (Paliga–Ziemiański, arXiv:2103.05336, henceforth **PZ**; Ziemiański,
arXiv:1901.05206, henceforth **Z**).

## Current structure

See **`ARCHITECTURE.md`** for the file map (the source of truth for where things
live). The tree is organized into three provenance tiers: `Machinery/` (generic, citable), `Precubical/` (the
precubical literature), `Concurrency/` (this work), plus `Testing/`.

This file records **decisions and their reasons** — conventions you must not deviate
from, and dead ends you must not re-explore. It is not a status board.

## 0. Toolchain and mathlib recon

- **Toolchain:** `leanprover/lean4:v4.30.0`, the latest *stable* Lean release at
  setup time. Mathlib is pinned to the matching release tag `v4.30.0`
  (`lakefile.toml`, `lake-manifest.json`). `lake exe cache get` populates the
  prebuilt `.olean` cache so no full mathlib rebuild is needed.

- **mathlib carries no cubical material.** There is no box/cube category, no cubical
  or precubical sets, and no `Cube`/`Cubical` namespace; the only `*cub*` files are
  about cubic polynomials and the Hilbert cube. It *does* have a mature simplicial
  story (`AlgebraicTopology/SimplicialObject`, `SimplicialSet`, `SimplexCategory`).
  **Decision:** define precubical sets from scratch (the concrete graded definition
  of §1), *mirroring* mathlib's simplicial conventions rather than reusing them.

## 1. Precubical identities (`Precubical/Basic/Basic.lean`)

- **Face signature.** `face : ∀ {n}, Bool → Fin (n+1) → cells (n+1) → cells n`.
  We keep `face` curried as `face ε i : cells (n+1) → cells n`.

- **`ε : Bool` convention (fixed once, never deviate):** `false = d⁰` =
  initial/source face, `true = d¹` = final/target face. (PZ §2; Z.)

- **The identity.** We mirror mathlib's `SimplicialObject.δ_comp_δ`
  (`Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean:115`), which states for
  `i ≤ j : Fin (n+2)` that `δ i ∘ δ j.succ = δ j ∘ δ i.castSucc`. The precubical
  version carries two independent labels `ε, η : Bool` (the two faces never
  interact), so the stored field is, for `i ≤ j : Fin (n+1)` and `c : cells (n+2)`:

  ```
  face ε i (face η j.succ c) = face η j (face ε i.castSucc c)
  ```

  This is the standard relation ∂ᵢ^ε ∂ⱼ^η = ∂_{j-1}^η ∂ᵢ^ε for i < j (PZ §2),
  transcribed in the `castSucc`/`succ` idiom so that mathlib `Fin` lemmas apply
  directly. It is a field of `PrecubicalSet` (`Basic.lean`) and a `simp`-usable
  rewrite lemma on the standard cube (`StandardCube.face_face`).

- **Vertex naming.** Superscript digits `⁰`/`¹` are **not** legal Lean
  identifier characters, so the paper's `vertex⁰`/`vertex¹` are read at the `ε : Bool`
  convention instead: `vertexEnd false` (source) and `vertexEnd true` (target), defined
  by pullback along `endVertexMap` so that order-independence is Yoneda, not an induction.

- **Lints.** The project keeps mathlib's standard linter set on, but disables
  `linter.style.header` in `lakefile.toml`: this is a research repo, not a
  mathlib PR, so the copyright-header requirement is noise.

## Universe policy (affects §1–§8)

`PrecubicalSet.cells : ℕ → Type` is fixed at `Type` (universe `0`), **not**
`Type u`.  All precubical sets here are concrete/small, and `§5`'s `Ch K` needs
bi-pointed maps `□^∨n → K` living in the *same* universe as `K`; fixing `Type 0`
keeps the standard cube (whose cells are `Fin N → Option Bool`-subtypes, already
`Type 0`) compatible with an arbitrary `K` without threading `ULift`. This is a
deliberate, documented narrowing of the `Type u` in the spec.

## 3. Standard cube (`Precubical/Basic/StandardCube.lean`)

- **Cells.** `cells N k := {c : Fin N → Option Bool // (noneSet c).card = k}`,
  where `noneSet c` is the finset of `none` (= ∗) positions.
- **`i`-th `none` position.** `nones c := (noneSet c.val).orderEmbOfFin c.prop`,
  the monotone bijection `Fin k ↪o Fin N` onto the `none`-positions. `face ε i c
  := update c.val (nones c i) (some ε)`; the cardinality drops by one because
  `noneSet (update c p (some ε)) = (noneSet c).erase p` (`noneSet_update`).
- **Precubical identity (the crux).** Proved via `face_nones`: the `none`-set
  embedding *after* a face equals `(succAboveOrderEmb a).trans (nones c)`,
  established with `Finset.orderEmbOfFin_unique'` (an order embedding into a
  finset of the right cardinality *is* `orderEmbOfFin`). Both sides of
  `face_face` then reduce to two `Function.update`s at the independent positions
  `nones c i.castSucc`, `nones c j.succ`; `Fin.succAbove_succ_of_le` /
  `succAbove_castSucc_of_le` compute the indices and `Function.update_comm`
  finishes — with no dependent rewrites.
- Bi-pointed at the constant-`some false`/`some true` vertices. Notation `□^N`.

## 3b. Serial wedge via pushouts (`Precubical/Wedge/Wedge.lean`)

Per the §3 spec the wedge `□^∨(n₁,…,n_l)` is the end-to-end gluing of standard
cubes, realized as the **pushout of a point**: `X ∨ Y` glues `X.final` to `Y.init`,
and the serial wedge is the `foldr` of `∨` over the standard cubes.

`PrecubicalSet := Boxᵒᵖ ⥤ Type` is a functor category into `Type`, which mathlib
proves cocomplete, so `HasPushouts PrecubicalSet` is `inferInstance`. **The wedge
does not use it.** `wedge2` is built on the bespoke `Glue.gluePsh` (a pointwise
`Quot`, `Precubical/Wedge/GluePushout.lean`) because mathlib's `Limits.pushout` is
`Classical.choice`-opaque and `serialWedge` / `Ch` / `Testing` have to compute. See
*Computable by default* below; do not "simplify" `Glue` into `Limits.pushout`.

## Two models: presheaf topos + concrete bridge

1. The concrete graded structure of §1 is **`PrecubicalConstructions`**
   (dir `Precubical/Basic/`); cube, wedge, chains build on it.
2. **`PrecubicalSet := Boxᵒᵖ ⥤ Type`** is the genuine definition — the presheaf
   topos on the **box category `Box`** (`Machinery/Cube/Box.lean`). `Box` has objects
   `ℕ` and morphisms `m ⟶ n :=` precubical maps `□^m ⟶ □^n`, with composition
   and the category axioms **inherited** from `PrecubicalConstructions` (no
   substitution-associativity bookkeeping). Being a functor category into `Type`,
   `PrecubicalSet` is cocomplete: `HasPushouts PrecubicalSet` is `inferInstance`.
3. The bridge between the two models is **representability of the standard cube**:
   `(□^n ⟶ K) ≃ K.cells n` (`Box.ofSign` / `StdCube.cubeRepr`, Yoneda for
   cubes, `Precubical/Basic/Representable.lean`). A global
   `PrecubicalSet ≌ PrecubicalConstructions` equivalence is deliberately **not**
   built: the cube Yoneda is the only bridge the downstream development uses.

**Working convention:** `PrecubicalSet` (topos) is the *default* type everywhere
downstream.  `PrecubicalConstructions` is consulted only for explicit cells/faces,
and then through the cube Yoneda lemma.  Concretely:

- `Precubical/Basic/Bipointed.lean`: `BPSet` is a `PrecubicalSet` (presheaf) with two
  chosen `0`-cells; `cells X n := X.obj [n]`; the extremal vertices
  `vertex₀/vertex₁` are `X.map` of the vertex-inclusion box maps.
- `Precubical/Wedge/Wedge.lean`: `□ⁿ := yoneda.obj [n]` (representable, bi-pointed);
  `X ∨ Y` is the **pushout** of a point in `PrecubicalSet`, cocompleteness being free.

## 5–7

- **§5 `Precubical/Chains/Category.lean`.** `Ch K` is *notation for the object type*
  `ChainCat.Obj K = (dims, ⋁dims ⟶ K)`; morphisms are wedge maps over `K`. The
  *functor* is `chFunctor : BPSet ⥤ Cat` (post-composition); its functor laws are
  `rfl` because `≫` in `BPSet` is componentwise in `Type`. **Lifting lemma**
  `Aut.liftToCh (K : BPSet) : Aut K →* Aut (chFunctor.obj K) := chFunctor.mapAut K`.

  GOTCHA: `Ch` is not a functor and `Ch.obj` / `Ch.mapAut` do not parse. Notation is for
  TERMS; the functor has its own name.
- **§6 `Precubical/Basic/Altitude.lean`.** Faces via cofaces `□ⁿ ⟶ □ⁿ⁺¹`
  (`PrecubicalSet.coface`, built from `Box.ofSign`).  `AdmitsAltitude` and `NonSelfLinked` (via the
  Yoneda canonical map `cubeMap`); reachability of cells is `PrecubicalSet.Reaches`
  (`Precubical/Basic/Reachability.lean`).

## Which product owns `⊗` on `BPSet`

Three products are in play. Only one gets the instance.

- **The wedge `∨`** (serial gluing) is the default `instance : MonoidalCategory BPSet`
  (`Precubical/Wedge/WedgeMonoidal.lean`), unit `□0`. It is the product the chain theory runs on, so it
  earns the slot: working at `BPSet` gives `⊗`/`α_`/`λ_`/`ρ_`/`monoidal` directly, no alias casting.
- **The geometric (parallel) tensor** lives on the alias `GeoBP := BPSet` with its own glyph `⊗ᵍ`.
  By convention we always write `∨` for the wedge and `⊗ᵍ` for the geometric one, so the two never
  visually collide even though bare `⊗` means the wedge.
- **The topos cartesian product** is not built.

Any further product goes on its own alias with a distinct notation — never a second
`MonoidalCategory BPSet`.

## Computable by default

`Precubical/Wedge/GeoTensor/` builds `⊗ᵍ` from the **closed form** of the Day coend
(`(X ⊗ Y)(▫n) = Σ p q, (p+q = n) × X(▫p) × Y(▫q)`) rather than from mathlib's Day convolution,
which is `Classical.choice`-opaque. The same choice explains `Precubical/Wedge/GluePushout`
(a pointwise `Quot`, not `Limits.pushout`), which is why `serialWedge` / `Ch` / `Testing` compute.

## `permOf` orders events by the run

The crossing permutation of a refinement must conjugate by the **run order** `runOrd` — the order
the chosen linearization performs the events — not by the run-free lexicographic flattening
`pos = finSigmaFinEquiv`. Ordering by `pos` makes `permOf` a function of the chain morphism alone,
hence an exact gradient: every loop becomes trivial and the braid group collapses. This is not an
optimization to be reversed. (`Concurrency/Salvetti/EventBraid.lean`.)

## One route to the slice presentation

The presentation of `Ch(K)[W⁻¹]` is a **colimit of slice presentations inherited from the base**
(`garsideRawFam`, `garsidePoly`). Two alternatives were built and deleted, and neither
is to be re-explored:

- **Cube-first.** `Ch(Z)/[n] ≅ Ch(□n)` and a slice is a product of cube slices
  (`locChConsEquiv`), so a slice presentation could be assembled bead by bead. It works, and it
  produced a *second* presentation chain beside the inherited one. "The slice is a product of cube
  slices" is a description of the category, not a construction step; `locChConsEquiv` and
  `Presents.prod` stay in the tree as results.
- **Through a monoid.** A monoid has one object, so routing a presentation through one forces a fixed
  strand count and every law gets restated with the count threaded through. A presentation works on
  the whole category at once.

The **discrete-fibration route** (`isLocalization_chDescent`, `hLocPresentation`) is a special case,
not a competitor: it asks the fibration to survive localization (`IsSegal`), which buys a smaller
presentation where it holds.

## The paper's polygraph is the statement; the bead cuts are the route

`Ch(K)[W⁻¹]` is presented by `Paper.poly K` — 0-cells the runs, 1- and 2-cells the objects of degree
one and two — and by `chCutLocFunctor.obj K`, which reaches the same category from the other end by
adjoining a formal inverse to each merge generator. A *third* presentation, spelling the paper's own
cells in `∫F`/`Cut` vocabulary, is not a third theorem: its content **is** that a cut-vocabulary
polygraph presents, so restating it in the surviving vocabulary *is* `paperPresents`. That is the
first kind of bloat `CLAUDE.md` names, at its largest scale. So the cut polygraph carries the route
(`chCutPoly`, `chCollapse`, `readCut`) and never a statement, and the generic machinery only the
rebuild asked for — a presentation theorem for a contraction, and one for dropping cells from a
presentation — is not built.

## Garside first, coherence second

The naming to build at is the **Garside** one, following Gaussent–Guiraud–Malbos, *Coherent
presentations of Artin monoids* (Compositio 151 (2015)); the Artin reading is taken from it by
Tietze, and the geometric phrasing from that.

**Naturality in `p` is dropped, deliberately.** The colimit is natural in `p` by construction —
`garsideFam` is a `comap` of the slice's own cells, so a map of presentations substitutes words and
never touches the shape. Squier's theorem is *not* natural in `p`: its output's 2-cells are the
critical branchings of its input presentation, and a Tietze transformation changes them. The two
are different mechanisms and neither construction should be asked for both. That is why
`BraidPresentation.Map` is not in the tree: it was generality nothing instantiated.

**The parameter divides the construction in two.** Everything from `garsideFam` up to
`garsideSlice_hP` is presentation-**independent** and no product appears in it; presentations
diverge only at the *value* step, where Garside splits over the categorical product
(`garsidePolyList`, `garsidePolyListCons`) and Artin would split over the Day tensor. The pairing is
forced: a product needs an idle generator, a tensor needs a length-preserving relation, and neither
presentation has both.

**Why Garside is the one to build.** It is the convergent presentation: `PosGermRel` rewrites a
length-additive pair `s·t ⇝ st`, strictly length-decreasing, and `lengthGraded_germBP_P` is that
termination certificate. `ArtinRel` is length-preserving (commutation 2↔2, braid 3↔3) so it
terminates in neither orientation — which is why GGM go Garside-first and Tietze down, and why the
same order is right here. Garside also splits over the **categorical product** where Artin splits
over the tensor and not conversely (`garsidePolyListCons`, `isEmpty_beadHom_pair_two`).

**The geometric phrasing.** `degree c = dimSum c.dims − c.dims.length` grades chains: a bead of
dimension `d` costs `d − 1`, additive over beads. The k-cells are the degree-k chains — runs at 0,
one 2-bead at 1, two 2-beads (square) or one 3-bead (hexagon) at 2 — which is the shape of
`Paper.poly`, and the species split is `artin_of_codim_two`.

Three constraints on the route:

- `isEmpty_germ_mul` — the Garside base carries no multiplication at all, so the block sum stays a
  field of `Graded.Tensor` (`posTensor`, with `posSumL`/`posSumR` its one-sided halves) rather than
  becoming a monoid object's `μ` on the polygraph.
- Higher coherence wants 3-cells, and the presheaf-topos theorem is **sharp at 2**
  (Makkai–Zawadowski, cited in `Foundations/Polygraph/Presheaf.lean`). Dimension 3 costs the topos,
  so stay in degree 2 until the base case is settled.
- The slice family is not induced by a functor on the localized base: `merge_fibres_clash` exhibits a
  merge whose two fibres disagree, so the family is built from the beads' own weak orders
  (`garsideSlicePresentation`) rather than descended along the fibration.

Lucas, *A cubical Squier's theorem* (arXiv 1612.06541), is the variant to read first: the
confluence diagram of two disjoint cuts is a **square**, not a globular 2-cell with a chosen
whiskering, and `Ch K` is proved acyclic and skeletal (`ChainCat.skeletal`), which is that
framework's hypothesis.

## A localization hypothesis is `≤` + `IsInvertedBy`, not an equality

`Presents.presentsLocalization` originally asked `W = (pickedArrows S).multiplicativeClosure` on the
nose. The primitive is now `presentsLocalizationOfLe`, taking
`(pickedArrows S).multiplicativeClosure ≤ W` together with `W.IsInvertedBy closure.Q` — *two classes
with the same localization* — and the equality form is a two-line corollary for callers that have it
on the nose.

This is not a weakening for its own sake: both steps of the original proof that used the equality
become **unconditional** once restated at the closure, and the widening is then one mathlib-shaped
lemma (`Functor.IsLocalization.of_le`, which is `of_equivalence_source` at `Equivalence.refl`). The
equality is genuinely false in a case that matters — the transitions of `transitionPoly` are fibrewise
*identities*, so their closure is strictly smaller than `fibrewiseIsos` even though the two
localizations agree. Asking for equality cost three bespoke 2-cell species there.

## Hypotheses, not axioms

An unproved input is a `Prop`-valued *argument* of the declaration that needs it, never an `axiom` —
so nothing in the tree depends on it unless it is supplied, and `#print axioms` stays at
`[propext, Classical.choice, Quot.sound]` everywhere. The one such input is **Garside's theorem**,
injectivity of `posToBraid n`, taken as `hg` by `posPureToPure_injective`
(`Machinery/Braid/PosGerm.lean`). **Matsumoto's theorem for `Sₙ` is not one of them** — it is proved
outright in `Machinery/Braid/Matsumoto.lean`, and nothing assumes it.

## Notation for TERMS, `abbrev` for TYPES

Notation expands at parse time, so the elaborated term is byte-identical and `simp`/`rw` keyed
matching keeps firing. An `abbrev` is a real definition: harmless in a *type* position (`cells`,
`Bead`, `DimList`), but in a *term* position it becomes a new head symbol — `omega` treats it as an
atom and `rw`'s `kabstract` cannot see through it. Measured on a bead-dimension abbreviation, which
is why there is none.

Two consequences worth remembering: binary notation needs **argument** precedences
(`notation:65 X:65 " ⊙ " Y:66`), or it parses greedily; and prefix notation cannot express an
unapplied function, so `congrArg Box.ob h` must stay spelled out (`congrArg ▫h` re-parses as
`congrArg (Box.ob h)`).

## The slice-colimit route, and why it was abandoned

The route presenting `Ch(K)[W⁻¹]` as a strict colimit of presentations of its localized slices is
not in the tree. It was retired with the Garside presentation it served; this records what was
established about it, so it is not re-attempted. Joint surjectivity of the colimit's cells went with
it: `Polygraph` is a presheaf topos (`Foundations/Polygraph/Presheaf.lean`), so anyone who needs the
statement back reads it off cellwise colimits rather than rebuilding a probe polygraph.

**Its compatibility hypothesis has to be an equality of functors.** Measured at the smallest base —
one object, one arrow, nothing inverted — take the polygraph with two 0-cells and a 1-cell each
way, relating every parallel pair of words. Over a base all of whose arrows are invertible each
slice is codiscrete, so that polygraph presents the localized slice, and it does so with *both* its
0-cells labelled by the same slice object: the naming map is not injective, by `rfl`. The category
of elements is a point, so the colimit of the constant diagram is that polygraph again, and it
presents the localized total category too — correctly, though two 0-cells name one object. Hence the
comparison's unit can only ever be an isomorphism: the two 0-cells are not glued, so any retraction
is merely isomorphic to the identity. And the 0-cells of the colimit are the copies' own 0-cells,
never their image in the category of elements — flattening them onto that image would identify
these two and invent a loop. So the theorem may ask nothing whatever of the 0-cells.

**Weakening that hypothesis to a natural isomorphism makes the conclusion false**, not merely
unproved. Measured at a base with one object whose endomorphisms are `ℤ/2`, generated by an
involution, same constant family. The slice is codiscrete, so the comparison isomorphism exists for
every arrow and is *unique* — every 2-cell into a thin category is a `Subsingleton.elim`, so no
cocycle or coherence condition can exclude this data. The strict comparison still fails: the slice
has one object per group element, pushing along the involution swaps them, and a 0-cell names the
top of its slice, so equality would force the involution to be the identity. What a 0-cell must name
*on the nose* is its slice object; the morphism half is free whenever the slice is thin. And the
family being constant over a loop, every leg is the identity and the colimit presents a **thin**
category, while the target — the category of elements — is the loop itself and is not thin. No
functor out of it is an equivalence at all. The missing datum is a cell for the involution: a strict
colimit of polygraphs has nowhere to record an automorphism of the base, which is why the strict
colimit is not the bicolimit.

## No monoidal structure on `Polygraph`

The wedge splits a chain, and a presentation that split along it would want `Polygraph` monoidal, so
the tensor `prod P Q` — each factor's cells at a frozen 0-cell of the other, plus an interchange
square per pair of 1-cells — was built, exhibited as the Day convolution for the promonoidal
structure on `PolyShape` (`Split.square` at `cell 2 2` *is* the interchange square, so it is not an
axiom), and carried to `MonoidalCategory Polygraph`. None of it is in the tree.

The presentation works on the whole category at once: `Paper.poly K` is the runs and the objects of
degree one and two, for every `K` and with no hypothesis, so there is no wedge to split along and no
place for a tensor to act. A splitting presentation would also fix a strand count in each factor,
which is the monoid detour by another name.

## The cut presentation is not a rewriting system

No additive invariant orients a 2-cell of `Cut.poly`: its two sides are two two-step factorisations
of one codimension-two refinement, so letter count, codimension and crossing count agree on them, as
does the multiset of the legs' crossing counts. The only orientation left is by which junction is
dropped first — sort-by-position, which `CLAUDE.md` names as the smell it is — and Tietze
elimination down to the atoms is not locally confluent either, a deletion being free to consume the
witness another needs. So the generic apparatus for it — abstract rewriting and "a convergent
orientation presents" — has no consumer and is not in the tree. Confluence arguments remain fine;
what is refuted is a *terminating* orientation of the cut cells.
