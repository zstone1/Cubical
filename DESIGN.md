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

- **mathlib recon (§0 mandate):** searched mathlib v4.30.0 for existing cubical /
  precubical material:
  - `find -iname '*cub*'` → only `Algebra/CubicDiscriminant.lean` (cubic
    polynomials) and `Topology/Compactness/HilbertCubeEmbedding.lean` (the
    Hilbert cube). Neither is relevant.
  - `grep -ri 'cubical|precubical|cube category|BoxCat'` over `Mathlib/` → no
    hits. There is **no** box/cube category, no cubical or precubical sets, and
    no `Cube`/`Cubical` namespace.
  - mathlib *does* have a mature simplicial story (`AlgebraicTopology/
    SimplicialObject`, `SimplicialSet`, `SimplexCategory`).
  - **Decision:** define precubical sets from scratch (the concrete graded
    definition of §1), as the spec directs when no degeneracy-free cubical
    development exists. We *mirror* mathlib's simplicial conventions rather than
    reuse them.

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
  identifier characters, so the paper's `vertex⁰`/`vertex¹` become `vertex₀`
  (all-`false`/source) and `vertex₁` (all-`true`/target). They are defined by
  repeatedly applying `face ε 0` and proved order-independent via
  `vertex_face` (the §1 well-definedness obligation).

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
  finishes. No `sorry`, no dependent rewrites.
- Bi-pointed at the constant-`some false`/`some true` vertices. Notation `□^N`.

## 3b. Serial wedge via pushouts (`Precubical/Wedge/Wedge.lean`)

Per the §3 spec the wedge `□^∨(n₁,…,n_l)` is the end-to-end gluing of standard
cubes. Following the project owner's guidance, we realize this as the **pushout**
of a point: `X ∨ Y` is `pushout (pt → X at X.final) (pt → Y at Y.init)`, and the
serial wedge is the `foldr` of `∨` over the standard cubes.

`PrecubicalSet := Boxᵒᵖ ⥤ Type` is a functor category into `Type`, which mathlib
proves cocomplete, so `HasPushouts PrecubicalSet` is just `inferInstance` — a
real, permanent instance, **not** a placeholder. The wedge carries **no**
`sorry`. Everything downstream is built against the abstract pushout universal
property (`pushout.inl/inr/desc/condition`).

## Architecture pivot: presheaf topos + concrete bridge

Per the project owner, the development is reorganized:

1. The concrete graded structure of §1 is renamed **`PrecubicalConstructions`**
   (dir `Precubical/Basic/`); cube, wedge, chains build on it.
2. **`PrecubicalSet := Boxᵒᵖ ⥤ Type`** is the genuine definition — the presheaf
   topos on the **box category `Box`** (`Machinery/Cube/Box.lean`). `Box` has objects
   `ℕ` and morphisms `m ⟶ n :=` precubical maps `□^m ⟶ □^n`, with composition
   and the category axioms **inherited** from `PrecubicalConstructions` (no
   substitution-associativity bookkeeping). Being a functor category into `Type`,
   `PrecubicalSet` is cocomplete: `HasPushouts PrecubicalSet` is `inferInstance`.
3. The bridge between the two models is **representability of the standard cube**:
   `(□^n ⟶ K) ≃ K.cells n` (`StdCube.cubeRepr`, Yoneda for cubes,
   `Precubical/Basic/Representable.lean`) — now **proved, sorry-free**. (A global
   `PrecubicalSet ≌ PrecubicalConstructions` equivalence was contemplated but
   never built; it is not needed — the cube Yoneda is the bridge that the
   downstream development actually uses.)

**Working convention (project owner):** `PrecubicalSet` (topos) is the *default*
type everywhere downstream.  `PrecubicalConstructions` is consulted only for
explicit cells/faces, and then through the cube Yoneda lemma.  Concretely:

- `Precubical/Basic/Bipointed.lean`: `BPSet` is a `PrecubicalSet` (presheaf) with two
  chosen `0`-cells; `cells X n := X.obj [n]`; the extremal vertices
  `vertex₀/vertex₁` are `X.map` of the vertex-inclusion box maps.
- `Precubical/Wedge/Wedge.lean`: `□ⁿ := yoneda.obj [n]` (representable, bi-pointed);
  `X ∨ Y` is the **pushout** of a point in `PrecubicalSet` — cocompleteness is
  free, so the wedge carries **no `sorry`**.
- `StdCube.canonicalMap` / `cubeRepr` (`Precubical/Basic/Representable.lean`) — the
  cube Yoneda lemma — is now **proved, sorry-free**; it is no longer admitted.

## 5–7 (topos era)

- **§5 `Precubical/Chains/Category.lean`.** `Ch K` is *notation for the object type*
  `ChainCat.Obj K = (dims, ⋁dims ⟶ K)`; morphisms are wedge maps over `K`. The
  *functor* is `chFunctor : BPSet ⥤ Cat` (post-composition); its functor laws are
  `rfl` because `≫` in `BPSet` is componentwise in `Type`. **Lifting lemma**
  `Aut.liftToCh (K : BPSet) : Aut K →* Aut (chFunctor.obj K) := chFunctor.mapAut K`.

  GOTCHA: `Ch` is not a functor and `Ch.obj` / `Ch.mapAut` do not parse. Notation is for
  TERMS; the functor has its own name.
- **§6 `Precubical/Basic/Altitude.lean`.** Faces via cofaces `□ⁿ ⟶ □ⁿ⁺¹`
  (`PrecubicalSet.coface`, built from `canonicalMap`).  `AdmitsAltitude`,
  `Accessible` (via an inductive `Reach` preorder), `NonSelfLinked` (via the
  Yoneda canonical map `cubeMap`, no `sorry`).

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
which is `Classical.choice`-opaque. `Machinery/DayTensor.lean` keeps the abstract version, and
`Precubical/Wedge/CubeTensor.lean` is the comparison. The same choice explains `Precubical/Wedge/GluePushout`
(a pointwise `Quot`, not `Limits.pushout`), which is why `serialWedge` / `Ch` / `Testing` compute.
Do **not** "simplify" `Glue` into `Limits.pushout`.

## `permOf` orders events by the run

The crossing permutation of a refinement must conjugate by the **run order** `runOrd` — the order
the chosen linearization performs the events — not by the run-free lexicographic flattening
`pos = finSigmaFinEquiv`. Ordering by `pos` makes `permOf` a function of the chain morphism alone,
hence an exact gradient: every loop becomes trivial and the braid group collapses. This is not an
optimization to be reversed. (`Concurrency/Salvetti/EventBraid.lean`.)

## Hypotheses, not axioms

`Matsumoto n` (`Machinery/Braid/Artin.lean`) is a `Prop`-valued *definition* taken as an argument, not an
`axiom` — so nothing in the tree depends on it unless it is supplied, and `#print axioms` stays at
`[propext, Classical.choice, Quot.sound]` everywhere. Any further unproved input enters the same
way.

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
