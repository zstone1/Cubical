# cube-chains: precubical sets and the cube chain category in Lean 4

This repository formalizes the basic theory of (bi-pointed) precubical sets and
Ziemiański's cube chain category `Ch(K)`, culminating in *statements* of two
lemmas about automorphisms:

1. **Lifting (prove this; it should be routine):** `Ch` is a functor, so every
   automorphism of a bi-pointed precubical set `K` lifts to an automorphism of
   the category `Ch(K)`, and the lift is a group homomorphism
   `Aut(K) →* Aut(Ch(K))`.
2. **Lowering (STATE ONLY — leave `sorry`):** under hypotheses
   (non-self-linked, admits an altitude function, accessible), every
   *orientation-preserving* automorphism of `Ch(K)` is induced by a unique
   automorphism of `K`.

The lowering lemma and everything marked **[RESEARCH]** below is mine to prove.
Your job is the infrastructure, the routine lemmas, and clean statements.

Mathematical references (definitions below are self-contained; consult these
only if something is ambiguous):
- K. Ziemiański, *Spaces of directed paths on pre-cubical sets II*,
  arXiv:1901.05206 (defines `Ch(K)`, Theorem 7.5/7.6).
- J. Paliga, K. Ziemiański, *Configuration spaces and directed paths on the
  final precubical set*, arXiv:2103.05336, Section 2 (the conventions used
  here: faces, cube chains, wedges, altitude, non-self-linked, accessible;
  Lemma 2.11 is the key structural lemma).

---

## 0. Project setup

- Lean 4 project built with `lake`, depending on **mathlib** (current stable).
  Use the standard mathlib-dependent project template and `lake exe cache get`.
  Pin the toolchain to whatever the chosen mathlib revision requires.
- Before defining anything: **search mathlib** (`Mathlib.AlgebraicTopology.*`
  and elsewhere) for existing cubical / precubical developments (cube
  categories, cubical sets, anything in a `Cube` or `Cubical` namespace). If a
  compatible definition of precubical sets (presheaves on a box category
  *without* degeneracies or symmetries) exists, build on it and adapt the plan
  below. If only cubical-with-degeneracies exists, do NOT use it; define
  precubical sets from scratch as below. Record what you found and the
  decision in `DESIGN.md`.
- Suggested layout:
  ```
  CubeChains/
    Precubical/Basic.lean      -- precubical sets, morphisms, category
    Precubical/Bipointed.lean  -- bi-pointed structure
    Precubical/StandardCube.lean
    Precubical/Wedge.lean      -- serial wedges of standard cubes
    Precubical/Altitude.lean   -- altitude, accessibility, non-self-linked
    Chains/Basic.lean          -- cube chains
    Chains/Category.lean       -- Ch(K) as a category, functoriality
    Chains/Aut.lean            -- lifting lemma (proved), lowering (stated)
    Conjectures.lean           -- all `sorry`/`proof_wanted` statements live here
  ```
- Rule: **no `sorry` anywhere except `Conjectures.lean`** (you may use
  Batteries' `proof_wanted` there instead of `sorry` if convenient). CI (or at
  minimum a `lake build` check) must pass.

## 1. Precubical sets (`Precubical/Basic.lean`)

A precubical set is a graded family of cell types with face maps satisfying
the precubical identities. Use the concrete graded definition (not free
categories with relations):

```lean
structure PrecubicalSet where
  cells : ℕ → Type u
  face  : ∀ {n : ℕ}, Bool → Fin (n + 1) → cells (n + 1) → cells n
  -- precubical identity: for i ≤ j (mind the off-by-one),
  -- face ε i ∘ face η j.succ = face η j ∘ face ε i.castSucc, or the
  -- equivalent formulation you find most workable.
```

Notes:
- The index gymnastics here are the fiddliest part of the whole project.
  Mirror mathlib's simplicial conventions (`SimplicialObject`, `Fin.succAbove`
  / `Fin.castSucc` style) where possible, and prove the handful of rewriting
  lemmas you need (`face_face` in both orientations) immediately, with `simp`
  attributes. Budget real effort here; everything downstream depends on these
  being usable.
- `ε : Bool` with `false` = the `d⁰` (initial/source) face and `true` = `d¹`
  (final/target) face. Fix this convention once, document it, never deviate.
- Morphisms: dimension-wise functions commuting with all faces. Give
  `PrecubicalSet` a `Category` instance (this is just structured functions;
  no presheaf machinery needed, though if you went the presheaf route in §0
  it comes for free).
- Iterated faces: for `A : Finset (Fin n)` define `faceSet ε A : cells n → cells (n - A.card)`
  (or an indexed variant you prefer), and the **extremal vertices**
  `vertex⁰ c`, `vertex¹ c : cells 0` of a cube `c : cells n` (apply all
  `false`-faces resp. all `true`-faces). Prove they are well defined
  (independent of application order) — this is a finite computation with
  `face_face`.

## 2. Bi-pointed structure (`Precubical/Bipointed.lean`)

```lean
structure BPSet extends PrecubicalSet where
  init  : cells 0
  final : cells 0
```

Morphisms preserve `init` and `final`; category instance; `Aut K` is then
mathlib's `Aut` in this category (a group, for free).

## 3. Standard cubes and wedges (`Precubical/StandardCube.lean`, `Wedge.lean`)

- **Standard cube** `□ⁿ`: cells in dimension `k` are functions
  `c : Fin n → Option Bool` with exactly `k` values equal to `none`
  (`none` = the symbol `∗` in the papers; `some false` = 0, `some true` = 1).
  Faces substitute `some ε` for the `i`-th `none`, counting `none`-positions
  in increasing order. Bi-point it with the constant-`some false` and
  constant-`some true` vertices.
- **Serial wedge** `□^∨(n₁,…,n_l)` for a list of *positive* naturals: the
  end-to-end gluing of `□^{n₁}, …, □^{n_l}` identifying the final vertex of
  block `i` with the initial vertex of block `i+1`. Implementation choice is
  yours; two viable encodings:
  (a) positive-dimension cells are `Σ i, (□^{n_i}).cells k` and 0-cells are a
  quotient (only 0-cells need quotienting); or
  (b) a normal-form encoding of 0-cells (interior vertices of each block,
  plus `l+1` junction vertices) avoiding quotients entirely.
  Prefer (b) if the proofs stay manageable. Provide the canonical inclusion
  of each block and the characterization of bi-pointed maps out of a wedge:
  **a bi-pointed map `□^∨(n₁,…,n_l) → K` is the same data as a cube chain in
  `K` of dimension sequence `(n₁,…,n_l)`** (see §4). Prove this equivalence;
  it is the workhorse for §5.

## 4. Cube chains (`Chains/Basic.lean`)

For `K : BPSet`:

```lean
structure CubeChain (K : BPSet) where
  dims    : List ℕ+                         -- dimension sequence, all > 0
  cube    : ∀ i, K.cells (dims.get i)       -- the i-th cube (use your preferred indexing)
  head_eq : vertex⁰ (cube 0) = K.init
  last_eq : vertex¹ (cube last) = K.final
  link    : ∀ i, vertex¹ (cube i) = vertex⁰ (cube (i+1))
```

plus `length c := (c.dims.map (·)).sum` and `dimSeq c := c.dims`.

## 5. The cube chain category (`Chains/Category.lean`)

Objects of `Ch K`: cube chains (equivalently, via §3, bi-pointed maps
`□^∨n → K`). Morphisms `a ⟶ b`: bi-pointed precubical maps
`φ : □^∨(dimSeq a) → □^∨(dimSeq b)` with `b ∘ φ = a` (a commuting triangle
over `K`). Identity and composition are inherited; give `Ch K` a `Category`
instance.

Then **functoriality**, the heart of the routine work:

```lean
def Ch : BPSet ⥤ Cat
```

On objects, `K ↦ Ch K`. On a bi-pointed map `f : K ⟶ L`: post-compose —
a chain in `K` pushes forward to a chain in `L` (all three chain conditions
are preserved because `f` commutes with faces and fixes the endpoints), and
triangle morphisms push forward trivially. Prove the functor laws.

## 6. Side conditions (`Precubical/Altitude.lean`)

- **Altitude function** on `K`: `alt : ∀ n, K.cells n → ℤ` with
  `alt (face ε i c) = alt c + (if ε then 1 else 0)` and (bi-pointed case)
  `alt K.init = 0`. Define `AdmitsAltitude K : Prop`.
- **Accessible**: define the reachability preorder `≼` on all cells generated
  by `face false i c ≼ c` and `c ≼ face true i c`; `K` is accessible when
  every cell `c` satisfies `K.init ≼ c ∧ c ≼ K.final` (suitably stated across
  dimensions).
- **Non-self-linked**: every bi-pointed-irrelevant precubical map
  `□ⁿ → K` is injective (equivalently every cube's canonical map is
  injective). Use the canonical-map formulation: for `c : K.cells n` define
  `canonicalMap c : □ⁿ ⟶ K` (the unique map sending the top cell to `c`;
  construct it) and require injectivity in every dimension.

Routine lemmas to PROVE here (paper: Prop 2.7 and Example 2.6 of
arXiv:2103.05336):
- A connected/accessible `K` admits at most one altitude function.
- Every bi-pointed map preserves altitude functions.
- Altitude of the cubes along a cube chain is strictly increasing;
  consequently `length` is read off the altitude of `K.final`.

## 7. The two lemmas (`Chains/Aut.lean`, `Conjectures.lean`)

**Lifting — prove it (should follow from §5 in a few lines):**

```lean
def Aut.liftToCh (K : BPSet) : Aut K →* Aut (Ch.obj K)
-- i.e. the group homomorphism induced by a functor on automorphism groups;
-- check whether mathlib already has `Functor → Aut →* Aut` glue and use it.
```

**Orientation-preserving (definition, provisional):** an automorphism
`Φ : Ch K ≌ Ch K` (equivalently `Aut (Ch.obj K)`) is *orientation-preserving*
when it preserves dimension sequences: `dimSeq (Φ.obj a) = dimSeq a` for every
chain `a`. Put this definition alone in its own small section with a comment:
**[RESEARCH] this definition is provisional and may need strengthening**
(e.g. compatibility with altitude); keep it isolated so it is easy to revise.

**Lowering — state only, in `Conjectures.lean`:**

```lean
theorem lower_orientationPreserving
    (K : BPSet) (h₁ : NonSelfLinked K) (h₂ : AdmitsAltitude K)
    (h₃ : Accessible K)
    (Φ : Aut (Ch.obj K)) (hΦ : OrientationPreserving Φ) :
    ∃! σ : Aut K, Aut.liftToCh K σ = Φ := sorry  -- [RESEARCH]
```

Also state (all `sorry`, all **[RESEARCH]** unless you find a short proof, in
which case proving them is welcome — they are Lemma 2.11 of arXiv:2103.05336):

```lean
-- (a) Ch K is a poset when K is non-self-linked:
theorem hom_subsingleton (h : NonSelfLinked K) (a b : Ch.obj K) :
    Subsingleton (a ⟶ b) := sorry
-- (b) chains are determined by their (finite multi)set of cubes when K
--     admits an altitude function:
theorem chain_ext_of_altitude (h : AdmitsAltitude K) ... := sorry
-- (c) existence of a morphism a ⟶ b iff every cube of a is a face of some
--     cube of b (non-self-linked + altitude):
theorem hom_iff_facewise ... := sorry
-- (d) faithfulness of the lift for accessible K:
theorem liftToCh_injective (h : Accessible K) :
    Function.Injective (Aut.liftToCh K) := sorry
```

Exact formulations of (b)/(c) are yours to engineer; pick statements that are
actually usable downstream (e.g. (b) as an `ext`-style lemma).

## 8. Sanity checks

Add an `Examples.lean` with:
- `□ⁿ` for small `n`: check `Aut (□²)` contains the axis swap; exhibit the
  unique cube chain of dimension sequence `[2]` and the two of `[1,1]`,
  and a morphism `[1,1] ⟶ [2]` in `Ch (□²)`.
- The interval `□¹`: `Ch (□¹)` has exactly one object and one morphism.
- (Optional, nice to have) the 3×3 subdivided square with the center 2-cell
  removed, bi-pointed at opposite corners: check it admits an altitude
  function and is non-self-linked, and exhibit two chains with no common
  upper bound (the two dihomotopy classes).

## 9. Non-goals

- No geometric realization, no topology, no d-spaces, no nerve, no homotopy
  theory of any kind. The bridge to `\vec{P}(K)` stays on paper.
- No attempt at the lowering proof, the poset lemmas, or anything tagged
  **[RESEARCH]** beyond stating them, unless a proof is genuinely short.
- No labels/HDA structure, no degeneracies, no symmetric/transverse variants.

## 10. Working style

- Small commits per milestone (§1 → §8), each building cleanly.
- When an index convention forces a choice, document it in `DESIGN.md` with a
  one-line justification and the paper equation it matches.
- Prefer explicit structures over heavy abstraction; this code is a substrate
  for research, and I will be reading and extending every definition.
