# Cube chains and the braid arrangement: formalization guide (v3)

Goal: extend this library the with 

```
Main theorem :  Ch(Z)_n  ≌  (Sal₀Br n // Perm (Fin n))ᵒᵖ        (iso of categories)
Nerve theorem:  nerve (Ch(Z)_n) ≅ (nerve ((Sal₀Br n)ᵒᵖ)) / Perm (Fin n)
Supporting   :  N (P // G) ≅ (N P) / G   for order-free actions on posets
```
where Z is the terminal BPSet and `n` is a grading by path length. We'll be working in 

Note that we care about the definitions here, and you should not change the definitions, or the goal lemmas.
But, we don't really care about the particular proof used. If you need to modify the proofs, just report that
at the end.

---

| structure | direction |
|---|---|
| `Ch Z` morphisms | finer dims → coarser dims |
| `Sal₀Br` order `⪯` (Paris) | deeper/coarser pair `⪯` shallower/finer pair; chamber pairs **maximal** |
| the functor Φ | contravariant-looking: lands in `(Sal₀Br // Perm)ᵒᵖ`; keep the op explicit |

`Perm (Fin n)` acts on level functions by `σ • f := f ∘ σ⁻¹`; with mathlib's
`mul_smul` this is a left action. Pin the direction with the n = 2 test.

---

## Step 0. Scaffold

Work in the new FinalPrecubical folder to build the modules for
`QuotientCat.lean`, `Salvetti.lean`, `Ev.lean`, `MainFunctor.lean`,
`NerveQuot.lean`, `Tests.lean`.
---

## Step 1. The quotient `P // G` (`QuotientCat.lean`)

For `[Group G] [PartialOrder P] [MulAction G P]` with

```lean
class OrderFreeAction (G P) ... : Prop where
  smul_le_smul_iff  : ∀ (g : G) {x y : P}, g • x ≤ g • y ↔ x ≤ y
  eq_one_of_le_smul : ∀ (g : G) (x : P), x ≤ g • x → g = 1
```

(the second implies freeness `g • x = x → g = 1`; derive, don't assume).

`P // G`:
- objects `Quotient (MulAction.orbitRel G P)`;
- `Hom X Y :=` diagonal-`G` quotient of
  `{p : P × P // p.1 ≤ p.2 ∧ ⟦p.1⟧ = X ∧ ⟦p.2⟧ = Y}`;
- **alignment**: `∀ b c, ⟦b⟧ = ⟦c⟧ → ∃! g, g • c = b`; composition of
  `⟦(a,b)⟧`, `⟦(c,d)⟧` is `⟦(a, (align …) • d)⟧` via `Quotient.lift₂`;
  well-definedness and associativity reduce to the uniqueness half.
- **Workhorse** (used in Steps 4 and 5): fixed-source representatives,
  `homEquivUpSet (a : P) Y : (⟦a⟧ ⟶ Y) ≃ {b : P // a ≤ b ∧ ⟦b⟧ = Y}`.

---

## Step 2. `Sal₀Br` (`Salvetti.lean`)

Faces of the braid arrangement in **level-function** coordinates:

```lean
structure BrFace (n : ℕ) where
  levels : ℕ
  f      : Fin n → Fin levels
  surj   : Function.Surjective f
```

- Face order: `F ⪯ F' ↔ ∃ m, Monotone m ∧ F.f = m ∘ F'.f`
  (witness unique and surjective — prove both).
- `IsChamber F := F.levels = n` (then `F.f` bijective).
- Adjacency to a chamber: `F ⪯ C ↔ ∀ a b, F.f a < F.f b → C.f a < C.f b`.

```lean
structure Sal₀Br (n : ℕ) where
  F : BrFace n
  C : BrFace n
  hC : IsChamber C
  adj : F ⪯ C
```

Order (Paris §3.1 transcribed): `(F,C) ⪯ (F',C') ↔ F ⪯ F' ∧
∀ a b, F'.f a = F'.f b → (C.f a < C.f b ↔ C'.f a < C'.f b)`.
`PartialOrder` hints — transitivity: ties in `F''` are ties in `F'` through
the merging witness; antisymmetry: equal `levels` + monotone surjection
`Fin k → Fin k = id` gives `F = F'`, then cross-level comparisons come from
`F` and within-level ones agree, so `C = C'`.

Action `σ • (F, C) := ⟨F.f ∘ σ⁻¹, C.f ∘ σ⁻¹⟩`; prove `OrderFreeAction`
(invariance of the conditions; `eq_one_of_le_smul` by the antisymmetry
argument on the orbit, ending with injectivity of `C.f`).

Standard representatives (used by the main functor):
- `stdFace (A : List ℕ+) : BrFace |A|` — `levels := A.length`, `f :=`
  "index of the block containing this coordinate" ;
- `stdChamber : BrFace n` — `levels := n`, `f := id`;
- `stdPair A : Sal₀Br |A|` — adjacency is `Monotone (stdFace A).f`-style,
  one line.
- Orbit lemma: every element is `σ • stdPair A` for a unique `σ` and unique
  `A` (σ := `C.f` read as a permutation; `A` := the level sizes of `F`).

---

## Step 3. Event tracking (`Ev.lean`)

The morphism analyzer for `Ch Z`. Global coordinates ("events") of
`serialWedge A` are `Fin |A|` in serial order (`|A| :=` dims-sum; reuse the
repo's). For a bipointed map `g : serialWedge A ⟶ serialWedge B`, the `i`-th
top cube maps to a face of the `jᵢ`-th top cube of the target; its
coordinates correspond, in order, to the star positions of that face.

```lean
def ev (g : serialWedge A ⟶ serialWedge B) : Fin |A| → Fin |B|
theorem ev_id   : ev (𝟙 _) = id
theorem ev_comp : ev (g ≫ h) = ev h ∘ ev g
```

**Search the library first** — if any coordinate/direction tracking for
wedge maps exists, `ev` wraps it. Otherwise build from the action on top
cubes; `ev_comp` is by the substitution normal form (composition
substitutes codes into star positions; tracking through a substitution is
composition of trackings) — an induction on positions, and the largest
single proof in the project. Then:

1. `ev_bijective` — altitude bookkeeping: `alt (start (g u_i)) = sizeUpTo i`
   forces target blocks weakly increasing, and the star sets over a fixed
   target block partition it. Package as `evPerm g : Fin |A| ≃ Fin |B|`.
2. `ev_strictMonoOn` — strictly increasing on each source block (star
   positions are read in order).
3. `ev_blocks` — the image of the source blocks over a target segment is
   exactly that target block (the partition statement).
4. **Reconstruction**: `g` is determined by `ev g`, and every equivalence
   satisfying (2), (3) arises (coordinate `p` of the face is `1` if `p` is
   the image of an earlier event of the same target block, `0` if later,
   `*` if current). Gives injectivity and the image characterization in one
   lemma. This predicate — an equivalence satisfying (2) and (3) — is PZ's
   Definition 6.11; keep the cross-reference as a doc-comment only.

---

## Step 4. The main functor (`MainFunctor.lean`)

Objects of `Ch Z`: a bipointed map `serialWedge A ⟶ Z` exists and is unique
(terminality — likely already in the library), so `(Ch Z).Obj ≃ List ℕ+`
and morphisms are *all* bipointed wedge maps. Work per grade `n`
(`ChZ n :=` full subcategory on `|A| = n`).

```lean
def Φ : (ChZ n) ⥤ (Sal₀Br n // Perm (Fin n))ᵒᵖ where
  obj A := ⟦stdPair A⟧
  map (g : A ⟶ B) := ⟦(stdPair B, (evPerm g) • stdPair A)⟧   -- as an op-morphism
```

- **Well-definedness** (one condition lemma): `stdPair B ⪯ (evPerm g) • stdPair A`.
  Unfolds to exactly `ev_strictMonoOn` (gives the tie-agreement clause) and
  `ev_blocks` (gives the face relation). Adjacency of the twisted pair is
  *free*: the action preserves adjacency and `stdPair A` is adjacent.
- **Functoriality**: the aligning element between the two representatives
  at the middle object is `evPerm h` itself (uniqueness half of alignment),
  so the composite is `⟦(stdPair C, (evPerm h) • ((evPerm g) • stdPair A))⟧`,
  and the claim is `ev_comp` + `mul_smul`. No transport lemma: the
  face/chamber bookkeeping is absorbed by the `MulAction` axioms.
- **Fully faithful**: `homEquivUpSet (stdPair B)` identifies quotient homs
  with `{σ // stdPair B ⪯ σ • stdPair A}` (freeness makes σ unique per
  element of the up-set orbit); the reconstruction lemma of Step 3 says
  `evPerm` is a bijection onto that set.
- **Bijective on objects**: the orbit lemma of Step 2.

Conclude an isomorphism of categories (object bijection + fully faithful),
stated per grade; assemble over `n` only if the repo wants a total form.

**Generalization hook (doc-comment, no code):** for any `K`, define
`Φ_K := Ch(! : K ⟶ Z) ⋙ Φ`. This is the universal comparison; it is an
isomorphism exactly for `K = Z`, a discrete fibration in general. Do not
build per-`K` arrangements in this phase.

---

## Step 5. Nerve quotient (`NerveQuot.lean`)

Mathlib nerve: `CategoryTheory.nerve C : SSet` with `m`-simplices
`CategoryTheory.ComposableArrows C m` — learn that API first (`mk₀`,
`precomp`, extensionality). `G`-action on `nerve P` **by functoriality of
`nerve`** applied to the action's order-iso functors. Quotient simplicial
set: check for existing levelwise-quotient machinery; else
`(N P / G) m := Quotient (MulAction.orbitRel G (ComposableArrows P m))`
with faces/degeneracies descending (~20 lines).

Comparison `θ : (N P)/G ⟶ N (P // G)` induced by the quotient functor
(levelwise `G`-invariant). **Unique chain lifting**: a simplex of
`N (P // G)` with a chosen representative of its initial vertex lifts
uniquely (induction along the chain; the step is `homEquivUpSet`);
degenerates lift to degenerates by uniqueness. Hence `θ` is levelwise
bijective: an isomorphism of simplicial sets.

Assembly: `Φ` is an isomorphism of categories, so `nerve Φ` is an
isomorphism of simplicial sets; compose with `θ` for
`nerve (ChZ n) ≅ (nerve ((Sal₀Br n)ᵒᵖ)) / Perm (Fin n)`.
Leave `nerve (Pᵒᵖ)` as written — no simplicial reversal in this phase.

---

## Working agreements

- One milestone per commit; each builds; `sorry` only mid-iteration.
- Extend `Tests.lean` after each milestone with the tables above.
- Prefer existing lemmas: repo docs first; mathlib surface:
  `Equiv`/`Equiv.Perm`, `MulAction`
  (`orbitRel`, `mul_smul`), `StrictMonoOn`,
  `Finset.orderIsoOfFin`/`orderEmbOfFin`, `Quotient`,
  `CategoryTheory.nerve`, `CategoryTheory.ComposableArrows`.
  `exact?`/Loogle when a name is stale.
- No topology, no realization, no axioms in this phase.