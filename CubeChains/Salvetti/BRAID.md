# The braiding is created, not inherited

Why there is a braid group in here at all, and where it comes from.

**The result itself is not here.** `BRAID_ENRICHMENT.md` (repo root) is the account of `CFund`/`Fund`,
the braid grading, and what forgetting the line loses. This file holds only the four facts that
explain *why the target is braids* — and a warning about a construction that was abandoned (§5).

---

## 1. `(PrecubicalSet, ⊗)` has no swap — not a braiding, not a symmetry

`Box` is strict monoidal: `▫m ⊗ ▫n = ▫(m+n)`, morphisms (sign vectors) concatenating. Day convolution
transports this to presheaves, giving the **parallel composition** `(K ⊗ L)_n = ⊕_{p+q=n} K_p × L_q`,
with `□m ⊗ □n ≅ □(m+n)`. Bi-point by `init := (init, init)`, `final := (final, final)`.

*Proof that there is no swap.* A braiding on representables is a presheaf map `□^{m+n} ⟶ □^{m+n}`,
i.e. by Yoneda a `Box` endomorphism. `Box` is **rigid** (`Aut ▫k = {id}` — the symmetry-free
convention), so only `id` is available; and `id` is not natural, because `f ⊗ 1` inserts fixed
coordinates in the *first* block while `1 ⊗ f` inserts them in the *last*. ∎

Bi-pointing is irrelevant: the obstruction lives in `Box`.

> **So the braiding is created by the passage to executions, not inherited from `BPSet`.** That is the
> whole content of the braid thread.

The same point, from the other end: `Z`, the *terminal* precubical set, has one cell in each
dimension — its events are **unlabelled**. Refining its square into a path can be done two ways, and
those two parallel arrows *are* the braid generator. `□ⁿ`'s cubes are rigid and labelled, so the two
ways become two distinct *objects* and the chain category collapses. Labelling is exactly what turns
`Bₙ` into `Pₙ`.

## 2. `ConcGrpd`, and the local model

```
ConcCat  K := (Lines K).Elements          -- Int(Lines K): a chain + a total order of each bead's events
ConcGrpd K := FreeGroupoid (ConcCat K)    -- groupoidification
```

mathlib's `FreeGroupoid` is the free groupoid **on a category** — it carries
`instance : (of C).IsLocalization ⊤` — so it *is* `C[all morphisms⁻¹]`, which by Gabriel–Zisman *is*
`Π₁(|N C|)`. No topology is needed to define anything.

Local model (`concWedgeSerialEquiv`, `Salvetti/FreeGroupoidProd.lean`):
`ConcGrpd (⋁dims) ≌ ∏ᵢ FreeGroupoid (Sal (braidCOM dᵢ))` — **one pure braid group `P_{dᵢ}` per bead**.
A `d`-dimensional bead is `d` concurrent events, and they braid.

⚠ This equivalence goes through `freeGroupoidProdEquiv = Localization.uniq`, so it is pinned only up
to natural iso. Fine for *identifying* the vertex groups; useless for anything that needs a strict
equality (which is why the enrichment's composition is built with `lift₂` instead — `Flow/Flow.lean`).

Note what this says: the vertex groups over a wedge are `∏ᵢ P_{dᵢ}`, the block-diagonal **pure**
subgroup of `Bₙ`. Non-pure braids never arise locally — they come only from **global** event
monodromy.

## 3. The winding cocycle, and why `β² ≠ 𝟙`

`Salvetti/Braiding.lean` (sorry-free):

```
salCross a b     :=  #{ e | a.tope e ≠ b.tope e }               -- the wall-crossing NUMBER
salCrossVec a b  :   E → ℤ                                      -- WHICH walls; salCross is its sum
salCross_add     :   a ≤ b → b ≤ c → salCross a c = salCross a b + salCross b c
salWind (L : COM E) [Fintype E] : Sal L ⥤ SingleObj (Multiplicative ℤ)
```

Additivity holds because once a coordinate is fixed by `b.face` it stays fixed in `c.face`
(`tope_eq_of_cross`), so a separating wall is crossed **exactly once**. Hence `salWind` is a functor
for *any* COM with a finite ground set — and the local COM at any chain of any `K` is a
`braidDirectSum`, so this is not a cube lemma. Lifting through `FreeGroupoid.lift` gives a
winding-number homomorphism.

For the braid arrangement a **wall is a pair of events**, so `salCrossVec` is the vector of pairwise
linking numbers and `salCross` is its sum — which is why `writhe` (the abelianisation of `Bₙ`, a single
`ℤ`) is strictly coarser than the pure-braid data (`Pₙ` abelianises to `ℤ^{n(n−1)/2}`).

Smallest instance, proved: `concBraid ≫ concBraid' ≠ 𝟙` in `ConcGrpd (□²)` — the 4-cycle of the
bipartite poset `Int(Lines(□²))`, i.e. the generator of `π₁(Sal (braidCOM 2)) = P₂ = ℤ`, the winding
around the tie locus `t_e = t_f` in complexified time.

> **Mazurkiewicz was wrong to write `ef = fe`.** Independent actions do not commute — they *braid*.
> The two interleavings are isomorphic, not equal, and the isomorphism has a winding number. Trace
> theory is the `π₀` shadow; the pure braid group of a `d`-bead is the `π₁`.

## 4. Why a braiding had to be here

The braiding comes from `ℂ`. A schedule is a point of `ℝ^(events)`; the concurrency space is the
**complexified** complement of the braid arrangement, locally `∏ᵢ F(ℂ, dᵢ)`. Configuration spaces of
`ℂ` carry the little-2-disks operad, and an `E₂`-algebra in `Cat` is a braided monoidal category
(Joyal–Street). That is the reason the target is braids and not permutations.

Machine-verified (`Testing/ConcSpace.lean`, `native_decide`): `Int(Lines(□ⁿ))` reproduces `F(ℂ,n)` on
the nose — Betti numbers `[1,1]`, `[1,3,2]`, `[1,6,11,6]` for `n = 2,3,4`, the coefficients of
`∏_{k<n}(1+kt)`; cell counts `n!·2^{n−1}`, the Salvetti cells of `A_{n−1}`.

## 5. ⛔ Abandoned — do not resurrect

An earlier version of this file announced

```
G : BPSet ⟶ BrMonCat            G K := ⨆_{n ≥ 0}  ConcGrpd (K^⊗n) ⋊ Sₙ
```

with `Sₙ` permuting `n` parallel copies of `K`, a block-transposition braiding, and `G K` as the free
`E₂`-algebra on `K`. **None of it exists in the repo**: there is no semidirect product, no tensor power
`K^⊗n`, no `Sₙ`-action on `ConcCat (K^⊗n)`, and no `∫ConcGrpd`. That route was abandoned.

What was built instead grades by **event count inside one `K`** — `ConcCatN K n`, and the graded functor
`braidGrading K : Int(Lines K) ⥤ 𝔅` (`Braid/Grading.lean`). The braid target is the **Garside germ**
category (`Braid/Germ.lean`), which is already a groupoid.

Two claims from that version are worth keeping as warnings:

- **`ConcGrpd K` is not monoidal.** Two objects are two *complete* executions of `K`, and `K` has
  nowhere to run them in parallel. So "`ConcGrpd` is a braided monoidal functor" is meaningless —
  there is no braiding on `(BPSet, ⊗)` for it to preserve (§1).
- **The composition-to-tensor statement is about the delooping, not about `ConcGrpd`.** It says
  concatenating executions **adds strand counts**, and it needs the delooping as an
  `EnrichedCategory Cat` on one object with hom-object `Braids`. `Salvetti/BraidDeloop`'s version
  cannot serve: its composition goes through `freeGroupoidProdEquiv = Localization.uniq`, so it is
  pinned only up to natural iso and can never satisfy an equality-of-functors `assoc`.
