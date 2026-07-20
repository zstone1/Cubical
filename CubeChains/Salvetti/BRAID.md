# The braiding is created, not inherited

Why there is a braid group in here at all, and where it comes from.

## 1. `(GeoBP, ⊗ᵍ)` has no swap — not a braiding, not a symmetry

`Box` is strict monoidal: `▫m ⊗ ▫n = ▫(m+n)`, morphisms (sign vectors) concatenating. Day
convolution transports this to presheaves (`Foundations/DayTensor`, `GeoTensor/BP`), giving the
**parallel composition** `(K ⊗ᵍ L)_n = ⊕_{p+q=n} K_p × L_q`, with `□m ⊗ᵍ □n ≅ □(m+n)`, bi-pointed by
`init := (init, init)`, `final := (final, final)`. (It lives on the alias `GeoBP := BPSet` because
bare `⊗` on `BPSet` is the wedge.)

*Proof that there is no swap.* A braiding on representables is a presheaf map `□^{m+n} ⟶ □^{m+n}`,
i.e. by cube Yoneda a `Box` endomorphism. `Box` is **rigid** (`Aut ▫k = {id}` — the symmetry-free
convention), so only `id` is available; and `id` is not natural, because `f ⊗ 1` inserts fixed
coordinates in the *first* block while `1 ⊗ f` inserts them in the *last*. ∎

> **So the braiding is created by the passage to executions, not inherited from `BPSet`.** That is
> the whole content of the braid thread.

The same point from the other end: `Z`, the terminal precubical set (`Foundations/Terminal`), has
one cell in each dimension — its events are **unlabelled**. Refining its square into a path can be
done two ways, and those two parallel arrows *are* the braid generator. `□ⁿ`'s cubes are rigid and
labelled, so the two ways become two distinct *objects* and the chain category collapses. Labelling
is exactly what turns `Bₙ` into `Pₙ`.

## 2. `ConcGrpd`, the execution groupoid

```
ConcCat  K := Int(Lines K)                 -- a chain + a run: an interleaving of its beads' edges
ConcGrpd K := FreeGroupoid (ConcCat K)     -- groupoidification
```

`Lines K : (Ch K)ᵒᵖ ⥤ Type` is the run presheaf (`Salvetti/Runs`); `Int(Lines K)` its category of
elements. mathlib's `FreeGroupoid` is the free groupoid **on a category** — it carries
`instance : (of C).IsLocalization ⊤` — so it *is* `C[all morphisms⁻¹]`, which by Gabriel–Zisman is
`Π₁(|N C|)`. No topology is needed to define anything.

Over a wedge the executions split, `Int(Lines(P ∨ Q)) ≌ Int(Lines P) × Int(Lines Q)`, so a
`d`-dimensional bead contributes its own `d` concurrent events, and they braid. The vertex groups
are block-diagonal **pure** braids; non-pure braids arise only from **global** event monodromy (the
terminal five-lemma). `ConcGrpd` and everything downstream of it live on `main`, not in this tree;
`Salvetti/BraidIso` is where the thread stops here, at `Sal(braidCOM n) ≌ Int(Lines(□ⁿ))`.

## 3. Why `β² ≠ 𝟙`

Independent actions do not commute — they braid. The two interleavings of a pair of concurrent
events are isomorphic, not equal, and the isomorphism has a winding number. The smallest instance is
`ConcBraid(□²) ≅ P₂ = ℤ`: the generator winds once around the tie locus `t_e = t_f` in complexified
time, and doing the interchange twice is the full twist, not the identity.

> **Mazurkiewicz was wrong to write `ef = fe`.** Trace theory is the `π₀` shadow; the pure braid
> group of a `d`-bead is the `π₁`.

## 4. Why a braiding had to be here

A schedule is a point of `ℝ^(events)`; the concurrency space is the **complexified** complement of
the braid arrangement (`Arrangements/BraidGeometry`), locally `∏ᵢ F(ℂ, dᵢ)`. Configuration spaces of
`ℂ` carry the little-2-disks operad, and an `E₂`-algebra in `Cat` is a braided monoidal category
(Joyal–Street). That is why the target is braids and not permutations.
