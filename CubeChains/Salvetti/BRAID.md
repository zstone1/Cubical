# The concurrency braid category

> ## ⚠ SUPERSEDED — the construction below was never built
>
> The object `G K := ⨆ₙ ConcGrpd (K^⊗n) ⋊ Sₙ` in §0 **does not exist in this repo**. There is no
> semidirect product, no tensor power `K^⊗n`, and no `Sₙ`-action on `ConcCat (K^⊗n)` anywhere in
> the code. That route was abandoned.
>
> What was actually built grades by **event count inside one `K`**, not by `n` parallel copies of
> `K`: `ConcCatN K n` (`Salvetti/BraidFunctor.lean`), and `braidFunctor K n : ConcGrpdN K n ⥤
> BraidGrpd n`. The §7 status table below is also wrong — it marks the Day-convolution tensor as
> "in progress", but it is done (`Foundations/{BoxMonoidal,DayTensor,BPTensor}.lean`).
>
> **The accurate account is `BRAID_ENRICHMENT_CLEANUP.md` (repo root).** Read that instead.
> Kept only for §1 (no swap on `PrecubicalSet`), §4 (independent actions braid), §5 (what is *not*
> monoidal), and §6 (the `E₂` argument + the machine-verified Betti data).

## 0. The statement

For every bi-pointed precubical set `K` there is a **braided, non-symmetric** monoidal category
`G K`.  It is functorial in `K`, and `G (□¹)` — one action — is the classical braid category.

```
G : BPSet ⟶ BrMonCat            G K  :=  ⨆_{n ≥ 0}  ConcGrpd (K^⊗n) ⋊ Sₙ
```

* **objects** `(n, x)`: a run of `n` parallel copies of `K`;
* **morphisms** `(σ, γ)`: `σ ∈ Sₙ` permutes the copies, `γ` is a braid of the events;
* **tensor** `(n,x) ⊗ (m,y) := (n+m, x·y)` — put the copies side by side;
* **braiding** `β`: let the second block of copies overtake the first;
* **not symmetric**: `β² =` the full twist `≠ 𝟙`.

`ConcGrpd K` is the one-strand part `n = 1`, so `ConcGrpd K ⊆ G K`.  Three warnings, discharged
below: `ConcGrpd K` is **not** monoidal (§5); `(BPSet, ⊗)` is **not** braided (§1); and `G` is **not**
a monoidal functor (§5).  None of these is a defect — each is the reason the construction is not
vacuous.

## 1. `⊗`, and why it has no swap

`Box` is strict monoidal: `▫m ⊗ ▫n = ▫(m+n)`, with morphisms (sign vectors) concatenating.  Day
convolution transports this to presheaves, giving the **parallel composition** of precubical sets,
`(K ⊗ L)_n = ⊕_{p+q=n} K_p × L_q`, with `□m ⊗ □n ≅ □(m+n)`.  Bi-point it by
`init := (init, init)`, `final := (final, final)`.

> **`(PrecubicalSet, ⊗)` has no swap at all — not a braiding, not a symmetry.**

*Proof.*  A braiding on representables is a presheaf map `□^{m+n} ⟶ □^{m+n}`, i.e. by Yoneda a `Box`
endomorphism.  `Box` is **rigid** (`Aut ▫k = {id}` — the symmetry-free convention), so only `id` is
available; and `id` is not natural, because `f ⊗ 1` inserts fixed coordinates in the *first* block
while `1 ⊗ f` inserts them in the *last*.  ∎

Bi-pointing is irrelevant: the obstruction is in `Box`.  **So the braiding below is created by the
passage to schedules, not inherited from `BPSet`.**  That is the whole content.

**But the transposition acts one level up.**  `τ : K ⊗ L ⟶ L ⊗ K` is not a precubical map, yet it
*does* induce an equivalence

```
τ_{K,L} :  ConcCat (K ⊗ L)  ≌  ConcCat (L ⊗ K)
```

because it is a dimension-preserving relabelling *inside each bead*: it carries chains to chains,
refinements to refinements, chambers to chambers.  This is what makes `Sₙ` act on `ConcCat (K^⊗n)`
by permuting the copies — an action that does **not** exist on `K^⊗n` in `BPSet`.  `G` is built on
exactly this gap.

## 2. `ConcGrpd`

```
ConcCat  K := (Lines K).Elements          -- Int(Lines K): a chain + a total order of each bead's events
ConcGrpd K := FreeGroupoid (ConcCat K)    -- groupoidification
```

mathlib's `FreeGroupoid` is the free groupoid **on a category** — it carries
`instance : (of C).IsLocalization ⊤` — so it *is* `C[all morphisms⁻¹]`, which by Gabriel–Zisman *is*
`Π₁(|N C|)`.  No topology is needed to define anything here.

Local model (**proved**, `FreeGroupoidProd.lean`): `ConcGrpd (⋁dims) ≌ ∏ᵢ FreeGroupoid (Sal (braidCOM dᵢ))`
— **one pure braid group `P_{dᵢ}` per bead**.  A `d`-dimensional bead is `d` concurrent events, and
they braid.

## 3. `G K` and its braiding

Fix `K`.  For each `n`, `Sₙ` acts on `ConcCat (K^⊗n)` by permuting the tensor factors (§1), hence on
`ConcGrpd (K^⊗n)`.  Set

```
G K  :=  ⨆_{n ≥ 0}  ConcGrpd (K^⊗n) ⋊ Sₙ

Obj      (n, x)                     x an object of ConcGrpd (K^⊗n)
Hom      (n,x) ⟶ (n,y)  =  { (σ, γ) | σ ∈ Sₙ ,  γ : σ·x ⟶ y in ConcGrpd (K^⊗n) }
                           ( empty between different n )
```

**Tensor.**  `(n,x) ⊗ (m,y) := (n+m, x·y)`, where `x·y` is the run of `K^⊗(n+m)` that runs `x` on the
first `n` copies (holding the rest at `init`) and then `y` on the last `m`.  Concretely its beads are
`(xᵢ, init)` followed by `(final, yⱼ)`.  On morphisms: block sum `Sₙ × Sₘ → S_{n+m}` and
juxtaposition of braids.  Unit `(0, ·)`.  Strictly associative (list concatenation), so **no
coherence isomorphisms to prove**.

**Braiding.**  `y·x` — beads `(init, yⱼ)` then `(xᵢ, final)` — is a run of the **same** `K^⊗(n+m)`.
So put

```
β_{(n,x),(m,y)}  :=  ( s_{n,m} ∈ S_{n+m} ,  the positive half-twist  x·y ⟶ y·x  in ConcGrpd (K^⊗(n+m)) )
```

where `s_{n,m}` is the block transposition of the copies and the half-twist crosses, in the positive
direction, exactly the walls separating the two blocks of events.  This needs no cube, no coordinate
choice, and no case analysis on `K`.

## 4. Not symmetric

`β_{Y,X} ∘ β_{X,Y}` has underlying permutation `s² = id`, so it is **pure**: an element of
`ConcGrpd (K^⊗(n+m))`.  It is the **full twist** of the two blocks, and it is not the identity.

The proof is uniform, and is **already in the repo** (`Salvetti/Braiding.lean`, sorry-free):

```
salCross a b  :=  #{ e | a.tope e ≠ b.tope e }                    -- wall-crossing number
salCross_add  :  a ≤ b → b ≤ c → salCross a c = salCross a b + salCross b c
salWind (L : COM E) [Fintype E] : Sal L ⥤ SingleObj (Multiplicative ℤ)
```

Additivity holds because once a coordinate is fixed by `b.face` it stays fixed in `c.face`, so a
separating wall is crossed *exactly once*.  Hence `salWind` is a functor **for any COM with a finite
ground set** — and the local COM at any chain of any `K` is a `braidDirectSum`, so this is not a cube
lemma.  Lifting `salWind` through `FreeGroupoid.lift` gives a winding-number homomorphism out of
`π₁(Sal L)`; the two half-twists cross the separating walls oppositely, so `β²` is sent to
`ofAdd (2N) ≠ 1`.

Smallest instance, proved: `concBraid ≫ concBraid' ≠ 𝟙` in `ConcGrpd (□²)` — the 4-cycle of the
bipartite poset `Int(Lines(□²))`, i.e. the generator of `π₁(Sal (braidCOM 2)) = P₂ = ℤ`, the winding
around the tie locus `t_e = t_f` in complexified time.

> **Mazurkiewicz was wrong to write `ef = fe`.**  Independent actions do not commute — they *braid*.
> The two interleavings are isomorphic, not equal, and the isomorphism has a winding number.  Trace
> theory is the `π₀` shadow of `G K`; the pure braid group of a `d`-bead is the `π₁`.

## 5. What is *not* monoidal, and why that is the point

**`ConcGrpd K` is not monoidal.**  There is no tensor: two objects of `ConcGrpd K` are two *complete*
executions of `K`, and `K` has nowhere to run them in parallel.  This is exactly what `G` repairs, by
freely adjoining the copies.

**`G` is not a monoidal functor.**  `G K × G L ⟶ G (K ⊗ L)` would have to send (`n` copies of `K`,
`m` copies of `L`) to some number of copies of `K ⊗ L`, and there is no such matching.  `G` is a
*free* construction (§6), and free functors are left adjoints, not monoidal functors.

**What *is* lax monoidal is `ConcGrpd` itself:**

```
ConcGrpd : (BPSet, ⊗, □⁰) ⟶ (Grpd, ×)      μ_{K,L} : ConcGrpd K × ConcGrpd L ⥤ ConcGrpd (K ⊗ L)
```

(`(x,y) ↦ x·y`.)  So the two facts sit on opposite sides and do not combine: the lax monoidal functor
has non-monoidal values; the functor with braided monoidal values is not monoidal.  Calling
`ConcGrpd` a "braided monoidal functor" is meaningless — there is no braiding on `(BPSet, ⊗)` for it
to preserve.

**The one global braided category.**  Assembling all `K` at once gives the Grothendieck construction
`∫ConcGrpd`, and it *is* braided monoidal once the base is given its transposition — i.e. over the
base `𝓗` of **action-labelled** HDAs (name cube directions by actions instead of numbering them; then
`Box` gains the block swap and `(𝓗, ⊗)` is *symmetric*).  Then:

| | total (braided) | base (symmetric) | fibre (pure) |
|---|---|---|---|
| classical | braid category `ℬ` | symmetric groupoid `Σ` | `P_n` |
| here | `∫ConcGrpd` | `𝓗` | `ConcGrpd K` |

The projection `∫ConcGrpd ⟶ 𝓗` is strict monoidal and sends `β ↦ τ`.  Downstairs `τ² = id`; upstairs
`β² ≠ 𝟙`.  **That projection is the passage from executions to Mazurkiewicz traces**, and the winding
is exactly what it discards.  `G K` is the braided monoidal subcategory of `∫ConcGrpd` generated by
`K`.

## 6. Why a braiding had to be here

The braiding comes from `ℂ`.  A schedule is a point of `ℝ^(events)`; the concurrency space is the
*complexified* complement of the braid arrangement, locally `∏ᵢ F(ℂ, dᵢ)`.  Configuration spaces of
`ℂ` carry the little-2-disks operad, so `⨆_n` of them is an `E₂`-algebra — and `E₂`-algebra in `Cat`
= braided monoidal category (Joyal–Street).  `G K` is the free `E₂`-algebra on `K`; `G (□¹)` is the
free `E₂`-algebra on a point, which is the braid category.

Machine-verified (`Testing/ConcSpace.lean`, `native_decide`): `Int(Lines(□ⁿ))` reproduces `F(ℂ,n)` on
the nose — Betti numbers `[1,1]`, `[1,3,2]`, `[1,6,11,6]` for `n = 2,3,4`, the coefficients of
`∏_{k<n}(1+kt)`; cell counts `n!·2^{n−1}`, the Salvetti cells of `A_{n−1}`.

## 7. Status

| piece | status |
|---|---|
| `ConcCat`, `ConcGrpd`, `freeGroupoidCongr` | ✅ `Salvetti/ConcGroupoid.lean` |
| `ConcGrpd (⋁dims) ≌ ∏ᵢ FreeGroupoid (Sal (braidCOM dᵢ))` | ✅ `Salvetti/FreeGroupoidProd.lean` |
| `salCross` / `salWind` (any finite-ground COM) | ✅ `Salvetti/Braiding.lean` |
| `β² ≠ 𝟙` for `□²` | ✅ `Salvetti/Braiding.lean` (`concBraid_comp_ne_id`) |
| `⊗` on `BPSet` (Day convolution along `Box`) | 🚧 in progress |
| `x·y`, `y·x` : the two serial runs of `K ⊗ L` | 🚧 |
| `τ` and the `Sₙ`-action on `ConcCat (K^⊗n)` | 🚧 |
| `G K` braided monoidal; `β² ≠ 𝟙` for general `K` | 🚧 — the `salWind` proof should transfer verbatim |
| asphericity of the concurrency space (`K(π,1)`) | ❓ open; local pieces are `K(π,1)` free (Fadell–Neuwirth), the global question is the arrangement `K(π,1)` conjecture transplanted |
