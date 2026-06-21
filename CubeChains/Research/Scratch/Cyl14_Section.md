# Cyl14_Section — weakening the cylinder's left leg: "equivalence" → "has a section"

**Status at a glance.**

- **Part A (section construction + equiv⟹section + non-vacuity): PROMOTION-READY.** Fully landed,
  sorry-free, green; depends only on `propext`/`Classical.choice`/`Quot.sound` (no `sorryAx`).
- **Part B (composition closure): mostly landed.** Sections compose ✓ (proven). Sections pull back
  ✓ (proven, at the precubical level, unconditionally — no right-properness). The d-path descent
  (precubical section → groupoid-functor `DPathSection`) is **isolated** as a single labelled `Prop`
  `DPathDescent` (NOT a sorry presented as proven); the closure conclusion is proven *modulo* it.

Build: `lake build CubeChains.Research.Scratch.Cyl14_Section` (decoupled from the green library).
File: `CubeChains/Research/Scratch/Cyl14_Section.lean`.

---

## The question

`cylToPointedObj` (`Cylinder/CylinderRefine.lean`) is built from a `CylMapWeqR K` object — a
cylinder whose left leg-functor `Lgrpd : DPathGrpdR src ⥤ DPathGrpdR K` is required to be a full
**equivalence**. But inspecting the construction shows it only ever consumes the single datum

```
(Lgrpd.inv ,  counitIso.inv : 𝟭 ⟹ Lgrpd.inv ⋙ Lgrpd)
```

It never touches the *other* composite `Lgrpd ⋙ Lgrpd.inv ≅ 𝟭`, nor the triangle identities. So
the hypothesis can be weakened from "`Lgrpd` is an equivalence" to "`Lgrpd` **has a section up to
iso**":

```
DPathSection F  :=  (Lstar : D ⥤ C ,  unit : 𝟭_D ≅ Lstar ⋙ F)
```

This is **strictly weaker** than an equivalence, even between groupoids: a *full adjunction*
between groupoids is forced to be an equivalence (its unit & counit become isos), so adjunction
would be the wrong weakening — a one-sided section is the right one, and it imposes no such collapse.

---

## Part A — the section-based construction (PROVEN, promotion-ready)

| Lean name | Statement | Status |
|---|---|---|
| `DPathSection F` | the datum `(Lstar : D ⥤ C, unit : 𝟭_D ≅ Lstar ⋙ F)` | def |
| `SecCyl K` | `CylMapR K` + a `DPathSection` of its `Lgrpd` (replaces `CylMapWeqR K`) | def |
| `cylToPointedObjOfSection c s` | the pointed endofunctor from a section: `pointedOfPaths` with `F₀ = Lstar ⋙ Rgrpd`, `η = unit.hom ≫ sweepR` | **PROVEN** (typechecks, sorry-free) |
| `SecCyl.toPointedObj` | the same for a `SecCyl K` object | def |
| `DPathSection.ofEquivalence F` | `IsEquivalence F ⟹ DPathSection F`, via `(F.inv, counitIso.symm)` | **PROVEN** |
| `CylMapWeqR.section_ c` | the canonical section of a weak-equiv cylinder's left leg | def |
| `cylToPointedObjOfSection_ofEquivalence c` | the equiv-section reproduces `cylToPointedObj c` **on the nose** (`rfl`) | **PROVEN** |
| `collapse`, `collapseSection` | `{a,b} ⇉ {∗}` discrete, with a section picking `a` | def |
| `collapse_not_isEquivalence` | the collapse functor is **not** an equivalence | **PROVEN** |
| `notEquivWitness` | `¬ IsEquivalence collapse ∧ Nonempty (DPathSection collapse)` | **PROVEN** |

**Key facts established.**

1. **The construction generalises with zero behavioural change.** `cylToPointedObjOfSection` is a
   *verbatim* copy of `cylToPointedObj` with two substitutions — `Lgrpd.inv ↝ s.Lstar` and
   `counitIso.inv ↝ s.unit.hom` — and `cylToPointedObjOfSection_ofEquivalence` proves they agree by
   `rfl` when `s = ofEquivalence`. So every existing `CylMapWeqR` cylinder is a `SecCyl`, with the
   *identical* induced endofunctor: a genuine generalisation, not a parallel construction.

2. **The weakening is real (non-vacuity).** `collapse : Discrete (Fin 2) ⥤ Discrete (Fin 1)` is not
   an equivalence (it identifies the two non-isomorphic source objects — `collapse_not_isEquivalence`
   reflects an iso `⟨0⟩ ≅ ⟨1⟩` and derives `(0:Fin 2) = 1`, false) yet carries a `DPathSection`
   (`collapseSection`, the constant-`⟨0⟩` functor with identity unit). So `DPathSection` strictly
   admits more functors than `IsEquivalence`.

**Promotion verdict for Part A: READY.** Clean defs, no `noncomputable` surprises beyond what the
existing construction already carries, exact agreement with `cylToPointedObj`, and a self-contained
non-vacuity witness. Suggested promotion: lift `DPathSection`/`SecCyl`/`cylToPointedObjOfSection`
into `Cylinder/CylinderRefine.lean` (or a new `Cylinder/Section.lean`), and re-define
`cylToPointedObj` as the `ofEquivalence` instance of `cylToPointedObjOfSection`.

---

## Part B — composition closure (the payoff)

The point of the section weakening: section-cylinders are **closed under composition**, where the
equivalence version was not (pullback of an equivalence need not be an equivalence without
right-properness; pullback of a *section* is a section unconditionally).

| Lean name | Statement | Status |
|---|---|---|
| `DPathSection.comp s s'` | sections compose: `DPathSection F → DPathSection G → DPathSection (F⋙G)`, `Lstar = G* ⋙ F*` | **PROVEN** |
| `MapSection f` | a *strict* precubical section `(s : Y ⟶ X, s ≫ f = 𝟙)` | def |
| `MapSection.pullbackFst p q σ` | sections pull back along `pullback.fst` (generic pullback, **no** properness) | **PROVEN** |
| `MapSection.pullbackComposeπ₁ c d σ` | specialised to the `mooreCompose` projection `composeπ₁` | **PROVEN** |
| `DPathDescent` | **labelled `Prop`** (NOT proven): precubical `MapSection f` ⟹ `DPathSection` of `FreeGroupoid.map (pushforwardBP f)` | isolated hypothesis |
| `DPathSection.transport e s` | a `DPathSection` transports across any iso `F ≅ F'` of the functor | **PROVEN** |
| `sections_compose_modulo_descent hd g f σg sf` | full closure, given `DPathDescent` | **PROVEN (modulo `DPathDescent`)** |

### B5 — sections compose ✓

`DPathSection.comp` glues `s : DPathSection F` and `s' : DPathSection G` into a
`DPathSection (F ⋙ G)` with `Lstar = s'.Lstar ⋙ s.Lstar` (inverses compose in opposite order) and
the unit assembled as the iso chain
`𝟭_E ≅ G* ⋙ G ≅ G* ⋙ ((F* ⋙ F) ⋙ G) ≅ (G* ⋙ F*) ⋙ (F ⋙ G)` (the last step is strict
associativity of functor composition). **Proven, sorry-free.**

### B6 — sections pull back ✓ (unconditional, precubical level)

`MapSection.pullbackFst`: for *any* `HasPullback p q` with `fst = pullback.fst p q`, a strict
section `σ` of `q` produces a strict section of `fst`, namely `t = pullback.lift 𝟙_X (p ≫ σ.s) (…)`.
The lift's square commutes precisely because `σ.s ≫ q = 𝟙` — **no hypothesis on `p`/`q`, no
right-properness.** This is the exact place where the section condition beats the equivalence
condition: *sections pull back along anything*. `MapSection.pullbackComposeπ₁` specialises this to
the geometric Moore composition's source pullback `composeSrc c d = c.src ×_K d.src` (so a section of
the second factor's start leg pulls back to a section of the composite's first projection).
**Proven, sorry-free.**

### B7 — the d-path descent: ISOLATED (not faked)

B6 lives at the **precubical** level (`composeπ₁` is a `PrecubicalSet` map). The `DPathSection`
apparatus lives over the **d-path groupoid**: a section of the *induced groupoid leg-functor*
`FreeGroupoid.map (Refine.pushforwardBP f)`. Bridging the two is the **d-path descent**, isolated as
the single labelled `Prop`:

```
DPathDescent : Prop :=
  ∀ (A B : BPSet) (f : A ⟶ B), MapSection f.hom →
    Nonempty (DPathSection (FreeGroupoid.map (Refine.pushforwardBP f)))
```

**Why it's genuinely the remaining work, not a triviality:** `Refine.pushforwardBP` and
`FreeGroupoid.map` preserve composition/identity only up to the coherence isos
`FreeGroupoid.mapComp`/`mapId` (plus `Refine.pushforward`'s own functoriality), so a *strict*
precubical splitting `s ≫ f = 𝟙` descends to a section only **up to iso** — which is exactly why the
target notion is `DPathSection` (section up to iso) and not a strict section. There is also a
basepoint subtlety: `mooreCompose`'s source `composeSrc` is a `PrecubicalSet`, not a `BPSet`, and
`composeπ₁` is a plain map, so even *stating* the descent for the composite needs basepoints chosen
on `composeSrc` — bookkeeping that the `BPSet`/`CylMapR` layer carries list-wise (cf.
`Cylinder/MooreMonoid.lean`'s explicitly list-carried staircase). `DPathDescent` packages exactly
this.

This is stated as a `Prop` so downstream results take it as a *hypothesis* — **no `sorry` is
introduced**, and `#print axioms` confirms every proven result depends only on
`propext`/`Classical.choice`/`Quot.sound`.

### Conclusion ✓ (modulo `DPathDescent`)

`sections_compose_modulo_descent`: assuming `hd : DPathDescent`, for `BPSet` maps `g : A ⟶ B`,
`f : B ⟶ C` with `g.hom` strictly sectioned and `f`'s d-path functor sectioned, the *composite*
d-path leg-functor `g-functor ⋙ f-functor` has a `DPathSection` — by descending `g`'s precubical
section (`hd`) and composing with `f`'s section (`DPathSection.comp`). `DPathSection.transport`
carries this across the `mapComp` coherence iso to the genuine `(g ≫ f)`-functor once that iso is
supplied. This is precisely the composition closure the equivalence version could **not** obtain.

---

## Summary ledger

**PROVEN (sorry-free, green):**
- the section datum `DPathSection`, the section-cylinder `SecCyl`, and the section-based pointed
  endofunctor `cylToPointedObjOfSection`;
- `IsEquivalence ⟹ DPathSection` (`ofEquivalence`), and exact agreement with the original
  `cylToPointedObj` (`cylToPointedObjOfSection_ofEquivalence`, by `rfl`);
- non-vacuity: a `DPathSection` of a non-equivalence (`notEquivWitness`);
- sections compose (`DPathSection.comp`);
- sections pull back along any pullback projection, unconditionally (`MapSection.pullbackFst`,
  `MapSection.pullbackComposeπ₁`);
- composition closure *modulo* the descent (`sections_compose_modulo_descent`), with
  `DPathSection.transport`.

**ISOLATED (single labelled `Prop`, not a sorry):**
- `DPathDescent` — the precubical-section → groupoid-functor-`DPathSection` descent; the one precise
  lemma between the (proven) precubical pullback-section and a fully groupoid-level closure.

**Promotion recommendation:** Part A is ready to promote as-is. For Part B, promote `DPathSection.comp`,
`MapSection`/`pullbackFst` (the unconditional pull-back is independently useful), and discharge
`DPathDescent` by giving `FreeGroupoid.map`/`Refine.pushforwardBP` their explicit `mapComp`-style
coherence, plus the `composeSrc` basepointing (the same list bookkeeping as `MooreMonoid`).
