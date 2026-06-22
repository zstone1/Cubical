# MAP.md — directed-cobordism build, repo inventory & reuse map

Inventory of the **existing** infrastructure the `dCob` build reuses, and the new
modules being added. (The global repo map is `ARCHITECTURE.md` at the root.)

## Reused from Foundations (do NOT re-derive)

| Need (spec) | Existing name | File |
|---|---|---|
| precubical set (topos model) | `PrecubicalSet := Boxᵒᵖ ⥤ Type` | `Foundations/Box.lean` |
| has all pushouts/colimits | `HasPushouts PrecubicalSet` (functor cat into `Type`) | `Foundations/Box.lean` |
| box category, dimensions | `Box`, `Box.ob n` | `Foundations/Box.lean` |
| cube Yoneda `(□ⁿ ⟶ K) ≃ K.cells n` | `cubeRepr`, `ev`, `canonicalMap` | `Foundations/Representable.lean` |
| face map `δ_i^ε` | `PrecubicalSet.faceMap ε i`, `cubeMap` | `Foundations/Bipointed.lean` |
| initial/terminal vertex `ι c`, `τ c` | `vertex₀`, `vertex₁` (iterated `δ⁰`/`δ¹`) | `Foundations/Bipointed.lean` |
| reachability preorder (vertices/cells) | `Reach` (currently on `BPSet`; generalized below) | `Foundations/Altitude.lean` |
| box shift `[n] ↦ [n+1]` (= `-⊗□¹` on Box) | `Box.shift`, `coface ε`, `snocFree`/`snocFix` | `Foundations/Shift.lean` |
| cocylinder / internal hom of `-⊗□¹` | `PathOb`, `endpoint ε` | `Foundations/Shift.lean` |
| cylinder map kernel (salvaged) | `CylMap := Over (PathOb K)`, `prism`, `cylTranspose` | `Cylinder/Cylinder.lean` |
| mono stable under pushout (adhesive) | `Adhesive.mono_of_isPushout_of_mono_{left,right}` | mathlib (used in `Chains/WedgeMap`, `Segal`) |
| Day convolution | `CategoryTheory.MonoidalCategory.DayConvolution` | mathlib `Monoidal/DayConvolution.lean` |

## New modules (this build) — namespace `Precubical.Cobordism`

### Foundations additions (tensor + reachability)
- `Foundations/CubeConcat.lean` — `MonoidalCategory Box` (cube concatenation
  `□ᵐ ⊗ □ⁿ = □^{m+n}`, unit `□⁰`).  [M0a]
- `Foundations/Tensor.lean` — Day-convolution tensor `⊗` on `PrecubicalSet`; the
  cylinder functor `Cyl X := X ⊗ □¹`, ends `δ⁰,δ¹ : X ⟶ Cyl X`, monos + disjointness.  [M0b]
- `Foundations/Reachability.lean` — `PrecubicalSet`-level reachability `Reaches`,
  reflexive-transitive, vertex components `π₀`.  [M0r]

### Cobordisms/
- `Cobordisms/DirectedBoundary.lean` — `Sieve`/`Cosieve` (past/future-closed),
  collars, end-of-cylinder is a sieve/cosieve, loop-barrier lemmas.  [M1]
- `Cobordisms/Cospan.lean` — cospan structure, pushout composition, disjoint legs.  [M2]
- `Cobordisms/Loops.lean` — SCCs, `LoopConfined`, loop-freeness inheritance.  [M3]
- `Cobordisms/Cobordism.lean` — `DirectedCobordism X Y` bundle, the algebra
  (cylinder = identity, `⊔`/`⊗`, pushout-closure).  [M4]
- `Cobordisms/DCob.lean` — rel-∂ `Setoid`, `Hom = Quotient`, the `Category dCob`.  [M5]
- `Cobordisms/NonTriviality.lean` — ∅-bottom, merge non-invertibility via π₀.  [M6]

### Future/ (statement-only stubs, sorry'd, no proofs)
- `Future/Morse.lean`, `Future/Profunctor.lean`, `Future/TQFT.lean`.

## Build status
See `SORRIES.md`.  Each module builds green via `lake build CubeChains.<Module>`;
modules are wired into the root `CubeChains.lean` only once green.
