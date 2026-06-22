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

## New modules (this build) — `[✓]` = green & sorry-free, wired into root

### Foundations additions (tensor, nerve, cylinder, reachability)
- `[✓]` `Foundations/CubeConcat.lean` — `MonoidalCategory Box` (cube concatenation
  `□ᵐ ⊗ □ⁿ = □^{m+n}`, unit `□⁰`; crux `app_append`).  [M0a]
- `[✓]` `Foundations/Tensor.lean` — Day-convolution geometric tensor `⊗` on `PSetDay`
  (= `Boxᵒᵖ ⊛⥤ Type`, mathlib `DayFunctor`); `pSetDayEquiv`; `cyl := tensorRight □¹`.  [M0b-1]
- `[✓]` `Foundations/Nerve.lean` — the **model bridge**: `realize`/`Nerve` (restricted
  Yoneda along `cubeι`), `nerveCellEquiv`, `nerveRealizeIso`, `faceMap_faceMap`.
- `[✓]` `Foundations/Cylinder.lean` — the **geometric cylinder** `Cyl := realize ⋙ cylC ⋙ Nerve`
  (concrete model + nerve, sidestepping the Day coend), `cylCellEquiv`
  (`(Cyl X)_n ≅ X_n ⊕ X_n ⊕ X_{n-1}`), ends `cylEnd ε`, mono/disjoint, sieve/cosieve.  [M0b-2]
- `[✓]` `Foundations/Reachability.lean` — `PrecubicalSet`-level `Reaches`,
  reflexive-transitive, vertex components `π₀`, `π₀.map`/`π₀.mapEquiv`.  [M0r]

### Cobordisms/ — namespaces `PrecubicalSet` / `Precubical.Cobordism`
- `[✓]` `DirectedBoundary.lean` — `IsSieve`/`IsCosieve`, `StronglyConnected`, loop-barrier lemmas.  [M1-core]
- `[✓]` `Loops.lean` — `IsLoopFree`, `LoopConfined`, loop-freeness inheritance.  [M3]
- `[✓]` `Cospan.lean` — cospan + pushout composition `Cospan.comp`, disjoint legs (van Kampen).  [M2]
- `[✓]` `Flags.lean` — `srcImage`/`sinkImage`, `Closed`/`Spanning` flags; **M6(a)** `no_closed_cobordism_from_empty`.
- `[✓]` `Union.lean` — `Cospan.union` (the `⊔` operation), disjointness.  [M4-⊔]
- `[✓]` `Collar.lean` — `SourceCollar`/`SinkCollar`, the cylinder's canonical collars, `cylCospan`.  [M1-collars]
- `[✓]` `Cobordism.lean` — `DirectedCobordism X Y` bundle; `idCob = ` cylinder.  [M4a]
- `[✓]` `Composition.lean` — **pushout-closure** `DirectedCobordism.comp` (the barrier lemmas — M4b heart).
- `[✓]` `DCob.lean` — rel-∂ `cobordismRel`, `HomCob = Quotient`, the `Category dCob` (one coherence
  input deferred to `Research/Conjectures.lean`).  [M5]
- `[✓]` `NonTriviality.lean` — **M6**: `merge_not_invertible` (the merge `{a,b}⇒{*}` is not a
  dCob-equivalence) + `merge_no_iso_inverse` (unconditional) + ∅-bottom + `idCob ≠ merge` (M6c).

### Future/ (statement-only stubs, sorry'd by design, decoupled from root — like Testing/)
- `[✓]` `Future/Morse.lean`, `Future/Profunctor.lean`, `Future/TQFT.lean`.

## Build status
M0–M4 + M5 are **green and sorry-free** (the only project `sorry`s remain in
`Research/Conjectures.lean`, now incl. the one deferred M5 pushout-coherence input).
See `SORRIES.md`. The Day `⊗` (`Tensor.lean`) is the general geometric tensor for the
M4 algebra; the operative cylinder for identities/collars is the nerve-based `Cyl`
(`Cylinder.lean`) — the two are the same object up to a (deferred) iso.
