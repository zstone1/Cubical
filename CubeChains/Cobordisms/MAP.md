# MAP.md — directed cobordisms: what exists, and what not to re-derive

Local inventory for `Cobordisms/`. The global repo map is `ARCHITECTURE.md` at the root;
status lives in beads (`bd ready`), not here.

## Reused from Foundations (do NOT re-derive)

| Need | Existing name | File |
|---|---|---|
| precubical set (topos model) | `PrecubicalSet := Boxᵒᵖ ⥤ Type` | `Foundations/Box.lean` |
| has all pushouts/colimits | `HasPushouts PrecubicalSet` (functor cat into `Type`) | `Foundations/Box.lean` |
| box category, dimensions | `Box`, `Box.ob n` | `Foundations/Box.lean` |
| cube Yoneda `(□ⁿ ⟶ K) ≃ K.cells n` | `cubeRepr`, `ev`, `canonicalMap` | `Foundations/Representable.lean` |
| face map `δ_i^ε` | `PrecubicalSet.faceMap ε i`, `cubeMap` | `Foundations/Bipointed.lean` |
| initial/terminal vertex `ι c`, `τ c` | `vertex₀`, `vertex₁` (iterated `δ⁰`/`δ¹`) | `Foundations/Bipointed.lean` |
| reachability preorder | `Reach` (on `BPSet`), `Reaches` (on `PrecubicalSet`) | `Foundations/Altitude.lean`, `Foundations/Reachability.lean` |
| box shift `[n] ↦ [n+1]` (= `-⊗□¹` on Box) | `Box.shift`, `coface ε`, `snocFree`/`snocFix` | `Foundations/Shift.lean` |
| cocylinder / internal hom of `-⊗□¹` | `PathOb`, `endpoint ε` | `Foundations/Shift.lean` |
| cylinder map kernel | `CylMap := Over (PathOb K)`, `prism`, `cylTranspose` | `Cylinder/Cylinder.lean` |
| mono stable under pushout (adhesive) | `Adhesive.mono_of_isPushout_of_mono_{left,right}` | mathlib |
| **geometric tensor `⊗` (Day convolution)** | `BoxMonoidal`, `dayTensor`, `BPSet ⊗` | `Foundations/{BoxMonoidal,DayTensor,BPTensor}.lean` |

The tensor row matters: `K ⊗ L` **is** the Day convolution of the underlying presheaves
(`BPTensor`), and it is load-bearing for the braid work. An earlier pair of files
(`Foundations/CubeConcat.lean`, `Foundations/Tensor.lean`) was deleted, but the *route* came
back under the names above. Do not conclude from their absence that the tensor doesn't exist.

## Foundations additions

- `Foundations/Nerve.lean` — the model bridge: `realize`/`Nerve` (restricted Yoneda along
  `cubeι`), `nerveCellEquiv`, `nerveRealizeIso`, `faceMap_faceMap`.
- `Foundations/Cylinder.lean` — the geometric cylinder `Cyl := realize ⋙ cylC ⋙ Nerve`, a
  concrete model rather than a coend. `cylCellEquiv : (Cyl X)_n ≅ X_n ⊕ X_n ⊕ X_{n-1}`,
  ends `cylEnd ε`, mono/disjoint, sieve/cosieve. This `Cyl` is the sole cylinder used for
  identities and collars.
- `Foundations/Reachability.lean` — `Reaches`, reflexive-transitive; vertex components `π₀`,
  `π₀.map`/`π₀.mapEquiv`.

## Cobordisms/ — namespaces `PrecubicalSet` / `Precubical.Cobordism`

- `DirectedBoundary.lean` — `IsSieve`/`IsCosieve`, `StronglyConnected`, loop-barrier lemmas.
- `Loops.lean` — `IsLoopFree`, `LoopConfined`, loop-freeness inheritance.
- `Cospan.lean` — cospan + pushout composition `Cospan.comp`, disjoint legs (van Kampen).
- `Flags.lean` — `srcImage`/`sinkImage`, `Closed`/`Spanning` flags;
  `no_closed_cobordism_from_empty`.
- `FlagsComp.lean` — flag behaviour under composition.
- `Union.lean` — `Cospan.union` (the `⊔` operation), disjointness.
- `Collar.lean` — `SourceCollar`/`SinkCollar`, the cylinder's canonical collars, `cylCospan`.
- `Cobordism.lean` — the `DirectedCobordism X Y` bundle; `idCob` = the cylinder.
- `Composition.lean` — pushout-closure `DirectedCobordism.comp`, resting on the barrier lemmas.
- `Associativity.lean` — associativity of `comp`.
- `DCob.lean` — rel-∂ `cobordismRel`, `HomCob = Quotient`, the `Category dCob` instance.
- `NonTriviality.lean` — `merge_no_iso_inverse`: the merge `{a,b} ⇒ {*}` has no boundary-fixing
  iso inverse; ∅-bottom; `idCob ≠ merge`.

  GOTCHA: the naive mapping cylinder is *not* a valid cobordism here — `fold` is non-mono, so
  the gluing legs stop being monos. The Λ-junction construction in that file exists to keep
  every leg mono, which is why it looks more elaborate than it "should".
