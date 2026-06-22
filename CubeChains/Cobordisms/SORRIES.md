# SORRIES.md — tracked scaffolding for the dCob build

Policy (from the spec): `sorry` allowed **only** as tracked scaffolding, tagged
`-- TODO(dCob): <reason>`. Target **zero sorries in M0–M4 and M6**; isolate any
unavoidable coherence scaffolding to **M5**. `Future/` is statement-only (sorry'd
by design, not counted as debt).

Baseline (pre-existing, inherited — not our debt): the repo is sorry-free except
`CubeChains/Research/Conjectures.lean` (by long-standing policy).

## Open scaffolding (this build)

M0–M4 are **fully sorry-free** (reachability, boundary, loops, cospan, `MonoidalCategory
Box`, Day tensor, nerve, cylinder, flags, union, collars, the cobordism bundle, and the
M4b pushout-closure barrier). M6(a) is sorry-free. Any M5-coherence scaffolding is logged
here as it lands.

| Milestone | File | Symbol | Reason | Status |
|---|---|---|---|---|
| M5 | DCob.lean | (see file) | coherence (assoc) up to rel-∂ may be isolated | TBD on agent report |

## Future/ statement-only stubs (by design — NOT counted as debt; not wired into root)

`Future/` is decoupled from `CubeChains.lean` (like `Testing/`), so `lake build CubeChains`
stays sorry-free except `Research/Conjectures.lean`. Build directly with
`lake build CubeChains.Future.<File>`.

| File | Symbol | Note |
|---|---|---|
| Future/Morse.lean | `gradientAcyclic_iff_loopConfined`, `altitude_isMorse`, `critical_classification` | directed discrete Morse theory; acyclicity ⇔ loop-confinement; cap/cup/saddle/cylinder |
| Future/Profunctor.lean | `cobProfunctor`, `cobProfunctor_comp` | `Φ_W : π₁(X)ᵒᵖ × π₁(Y) → Set`; composition ↦ coend; `dCob → Prof` |
| Future/TQFT.lean | (docstring only) | Frobenius presentation of `dCob_{≤2}`; directed Khovanov-type homology |
