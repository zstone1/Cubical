import CubeChains.Cobordisms.Cobordism

/-!
# Future/TQFT — Frobenius / TQFT presentation and Khovanov-type homology (docstring only)

**Out of scope for the current build** (spec §"Out of scope"): documentation only, no
proofs and essentially no statements — this file records the intended research directions.

## The program

* **Frobenius presentation of `dCob_{≤2}`.**  Restricting to objects that are disjoint
  unions of points and `1`-cobordisms between them, the directed cobordism category
  `dCob_{≤2}` should admit a generators-and-relations (PROP-like) presentation by the
  directed **merge / split / birth / death** cobordisms — the directed analogue of the
  Frobenius-algebra presentation of `2Cob`.  Unlike the symmetric `2Cob`, directedness
  breaks the commutative-Frobenius symmetry: the oriented cylinder is an *iso* `X ≃ X`,
  not a nullbordism, so `dCob` is a **semiring**-flavoured (non-groupoid) category, not a
  compact-closed one — see the `M6` non-triviality results.

* **A symmetric monoidal functor `dCob_{≤2} ⟶ Mod_R`** (a directed 2d TQFT) would send the
  merge `{a,b} ⇒ {*}` to a non-iso multiplication, witnessing again that `dCob` is not a
  groupoid (`NonTriviality.merge_not_invertible`).

* **Khovanov-type homology.**  The cube-of-resolutions / Bar-Natan cobordism category
  underlying Khovanov homology is a *cobordism* category much like this one; the directed
  cube-chain structure (`Ch(K)`, the rest of this repo) suggests a directed Khovanov-type
  complex built from `dCob` morphisms, with the loop-barrier lemmas controlling the
  differential's well-definedness.

These are recorded as targets only; see `Cobordisms/Cobordism.lean`, `Cobordisms/DCob.lean`,
and `Cobordisms/NonTriviality.lean` for the concrete category they would presental.
-/
