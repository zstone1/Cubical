# Cubical

A Lean 4 + mathlib formalization of Ziemiański's cube-chain category `Ch(K)`
and the lifting/lowering of automorphisms between a bi-pointed precubical set
`K` and `Ch(K)` — directed topology in Lean for concurrent program analysis.

Two headline results, both sorry-free:

- **`equivWedgeCat`** (`Chains/Correspondence.lean`) — the refinement category
  `RefineObj K` is equivalent to the cube-chain category `ChainCat.Obj K` (under
  `NonSelfLinked` + `AdmitsAltitude`).
- **`cylToPointedR`** (`Cylinder/CylinderRefine.lean`) — a cylinder weak
  equivalence yields a pointed endofunctor on the directed-path groupoid.

See [`ARCHITECTURE.md`](ARCHITECTURE.md) for the file map (read it first to find
the right module). Build the whole project with `lake build CubeChains`. The
only `sorry`s live in `Research/Conjectures.lean` (by policy).

Papers: Paliga–Ziemiański, [arXiv:2103.05336](https://arxiv.org/abs/2103.05336);
Ziemiański, [arXiv:1901.05206](https://arxiv.org/abs/1901.05206).
