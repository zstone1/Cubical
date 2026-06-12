# DESIGN.md — conventions and decisions

This file records every non-obvious design choice, per ClaudeSetup.md §10. Each
entry gives a one-line justification and, where relevant, the paper equation it
matches (Paliga–Ziemiański, arXiv:2103.05336, henceforth **PZ**; Ziemiański,
arXiv:1901.05206, henceforth **Z**).

## 0. Toolchain and mathlib recon

- **Toolchain:** `leanprover/lean4:v4.30.0`, the latest *stable* Lean release at
  setup time. Mathlib is pinned to the matching release tag `v4.30.0`
  (`lakefile.toml`, `lake-manifest.json`). `lake exe cache get` populates the
  prebuilt `.olean` cache so no full mathlib rebuild is needed.

- **mathlib recon (§0 mandate):** searched mathlib v4.30.0 for existing cubical /
  precubical material:
  - `find -iname '*cub*'` → only `Algebra/CubicDiscriminant.lean` (cubic
    polynomials) and `Topology/Compactness/HilbertCubeEmbedding.lean` (the
    Hilbert cube). Neither is relevant.
  - `grep -ri 'cubical|precubical|cube category|BoxCat'` over `Mathlib/` → no
    hits. There is **no** box/cube category, no cubical or precubical sets, and
    no `Cube`/`Cubical` namespace.
  - mathlib *does* have a mature simplicial story (`AlgebraicTopology/
    SimplicialObject`, `SimplicialSet`, `SimplexCategory`).
  - **Decision:** define precubical sets from scratch (the concrete graded
    definition of §1), as the spec directs when no degeneracy-free cubical
    development exists. We *mirror* mathlib's simplicial conventions rather than
    reuse them.

## 1. Precubical identities (`Precubical/Basic.lean`)

- **Face signature.** `face : ∀ {n}, Bool → Fin (n+1) → cells (n+1) → cells n`.
  We keep `face` curried as `face ε i : cells (n+1) → cells n`.

- **`ε : Bool` convention (fixed once, never deviate):** `false = d⁰` =
  initial/source face, `true = d¹` = final/target face. (PZ §2; Z.)

- **The identity.** We mirror mathlib's `SimplicialObject.δ_comp_δ`
  (`Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean:115`), which states for
  `i ≤ j : Fin (n+2)` that `δ i ∘ δ j.succ = δ j ∘ δ i.castSucc`. The precubical
  version carries two independent labels `ε, η : Bool` (the two faces never
  interact), so the stored field is, for `i ≤ j : Fin (n+1)` and `c : cells (n+2)`:

  ```
  face ε i (face η j.succ c) = face η j (face ε i.castSucc c)
  ```

  This is the standard relation ∂ᵢ^ε ∂ⱼ^η = ∂_{j-1}^η ∂ᵢ^ε for i < j (PZ §2),
  transcribed in the `castSucc`/`succ` idiom so that mathlib `Fin` lemmas apply
  directly. Both orientations (`face_face` and a swapped `face_face'`) are proved
  as `simp`-usable rewrite lemmas.

- **Vertex naming.** Superscript digits `⁰`/`¹` are **not** legal Lean
  identifier characters, so the paper's `vertex⁰`/`vertex¹` become `vertex₀`
  (all-`false`/source) and `vertex₁` (all-`true`/target). They are defined by
  repeatedly applying `face ε 0` and proved order-independent via
  `vertex_face` (the §1 well-definedness obligation).

- **Lints.** The project keeps mathlib's standard linter set on, but disables
  `linter.style.header` in `lakefile.toml`: this is a research repo, not a
  mathlib PR, so the copyright-header requirement is noise.

## Universe policy (affects §1–§8)

`PrecubicalSet.cells : ℕ → Type` is fixed at `Type` (universe `0`), **not**
`Type u`.  All precubical sets here are concrete/small, and `§5`'s `Ch K` needs
bi-pointed maps `□^∨n → K` living in the *same* universe as `K`; fixing `Type 0`
keeps the standard cube (whose cells are `Fin N → Option Bool`-subtypes, already
`Type 0`) compatible with an arbitrary `K` without threading `ULift`. This is a
deliberate, documented narrowing of the `Type u` in the spec.

## 3. Standard cube (`Precubical/StandardCube.lean`)

- **Cells.** `cells N k := {c : Fin N → Option Bool // (noneSet c).card = k}`,
  where `noneSet c` is the finset of `none` (= ∗) positions.
- **`i`-th `none` position.** `nones c := (noneSet c.val).orderEmbOfFin c.prop`,
  the monotone bijection `Fin k ↪o Fin N` onto the `none`-positions. `face ε i c
  := update c.val (nones c i) (some ε)`; the cardinality drops by one because
  `noneSet (update c p (some ε)) = (noneSet c).erase p` (`noneSet_update`).
- **Precubical identity (the crux).** Proved via `face_nones`: the `none`-set
  embedding *after* a face equals `(succAboveOrderEmb a).trans (nones c)`,
  established with `Finset.orderEmbOfFin_unique'` (an order embedding into a
  finset of the right cardinality *is* `orderEmbOfFin`). Both sides of
  `face_face` then reduce to two `Function.update`s at the independent positions
  `nones c i.castSucc`, `nones c j.succ`; `Fin.succAbove_succ_of_le` /
  `succAbove_castSucc_of_le` compute the indices and `Function.update_comm`
  finishes. No `sorry`, no dependent rewrites.
- Bi-pointed at the constant-`some false`/`some true` vertices. Notation `□^N`.

## 4–7

(Recorded as each milestone lands. Key rule, ClaudeSetup.md §0: **no `sorry`
outside `Conjectures.lean`**; that file may use Batteries `proof_wanted`.)
