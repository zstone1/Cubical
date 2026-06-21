import CubeChains.Testing.CylinderObstruction

-- This is a property-testing file; `native_decide` is the intended engine here.
set_option linter.style.nativeDecide false

/-!
# Testing/WedgeMapDivergence

Why the `chLe` (face-poset) connectivity does NOT settle the wedge-map base (the gate fails).
`Testing/CylinderObstruction.lean` showed that, for the smallest rel-interface
cylinder `K = cylSquare`, the two flat ends `b₀ = [b0e]` and `b₁ = [b1e]` are
zigzag-connected via `b₀ ⟶ R ⟵ b₁` **in the relation `chLe`** — which is the
*face-poset* (Lemma 2.11(c)) order `a ⟶ b ⇔ every cube of a is a face of a cube of b`
(`Model.lean:111`).  That is exactly the morphism relation of `RefineObj`
(`Chains/Refine.lean`), **not** of the wedge-map category `ChainCat.Obj K`
(`Chains/Category.lean`), whose morphisms are interface-preserving `BPSet` maps of
serial wedges.

The two categories agree only via `equivWedgeCat`
(`Chains/Correspondence.lean:841`), which carries **both** side conditions
`NonSelfLinked` **and** `AdmitsAltitude`.  This file pins, by `native_decide`, the
decisive obstruction the prose only asserted:

> the minimal rel-interface cylinder `K` fails **both** gates,

so the `chLe`/face-poset connectivity provably does **not** transfer to
`ChainCat.Obj K`.  (The complementary fact — that in `ChainCat.Obj K` the objects
`b₀`, `b₁` are in fact *isolated*, so genuinely disconnected — is a short rigidity
argument given in the writeup: no `Box` morphism `□¹ ⟶ □²` preserves both the all-`0`
and the all-`1` corner, and in a serial wedge the only init-corner→final-corner edge
lives in a single `[1]` block.)

## Why a self-loop breaks *both* gates

`cylSquare` is self-linked: the cylinder over the interface vertices forces the
self-loop edges `sInit : init ⟶ init` and `sFin : final ⟶ final`.

* **`NonSelfLinked`** asks every cube's canonical map `□ⁿ ⟶ K` to be injective
  (`Altitude.lean:66`).  The self-loop `sInit`'s canonical map `□¹ ⟶ K` sends both
  endpoints of `□¹` to `init`, so it is not injective.
* **`AdmitsAltitude`** asks for `alt (vertex₁ c) = alt (vertex₀ c) + dim c`
  (`Altitude.lean:42`).  For `sInit` this reads `alt init = alt init + 1`, a
  contradiction.

So the *same* self-loop that a rel-interface cylinder forces (and which makes the
cylinder non-vacuous, since `NonSelfLinked` would make `CylMapB K` empty) is exactly
what voids `equivWedgeCat`.  The face-poset and the wedge-map category therefore
diverge precisely on the `K` the program needs.

**Layer:** Testing.  **Imports:** `Testing/CylinderObstruction`.
-/

namespace CubeTest
namespace Examples

open FinBPSet

/-! ## The face-poset connectivity (re-confirmed): holds in `chLe = RefineObj` -/

-- `b₀ ⟶ R ⟵ b₁` connects the flat ends in the **face-poset** order `chLe`.
example : cylSquare.chainsConnected [b0Chain, RChain, b1Chain] = true := by native_decide

/-! ## The gate fails: `cylSquare` admits NEITHER side condition of `equivWedgeCat` -/

-- It is a genuine (well-formed) precubical set.
example : cylSquare.wellFormed = true := by native_decide

-- But the self-loop `sInit`/`sFin` breaks `NonSelfLinked` …
example : cylSquare.nonSelfLinked = false := by native_decide

-- … and breaks `AdmitsAltitude` (`alt init = alt init + 1` is inconsistent) …
example : cylSquare.admitsAltitude = false := by native_decide

-- … hence it is not a valid input to the correspondence at all.
example : cylSquare.validInput = false := by native_decide

/-!
## Verdict

`equivWedgeCat : RefineObj ≌ ChainCat.Obj K` needs `NonSelfLinked ∧ AdmitsAltitude`,
and the minimal rel-interface cylinder `K` satisfies **neither** (`native_decide`
above).  So the `chLe`/`RefineObj` connectivity `b₀ ⟶ R ⟵ b₁` established in
`CylinderObstruction.lean` is connectivity in the **face-poset only**; it does not
lift to a zigzag of `ChainCat.Hom`s.

Combined with the rigidity argument (no `Box` morphism `□¹ ⟶ □²` preserves both
corners ⟹ `b₀`, `b₁` are *isolated* in `ChainCat.Obj K`), the conclusion is:

* **face-poset base** `FreeGroupoid (RefineObj)`: per-chain connectivity `x ⇝ F₀ x`
  **holds** (direct cospan into the prism cube, unconditional);
* **wedge-map base** `FreeGroupoid (ChainCat.Obj K)`: per-chain connectivity
  **fails** for self-linked `K` (the ends are isolated).

Hence the d-path groupoid for the cylinder program must be built on `RefineObj`.
-/

end Examples
end CubeTest
