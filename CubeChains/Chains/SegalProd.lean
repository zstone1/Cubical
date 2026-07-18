import CubeChains.Chains.SegalSplit
import CubeChains.Chains.SegalAltitude
import CubeChains.Chains.WedgeSplitMap
import Mathlib.CategoryTheory.Products.Bifunctor

/-!
# Chains/SegalProd — the Segal equivalence `chSegal` and its n-ary form

The **Segal monoidality** of the cube-chain category, assembled from the splitting lemmas of
`Chains/SegalSplit.lean` (`chain_split` / `chConcat_map_surjective`):

* `chConcat_essSurj`, `chConcat_full` — the two remaining halves of `chConcat X Y`'s
  being an equivalence (`chConcat` itself and its faithfulness are in `Chains/Segal.lean`);
* `chSegal X Y : Ch X × Ch Y ≌ Ch (X ∨ Y)` — the binary Segal equivalence;
* `chSegalProd dims : ∏ᵢ Ch(□^{dimᵢ}) ≌ Ch(□^∨(dims))` — the n-ary decomposition,
  by recursion on `dims`.

The only side condition is `(wedge2 X Y).AdmitsAltitude`, which rules out a chain re-crossing
the junction vertex; it is discharged for cubes/serial wedges by `Chains/SegalAltitude.lean`.
-/

open CategoryTheory Opposite BPSet

namespace ChainCat

/-! ## The binary Segal equivalence -/

/-- **Essential surjectivity of `chConcat`** (the Segal splitting).  Every chain in `X ∨ Y` is
isomorphic to a concatenation of a chain in `X` and a chain in `Y`.

The hypothesis `(wedge2 X Y).AdmitsAltitude` rules out a chain that *re-crosses* the junction
vertex `v`: along a chain the junction vertices have strictly increasing altitude, so `v` is
visited at most once, forcing the `X`-blocks into a prefix and the `Y`-blocks into a suffix.
Without it (e.g. when `X`/`Y` have a positive cube looping at `v`) the statement is false. -/
theorem chConcat_essSurj (X Y : BPSet) (h : (wedge2 X Y).AdmitsAltitude) :
    (chConcat X Y).EssSurj where
  mem_essImage c := by
    -- Read off `c`'s cubes; they form a chain from `init` to `final`.
    have hch : IsCubeChain (wedge2 X Y).init
        (CubeChain.wedgeToCubes ⟨c.dims, c.map.hom⟩) (wedge2 X Y).final := by
      have h0 := CubeChain.wedgeToCubes_isCubeChain c.dims c.map.hom
      rwa [c.map.app_init, c.map.app_final] at h0
    -- Split into an `X`-chain and a `Y`-chain.
    obtain ⟨xc, yc, hchx, hchy, hsplit⟩ := ChainCat.chain_split X Y h _ hch
    set a : Ch X :=
      ⟨xc.map (·.1), CubeChain.wedgeDescHom xc (CubeChain.wedgeDesc X.init X.final xc hchx)⟩ with ha
    set b : Ch Y :=
      ⟨yc.map (·.1), CubeChain.wedgeDescHom yc (CubeChain.wedgeDesc Y.init Y.final yc hchy)⟩ with hb
    have hax : CubeChain.wedgeToCubes ⟨a.dims, a.map.hom⟩ = xc :=
      CubeChain.wedgeToCubes_wedgeDesc X.init X.final xc hchx
    have hby : CubeChain.wedgeToCubes ⟨b.dims, b.map.hom⟩ = yc :=
      CubeChain.wedgeToCubes_wedgeDesc Y.init Y.final yc hchy
    refine ⟨(a, b), ⟨eqToIso (ChainCat.Obj.eq_of_wedgeToCubes ?_)⟩⟩
    change CubeChain.wedgeToCubes ⟨a.dims ++ b.dims, (concatChainMap X Y a b).hom⟩
        = CubeChain.wedgeToCubes ⟨c.dims, c.map.hom⟩
    rw [ChainCat.wedgeToCubes_concatChainMap X Y a b, hax, hby]
    exact hsplit.symm

/-- **Fullness of `chConcat`** (the Segal splitting).  A refinement between two concatenated
chains in `X ∨ Y` itself splits into a refinement of the `X`-halves and one of the `Y`-halves. -/
theorem chConcat_full (X Y : BPSet) (_h : (wedge2 X Y).AdmitsAltitude) :
    (chConcat X Y).Full where
  map_surjective {_ _} hh := ChainCat.chConcat_map_surjective X Y hh

/-- `chConcat X Y` is an equivalence: faithful (`Chains/Segal.lean`), full and essentially
surjective (the two Segal-splitting halves above, under the altitude hypothesis). -/
theorem chConcat_isEquivalence (X Y : BPSet) (h : (wedge2 X Y).AdmitsAltitude) :
    (chConcat X Y).IsEquivalence :=
  haveI := chConcat_full X Y h
  haveI := chConcat_essSurj X Y h
  Functor.IsEquivalence.mk

/-- **The Segal monoidality of `Ch` (binary).**  `Ch(X ∨ Y) ≌ Ch X × Ch Y`: a chain through the
wedge splits canonically at the junction vertex.  Built from `chConcat X Y` once it is shown to be
an equivalence (under the altitude hypothesis that rules out junction re-crossing). -/
def chSegal (X Y : BPSet) (h : (wedge2 X Y).AdmitsAltitude) :
    Ch X × Ch Y ≌ Ch (wedge2 X Y) :=
  chSegalC h

/-! ## The n-ary Segal decomposition

By recursion on the dimension sequence, `Ch(□^∨(dims))` is the product of the `Ch(□^{dimᵢ})`.
The base case is the monoidal unit `chUnit : Ch(□⁰) ≌ Discrete PUnit` (`Chains/Segal.lean`);
the step glues one more cube with `chSegal`. -/

/-- The product of the chain categories of the individual cubes in a dimension sequence
(right-folded, matching `serialWedge`). -/
def chainProd : List ℕ+ → Type
  | [] => Discrete PUnit.{1}
  | n :: rest => Ch (□(n : ℕ)) × chainProd rest

instance instCategoryChainProd : ∀ dims : List ℕ+, Category (chainProd dims)
  | [] => inferInstanceAs (Category (Discrete PUnit))
  | n :: rest =>
      letI := instCategoryChainProd rest
      inferInstanceAs (Category (Ch (□(n : ℕ)) × chainProd rest))

/-- **The n-ary Segal decomposition.**  `Ch(□^∨(dims)) ≌ ∏ᵢ Ch(□^{dimᵢ})`.  Recursion on `dims`:
`[]` is the unit `chUnit`, and `n :: rest` glues the head cube via
`chSegal (cube n) (serialWedge rest)` and recurses on the tail. -/
def chSegalProd : ∀ dims : List ℕ+,
    chainProd dims ≌ Ch (⋁dims)
  | [] => chUnit.{0}.symm
  | n :: rest =>
      letI := instCategoryChainProd rest
      ((CategoryTheory.Equivalence.refl :
          Ch (□(n : ℕ)) ≌ Ch (□(n : ℕ))).prod
        (chSegalProd rest)).trans
        (chSegal (□(n : ℕ)) (⋁rest)
          (wedge2_admitsAltitude (cube_admitsAltitude (n : ℕ))
            (serialWedge_admitsAltitude rest)))

end ChainCat
