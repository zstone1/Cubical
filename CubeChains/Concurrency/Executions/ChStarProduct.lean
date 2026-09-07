import CubeChains.Precubical.Basic.BipointedProd
import CubeChains.Concurrency.Executions.Runs
import Mathlib.CategoryTheory.Category.Cat

/-!
# Concurrency/Executions/ChStarProduct — a complexified chain is a chain in a product

A run refining `⋁d` is a map into the run presheaf, and the endpoints of `runBp` are forced, so it
is a *bi-pointed* map `⋁d ⟶ runBp`; the product then pairs it with the chain, and the arrows of
`Ch⋆` — refinements, contravariant on wedges — are those of the product chain category read
backwards.

    ⋁d --chain--> K   and   ⋁d --run--> runBp    ≡    ⋁d --prodLift--> K.prod runBp

Spelled at the computable cone `BPSet.prod`, whose universal property (`BipointedProd`) makes both
round trips hold on the nose; `prodFanIsLimit` is what says it *is* the binary product.
-/

open CategoryTheory Opposite BPSet ChainCat

namespace CubeChains

variable (K : BPSet)

/-- **A complexified chain, as a chain in `K.prod runBp`**: pair the chain map with the run. -/
def chStarToProd : Ch⋆ K ⥤ (Ch (K.prod runBp))ᵒᵖ where
  obj x := op ⟨x.chain.dims, prodLift x.chain.map ((homEquivPsh _ runBp).symm x.2)⟩
  map {x y} f := Quiver.Hom.op ⟨f.1.unop.φ, by
    refine prod_hom_ext ?_ ?_
    · rw [Category.assoc, prodLift_fst, prodLift_fst]
      exact f.1.unop.w
    · rw [Category.assoc, prodLift_snd, prodLift_snd]
      exact hom_ext f.2⟩
  map_id x := rfl
  map_comp f g := rfl

/-- **A chain in `K.prod runBp`, as a complexified chain**: project to `K`, read the run off
`runBp`. -/
def prodToChStar : (Ch (K.prod runBp))ᵒᵖ ⥤ Ch⋆ K where
  obj a := ⟨op ⟨a.unop.dims, a.unop.map ≫ prodFst K runBp⟩,
    homEquivPsh _ runBp (a.unop.map ≫ prodSnd K runBp)⟩
  map {a b} f := ⟨Quiver.Hom.op ⟨f.unop.φ, by rw [← Category.assoc, f.unop.w]⟩,
    congrArg BPSet.Hom.hom (show f.unop.φ ≫ (a.unop.map ≫ prodSnd K runBp)
      = b.unop.map ≫ prodSnd K runBp by rw [← Category.assoc, f.unop.w])⟩
  map_id a := rfl
  map_comp f g := rfl

/-! ### The isomorphism of categories

Both round trips are the identity *on the nose*: `prodLift`'s two legs and its universal property
are definitional, as is `homEquivPsh` (the endpoint conditions are proofs). -/

theorem chStarToProd_comp_prodToChStar :
    chStarToProd K ⋙ prodToChStar K = 𝟭 (Ch⋆ K) := rfl

theorem prodToChStar_comp_chStarToProd :
    prodToChStar K ⋙ chStarToProd K = 𝟭 ((Ch (K.prod runBp))ᵒᵖ) := rfl

/-- **A complexified chain is a chain in a product**, as an isomorphism of categories: the object
correspondence is a bijection, not merely an equivalence. -/
def chStarProdIso : Cat.of (Ch⋆ K) ≅ Cat.of ((Ch (K.prod runBp))ᵒᵖ) where
  hom := (chStarToProd K).toCatHom
  inv := (prodToChStar K).toCatHom
  hom_inv_id := Cat.ext (chStarToProd_comp_prodToChStar K)
  inv_hom_id := Cat.ext (prodToChStar_comp_chStarToProd K)

/-- `Ch⋆ K ≌ (Ch (K.prod runBp))ᵒᵖ`. -/
def chStarProdEquiv : Ch⋆ K ≌ (Ch (K.prod runBp))ᵒᵖ :=
  Cat.equivOfIso (chStarProdIso K)

end CubeChains
