import CubeChains.Machinery.Braid.BraidPresentation

/-!
# Machinery/Braid/GermPresentation — the germ presentation

`PosBraid n` *is* `PresentedMonoid (PosGermRel n)`, so the germ family presents it on the nose: a
generator for every permutation, relators the length-additive products.
-/

open CategoryTheory Equiv

namespace CubeChains

/-- **The germ presentation**: a generator for each permutation, relators the length-additive
products. -/
def germPresentation : BraidPresentation where
  gen n := Perm (Fin n)
  rel := PosGermRel
  perm := fun {_} σ => σ
  monoidEquiv n := MulEquiv.refl (PosBraid n)
  monoidEquiv_gen _ := rfl

end CubeChains
