import CubeChains.Foundations.DeckSequence
import CubeChains.Salvetti.ConcGroupoid
import CubeChains.Braid.CubeCovering

/-!
# Braid/CubeDeckTest — the cube's covering injection via the deck sequence

The pure-braid injection `ConcBraid (□n) ↪ π₁(FreeGroupoid (QuotCat …))` at a cube execution,
routed through the already-green `OrderQuotient.mapAut_injective` (a covering is π₁-injective) and
`salVertexMulEquiv` (vertex groups transport along `concCubeEquiv`).  No `concToZ`/`Ψ`/wedge-map.
-/

open CategoryTheory

namespace CubeChains

/-- The deck-sequence injection at a Salvetti basepoint — `mapAut_injective` at the braid
instance (`G = Sₙ`, `P = Sal (braidCOM n)`). -/
theorem cube_covering_injective (n : ℕ) (a : Sal (braidCOM n)) :
    Function.Injective
      ((FreeGroupoid.map (OrderQuotient.quotFunctor (G := Equiv.Perm (Fin n))
          (P := Sal (braidCOM n)))).mapAut (FreeGroupoid.mk a)) :=
  OrderQuotient.mapAut_injective a

/-- Transport to a cube execution: `ConcBraid (□n)` at the execution of a Salvetti cell injects,
via `salVertexMulEquiv`, into the quotient covering's vertex group. -/
theorem cube_concCubeEquiv_covering_injective (n : ℕ) (a : Sal (braidCOM n)) :
    Function.Injective
      (fun γ : ConcBraid (□n) ((braidSalEquiv n).functor.obj a) =>
        (FreeGroupoid.map (OrderQuotient.quotFunctor (G := Equiv.Perm (Fin n))
            (P := Sal (braidCOM n)))).mapAut (FreeGroupoid.mk a)
          ((salVertexMulEquiv n a).symm γ)) :=
  (cube_covering_injective n a).comp (salVertexMulEquiv n a).symm.injective

end CubeChains
