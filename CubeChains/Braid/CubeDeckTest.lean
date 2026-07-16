import CubeChains.Foundations.DeckSequence
import CubeChains.Foundations.DeckExact
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

/-- **Middle exactness at a Salvetti basepoint** — `deck_ker_eq_range` at the braid instance.  The
kernel of the axis-permutation monodromy `deck` is exactly the image of the quotient covering: a
loop in `π₁(Sal/Sₙ)` is the image of a `π₁(Sal)`-loop iff its permutation shadow is trivial.  This
is the middle term of the deck SES `1 → π₁(Sal) → π₁(Sal/Sₙ) → Sₙ → 1`; paired with
`cube_covering_injective` it is the covering content the `xhj.6` five-lemma consumes. -/
theorem cube_covering_ker_eq_range (n : ℕ) (a : Sal (braidCOM n)) :
    (OrderQuotient.deck (G := Equiv.Perm (Fin n)) a).ker
      = ((FreeGroupoid.map (OrderQuotient.quotFunctor (G := Equiv.Perm (Fin n))
          (P := Sal (braidCOM n)))).mapAut (FreeGroupoid.mk a)).range :=
  OrderQuotient.deck_ker_eq_range a

end CubeChains
