import CubeChains.Braid.SalvettiSurj
import CubeChains.Salvetti.ConcConnectivity

/-!
# Braid/SalvettiBraidResult — the deck five-lemma's remaining inputs, and the result

`hconn` (the deck-sequence fibre-connectivity) transports `concGrpd_nEvents_connected` through the
equivalence `concCubeEquiv`.  Combined with `pureMonodromy` surjectivity it closes
`braidMonodromy_bijective'`: `Aut(mk⟦x⟧) ≌ Bₙ`.
-/

open CategoryTheory CategoryTheory.FreeGroupoid OrderQuotient

namespace CubeChains

/-- **Fibre connectivity upstairs.**  A cell and its reorientation are joined in
`FreeGroupoid (Sal (braidCOM n))`: their `braidSalEquiv`-images are `n`-event executions of `□n`,
joined by `concGrpd_nEvents_connected`, and `concCubeEquiv` is fully faithful. -/
theorem salvetti_fibre_connected (n : ℕ) (hn : 0 < n) (x : Sal (braidCOM n))
    (g : Equiv.Perm (Fin n)) :
    Nonempty ((FreeGroupoid.mk x : FreeGroupoid (Sal (braidCOM n)))
      ⟶ FreeGroupoid.mk (g • x)) := by
  obtain ⟨hh⟩ := concGrpd_nEvents_connected hn
    ((braidSalEquiv n).functor.obj x) ((braidSalEquiv n).functor.obj (g • x))
    (nEvents_braidSalEquiv_obj n x) (nEvents_braidSalEquiv_obj n (g • x))
  exact ⟨(concCubeEquiv n).fullyFaithfulFunctor.preimage hh⟩

/-- **The reorient-quotient vertex group is the full braid group.**  The descended Salvetti
construction `braidMonodromy` on `Aut(mk⟦x⟧)` is a bijection onto `Bₙ` — the deck five-lemma with
both remaining inputs discharged: fibre connectivity (`salvetti_fibre_connected`) and pure
surjectivity (`pureMonodromy_surjective`, the cube/pure-braid iso transported by connectivity). -/
theorem braidMonodromy_bijective_unconditional (n : ℕ) (hn : 0 < n) (x : Sal (braidCOM n)) :
    Function.Bijective (braidMonodromy n x) :=
  braidMonodromy_bijective' n x
    (fun g => salvetti_fibre_connected n hn x g)
    (pureMonodromy_surjective n hn x (concGrpd_nEvents_connected hn))

/-- **The reorient-quotient vertex group *is* `Bₙ`.**  `Aut(mk⟦x⟧)` in the free groupoid of the
`Sₙ`-reorient quotient of the braid Salvetti poset is isomorphic to the braid group `Bₙ`. -/
noncomputable def braidMonodromyMulEquiv (n : ℕ) (hn : 0 < n) (x : Sal (braidCOM n)) :
    Aut (mk (Quotient.mk'' x) :
        FreeGroupoid (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))) ≃* Braid n :=
  MulEquiv.ofBijective (braidMonodromy n x) (braidMonodromy_bijective_unconditional n hn x)

end CubeChains
