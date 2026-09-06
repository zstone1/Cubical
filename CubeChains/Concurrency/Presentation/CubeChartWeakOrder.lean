import CubeChains.Concurrency.Presentation.CubeChartAction

/-!
# Concurrency/Presentation/CubeChartWeakOrder — the cube's defined charts are the weak order

A chart of `□n` over the run is its crossing permutation (`crossOnesEquiv`) and the atom action is
the weak action on all of `Sₙ` (`chartActionAt_eq_weakActionOn`), so `chartsWeakEquiv` reads the
defined charts off as the right weak Bruhat order.  Compare `locCubeWeakOrder`, the same order
reached through the base's slice.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

/-- The defined charts of `□n` over the run of `n` events. -/
abbrev ChartCat (n : ℕ) : Type := ChartsAt (chartActionAt n) n

/-- **The defined charts of `□n` over the run are the right weak order on `Sₙ`.** -/
noncomputable def chartWeakEquiv (n : ℕ) : ChartCat n ≌ WeakOrder n :=
  chartsWeakEquiv (chartActionAt n) (crossOnesEquiv n) (chartActionAt_eq_weakActionOn n)

end ChainCat
