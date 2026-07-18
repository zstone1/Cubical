import CubeChains.Chains.WedgeMonoidal
open CategoryTheory MonoidalCategory

-- (1) letI for the whole tactic proof
example (X Y : BPSet) : BPSet := by
  letI := ChainCat.wedgeMonoidal
  exact X ⊗ Y

-- (2) haveI, same
example (X Y : BPSet) : BPSet := by
  haveI := ChainCat.wedgeMonoidal
  exact X ⊗ Y

-- (3) TIGHTEST: scoped to a single subterm; ⊗ resolves only inside these parens
example (X Y : BPSet) : BPSet := by
  exact (letI := ChainCat.wedgeMonoidal; X ⊗ Y)

-- (4) inside a nested `have` within a larger proof
example (X Y : BPSet) : True := by
  have _z : BPSet := by letI := ChainCat.wedgeMonoidal; exact X ⊗ Y
  trivial
