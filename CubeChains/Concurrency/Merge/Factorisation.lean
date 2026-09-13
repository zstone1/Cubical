import CubeChains.Concurrency.Grading.Coarser

/-!
# Concurrency/Merge/Factorisation — a factorisation is its middle shape

A two-step factorisation of `f : a ⟶ b` is pinned by the **shape** of its middle: `factor_ext`
(`Concurrency/Grading/Coarser`) forces the legs once the middle chain is fixed, and the chain over
a shape is the cartesian lift of the second leg, so nothing but the shape is free.
-/

open CategoryTheory CubeChains CubeChain BPSet

namespace ChainCat

variable {K : BPSet} {a b : Ch K}

/-- A two-step factorisation of a refinement. -/
structure Factorisation (f : a ⟶ b) where
  /-- The intermediate chain. -/
  mid : Ch K
  /-- The first leg. -/
  fst : a ⟶ mid
  /-- The second leg. -/
  snd : mid ⟶ b
  /-- …and they compose to `f`. -/
  comp : fst ≫ snd = f

/-- **A factorisation is pinned by its middle** — the legs are forced (`factor_ext`). -/
theorem Factorisation.ext {f : a ⟶ b} : ∀ {F G : Factorisation f}, F.mid = G.mid → F = G := by
  rintro ⟨m, g, e, hge⟩ ⟨m', g', e', hge'⟩ (rfl : m = m')
  obtain ⟨hg, he⟩ := factor_ext hge hge'
  subst hg
  subst he
  rfl

/-- **…and in fact by its middle *shape*** — the two second legs agree, and a second leg carries
the chain over the shape (`eq_of_join_of_dims_eq`). -/
theorem Factorisation.ext_dims {f : a ⟶ b} {F G : Factorisation f} (h : F.mid.dims = G.mid.dims) :
    F = G :=
  Factorisation.ext (eq_of_join_of_dims_eq h (F.comp.trans G.comp.symm))

end ChainCat
