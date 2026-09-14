import CubeChains.Concurrency.Grading.Coarser
import Mathlib.CategoryTheory.Category.Factorisation

/-!
# Concurrency/Merge/Factorisation — a factorisation is its middle shape

A `CategoryTheory.Factorisation` of `f : a ⟶ b` is pinned by the **shape** of its middle:
`factor_ext` (`Concurrency/Grading/Coarser`) forces the legs once the middle chain is fixed, and the
chain over a shape is the cartesian lift of the second leg, so nothing but the shape is free.
-/

open CategoryTheory CubeChains CubeChain BPSet ChainCat

namespace CategoryTheory.Factorisation

variable {K : BPSet} {a b : Ch K}

/-- **A factorisation is pinned by its middle** — the legs are forced (`factor_ext`). -/
theorem ext {f : a ⟶ b} : ∀ {F G : Factorisation f}, F.mid = G.mid → F = G := by
  rintro ⟨m, g, e, hge⟩ ⟨m', g', e', hge'⟩ (rfl : m = m')
  obtain ⟨hg, he⟩ := factor_ext hge hge'
  subst hg
  subst he
  rfl

/-- **…and in fact by its middle *shape*** — the two second legs agree, and a second leg carries
the chain over the shape (`eq_of_join_of_dims_eq`). -/
theorem ext_dims {f : a ⟶ b} {F G : Factorisation f} (h : F.mid.dims = G.mid.dims) : F = G :=
  ext (eq_of_join_of_dims_eq h (F.ι_π.trans G.ι_π.symm))

end CategoryTheory.Factorisation
