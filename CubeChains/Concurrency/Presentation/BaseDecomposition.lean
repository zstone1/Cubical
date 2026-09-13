import CubeChains.Concurrency.Presentation.BaseComponent

/-!
# Concurrency/Presentation/BaseDecomposition — the strand count is the invariant

An object of the localization is a chain on the nose (`objEquiv`), so it has a strand count, and
`isEmpty_loc_hom` says no arrow changes it — which is what makes `AtStrands N` convex, so that a
presentation of the base restricts to each component.  That the base *is* the disjoint union of
those components is `zLocEquiv`, which also names the monoid each one carries.
-/

open CategoryTheory Opposite CubeChains

namespace ChainCat

/-- Every object of the localized base is a chain, hence has a strand count. -/
theorem exists_atStrands (c : ((W Zbp).op).Localization) : ∃ N, AtStrands N c :=
  let ⟨a, ha⟩ := exists_chain_Q_obj c
  ⟨BPSet.dimSum a.dims, a, rfl, ha⟩

/-- **The strand count is an invariant of the localized base** — `isEmpty_loc_hom`, read on the
components. -/
theorem atStrands_eq_of_hom {M N : ℕ} {X Y : ((W Zbp).op).Localization}
    (hX : AtStrands M X) (hY : AtStrands N Y) (f : X ⟶ Y) : M = N := by
  obtain ⟨a, rfl, rfl⟩ := hX
  obtain ⟨b, rfl, rfl⟩ := hY
  by_contra h
  exact (isEmpty_loc_hom h).elim f

end ChainCat
