import CubeChains.Concurrency.Presentation.BaseComponent
import CubeChains.Machinery.SigmaComponents

/-!
# Concurrency/Presentation/BaseDecomposition — the localized base, one piece per strand count

An object of the localization is a chain on the nose (`objEquiv`), so it has a strand count, and
`isEmpty_loc_hom` says no arrow changes it.  So `Ch Zbp[W⁻¹]` is the disjoint union of the
`AtStrands N`, each of which is `strandComponentGarside N`.
-/

open CategoryTheory Opposite CubeChains

namespace ChainCat

/-- Every object of the localized base is a chain, hence has a strand count. -/
theorem exists_atStrands (c : ((W Zbp).op).Localization) : ∃ N, AtStrands N c :=
  ⟨_, ((Localization.Construction.objEquiv ((W Zbp).op)).symm c).unop, rfl, by
    rw [Opposite.op_unop]
    exact (Localization.Construction.objEquiv ((W Zbp).op)).right_inv c⟩

/-- **The strand count is an invariant of the localized base** — `isEmpty_loc_hom`, read on the
components. -/
theorem atStrands_eq_of_hom {M N : ℕ} {X Y : ((W Zbp).op).Localization}
    (hX : AtStrands M X) (hY : AtStrands N Y) (f : X ⟶ Y) : M = N := by
  obtain ⟨a, rfl, rfl⟩ := hX
  obtain ⟨b, rfl, rfl⟩ := hY
  by_contra h
  exact (isEmpty_loc_hom h).elim f

/-- **The localized base is the disjoint union of its strand components.** -/
noncomputable def strandDecomposition :
    ((W Zbp).op).Localization ≌ Σ N : ℕ, (AtStrands N).FullSubcategory :=
  ObjectProperty.sigmaEquiv AtStrands exists_atStrands
    fun hX hY f => atStrands_eq_of_hom hX hY f

end ChainCat
