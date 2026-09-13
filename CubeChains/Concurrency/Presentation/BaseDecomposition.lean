import CubeChains.Concurrency.Presentation.BaseComponent
import CubeChains.Machinery.SigmaComponents
import CubeChains.Machinery.Presentation.Restrict

/-!
# Concurrency/Presentation/BaseDecomposition — the strand count is the invariant

An object of the localization is a chain on the nose (`objEquiv`), so it has a strand count, and
`isEmpty_loc_hom` says no arrow changes it — which is what makes `AtStrands N` convex.  Hence
`zLocComponent`: *any* presentation of the localized base restricts to one of each strand
component.
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

/-- No arrow enters or leaves a strand component, so a word between two of its objects stays
inside — the one hypothesis `Presents.restrict` takes. -/
theorem convex_atStrands (N : ℕ) : (AtStrands N).Convex := fun ha _ f _ =>
  (ObjectProperty.prop_iff_of_hom AtStrands exists_atStrands
    (fun hX hY g => atStrands_eq_of_hom hX hY g) f).mp ha

/-- **Every presentation of the localized base restricts to one of each strand component** —
`Presents.restrict` at a strand component, read through `strandComponentGarside`. -/
noncomputable def zLocComponent {P : Polygraph} (p : Presents P (((W Zbp).op).Localization))
    (N : ℕ) : Presents (p.restrictPoly (AtStrands N)) ((SingleObj (PosBraid N))ᵒᵖ) :=
  (p.restrict (AtStrands N) (convex_atStrands N)).transport (strandComponentGarside N).symm

end ChainCat
