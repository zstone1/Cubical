import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Foundations/GroupExtensionChase

An elementary four-lemma for a map of group extensions: bijectivity of the middle map
transfers to a bijection on kernels. Given a commuting square `π' ∘ g = h ∘ π` with `g`
bijective and `h` injective, `g` induces a bijection `ker π ≃ ker π'`.
-/

namespace CubeChains

/-- In a commuting square `π' ∘ g = h ∘ π`, if `g` is surjective and `h` is injective,
then every element of `ker π'` is `g` of some element of `ker π`. -/
theorem surjective_onto_ker
    {E E' Q Q' : Type*} [Group E] [Group E'] [Group Q] [Group Q']
    {π : E →* Q} {π' : E' →* Q'} {g : E →* E'} {h : Q →* Q'}
    (hcomm : ∀ e, π' (g e) = h (π e))
    (hg : Function.Surjective g) (hh : Function.Injective h) :
    ∀ y : E', π' y = 1 → ∃ x : E, π x = 1 ∧ g x = y := by
  intro y hy
  obtain ⟨x, rfl⟩ := hg y
  refine ⟨x, ?_, rfl⟩
  apply hh
  rw [← hcomm x, hy, map_one]

/-- `g` restricted to kernels, when the square `π' ∘ g = h ∘ π` commutes. -/
def kerHom {E E' Q Q' : Type*} [Group E] [Group E'] [Group Q] [Group Q']
    {π : E →* Q} {π' : E' →* Q'} {g : E →* E'} {h : Q →* Q'}
    (hcomm : ∀ e, π' (g e) = h (π e)) : π.ker →* π'.ker :=
  (g.restrict π.ker).codRestrict π'.ker fun x => by
    rw [MonoidHom.mem_ker, MonoidHom.restrict_apply, hcomm, (MonoidHom.mem_ker.mp x.2), map_one]

@[simp]
theorem kerHom_coe {E E' Q Q' : Type*} [Group E] [Group E'] [Group Q] [Group Q']
    {π : E →* Q} {π' : E' →* Q'} {g : E →* E'} {h : Q →* Q'}
    (hcomm : ∀ e, π' (g e) = h (π e)) (k : π.ker) :
    ((kerHom hcomm k : π'.ker) : E') = g (k : E) := rfl

/-- If `g` is bijective and `h` is injective, the induced map on kernels is bijective. -/
theorem kerHom_bijective {E E' Q Q' : Type*} [Group E] [Group E'] [Group Q] [Group Q']
    {π : E →* Q} {π' : E' →* Q'} {g : E →* E'} {h : Q →* Q'}
    (hcomm : ∀ e, π' (g e) = h (π e))
    (hg : Function.Bijective g) (hh : Function.Injective h) :
    Function.Bijective (kerHom hcomm) := by
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · have hval : g (a : E) = g (b : E) := by
      have := congrArg Subtype.val hab
      rwa [kerHom_coe, kerHom_coe] at this
    exact Subtype.ext (hg.1 hval)
  · obtain ⟨x, hx, hgx⟩ :=
      surjective_onto_ker hcomm hg.surjective hh (y : E') (MonoidHom.mem_ker.mp y.2)
    exact ⟨⟨x, MonoidHom.mem_ker.mpr hx⟩, Subtype.ext (by rw [kerHom_coe]; exact hgx)⟩

end CubeChains
