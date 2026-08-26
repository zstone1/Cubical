import CubeChains.Salvetti.Runs
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Salvetti/Covering — `proj` and `π` are discrete opfibrations

`proj K : Ch⋆ K ⥤ RunWedge` (forget the map to `K`) and `π = CategoryOfElements.π (Lines K)`
(forget the run) both lift arrows uniquely out of each object — they are **discrete opfibrations**
(the `Quiver.star` map is a bijection at every object).  For `proj K` the lift is forced by the
refinement triangle: the target's map to `K` is `φ ≫ x.chain.map`.

Discrete opfibration is the *forward* half of a quiver covering (`Prefunctor.IsCovering`); neither
`proj` nor `π` is a covering (their fibres — labelings, runs — vary), which is why the total space
can be non-contractible over a contractible base.
-/

open CategoryTheory Opposite Quiver CategoryOfElements ChainCat

namespace CubeChains

universe w

variable {E B D : Type*} [Category E] [Category B] [Category D]

/-- A functor is a **discrete opfibration** when its `Quiver.star` map is a bijection at every
object: arrows lift uniquely out of each object. -/
def IsDiscreteOpfibration (p : E ⥤ B) : Prop :=
  ∀ e : E, Function.Bijective (p.toPrefunctor.star e)

theorem IsDiscreteOpfibration.comp {p : E ⥤ B} {q : B ⥤ D}
    (hp : IsDiscreteOpfibration p) (hq : IsDiscreteOpfibration q) :
    IsDiscreteOpfibration (p ⋙ q) :=
  fun e => (hq _).comp (hp e)

/-- **`proj K` is a discrete opfibration.**  Out of `x`, a `RunWedge` arrow `g : proj x ⟶ W`
lifts to
the unique chain `⟨W.dims, g.1 ≫ x.chain.map⟩` carrying `W`'s run, with wedge map `g.1`. -/
theorem proj_isDiscreteOpfibration (K : BPSet) : IsDiscreteOpfibration (proj K) := by
  intro x
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun s => ⟨⟨op ⟨s.1.dims, s.2.1 ≫ x.chain.map⟩, s.1.cls⟩,
      Quiver.Hom.op (⟨s.2.1, rfl⟩ : (⟨s.1.dims, s.2.1 ≫ x.chain.map⟩ : Ch K) ⟶ x.chain),
      s.2.2⟩, ?_, ?_⟩
  · -- LeftInverse: substituting the triangle `φ ≫ x.map = y.map` makes both sides definitional.
    rintro ⟨⟨yc, ys⟩, ⟨fbase, fcompat⟩⟩
    obtain ⟨ycu⟩ := yc
    obtain ⟨ydims, ymap⟩ := ycu
    obtain ⟨φ, w⟩ := fbase
    dsimp only [Opposite.unop_op] at φ w ⊢
    subst w
    rfl
  · rintro ⟨W, g⟩
    rfl

/-- **The category-of-elements projection is a discrete opfibration**, for any `Set`-valued functor:
out of `(c, s)`, an arrow `g : c ⟶ c'` lifts uniquely to `(c', F.map g s)`. -/
theorem categoryOfElements_π_isDiscreteOpfibration {C : Type*} [Category C] (F : C ⥤ Type w) :
    IsDiscreteOpfibration (CategoryOfElements.π F) := by
  intro e
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun s => ⟨⟨s.1, F.map s.2 e.2⟩, s.2, rfl⟩, ?_, ?_⟩
  · rintro ⟨y, f⟩
    refine Sigma.ext (congrArg (fun s : F.obj y.fst => (⟨y.fst, s⟩ : F.Elements)) f.2)
      ((Subtype.heq_iff_coe_eq fun v => iff_of_eq ?_).mpr rfl)
    simp only [Prefunctor.star_apply]
    erw [f.2]
    rfl
  · rintro ⟨W, g⟩
    rfl

/-- **`π K = CategoryOfElements.π (Lines K)`** — forget the run — is a discrete opfibration for
every `K`, being a category-of-elements projection. -/
theorem lines_π_isDiscreteOpfibration (K : BPSet) :
    IsDiscreteOpfibration (CategoryOfElements.π (Lines K)) :=
  categoryOfElements_π_isDiscreteOpfibration (Lines K)

end CubeChains
