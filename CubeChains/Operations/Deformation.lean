import CubeChains.Operations.Span
import Mathlib.CategoryTheory.ConnectedComponents

/-!
# Deformations: how an operation induces zigzags in `Ch K`

This is design condition **(2)** — the bridge from the abstract equivalence
`Φ K ≌ Φ L` (condition (1), `Operations.Span.equivalence`) to concrete **paths
through the undirected nerve of `Ch K`**.

The dictionary (PZ Lemma 2.11 makes `Ch K` a poset, so its nerve is the order
complex and a path in it is a zigzag of refinements):

* **A homotopy of d-paths** `p ⇝ q` is a `Zigzag p q` in the chain category — a finite
  alternating chain of refinement morphisms `p = a₀ ≤ a₁ ≥ a₂ ≤ ⋯ = q`
  (`DHomotopic`).  Homotopy classes are `ConnectedComponents (Φ K) = π₀(Ch K)`.
* **A single morphism (refinement) is a homotopy** (`dhomotopic_of_hom`).
* **A natural transformation is a homotopy of nerves** — its components give a
  pointwise zigzag (`dhomotopic_of_natTrans`).  This is the categorical fact
  `η : F ⟶ G  ⟹  N(F) ≃ N(G)`, in its combinatorial (π₀) shadow.

How an **operation** `s : K ⤳ L` induces zigzags:

1. *Transport.*  `s` gives a bijection of homotopy classes
   `π₀(Ch K) ≃ π₀(Ch L)` (`Span.homotopyClassEquiv`); equivalently it preserves
   *and reflects* the homotopy relation (`Span.dhomotopic_map_iff`).  This is the
   precise sense in which `p` and `Fp` "live in the same category" and homotopies of
   d-paths correspond across the operation.
2. *The deformation itself.*  The round-trip endofunctor `R = e.functor ⋙ e.inverse`
   of `Ch K` is connected to the identity by the unit *natural transformation*
   `𝟭 ⟹ R`; so for every chain `p`, `s` realizes a canonical zigzag `p ⇝ R p` in the
   nerve of `Ch K` (`Span.deformation`).  This is the "ambient isotopy slowly editing
   `p`" — assembled, when `s` is a composite of elementary edits, from one refinement
   step per edit.
-/

open CategoryTheory

namespace Operations

variable {J : Type*} [Category J] {J' : Type*} [Category J']

/-- **Homotopy of d-paths**: a zigzag in the chain category, i.e. a path through the
(undirected) nerve.  `abbrev` so all of mathlib's `Zigzag` API applies. -/
abbrev DHomotopic (p q : J) : Prop := Zigzag p q

/-- A morphism (a refinement) is a homotopy. -/
theorem dhomotopic_of_hom {p q : J} (f : p ⟶ q) : DHomotopic p q := Zigzag.of_hom f

/-- **A natural transformation is a homotopy of nerves**: each component `η.app x`
gives a homotopy `F x ⇝ G x`. -/
theorem dhomotopic_of_natTrans {F G : J ⥤ J'} (η : F ⟶ G) (x : J) :
    DHomotopic (F.obj x) (G.obj x) := Zigzag.of_hom (η.app x)

/-- Any functor preserves homotopy of d-paths. -/
theorem dhomotopic_map (F : J ⥤ J') {p q : J} (h : DHomotopic p q) :
    DHomotopic (F.obj p) (F.obj q) := zigzag_obj_of_zigzag F h

/-- `p` and `q` are homotopic iff they have the same homotopy class (`π₀`). -/
theorem dhomotopic_iff_mk_eq {p q : J} :
    DHomotopic p q ↔ ConnectedComponents.mk p = ConnectedComponents.mk q :=
  ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

/-- **An equivalence of categories induces a bijection of homotopy classes** (`π₀`).
The inverse is `e.inverse` on classes; the round-trips collapse by the unit/counit. -/
def connectedComponentsEquiv (e : J ≌ J') :
    ConnectedComponents J ≃ ConnectedComponents J' where
  toFun := e.functor.mapConnectedComponents
  invFun := e.inverse.mapConnectedComponents
  left_inv := fun x => Quotient.inductionOn x fun p => by
    simp only [Functor.mapConnectedComponents_mk]
    exact (Quotient.sound (Zigzag.of_hom (e.unitIso.hom.app p))).symm
  right_inv := fun x => Quotient.inductionOn x fun q => by
    simp only [Functor.mapConnectedComponents_mk]
    exact Quotient.sound (Zigzag.of_hom (e.counitIso.hom.app q))

namespace Span

variable {C : Type*} [Category C] {Φ : C ⥤ Cat.{v, u}} {K L : C}

/-- **Operations transport homotopy classes.**  The bijection `π₀(Ch K) ≃ π₀(Ch L)`
induced by an operation — homotopy classes of d-paths in `K` and `L` correspond. -/
noncomputable def homotopyClassEquiv (s : Span Φ K L) :
    ConnectedComponents (Φ.obj K) ≃ ConnectedComponents (Φ.obj L) :=
  connectedComponentsEquiv s.equivalence

@[simp] theorem homotopyClassEquiv_mk (s : Span Φ K L) (p : Φ.obj K) :
    s.homotopyClassEquiv (ConnectedComponents.mk p)
      = ConnectedComponents.mk (s.equivalence.functor.obj p) := rfl

/-- **The deformation.**  For each chain `p` in `Ch K`, the operation realizes a
canonical homotopy (zigzag through the nerve of `Ch K`) from `p` to its round-trip
`R p`, `R = e.functor ⋙ e.inverse` — the image of `p` under the unit natural
transformation `𝟭 ⟹ R`. -/
theorem deformation (s : Span Φ K L) (p : Φ.obj K) :
    DHomotopic p ((s.equivalence.functor ⋙ s.equivalence.inverse).obj p) :=
  dhomotopic_of_natTrans s.equivalence.unitIso.hom p

/-- **Operations preserve and reflect homotopy.**  Chains `p`, `q` of `K` are homotopic
iff their images `Fp`, `Fq` are homotopic in `L`. -/
theorem dhomotopic_map_iff (s : Span Φ K L) {p q : Φ.obj K} :
    DHomotopic (s.equivalence.functor.obj p) (s.equivalence.functor.obj q) ↔ DHomotopic p q := by
  refine ⟨fun h => ?_, dhomotopic_map s.equivalence.functor⟩
  exact (deformation s p).trans
    ((dhomotopic_map s.equivalence.inverse h).trans (deformation s q).symm)

end Span
end Operations
