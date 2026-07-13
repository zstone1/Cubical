import CubeChains.Salvetti.Elements
import CubeChains.Salvetti.SerialSalLines
import CubeChains.Schedule.LocalCOM

/-!
# Salvetti/SalLocal — the Salvetti complex of the local COM at a schedule

`salFunctorSlice` was stated about a chain.  Read at a *schedule* it becomes geometry: the local COM
at `x` is the braid arrangement localized at `x`, and its Salvetti complex computes the local
structure of `Sched K` at `x`.

    Sal (localCOM x)  ≌  Int (Lines (⋁ x.chain.dims))  ≌  the strata of the open star of x

The star of `x` is `C (x.chain)`, whose strata are the chains refining `x.chain`
(`ChainCat.sliceEquiv`), which are the faces of `localCOM x` (`serialSalBaseEquiv`).  Three names
for one poset; `salFunctorSlice` transports the fibres.

## Localization

`Int(Lines K)` is glued from these local pieces exactly as `Sched K` is glued from chart stars.
`localToGlobal a` is the base change of `Lines K` along `(Over.forget a).op`; it is fully faithful
as soon as `Ch K` is thin (a refinement `c ⟶ a` is then a *property* of `c`, not extra data), its
image is the star of `a` (`localToGlobal_essImage`), and the stars cover (`mem_localToGlobal_self`).
-/

open CategoryTheory Opposite CubeChain

namespace CategoryTheory.Over

universe v₁ u₁

/-- In a thin category the triangle over `X` commutes for free, so every base morphism lifts.
(`Over.forget` is faithful unconditionally — `Over.forget_faithful`.) -/
instance forget_full {C : Type u₁} [Category.{v₁} C] [Quiver.IsThin C] (X : C) :
    (Over.forget X).Full where
  map_surjective g := ⟨Over.homMk g (Subsingleton.elim _ _), rfl⟩

end CategoryTheory.Over

namespace CubeChains

variable {K : BPSet}

/-- The fibre iso of `salFunctorSlice`, read at a schedule: the Salvetti presheaf of the local COM
at `x` is the `Lines` presheaf on the chains refining `x.chain`. -/
noncomputable def salFunctorLocal (x : Sched K) :
    COM.salFunctor (localCOM x)
      ≅ ((serialSalBaseEquiv x.chain.dims).inverse ⋙ (ChainCat.sliceEquiv x.chain).op.inverse)
          ⋙ (Over.forget x.chain).op ⋙ Lines K :=
  salFunctorSlice x.chain

/-- The Salvetti complex of the local COM at `x` is `Int(Lines)` of `x`'s own shape. -/
noncomputable def salLocalEquiv (x : Sched K) :
    Sal (localCOM x) ≌ (Lines (⋁x.chain.dims)).Elements :=
  braidSerialSalEquiv x.chain.dims

/-- The faces of the local COM at `x` are the chains refining `x.chain` — i.e. the strata of the
open star of `x` in `Sched K`. -/
noncomputable def localFaceEquiv (x : Sched K) :
    (Over x.chain)ᵒᵖ ≌ COM.Face (localCOM x) :=
  (ChainCat.sliceEquiv x.chain).op.trans (serialSalBaseEquiv x.chain.dims)

/-! ## The local Salvetti complex as a base change of the global one -/

/-- `(localFaceEquiv x).symm.functor` is *syntactically* the base functor of `salFunctorLocal`
(`Equivalence.symm`/`trans` reduce to it), so `preEquivalence` applies with no `eqToIso` shim. -/
noncomputable def salLocalElements (x : Sched K) :
    Sal (localCOM x) ≌ ((Over.forget x.chain).op ⋙ Lines K).Elements :=
  (COM.salElementsEquiv (localCOM x)).trans
    ((CategoryOfElements.mapEquivalence (salFunctorLocal x)).trans
      (CategoryOfElements.preEquivalence ((Over.forget x.chain).op ⋙ Lines K)
        (localFaceEquiv x).symm))

/-- Base change of `Lines K` along `(Over.forget a).op`.  `∫(Lines K) → (Ch K)ᵒᵖ` is a discrete
fibration, so this exhibits the local Salvetti complex as the pullback
`(Over a)ᵒᵖ ×_{(Ch K)ᵒᵖ} Int(Lines K)`. -/
noncomputable def localToGlobal (a : Ch K) :
    ((Over.forget a).op ⋙ Lines K).Elements ⥤ (Lines K).Elements :=
  CategoryOfElements.pre (Lines K) ((Over.forget a).op)

@[simp] theorem localToGlobal_obj (a : Ch K) (X : ((Over.forget a).op ⋙ Lines K).Elements) :
    (localToGlobal a).obj X = ⟨op X.1.unop.left, X.2⟩ := rfl

instance localToGlobal_faithful (a : Ch K) : (localToGlobal a).Faithful :=
  CategoryOfElements.pre_faithful _ _

instance localToGlobal_full [Quiver.IsThin (Ch K)] (a : Ch K) : (localToGlobal a).Full :=
  CategoryOfElements.pre_full _ _

/-- Thinness makes "refines `a`" a property of a chain, not data, so the star of `a` sits inside
`Int(Lines K)` as a full subcategory. -/
noncomputable def localToGlobalFullyFaithful [Quiver.IsThin (Ch K)] (a : Ch K) :
    (localToGlobal a).FullyFaithful :=
  .ofFullyFaithful _

/-- **Localization:** the Salvetti complex of `localCOM x` is a full subcategory of `Int(Lines K)`
— the part lying over the open star of `x.chain`. -/
noncomputable def salLocalFullyFaithful [Quiver.IsThin (Ch K)] (x : Sched K) :
    ((salLocalElements x).functor ⋙ localToGlobal x.chain).FullyFaithful :=
  .ofFullyFaithful _

/-! ## The image is the star of `a`, and the stars cover -/

/-- The objects of `Int(Lines K)` hit by `localToGlobal a` are exactly the lines on the chains
that refine `a`. -/
theorem localToGlobal_range (a : Ch K) :
    Set.range (localToGlobal a).obj = {Z : (Lines K).Elements | Nonempty (Z.1.unop ⟶ a)} := by
  ext Z
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨X.1.unop.hom⟩
  · rintro ⟨f⟩
    exact ⟨⟨op (Over.mk f), Z.2⟩, rfl⟩

/-- The essential image agrees with the strict image `localToGlobal_range`: the star of `a`. -/
theorem localToGlobal_essImage (a : Ch K) (Z : (Lines K).Elements) :
    (localToGlobal a).essImage Z ↔ Nonempty (Z.1.unop ⟶ a) := by
  constructor
  · rintro ⟨X, ⟨i⟩⟩
    exact ⟨i.hom.1.unop ≫ X.1.unop.hom⟩
  · rintro ⟨f⟩
    exact ⟨⟨op (Over.mk f), Z.2⟩, ⟨Iso.refl _⟩⟩

/-- **The stars cover:** every object of `Int(Lines K)` is in the local Salvetti complex at its own
chain (take the identity refinement). -/
theorem mem_localToGlobal_self (Z : (Lines K).Elements) :
    Z ∈ Set.range (localToGlobal Z.1.unop).obj := by
  rw [localToGlobal_range]
  exact ⟨𝟙 _⟩

end CubeChains
