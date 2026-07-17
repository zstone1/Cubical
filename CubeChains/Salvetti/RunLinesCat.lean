import CubeChains.Salvetti.RunLines
import CubeChains.Salvetti.ConcGroupoid
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Category.Cat

/-!
# Salvetti/RunLinesCat — the run-map line presheaf has `ConcCat` as its elements

Transport `Lines` through the linchpin `runLineEquiv : RunLine a ≃ LinesObj a` to get the run-map
presheaf `RunLinesPsh`, natural-isomorphic to `Lines`; hence `∫(RunLinesPsh) ≌ ConcCat`.
-/

open CategoryTheory Opposite

namespace CubeChains

/-- The run-map line presheaf: `Lines` re-encoded with a line of `a` as a bi-pointed map out of the
all-edges run (`RunLine a`), restriction transported through `runLineEquiv`. -/
noncomputable def RunLinesPsh (K : BPSet) : (Ch K)ᵒᵖ ⥤ Type where
  obj X := RunLine X.unop
  map φ := TypeCat.ofHom
    (fun r => (runLineEquiv _).symm (linesRestrict φ.unop (runLineEquiv _ r)))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro r
    change (runLineEquiv X.unop).symm (linesRestrict (𝟙 X.unop) (runLineEquiv X.unop r)) = r
    rw [linesRestrict_id]
    exact (runLineEquiv X.unop).symm_apply_apply r
  map_comp φ ψ := by
    apply ConcreteCategory.hom_ext
    intro r
    change (runLineEquiv _).symm (linesRestrict (φ ≫ ψ).unop (runLineEquiv _ r))
      = (runLineEquiv _).symm (linesRestrict ψ.unop
          (runLineEquiv _ ((runLineEquiv _).symm (linesRestrict φ.unop (runLineEquiv _ r)))))
    rw [Equiv.apply_symm_apply]
    exact congrArg (runLineEquiv _).symm (linesRestrict_comp ψ.unop φ.unop (runLineEquiv _ r))

/-- The linchpin `runLineEquiv`, packaged as a natural iso `RunLinesPsh K ≅ Lines K`: both
presheaves restrict by `linesRestrict`, one just reads it through the run-map coordinates. -/
noncomputable def runLinesPshIso (K : BPSet) : RunLinesPsh K ≅ Lines K :=
  NatIso.ofComponents (fun X => (runLineEquiv X.unop).toIso) fun {X Y} φ => by
    apply ConcreteCategory.hom_ext
    intro r
    change runLineEquiv Y.unop
        ((runLineEquiv Y.unop).symm (linesRestrict φ.unop (runLineEquiv X.unop r)))
      = linesRestrict φ.unop (runLineEquiv X.unop r)
    rw [Equiv.apply_symm_apply]

/-- `∫(run-Lines) ≌ ConcCat`: the run-map line presheaf has the same category of elements as
`Lines`, i.e. as `ConcCat K`.  This is the `Int(Lines') = Int(Lines)` check, via the linchpin. -/
noncomputable def runConcCatEquiv (K : BPSet) : (RunLinesPsh K).Elements ≌ ConcCat K :=
  Cat.equivOfIso (Functor.elementsFunctor.mapIso (runLinesPshIso K))

end CubeChains
