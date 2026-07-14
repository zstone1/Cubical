import CubeChains.Flow.CFund
import CubeChains.Flow.Fund

/-!
# Flow/Project — the projection `CFund ↠ Fund`, forgetting the line

An `EnrichedFunctor Cat (CFund K) (Fund K)`: the identity on vertices, and on hom-objects the
groupoidification of the category-of-elements projection `π : Int(Lines K) ⥤ (Ch K)ᵒᵖ`.

The whole content is that **forgetting the line commutes with concatenation** — and on generators
that is `rfl`, because the chain half of `concConc` *is* `chConc`.  `lift₂_ext` carries it to the
groupoids.
-/

open CategoryTheory Opposite BPSet

namespace CubeChains

variable {K : BPSet}

/-! ## Forgetting the line -/

/-- Forgetting the line, on a hom-object: `CFund(u,v) ⥤ Fund(u,v)`. -/
noncomputable def flowProj (K : BPSet) (u v : K.cells 0) :
    ConcGrpd (K.repoint u v) ⥤ fundHom K u v :=
  FreeGroupoid.map (CategoryOfElements.π (Lines (K.repoint u v)))

/-- **Forgetting the line commutes with concatenation** — before groupoidification, on the nose. -/
theorem concConc_comp_π (K : BPSet) (u v w : K.cells 0) :
    concConc K u v w ⋙ CategoryOfElements.π (Lines (K.repoint u w))
      = (CategoryOfElements.π (Lines (K.repoint u v))).prod
          (CategoryOfElements.π (Lines (K.repoint v w))) ⋙ chConcatOp K u v w := rfl

/-- The identity execution forgets to the identity chain. -/
theorem flowProj_flowId (K : BPSet) (v : K.cells 0) :
    (flowProj K v v).obj (flowId K v) = fundId K v := rfl

/-- **Forgetting the line commutes with concatenation, on the groupoids.**  This is what makes the
projection an *enriched* functor: it respects the composition law. -/
theorem concGrpdConc_comp_flowProj (K : BPSet) (u v w : K.cells 0) :
    concGrpdConc K u v w ⋙ flowProj K u w
      = (flowProj K u v).prod (flowProj K v w) ⋙ fundConc K u v w := by
  refine FreeGroupoid.lift₂_ext ?_
  rw [← Functor.assoc, concGrpdConc, FreeGroupoid.lift₂_spec, Functor.assoc, flowProj,
    FreeGroupoid.of_comp_map, ← Functor.assoc, concConc_comp_π]
  rw [show ((FreeGroupoid.of (ConcCat (K.repoint u v))).prod
        (FreeGroupoid.of (ConcCat (K.repoint v w)))) ⋙
      ((flowProj K u v).prod (flowProj K v w) ⋙ fundConc K u v w)
      = (((FreeGroupoid.of (ConcCat (K.repoint u v))) ⋙ flowProj K u v).prod
          ((FreeGroupoid.of (ConcCat (K.repoint v w))) ⋙ flowProj K v w))
        ⋙ fundConc K u v w from rfl]
  rw [flowProj, flowProj, FreeGroupoid.of_comp_map, FreeGroupoid.of_comp_map]
  rw [show (((CategoryOfElements.π (Lines (K.repoint u v))) ⋙
        FreeGroupoid.of ((Ch (K.repoint u v))ᵒᵖ)).prod
      ((CategoryOfElements.π (Lines (K.repoint v w))) ⋙
        FreeGroupoid.of ((Ch (K.repoint v w))ᵒᵖ))) ⋙ fundConc K u v w
      = ((CategoryOfElements.π (Lines (K.repoint u v))).prod
          (CategoryOfElements.π (Lines (K.repoint v w))))
        ⋙ (((FreeGroupoid.of ((Ch (K.repoint u v))ᵒᵖ)).prod
              (FreeGroupoid.of ((Ch (K.repoint v w))ᵒᵖ))) ⋙ fundConc K u v w) from rfl]
  rw [fundConc, FreeGroupoid.lift₂_spec]
  rfl

/-! ## The projection as an enriched functor -/

/-- **The projection `CFund K ↠ Fund K`**: forget the line.

Identity on 0-cells; on hom-objects it is `flowProj`.  `map_comp` is exactly
`concGrpdConc_comp_flowProj` — forgetting the line commutes with concatenating executions. -/
noncomputable def cfundToFund (K : BPSet) : EnrichedFunctor Cat (CFund K) (Fund K) where
  obj u := u
  map u v := Cat.Hom.ofFunctor (flowProj K u v)
  map_id u := by
    ext
    refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => ?_)
    -- both `eId`s are constant functors, and the `eqToHom`s sit between definitionally equal
    -- objects, so this is `flowProj.map 𝟙 = 𝟙`
    show (flowProj K u u).map (𝟙 (flowId K u))
        = 𝟙 (fundId K u) ≫ 𝟙 (fundId K u) ≫ 𝟙 (fundId K u)
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    rfl
  map_comp u v w := by
    ext
    exact concGrpdConc_comp_flowProj K u v w

end CubeChains
