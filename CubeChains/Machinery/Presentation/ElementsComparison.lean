import CubeChains.Machinery.Presentation.Comparison
import CubeChains.Machinery.Presentation.Elements

/-!
# Machinery/Presentation/ElementsComparison — a comparison of bases compares the total polygraphs

A spelling of one base by another lifts along the fibration: a base word acting on an element lifts
uniquely (`wordLift`), so a 1-cell of `∫F` spells the lift of the word its base 1-cell spells.  The
2-cells need no check — the lift names the same arrow and `E` is faithful, which is what
`Presents.Map.ofSpelling` consumes.  Reindexing the presheaf moves only the element, so the square
over a map of presheaves is an equality of prefunctors, with the element's transport the only
`homOfEq` in it.
-/

universe w₂' w₂ w''' w'' w' w v u''' u' u

namespace CategoryTheory.Presents

open Polygraph

variable {P : Polygraph.{w, u', w₂}} {P' : Polygraph.{w'', u''', w₂'}} {C : Type u}
  [Category.{v} C] (p : Presents P C) (p' : Presents P' C) (φ : GenObj P.Gen ⥤q P'.Word)
  (θ : ∀ x : GenObj P.Gen, p'.eval.obj (φ.obj x) ≅ p.at' x)
  (hφ : ∀ {x y : GenObj P.Gen} (e : x ⟶ y),
    p'.eval.map (φ.map e) = (θ x).hom ≫ p.arrow e ≫ (θ y).inv)

section Lift

variable (F : C ⥤ Type w')

include hφ in
/-- The element a spelled word carries, at its target. -/
theorem elementsSpell_prop {z z' : GenObj (p.elementsGen F)} (e : z ⟶ z') :
    F.map (p'.eval.map (φ.map e.1)) (F.map (θ (P.pt z.as.1)).inv z.as.2)
      = F.map (θ (P.pt z'.as.1)).inv z'.as.2 := by
  rw [← Functor.map_comp_apply, hφ e.1, ← Category.assoc, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp, Functor.map_comp_apply, e.2]

/-- **A 1-cell of `∫F` spells the lift of the word its base 1-cell spells.** -/
noncomputable def elementsCells : GenObj (p.elementsGen F) ⥤q (p'.elementsPoly F).Word where
  obj z := ⟨⟨(φ.obj (P.pt z.as.1)).as, F.map (θ (P.pt z.as.1)).inv z.as.2⟩⟩
  map {_ _} e := p'.wordLift F (φ.map e.1) (elementsSpell_prop p p' φ θ hφ F e)

@[simp] theorem elementsProj_elementsCells {z z' : GenObj (p.elementsGen F)} (e : z ⟶ z') :
    (p'.elementsProj F).mapPath ((elementsCells p p' φ θ hφ F).map e) = φ.map e.1 :=
  p'.elementsProj_mapPath_wordLift F _ _

/-- The 0-cells, named compatibly — the base's isomorphism, carrying its element. -/
noncomputable def elementsTheta (z : GenObj (p.elementsGen F)) :
    (p'.elements F).eval.obj ((elementsCells p p' φ θ hφ F).obj z) ≅ (p.elements F).at' z :=
  CategoryOfElements.isoMk _ _ (θ (P.pt z.as.1)) (by
    change F.map (θ (P.pt z.as.1)).hom (F.map (θ (P.pt z.as.1)).inv z.as.2) = z.as.2
    rw [← Functor.map_comp_apply, Iso.inv_hom_id, F.map_id_apply])

include hφ in
/-- **A comparison of bases compares the total polygraphs** — the words are the lifts, and the
2-cells cost nothing. -/
noncomputable def elementsMap : Presents.Map (p.elements F) (p'.elements F) :=
  Presents.Map.ofSpelling (elementsCells p p' φ θ hφ F) (elementsTheta p p' φ θ hφ F) (by
    intro z z' e
    refine Subtype.ext ?_
    rw [p'.elements_eval_val F, elementsProj_elementsCells, CategoryOfElements.comp_val,
      CategoryOfElements.comp_val, p.elements_arrow_val F e]
    exact hφ e.1)

/-- **…as a spelling.** -/
noncomputable def elementsSpelling : Spelling (p.elementsPoly F) (p'.elementsPoly F) :=
  (elementsMap p p' φ θ hφ F).hom

@[simp] theorem elementsSpelling_cells :
    (elementsSpelling p p' φ θ hφ F).cells = elementsCells p p' φ θ hφ F := rfl

end Lift

/-! ## Natural in the presheaf -/

section Natural

variable {F F' : C ⥤ Type w'} (τ : F ⟶ F')

/-- **Reindexing moves the element and nothing else.** -/
theorem elementsCells_naturality_obj (z : GenObj (p.elementsGen F)) :
    (p'.elementsQuiver τ).obj ((elementsCells p p' φ θ hφ F).obj z)
      = (elementsCells p p' φ θ hφ F').obj ((p.elementsQuiver τ).obj z) :=
  congrArg (fun m => (⟨⟨(φ.obj (P.pt z.as.1)).as, m⟩⟩ : GenObj (p'.elementsGen F')))
    (NatTrans.naturality_apply τ (θ (P.pt z.as.1)).inv z.as.2)

include hφ in
/-- **The spelling is natural in the presheaf.**  Both composites lift the same base word, and a
word of `∫F` is pinned by its 0-cells and its projection. -/
theorem elementsCells_naturality :
    elementsCells p p' φ θ hφ F ⋙q (p'.elementsQuiver τ).pathsFunctor.toPrefunctor
      = p.elementsQuiver τ ⋙q elementsCells p p' φ θ hφ F' :=
  p'.prefunctor_ext_of_elementsProj F' (elementsCells_naturality_obj p p' φ θ hφ τ)
    fun _ _ e => heq_of_eq
      (((Prefunctor.mapPath_comp_apply (p'.elementsQuiver τ) (p'.elementsProj F')
            ((elementsCells p p' φ θ hφ F).map e)).symm.trans
          (elementsProj_elementsCells p p' φ θ hφ F e)).trans
        (elementsProj_elementsCells p p' φ θ hφ F' ((p.elementsQuiver τ).map e)).symm)

end Natural

end CategoryTheory.Presents
