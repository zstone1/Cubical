import CubeChains.Concurrency.Presentation.LiftPresentation
import CubeChains.Concurrency.Presentation.LocFunctor
import CubeChains.Machinery.Presentation.ElementsLocalize

/-!
# Concurrency/Presentation/LiftLocalize — the localized presentation, over every `K`

A presentation of `(Ch Zbp)ᵒᵖ` whose picked 1-cells generate `(W Zbp).op` lifts to one of `(Ch K)ᵒᵖ`
whose lifted picked 1-cells generate `(W K).op`: the class sees only the wedge map, and the
fibration lifts a word of picked arrows letter by letter.  Adjoining a formal inverse to each is
then a functor of `K` — a map of `K` re-indexes the elements and moves no base 1-cell.
-/

universe w₂ w u' u

open CategoryTheory CategoryTheory.Polygraph Opposite CubeChains BPSet

namespace ChainCat

/-! ## The picked 1-cells, lifted along the fibration -/

section Lift

variable {P : Polygraph.{w, u', w₂}} (p : Presents P ((Ch Zbp)ᵒᵖ))
  (S : ∀ {a b : P.V}, P.Gen a b → Prop)

/-- **The picked base 1-cells, acting on a chain of `K`.** -/
def chPicked (K : BPSet) :
    ∀ {z z' : p.elementsV (wedgeHoms K)}, (p.elementsPoly (wedgeHoms K)).Gen z z' → Prop :=
  p.elementsPicked (wedgeHoms K) S

variable (hW : (W Zbp).op = (p.pickedArrows S).multiplicativeClosure)

include hW in
/-- **A lifted picked 1-cell names a merge** — its cartesian lift has the same wedge map. -/
theorem chPicked_le (K : BPSet) :
    (chPresentation K p).pickedArrows (chPicked p S K) ≤ (W K).op := by
  rintro A B f ⟨e, he⟩
  have hz : W Zbp (unop (p.arrow (Polygraph.cell e.1))) := by
    have h : (W Zbp).op (p.arrow (Polygraph.cell e.1)) := by
      rw [hW]
      exact MorphismProperty.le_multiplicativeClosure _ _ (Presents.Picked.mk e.1 he)
    exact h
  have h2 : W K (homOfRestrict (unop (p.arrow (Polygraph.cell e.1))) e.2) :=
    (W_homOfRestrict _ e.2).mpr hz
  change (W K).op ((chPresentation K p).arrow (Polygraph.cell e))
  rw [chPresentation_arrow]
  exact h2

include hW in
/-- **…and every merge is a word of them** — the fibration lifts the factorization downstairs, and
a letter upstairs *is* its projection. -/
theorem W_op_le_chPicked (K : BPSet) :
    (W K).op ≤ ((chPresentation K p).pickedArrows (chPicked p S K)).multiplicativeClosure := by
  intro A B f hf
  set v : (wedgeHoms K).elementsMk (op (zObj (unop A).dims)) (unop A).map
      ⟶ (wedgeHoms K).elementsMk (op (zObj (unop B).dims)) (unop B).map :=
    CategoryOfElements.homMk _ _ (Quiver.Hom.op (zHom (unop f).φ)) (unop f).w with hv
  have h1 : ((W Zbp).op.inverseImage (CategoryOfElements.π (wedgeHoms K))) v := by
    change W Zbp (zHom (unop f).φ)
    rw [W_iff_flat]
    exact (W_iff_flat (unop f)).mp hf
  have h2 : (((p.elements (wedgeHoms K)).pickedArrows
      (p.elementsPicked (wedgeHoms K) S)).multiplicativeClosure) v := by
    rw [p.multiplicativeClosure_pickedArrows_elements (wedgeHoms K) S, ← hW]
    exact h1
  have h3 := MorphismProperty.multiplicativeClosure_map _
    ((chPresentation K p).pickedArrows (chPicked p S K)) (chOfElements K)
    (fun g hg => (p.elements (wedgeHoms K)).pickedArrows_transport
      (p.elementsPicked (wedgeHoms K) S) (elementsEquivChOp K) g hg) h2
  rwa [show (chOfElements K).map v = f from Quiver.Hom.unop_inj (hom_ext' rfl)] at h3

include hW in
/-- **The lifted picked 1-cells generate the merges of `Ch K`**, for every `K`. -/
theorem multiplicativeClosure_chPicked (K : BPSet) :
    (W K).op = ((chPresentation K p).pickedArrows (chPicked p S K)).multiplicativeClosure :=
  _root_.le_antisymm (W_op_le_chPicked p S hW K)
    ((MorphismProperty.multiplicativeClosure_le_iff _ _).mpr (chPicked_le p S hW K))

include hW in
/-- **`Ch K` with the merges inverted is presented by the lifted 1-cells plus a formal inverse for
each lifted picked one**, for every `K` and with no hypothesis on `K`. -/
noncomputable def chLocPresentation (K : BPSet) :
    Presents (invPoly (p.elementsPoly (wedgeHoms K)) (chPicked p S K))
      ((W K).op).Localization :=
  (chPresentation K p).presentsLocalization (chPicked p S K)
    (multiplicativeClosure_chPicked p S hW K)

end Lift

/-! ## …as a functor of `K` -/

section Functorial

variable {P : Polygraph.{w, u', w₂}} (p : Presents P ((Ch Zbp)ᵒᵖ))
  (S : ∀ {a b : P.V}, P.Gen a b → Prop)

/-- **The lifted polygraph, as a functor of `K`** — `wedgeHoms` is a functor of `K` and the total
polygraph a functor of the presheaf. -/
noncomputable def chLiftFunctor : BPSet ⥤ Polygraph.{w, u', max u' w w₂} :=
  wedgeHomsFunctor ⋙ p.elementsPolyFunctor

/-- **…and with the lifted picked 1-cells formally inverted.** -/
noncomputable def chLocFunctor : BPSet ⥤ Polygraph.{w, u', max u' w w₂} :=
  Polygraph.invFunctor (chLiftFunctor p) (fun K => chPicked p S K)
    fun {_ _} f _ _ e he => p.elementsPicked_map S (wedgeHomsFunctor.map f) e he

variable (hW : (W Zbp).op = (p.pickedArrows S).multiplicativeClosure)

include hW in
/-- **Each value of the functor presents the localization at that `K`.** -/
noncomputable def presentsChLoc (K : BPSet) :
    Presents ((chLocFunctor p S).obj K) (((W K).op).Localization) :=
  chLocPresentation p S hW K

end Functorial

/-! ## …and the lifted presentation is natural in `K`

A map of `K` post-composes a chain's classifying map and moves no shape, which is the pushforward;
so the presentation of `Ch K` by the acting base cells is natural on the nose. -/

section Pushforward

/-- **Reindexing the elements is the pushforward** — the chain's dimensions and the base arrow it
refines along are untouched. -/
theorem mapElements_comp_chOfElements {K K' : BPSet} (f : K ⟶ K') :
    NatTrans.mapElements (wedgeHomsFunctor.map f) ⋙ chOfElements K'
      = chOfElements K ⋙ (ChainCat.pushforward f).op :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => Quiver.Hom.unop_inj (hom_ext' rfl)

variable {P : Polygraph.{w, u', w₂}} (p : Presents P ((Ch Zbp)ᵒᵖ))

/-- **The lifted presentation is natural in `K`** — on the nose; no localization is involved. -/
theorem chPresentation_E_naturality {K K' : BPSet} (f : K ⟶ K') :
    ((chLiftFunctor p).map f).functor ⋙ (chPresentation K' p).E
      = (chPresentation K p).E ⋙ (ChainCat.pushforward f).op := by
  refine Eq.trans (congrArg (fun G => G ⋙ chOfElements K')
    (p.elements_E_naturality (wedgeHomsFunctor.map f))) ?_
  exact congrArg (fun G => (p.elements (wedgeHoms K)).E ⋙ G) (mapElements_comp_chOfElements f)

end Pushforward

/-! ## The bead cuts

`zCutPresentation` presents `(Ch Zbp)ᵒᵖ` by its bead cuts and `Cut.mergeGen` picks out the merges,
so the hypothesis is discharged and nothing is left free but `K`. -/

/-- **The bead-cut polygraph of `Ch K` with the merges inverted, as a functor of `K`.** -/
noncomputable def chCutLocFunctor : BPSet ⥤ Polygraph :=
  chLocFunctor zCutPresentation Cut.mergeGen

/-- **`Ch K` with the bead merges inverted is presented by the bead cuts acting on a chain, plus a
formal inverse for each merge generator** — for every `K`, with no hypothesis on `K`. -/
noncomputable def chCutLocPresentation (K : BPSet) :
    Presents (chCutLocFunctor.obj K) (((W K).op).Localization) :=
  presentsChLoc zCutPresentation Cut.mergeGen W_op_eq_multiplicativeClosure_mergeGen K

end ChainCat
