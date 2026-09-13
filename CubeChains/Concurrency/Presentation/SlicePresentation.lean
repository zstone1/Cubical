import CubeChains.Concurrency.Presentation.SliceThin
import CubeChains.Machinery.Presentation.SliceColimit

/-!
# Concurrency/Presentation/SlicePresentation — the colimit of the localized slices

`Ch(K)[W⁻¹]` is the localized category of elements of `wedgeHoms K` (`locEquivElements`), so a
functor of slice presentations descends to a presentation of the whole: a colimit over the elements
category, one copy per chain, joined along the arrows of `Ch K` (`presentsChainsColimit`).

The slice is *not* the elements of a functor on the localized base — the obstruction is the fibres,
not the formula (`merge_fibres_clash`) — so the family cannot be induced by descent; it is the
beads' own weak orders instead (`Concurrency/Presentation/Dehornoy`).
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph

namespace ChainCat

/-! ## The slice of `Ch K`, for an arbitrary `K`

A chain of `K` lies over its own shape, and `toChZ K` is a discrete fibration, so the slice under
it *is* the base's slice over that shape — and `W K` is the base's class pulled back.  So the
localized slice under a chain depends only on the chain's dimension sequence. -/

/-- A chain lies over its own shape. -/
theorem toChZ_obj (K : BPSet) (c : Ch K) : (toChZ K).obj c = zObj c.dims := Obj.eq_of_dims rfl

/-- **The localized slice of `Ch K` under a chain is the base's under its shape.** -/
noncomputable def locOverEquivBase (K : BPSet) (c : Ch K) :
    ((W K).over (X := c)).Localization ≌ ((W Zbp).over (X := zObj c.dims)).Localization := by
  rw [W_eq_inverseImage_toChZ K]
  exact toChZ_obj K c ▸ sliceLocEquiv (toChZ K) (W Zbp) c

/-! ## Gluing the slices

One copy of the slice polygraph per chain of `K`, joined along the arrows of `Ch K` — a colimit over
the elements category, transported along `locEquivElements`. -/

/-- `W K` read on the category of elements, in the spelling the colimit route uses. -/
theorem W_eq_inverseImage_elements (K : BPSet) :
    W K = ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).inverseImage
      (toElements K) := by
  ext a b f
  rw [W_eq_inverseImage_toChZ]
  rfl

/-- **The elements route localizes `Ch K`**: `toElements K` is an equivalence and carries one class
to the other (`of_inverseImage`). -/
instance isLocalization_toElements (K : BPSet) :
    (toElements K ⋙
      ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q).IsLocalization (W K) :=
  Functor.IsLocalization.of_inverseImage (toElements K) _ _ (W K)
    (W_eq_inverseImage_elements K)

/-- **`Ch(K)[W⁻¹]` is the localized category of elements.** -/
noncomputable def locEquivElements (K : BPSet) :
    (W K).Localization ≌
      ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Localization :=
  Localization.uniq (W K).Q
    (toElements K ⋙ ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q) (W K)

/-- **`Ch(K)[W⁻¹]` is presented by the colimit of the slice presentations, for every `K`.**  The
slices being posets is supplied here; the caller brings only a functor of slice presentations
(`P`, `hP`). -/
noncomputable def presentsChainsColimit (K : BPSet) {P : Ch Zbp ⥤ Polygraph.{0, 0, 0}}
    (p : ∀ d : Ch Zbp, Presents (P.obj d) (((W Zbp).over (X := d)).Localization))
    (hP : ∀ {d' d : Ch Zbp} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc (W Zbp) f) :
    Presents (Limits.colimit (elementsPoly (wedgeHoms K) P)) ((W K).Localization) :=
  (presentsSliceColimit (wedgeHoms K) (W Zbp) p hP).transport
    (locEquivElements K).symm

/-! ## The cells of the colimit

A copy is indexed by an element of `wedgeHoms K` — a chain of the base with a map into `K` — and
its cells are that chain's slice polygraph's.  Everything here is the colimit's universal property
read on a leg; no cell of the colimit is ever examined. -/

section Cells

variable (K : BPSet) (P : Ch Zbp ⥤ Polygraph.{0, 0, 0})

/-- **A 0-cell of the colimit**: a 0-cell of a copy. -/
noncomputable def ιV (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a : (P.obj (eltBase (wedgeHoms K) c)).V) :
    GenObj (Limits.colimit (elementsPoly (wedgeHoms K) P)).Gen :=
  (Limits.colimit.ι (elementsPoly (wedgeHoms K) P) c).pre.obj ⟨a⟩

variable (p : ∀ d : Ch Zbp, Presents (P.obj d) (((W Zbp).over (X := d)).Localization))
  (hP : ∀ {d' d : Ch Zbp} (f : d' ⟶ d),
    (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc (W Zbp) f)

/-- **The object a 0-cell of the colimit names**: its own slice object, lifted at the copy's
element.  `colimIncl_desc` computes the comparison on a leg, and that is all a cell ever meets. -/
theorem at_ιV (c : ((wedgeHoms K).Elements)ᵒᵖ) (a : (P.obj (eltBase (wedgeHoms K) c)).V) :
    (presentsChainsColimit K p hP).at' (ιV K P c a)
      = (locEquivElements K).inverse.obj
          ((colimSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).obj
            ((p (eltBase (wedgeHoms K) c)).at' ⟨a⟩)) := by
  have h1 : (presentsChainsColimit K p hP).at' (ιV K P c a)
      = (locEquivElements K).inverse.obj
          ((colimInclFun (wedgeHoms K) P c ⋙
            colimDesc (P := P) (wedgeHoms K) (W Zbp) p hP).obj
              ((P.obj (eltBase (wedgeHoms K) c)).quot.obj ⟨a⟩)) := rfl
  exact h1.trans (congrArg (locEquivElements K).inverse.obj (Functor.congr_obj
    (colimIncl_desc (P := P) (wedgeHoms K) (W Zbp) p hP c)
    ((P.obj (eltBase (wedgeHoms K) c)).quot.obj ⟨a⟩)))

/-- **…and the arrow a word of a copy names**: the arrow its own slice presentation names, lifted.
The `eqToHom`s are `at_ιV`, which the braid does not see. -/
theorem eval_ιWord (c : ((wedgeHoms K).Elements)ᵒᵖ)
    {a b : GenObj (P.obj (eltBase (wedgeHoms K) c)).Gen} (w : Quiver.Path a b) :
    (presentsChainsColimit K p hP).eval.map
        ((Limits.colimit.ι (elementsPoly (wedgeHoms K) P) c).words.map w)
      = eqToHom (at_ιV K P p hP c a.as) ≫ (locEquivElements K).inverse.map
            ((colimSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).map
              ((p (eltBase (wedgeHoms K) c)).eval.map w))
          ≫ eqToHom (at_ιV K P p hP c b.as).symm := by
  have h1 : (presentsChainsColimit K p hP).eval.map
      ((Limits.colimit.ι (elementsPoly (wedgeHoms K) P) c).words.map w)
      = ((colimInclFun (wedgeHoms K) P c ⋙
          colimDesc (P := P) (wedgeHoms K) (W Zbp) p hP) ⋙
            (locEquivElements K).inverse).map
          ((P.obj (eltBase (wedgeHoms K) c)).quot.map w) := rfl
  rw [h1, Functor.congr_hom (congrArg (fun F => F ⋙ (locEquivElements K).inverse)
    (colimIncl_desc (P := P) (wedgeHoms K) (W Zbp) p hP c))]
  rfl

end Cells

/-! ## Why the slice presentations are not induced from the base

A presentation of a category induces one of the category of elements of any functor on it
(`Presents.elements`).  Gluing would be parametric in the base that way if the localized slice were
a category of elements over the *localized* base.  It is not. -/

/-- **The square does not refine the run**: arrows only ever add cuts, and `1` is a boundary of
`[1,1]` but not of `[2]`. -/
theorem isEmpty_hom_two_ones : IsEmpty (zObj ([2] : List ℕ+) ⟶ zObj (𝟙^2)) := by
  have hones : (1 : ℕ) ∈ boundaries (𝟙^2) := by
    rw [show (𝟙^2 : List ℕ+) = [1, 1] from rfl, boundaries_cons, boundaries_singleton]; decide
  have htwo : (1 : ℕ) ∉ boundaries ([2] : List ℕ+) := by rw [boundaries_singleton]; decide
  rw [← not_nonempty_iff, nonempty_hom_iff]
  rintro ⟨-, hsub⟩
  exact htwo (hsub hones)

theorem dimSum_two : BPSet.dimSum ((zObj ([2] : List ℕ+)).dims) = 2 := dimSum_single 2

/-- **The localized slice is not the elements of a functor that descends to the localized base.**
A functor on the localized base sends an inverted arrow to a *bijection*; `Over.forget d` is a
discrete fibration before localizing — which is exactly why `Over d` is the elements category of
`Hom(-, d)` — and it cannot stay one after, because the merge below is inverted while its two
fibres over `d = 1∨1` are `∅` and `{𝟙}`.  The obstruction is the fibres, not the formula, so no
choice of *descending* functor escapes it; what `garsideSlicePresentation` does instead is apply
the germ presentation to the runs over `d`, a germ **down-set**, asking no functor to descend. -/
theorem merge_fibres_clash :
    W Zbp (runMerge (zObj ([2] : List ℕ+)) dimSum_two) ∧
      IsEmpty (zObj ([2] : List ℕ+) ⟶ zObj (𝟙^2)) ∧
      Nonempty (zObj (𝟙^2) ⟶ zObj (𝟙^2)) :=
  ⟨W_runMerge _ dimSum_two, isEmpty_hom_two_ones, ⟨𝟙 _⟩⟩

end ChainCat
