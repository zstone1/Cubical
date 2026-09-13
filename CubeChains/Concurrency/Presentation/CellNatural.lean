import CubeChains.Concurrency.Presentation.RunCellFunctor

/-!
# Concurrency/Presentation/CellNatural — the presentation of `Ch(K)[W⁻¹]` is natural in `K`

Squares over a map `f : K ⟶ K'`, reading the polygraph functor against the localized pushforward
`chLocOpMap f`.  All but one commute on the nose: `invIncl`, `backSpelling`, the inclusion of the
kept cells and `chPresentation` are equalities of functors.  The exception is
`presentsLocalization`, which reaches `((W K).op).Localization` through `equivalenceFromModel`; two
localization functors with the same target differ by an automorphism, so its comparison is only an
isomorphism, and the family is pseudonatural rather than natural.  Nothing is chosen: the
comparison is lifted from `cutComparison` along the localization `chCutLocIncl`, and
`chCutLocPresentationIso_unique` says that pins it.
-/

open CategoryTheory Opposite CubeChains BPSet

namespace ChainCat

variable {K K' : BPSet}

/-- **The lifted cut polygraph, localized at the merges** — the functor `cutComparison` compares
along. -/
noncomputable abbrev chCutLocIncl (K : BPSet) :
    (chCutPoly K).presented ⥤ (chCutLocFunctor.obj K).presented :=
  (Polygraph.invIncl (chCutPoly K) (chCutPicked K)).functor

/-- …and the class it inverts. -/
noncomputable abbrev chCutLocClass (K : BPSet) :
    MorphismProperty (chCutPoly K).presented :=
  Polygraph.pickedClosure (chCutPoly K) (chCutPicked K)

/-- The lifted cut polygraph on a map of `K`, read in the presented categories. -/
noncomputable abbrev chCutMap (f : K ⟶ K') :
    (chCutPoly K).presented ⥤ (chCutPoly K').presented :=
  ((chLiftFunctor zCutPresentation).map f).functor

/-! ## The strict halves -/

/-- **Adjoining the formal inverses is natural in `K`.** -/
theorem chCutLocIncl_naturality (f : K ⟶ K') :
    chCutLocIncl K ⋙ (chCutLocFunctor.map f).functor = chCutMap f ⋙ chCutLocIncl K' :=
  Polygraph.invIncl_functor_naturality (chCutPicked K) (chCutPicked K')
    (zCutPresentation.elementsPolyMap (wedgeHomsFunctor.map f))
    fun e he => zCutPresentation.elementsPicked_map Cut.mergeGen (wedgeHomsFunctor.map f) e he

/-- **A cut names, in `Ch(K)[W⁻¹]`, the arrow it named in `Ch K`** — `locComparison`, at the bead
cuts lifted to `K`. -/
noncomputable def cutComparison (K : BPSet) :
    chCutLocIncl K ⋙ (chCutLocPresentation K).E
      ≅ (chCutPresentation K).E ⋙ ((W K).op).Q :=
  (chCutPresentation K).locComparison (chCutPicked K)
    (multiplicativeClosure_chPicked zCutPresentation Cut.mergeGen
      W_op_eq_multiplicativeClosure_mergeGen K)

/-! ## The square at the localized cut polygraph -/

/-- **The square, restricted along the localization** — the three strict halves, with
`cutComparison` at each end. -/
noncomputable def cutRestrictIso (f : K ⟶ K') :
    chCutLocIncl K ⋙ ((chCutLocFunctor.map f).functor ⋙ (chCutLocPresentation K').E)
      ≅ chCutLocIncl K ⋙ ((chCutLocPresentation K).E ⋙ chLocOpMap f) :=
  eqToIso (congrArg (fun G => G ⋙ (chCutLocPresentation K').E) (chCutLocIncl_naturality f))
    ≪≫ Functor.isoWhiskerLeft (chCutMap f) (cutComparison K')
    ≪≫ eqToIso ((congrArg (fun G => G ⋙ ((W K').op).Q)
          (chPresentation_E_naturality zCutPresentation f)).trans
        (congrArg (fun H => (chCutPresentation K).E ⋙ H) (Q_comp_chLocOpMap f).symm))
    ≪≫ Functor.isoWhiskerRight (cutComparison K).symm (chLocOpMap f)

instance isLocalization_chCutLocIncl (K : BPSet) :
    (chCutLocIncl K).IsLocalization (chCutLocClass K) :=
  Polygraph.isLocalization_invIncl (chCutPoly K) (chCutPicked K)

/-- **The cut presentation of `Ch(K)[W⁻¹]` is natural in `K`, up to isomorphism.** -/
noncomputable def chCutLocPresentationIso (f : K ⟶ K') :
    (chCutLocFunctor.map f).functor ⋙ (chCutLocPresentation K').E
      ≅ (chCutLocPresentation K).E ⋙ chLocOpMap f :=
  Localization.liftNatIso (chCutLocIncl K) (chCutLocClass K)
    (chCutLocIncl K ⋙ ((chCutLocFunctor.map f).functor ⋙ (chCutLocPresentation K').E))
    (chCutLocIncl K ⋙ ((chCutLocPresentation K).E ⋙ chLocOpMap f))
    ((chCutLocFunctor.map f).functor ⋙ (chCutLocPresentation K').E)
    ((chCutLocPresentation K).E ⋙ chLocOpMap f) (cutRestrictIso f)

/-- **…restricting to the square it was lifted from**, which pins it. -/
@[simp] theorem isoWhiskerLeft_chCutLocPresentationIso (f : K ⟶ K') :
    Functor.isoWhiskerLeft (chCutLocIncl K) (chCutLocPresentationIso f) = cutRestrictIso f :=
  Localization.isoWhiskerLeft_liftNatIso (chCutLocIncl K) (chCutLocClass K) (cutRestrictIso f)

/-- **…and it is the only comparison that does.** -/
theorem chCutLocPresentationIso_unique (f : K ⟶ K')
    {θ θ' : (chCutLocFunctor.map f).functor ⋙ (chCutLocPresentation K').E
      ≅ (chCutLocPresentation K).E ⋙ chLocOpMap f}
    (h : Functor.isoWhiskerLeft (chCutLocIncl K) θ
      = Functor.isoWhiskerLeft (chCutLocIncl K) θ') : θ = θ' :=
  Localization.iso_ext_isoWhiskerLeft (chCutLocIncl K) (chCutLocClass K) h

/-! ## …at the runs, and at the degree-zero cells

Both layers contribute equalities, so each square is the one above conjugated by a commuting
triangle. -/

/-- **Reading a cut back at the runs is natural in `K`** — on the nose. -/
theorem chRunBack_naturality (f : K ⟶ K') :
    (chRunFunctor.map f).functor ⋙ (chContraction K').backSpelling.functor
      = (chContraction K).backSpelling.functor ⋙ (chCutLocFunctor.map f).functor :=
  Contraction.Map.backSpelling_functor_naturality (chRunMap f)

/-- **The run presentation of `Ch(K)[W⁻¹]` is natural in `K`, up to isomorphism.** -/
noncomputable def chRunPresentationIso (f : K ⟶ K') :
    (chRunFunctor.map f).functor ⋙ (chRunPresentation K').E
      ≅ (chRunPresentation K).E ⋙ chLocOpMap f :=
  eqToIso (congrArg (fun G => G ⋙ (chCutLocPresentation K').E) (chRunBack_naturality f))
    ≪≫ Functor.isoWhiskerLeft (chContraction K).backSpelling.functor
        (chCutLocPresentationIso f)

/-- **The degree-zero presentation is natural in `K`, up to isomorphism** — for every `K` and with
no hypothesis on `K`. -/
noncomputable def chCellPresentationIso (f : K ⟶ K') :
    (chCellFunctor.map f).functor ⋙ (chCellPresentation K').E
      ≅ (chCellPresentation K).E ⋙ chLocOpMap f :=
  eqToIso (congrArg (fun G => G ⋙ (chRunPresentation K').E) (chCellFunctor_incl f))
    ≪≫ Functor.isoWhiskerLeft (chRunCutSpans K).incl.functor (chRunPresentationIso f)

/-! ## The unit coherence

At the identity every strict half is an identity and the two ends of `cutComparison` cancel, so the
comparison is the transport it has to be — and each layer above inherits that by whiskering. -/

theorem chCutLocSquare_id (K : BPSet) :
    (chCutLocFunctor.map (𝟙 K)).functor ⋙ (chCutLocPresentation K).E
      = (chCutLocPresentation K).E ⋙ chLocOpMap (𝟙 K) :=
  square_id (Polygraph.functor_map_id chCutLocFunctor K) (chLocOpMap_id K) _

theorem chCutLocPresentationIso_id (K : BPSet) :
    chCutLocPresentationIso (𝟙 K) = eqToIso (chCutLocSquare_id K) := by
  refine chCutLocPresentationIso_unique (𝟙 K) ?_
  rw [isoWhiskerLeft_chCutLocPresentationIso, isoWhiskerLeft_eqToIso]
  exact conj_id_eq_eqToIso (cutComparison K)
    (Polygraph.functor_map_id (chLiftFunctor zCutPresentation) K) (chLocOpMap_id K) _ _ _

theorem chRunSquare_id (K : BPSet) :
    (chRunFunctor.map (𝟙 K)).functor ⋙ (chRunPresentation K).E
      = (chRunPresentation K).E ⋙ chLocOpMap (𝟙 K) :=
  square_id (Polygraph.functor_map_id chRunFunctor K) (chLocOpMap_id K) _

theorem chRunPresentationIso_id (K : BPSet) :
    chRunPresentationIso (𝟙 K) = eqToIso (chRunSquare_id K) := by
  rw [chRunPresentationIso, chCutLocPresentationIso_id]
  refine Eq.trans (congrArg (Iso.trans _) (isoWhiskerLeft_eqToIso _ _)) ?_
  exact eqToIso_trans _ _

theorem chCellSquare_id (K : BPSet) :
    (chCellFunctor.map (𝟙 K)).functor ⋙ (chCellPresentation K).E
      = (chCellPresentation K).E ⋙ chLocOpMap (𝟙 K) :=
  square_id (Polygraph.functor_map_id chCellFunctor K) (chLocOpMap_id K) _

/-- **The unit coherence, at the degree-zero cells.** -/
theorem chCellPresentationIso_id (K : BPSet) :
    chCellPresentationIso (𝟙 K) = eqToIso (chCellSquare_id K) := by
  rw [chCellPresentationIso, chRunPresentationIso_id]
  refine Eq.trans (congrArg (Iso.trans _) (isoWhiskerLeft_eqToIso _ _)) ?_
  exact eqToIso_trans _ _

end ChainCat
