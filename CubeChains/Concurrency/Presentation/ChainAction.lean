import CubeChains.Concurrency.Presentation.ArtinChains

/-!
# Concurrency/Presentation/ChainAction — the localized chains are the positive braid action

`artinChainPoly n` presents `Ch(H(□ⁿ))[W⁻¹]` (`presentsArtinChains`).  Reversed, it **is** the
total polygraph of the Artin presentation of `PosBraid n` acting on the orderings: a run is an
ordering (`runFibreEquiv`), a codimension-one chain is a cut acting on one, and a codimension-two
chain is a commutation or a braid relation there.  Two presentations of one polygraph name one
category, so the positive braid action falls out of the presentation and not out of the descent.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph

namespace ChainCat

variable {n : ℕ}

/-! ## The action polygraph -/

/-- **The Artin generators acting on the orderings**, as a 2-polygraph: the total polygraph of the
Artin presentation of `PosBraid n` over the `n!` orderings. -/
noncomputable def actPoly (n : ℕ) : Polygraph := (artinBP.comp n).elementsPoly (permPresheaf n)

/-- The 0-cell a run names: its ordering. -/
noncomputable def actPt (z : CubeRun n) : GenObj (actPoly n).Gen :=
  ⟨⟨artinBP.v n, runFibreEquiv n z⟩⟩

theorem actPt_injective : Function.Injective (actPt (n := n)) := by
  intro z z' h
  have h2 : (⟨artinBP.v n, runFibreEquiv n z⟩ :
        (artinBP.comp n).elementsV (permPresheaf n))
      = ⟨artinBP.v n, runFibreEquiv n z'⟩ := congrArg GenObj.as h
  exact (runFibreEquiv n).injective (eq_of_heq (Sigma.mk.inj_iff.mp h2).2)

theorem actPt_surjective : Function.Surjective (actPt (n := n)) := by
  rintro ⟨⟨x, σ⟩⟩
  obtain rfl : x = artinBP.v n := artinBP.eq_v x
  exact ⟨(runFibreEquiv n).symm σ,
    congrArg GenObj.mk (Sigma.ext rfl (heq_of_eq ((runFibreEquiv n).apply_symm_apply σ)))⟩

/-- **A cut acts on an ordering by its transposition.** -/
theorem permPresheaf_map_arrow (k : Fin (n - 1)) (σ : Equiv.Perm (Fin n)) :
    (permPresheaf n).map ((artinBP.comp n).arrow
        (x := (⟨artinBP.v n⟩ : GenObj (artinBP.P n).Gen)) (y := ⟨artinBP.v n⟩) k) σ
      = (adjT k)⁻¹ * σ := by
  show (posPermHom n (artinBP.braid k))⁻¹ * σ = _
  rw [← BraidPresentation.perm, artinBP_perm]

/-- The 1-cell a codimension-one chain names: its cut, acting. -/
noncomputable def actGen {x y : CubeRun n} (e : AtomGen n x y) : actPt y ⟶ actPt x :=
  ⟨e.1, by
    refine (permPresheaf_map_arrow e.1 (runFibreEquiv n y)).trans ?_
    rw [← runFibreEquiv_atomStep, e.2.atomLoop]
    rfl⟩

/-- **The 0-cells and the 1-cells, mapped into the action polygraph.** -/
noncomputable def actPre (n : ℕ) :
    GenObj ((artinChainPoly n).op).Gen ⥤q GenObj (actPoly n).Gen where
  obj A := actPt A.as
  map {_ _} e := actGen e

/-- The word of the base a word of chains projects to. -/
noncomputable def actWord {A B : GenObj ((artinChainPoly n).op).Gen} (p : Quiver.Path A B) :
    Quiver.Path (⟨artinBP.v n⟩ : GenObj (artinBP.P n).Gen) ⟨artinBP.v n⟩ :=
  ((artinBP.comp n).elementsProj (permPresheaf n)).mapPath ((actPre n).mapPath p)

/-- **A square or a hexagon projects to its own Artin relation.** -/
theorem artinRel_actWord {A B : GenObj ((artinChainPoly n).op).Gen}
    (α : ((artinChainPoly n).op).Rel A B) :
    ArtinRel n (MonoidPoly.word (rels := ArtinRel n) (actWord (((artinChainPoly n).op).src α)))
      (MonoidPoly.word (rels := ArtinRel n) (actWord (((artinChainPoly n).op).tgt α))) := by
  refine cell_induction (motive := fun {A B} α =>
    ArtinRel n
      (MonoidPoly.word (rels := ArtinRel n)
        (actWord (Polygraph.revPath (Gen := Polygraph.opGen (artinChainPoly n).Gen)
          ((artinChainPoly n).src α))))
      (MonoidPoly.word (rels := ArtinRel n)
        (actWord (Polygraph.revPath (Gen := Polygraph.opGen (artinChainPoly n).Gen)
          ((artinChainPoly n).tgt α))))) ?_ α
  rintro (⟨i, j, hij⟩ | ⟨i, j, hij⟩) z
  · exact ArtinRel.comm i j hij
  · exact ArtinRel.braid i j hij

/-- **The hand-written polygraph, reversed, mapped into the action polygraph.** -/
noncomputable def actMap (n : ℕ) : (artinChainPoly n).op ⟶ actPoly n where
  pre := actPre n
  two {_ _} α :=
    { src := (actPre n).mapPath (((artinChainPoly n).op).src α)
      tgt := (actPre n).mapPath (((artinChainPoly n).op).tgt α)
      cell := ⟨(actWord (((artinChainPoly n).op).src α), actWord (((artinChainPoly n).op).tgt α)),
        artinRel_actWord α⟩
      src_eq := rfl
      tgt_eq := rfl }
  src_two _ := rfl
  tgt_two _ := rfl

/-! ## The comparison is a bijection in every dimension

The 0-cells are the orderings (`runFibreEquiv`), the 1-cells the cuts that act, and a 2-cell of the
action polygraph is its relation and the ordering it stands over — the words above it are the
unique lifts along the covering (`elementsProj_star_injective`). -/

theorem actWord_src_cell (K : PairKind n) (z : CubeRun n) :
    actWord (((artinChainPoly n).op).src (K.cell z)) = (artinBP.P n).src K.rel := by
  cases K <;> rfl

theorem actWord_tgt_cell (K : PairKind n) (z : CubeRun n) :
    actWord (((artinChainPoly n).op).tgt (K.cell z)) = (artinBP.P n).tgt K.rel := by
  cases K <;> rfl

theorem bijective_actMap_obj (n : ℕ) : Function.Bijective (actMap n).pre.obj := by
  refine ⟨fun _ _ h => congrArg GenObj.mk (actPt_injective h), fun a => ?_⟩
  obtain ⟨z, hz⟩ := actPt_surjective a
  exact ⟨⟨z⟩, hz⟩

theorem bijective_actMap_map (n : ℕ) (A B : GenObj ((artinChainPoly n).op).Gen) :
    Function.Bijective ((actMap n).pre.map : (A ⟶ B) → _) := by
  constructor
  · rintro ⟨k, e⟩ ⟨k', e'⟩ h
    obtain rfl : k = k' := congrArg Subtype.val h
    exact Sigma.ext rfl (heq_of_eq (AtomChain.ext _ _))
  · rintro ⟨k, hk⟩
    refine ⟨⟨k, AtomChain.of ((runFibreEquiv n).injective ?_)⟩, Subtype.ext rfl⟩
    rw [runFibreEquiv_atomStep, ← permPresheaf_map_arrow k (runFibreEquiv n A.as)]
    exact hk

theorem bijective_actMap_two (n : ℕ) (A B : GenObj ((artinChainPoly n).op).Gen) :
    Function.Bijective ((actMap n).two : ((artinChainPoly n).op).Rel A B → _) := by
  haveI := Polygraph.pathsFunctor_faithful' (actMap n) (bijective_actMap_obj n)
    (bijective_actMap_map n)
  constructor
  · intro α α' h
    refine boundaryDetermined_artinChainPoly α α' ?_ ?_
    · refine ((artinChainPoly n).revPath_op_src α).symm.trans
        (Eq.trans ?_ ((artinChainPoly n).revPath_op_src α'))
      exact congrArg
        (fun p : Quiver.Path A B =>
          Polygraph.revPath (Gen := (artinChainPoly n).Gen) p)
        ((actMap n).pre.pathsFunctor.map_injective (congrArg Polygraph.ComapRel.src h))
    · refine ((artinChainPoly n).revPath_op_tgt α).symm.trans
        (Eq.trans ?_ ((artinChainPoly n).revPath_op_tgt α'))
      exact congrArg
        (fun p : Quiver.Path A B =>
          Polygraph.revPath (Gen := (artinChainPoly n).Gen) p)
        ((actMap n).pre.pathsFunctor.map_injective (congrArg Polygraph.ComapRel.tgt h))
  · intro β
    obtain ⟨K, hK⟩ := eq_pairKind_rel β.cell
    have hproj : ∀ {b : GenObj (actPoly n).Gen}
        (S : Quiver.Path ((actMap n).pre.obj A) b)
        (T : Quiver.Path ((actMap n).pre.obj A)
          ((actMap n).pre.obj (⟨K.top A.as⟩ : GenObj ((artinChainPoly n).op).Gen)))
        (_ : ((artinBP.comp n).elementsProj (permPresheaf n)).mapPath S
          = ((artinBP.comp n).elementsProj (permPresheaf n)).mapPath T),
        (⟨b, S⟩ : Quiver.PathStar ((actMap n).pre.obj A)) = ⟨_, T⟩ := by
      intro b S T hST
      exact ((artinBP.comp n).elementsProj (permPresheaf n)).pathStar_injective
        (Presents.elementsProj_star_injective (artinBP.comp n) (permPresheaf n)) _
        (Sigma.ext rfl (heq_of_eq hST))
    have hs := hproj β.src ((actMap n).two (K.cell A.as)).src
      ((β.src_eq.trans (congrArg (artinBP.P n).src hK)).trans (actWord_src_cell K A.as).symm)
    obtain rfl : B = (⟨K.top A.as⟩ : GenObj ((artinChainPoly n).op).Gen) :=
      (bijective_actMap_obj n).1 (congrArg Sigma.fst hs)
    refine ⟨K.cell A.as, Polygraph.ComapRel.ext ?_ ?_ ?_⟩
    · exact (eq_of_heq (Sigma.mk.inj_iff.mp hs).2).symm
    · exact (eq_of_heq (Sigma.mk.inj_iff.mp (hproj β.tgt ((actMap n).two (K.cell A.as)).tgt
        ((β.tgt_eq.trans (congrArg (artinBP.P n).tgt hK)).trans
          (actWord_tgt_cell K A.as).symm))).2).symm
    · exact Subtype.ext (Prod.ext ((actWord_src_cell K A.as).trans
        (congrArg (fun ρ => (artinBP.P n).src ρ) hK).symm)
        ((actWord_tgt_cell K A.as).trans
          (congrArg (fun ρ => (artinBP.P n).tgt ρ) hK).symm))

/-! ## The two presentations meet -/

/-- **The action polygraph presents the positive braid action.** -/
noncomputable def presentsActPoly (n : ℕ) : Presents (actPoly n) ((PosBraidAction n)ᵒᵖ) :=
  ((artinBP.comp n).elements (permPresheaf n)).transport
    (opOpEquivalence _).symm |>.transport (permPresheafElementsEquiv (n := n)).op

/-- **…and so, read on the chains, does the hand-written polygraph.** -/
noncomputable def presentsChainAction (n : ℕ) :
    Presents ((artinChainPoly n).op) ((PosBraidAction n)ᵒᵖ) :=
  Polygraph.Presents.ofBijective (actMap n) (bijective_actMap_obj n) (bijective_actMap_map n)
    (bijective_actMap_two n) (presentsActPoly n)

/-- **The decorated cube's localized chains are the positive braid action** — a corollary of the
presentation: `artinChainPoly n` presents both sides, so they are the same category.  No descent
and no discrete fibration enter the statement. -/
noncomputable def chainActionEquiv (n : ℕ) :
    (W (Hbp.obj (□n))).Localization ≌ PosBraidAction n :=
  (((presentsArtinChains n).op).equiv.symm.trans (presentsChainAction n).equiv).unop

end ChainCat
