import CubeChains.Concurrency.Presentation.BrFunctor

/-!
# Concurrency/Presentation/BrMap — a map of braid presentations, lifted

A map `p ⟶ q` spells a generator of `p` by a **word** of `q` performing the same braid
(`braid_word`).  Above a chain that word lifts once and for all: the projection to the base is a
covering, `bot` is absorbing, and the target run is carried as *data* — so `Presents.definedPath`
gives the lifted word with no recursion, and `famPre_mapPath_definedPath` makes the family strictly
natural in the chain.  Everything above is then the colimit's own functoriality.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits

namespace ChainCat

namespace BraidPresentation.Map

variable {p q : BraidPresentation} (m : BraidPresentation.Map p q)

/-! ## The spelling of the base

`p`'s components are spelled by `q`'s, one strand count at a time, so the coproduct of the
spellings is a spelling of the whole localized base. -/

/-- The 0-cell of `q`'s base a 0-cell of `p`'s spells. -/
def polyObj (a : Σ N, (p.P N).V) : GenObj q.poly.Gen :=
  ⟨⟨a.1, ((m.comp a.1).hom.cells.obj ⟨a.2⟩).as⟩⟩

/-- The word of `q`'s base a generator of `p`'s spells: its own component's word, included. -/
def polyMap : ∀ (a b : Σ N, (p.P N).V), Polygraph.CoproductGen p.P a b →
    Quiver.Path (m.polyObj a) (m.polyObj b)
  | _, _, .mk (i := N) s => (Polygraph.coproductPre q.P N).mapPath (m.word s)

/-- **`p`'s base, spelled in `q`'s.** -/
def polyPre : GenObj p.poly.Gen ⥤q q.poly.Word where
  obj x := m.polyObj x.as
  map {_ _} e := m.polyMap _ _ e

/-- **A spelled generator names the arrow it spells** — `braid_word`, read in the localized base.
There is no isomorphism left over: `PosBraid N` has no non-trivial units. -/
theorem base_eval_polyPre {x y : GenObj p.poly.Gen} (e : x ⟶ y) :
    q.base.eval.map (m.polyPre.map e) = p.base.arrow e := by
  obtain ⟨⟨N, a⟩⟩ := x
  obtain ⟨⟨M, b⟩⟩ := y
  cases e with
  | @mk _ _ _ s =>
      exact (q.base_eval_coproductPre (m.word s)).trans
        ((congrArg (fun β => (runBase N).map (posArrow N β)) (m.braid_word s)).trans
          (p.base_arrow s).symm)

/-! ## The spelling of a slice

A 0-cell of the slice is a base 0-cell carrying a run, and the spelling leaves the run alone: both
presentations name the *same* object of the localized base at a strand count, so the run is
literally the same datum.  Hence the 0-cell map commutes with pushing runs forward on the nose. -/

variable {d' d : Ch Zbp}

/-- The 0-cell of `q`'s slice a 0-cell of `p`'s spells: the same run, at `q`'s own 0-cell. -/
def sliceV (a : (slicePolyRaw p.base d).V) : (slicePolyRaw q.base d).V :=
  ⟨⟨(m.polyObj a.1.1).as, a.1.2⟩, a.2⟩

/-- **The spelling leaves the run alone.** -/
theorem sliceCellRun_sliceV (a : (slicePolyRaw p.base d).V) :
    sliceCellRun (m.sliceV a) = sliceCellRun a := rfl

/-- **The spelled word makes the step the 1-cell makes** — it names the same arrow. -/
theorem sliceMap_step {a b : (slicePolyRaw p.base d).V}
    (e : (⟨a⟩ : GenObj (slicePolyRaw p.base d).Gen) ⟶ ⟨b⟩) :
    (sliceFibre d).map (q.base.eval.map (m.polyPre.map e.1)) a.1.2 = b.1.2 :=
  (congrArg (fun t => (sliceFibre d).map t a.1.2) (m.base_eval_polyPre e.1)).trans e.2

/-- The word of `q`'s slice a 1-cell of `p`'s spells: the base word, lifted at the run. -/
noncomputable def sliceMap {a b : (slicePolyRaw p.base d).V}
    (e : (⟨a⟩ : GenObj (slicePolyRaw p.base d).Gen) ⟶ ⟨b⟩) :
    Quiver.Path (⟨m.sliceV a⟩ : GenObj (slicePolyRaw q.base d).Gen) ⟨m.sliceV b⟩ :=
  Presents.definedPath (sliceFibre d) (sliceBot d) (sliceBot_absorbing d) q.base
    (m.polyPre.map e.1) (m.sliceMap_step e) a.2 b.2

/-- **The spelling is strictly natural in the chain.**  Pushing a run forward is only *laxly*
natural, but a lifted word is pinned by its projection, and the projection does not move. -/
theorem sliceMap_push (f : d' ⟶ d) {a b : (slicePolyRaw p.base d').V}
    (e : (⟨a⟩ : GenObj (slicePolyRaw p.base d').Gen) ⟶ ⟨b⟩) :
    m.sliceMap (((slicePolyRawFunctor p.base).map f).pre.map e)
      = ((slicePolyRawFunctor q.base).map f).pre.mapPath (m.sliceMap e) :=
  (Presents.famPre_mapPath_definedPath q.base (sliceBot_absorbing d') (sliceBot_absorbing d)
    _ (partialFam_push f) (m.polyPre.map e.1) (m.sliceMap_step e) a.2 b.2).symm

/-! ## …in the orientation the glue route uses

`Br` is built on the *reversed* slice — a braid raises the weak order where an arrow of the
localized slice lowers it — so the spelling is read backwards, and `opPre_mapPath` carries the
naturality across. -/

/-- **`p`'s slice, spelled in `q`'s**, with words read backwards. -/
noncomputable def famCells (d : Ch Zbp) :
    GenObj (p.fam.obj d).Gen ⥤q (q.fam.obj d).Word where
  obj a := ⟨m.sliceV a.as⟩
  map {_ _} e := revPath (Gen := opGen (slicePolyRaw q.base d).Gen) (m.sliceMap (opHom e))

theorem famCells_push (f : d' ⟶ d) :
    (p.fam.map f).pre ⋙q m.famCells d
      = m.famCells d' ⋙q (q.fam.map f).pre.pathsFunctor.toPrefunctor :=
  Prefunctor.ext' (fun _ => rfl) fun _ _ e =>
    (congrArg (fun t => revPath (Gen := opGen (slicePolyRaw q.base d).Gen) t)
        (m.sliceMap_push f (opHom e))).trans
      (opPre_mapPath ((slicePolyRawFunctor q.base).map f).pre (m.sliceMap (opHom e))).symm

/-! ## The spelling of `Br`

The copies are compatible, so the colimit's own universal property descends them: no cell of
`Br p K` is examined. -/

variable (K : BPSet)

/-- The copy's spelling, read in `Br q K`. -/
noncomputable def brLeg (c : ((wedgeHoms K).Elements)ᵒᵖ) :
    GenObj (p.fam.obj (eltBase (wedgeHoms K) c)).Gen ⥤q (q.Br K).Word :=
  m.famCells (eltBase (wedgeHoms K) c) ⋙q
    (colimit.ι (elementsPoly (wedgeHoms K) q.fam) c).words.toPrefunctor

theorem brLeg_push {c c' : ((wedgeHoms K).Elements)ᵒᵖ} (u : c ⟶ c') :
    ((elementsPoly (wedgeHoms K) p.fam).map u).pre ⋙q m.brLeg K c' = m.brLeg K c :=
  have hw : ((elementsPoly (wedgeHoms K) q.fam).map u).pre ⋙q
      (colimit.ι (elementsPoly (wedgeHoms K) q.fam) c').pre
      = (colimit.ι (elementsPoly (wedgeHoms K) q.fam) c).pre :=
    congrArg Polygraph.Hom.pre (colimit.w (elementsPoly (wedgeHoms K) q.fam) u)
  (congrArg (fun π => π ⋙q (colimit.ι (elementsPoly (wedgeHoms K) q.fam) c').words.toPrefunctor)
      (m.famCells_push ((CategoryOfElements.π (wedgeHoms K)).leftOp.map u))).trans
    (congrArg (fun π : (q.fam.obj (eltBase (wedgeHoms K) c)).Word ⥤ (q.Br K).Word =>
        m.famCells (eltBase (wedgeHoms K) c) ⋙q π.toPrefunctor)
      ((Prefunctor.pathsFunctor_comp _ _).symm.trans (congrArg Prefunctor.pathsFunctor hw)))

/-- **`Br p K`, spelled in `Br q K`** — one copy's spelling per element of `wedgeHoms K`. -/
noncomputable def brCells : GenObj (p.Br K).Gen ⥤q (q.Br K).Word :=
  Polygraph.colimitSpell (elementsPoly (wedgeHoms K) p.fam) (q.Br K) (m.brLeg K)
    fun u => m.brLeg_push K u

/-- **…restricting to the copy it came from.** -/
theorem ι_pre_comp_brCells (c : ((wedgeHoms K).Elements)ᵒᵖ) :
    (colimit.ι (elementsPoly (wedgeHoms K) p.fam) c).pre ⋙q m.brCells K = m.brLeg K c :=
  Polygraph.ι_pre_comp_colimitSpell (elementsPoly (wedgeHoms K) p.fam) (q.Br K)
    (m.brLeg K) (fun u => m.brLeg_push K u) c

/-! ## …names the same arrows

The two presentations name the same object at every 0-cell and the same arrow at every 1-cell:
each is read inside one copy, where both sides factor through the localized slice — and that is a
poset (`locOver_isThin`), so equality of the objects is the whole argument. -/

/-- **A 0-cell of a copy is spelled inside that copy.** -/
theorem brCells_glueV (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a : (slicePolyRaw p.base (eltBase (wedgeHoms K) c)).V) :
    (m.brCells K).obj (glueV K p.fam c a) = glueV K q.fam c (m.sliceV a) :=
  congrArg
    (fun π : GenObj (p.fam.obj (eltBase (wedgeHoms K) c)).Gen ⥤q (q.Br K).Word => π.obj ⟨a⟩)
    (m.ι_pre_comp_brCells K c)

/-- **The spelling names the same object.** -/
theorem at_brCells (A : GenObj (p.Br K).Gen) :
    (q.presentsBr K).at' ((m.brCells K).obj A) = (p.presentsBr K).at' A := by
  refine Polygraph.colimit_obj_induction (elementsPoly (wedgeHoms K) p.fam)
    (fun A => (q.presentsBr K).at' ((m.brCells K).obj A) = (p.presentsBr K).at' A)
    (fun c x => ?_) A
  obtain ⟨a⟩ := x
  rw [show (colimit.ι (elementsPoly (wedgeHoms K) p.fam) c).pre.obj ⟨a⟩ = glueV K p.fam c a from
      rfl, m.brCells_glueV K c a, q.at_glueV K c (m.sliceV a), p.at_glueV K c a]
  rfl

/-- **The spelling names the same arrow.** -/
theorem eval_brCells {A B : GenObj (p.Br K).Gen} (e : A ⟶ B) :
    (q.presentsBr K).eval.map ((m.brCells K).map e)
      = eqToHom (m.at_brCells K A) ≫ (p.presentsBr K).arrow e
          ≫ eqToHom (m.at_brCells K B).symm := by
  refine Polygraph.colimit_gen_induction (elementsPoly (wedgeHoms K) p.fam)
    (Φ := fun {A B} f => (q.presentsBr K).eval.map ((m.brCells K).map f)
      = eqToHom (m.at_brCells K A) ≫ (p.presentsBr K).arrow f
          ≫ eqToHom (m.at_brCells K B).symm) (fun c {x y} g => ?_) e
  obtain ⟨a⟩ := x
  obtain ⟨b⟩ := y
  have hslice : (slicePresentationOf q.base (eltBase (wedgeHoms K) c)).eval.map
        ((m.famCells (eltBase (wedgeHoms K) c)).map g)
      = (slicePresentationOf p.base (eltBase (wedgeHoms K) c)).arrow g := Subsingleton.elim _ _
  have hL : (q.presentsBr K).eval.map ((m.brLeg K c).map g)
      = eqToHom (q.at_glueV K c (m.sliceV a)) ≫ (locEquivElements K).inverse.map
            ((glueSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).map
              ((slicePresentationOf p.base (eltBase (wedgeHoms K) c)).arrow g))
          ≫ eqToHom (q.at_glueV K c (m.sliceV b)).symm :=
    (q.eval_glueWord K c ((m.famCells (eltBase (wedgeHoms K) c)).map g)).trans
      (congrArg (fun t => eqToHom (q.at_glueV K c (m.sliceV a)) ≫
        (locEquivElements K).inverse.map
          ((glueSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).map t)
        ≫ eqToHom (q.at_glueV K c (m.sliceV b)).symm) hslice)
  have hR : (p.presentsBr K).arrow ((colimit.ι (elementsPoly (wedgeHoms K) p.fam) c).pre.map g)
      = eqToHom (p.at_glueV K c a) ≫ (locEquivElements K).inverse.map
            ((glueSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).map
              ((slicePresentationOf p.base (eltBase (wedgeHoms K) c)).arrow g))
          ≫ eqToHom (p.at_glueV K c b).symm :=
    p.arrow_glueE K c a b g
  refine Eq.trans (congrArg (q.presentsBr K).eval.map
    (Prefunctor.map_of_eq (m.ι_pre_comp_brCells K c) g)) ?_
  refine Eq.trans (Functor.map_homOfEq (q.presentsBr K).eval ((m.brLeg K c).map g) _ _) ?_
  rw [hL, hR]
  exact Polygraph.eqToHom_sandwich _ _ _ _ _ _ _ _ _

/-- **A map of braid presentations compares the two presentations of `Ch(K)[W⁻¹]`**, for every `K`:
the spelling names the same object at each 0-cell and the same arrow at each 1-cell, so the two
polygraphs present `Ch(K)[W⁻¹]` compatibly (`Presents.Map.isEquivalence`). -/
noncomputable def presentsMap : Presents.Map (p.presentsBr K) (q.presentsBr K) :=
  Presents.Map.ofSpelling (m.brCells K) (fun A => eqToIso (m.at_brCells K A))
    fun {_ _} e => m.eval_brCells K e

/-- **…and the comparison is natural in `K`**: `Br p` and `Br q` are functors on `BPSet`
(`brFunctor`), and re-indexing the copies along `f` commutes with the spelling. -/
theorem brCells_brMap {K K' : BPSet} (f : K ⟶ K') :
    (p.brMap f).pre ⋙q m.brCells K' = m.brCells K ⋙q (q.brMap f).words.toPrefunctor := by
  refine Polygraph.colimit_spell_ext (elementsPoly (wedgeHoms K) p.fam) (q.Br K') fun c => ?_
  have hp : (colimit.ι (elementsPoly (wedgeHoms K) p.fam) c).pre ⋙q (p.brMap f).pre
      = (colimit.ι (elementsPoly (wedgeHoms K') p.fam) ((brElt f).obj c)).pre :=
    congrArg Polygraph.Hom.pre (p.ι_brMap f c)
  have hq : (colimit.ι (elementsPoly (wedgeHoms K) q.fam) c).pre ⋙q (q.brMap f).pre
      = (colimit.ι (elementsPoly (wedgeHoms K') q.fam) ((brElt f).obj c)).pre :=
    congrArg Polygraph.Hom.pre (q.ι_brMap f c)
  have hA : (colimit.ι (elementsPoly (wedgeHoms K) p.fam) c).pre ⋙q
      ((p.brMap f).pre ⋙q m.brCells K') = m.brLeg K' ((brElt f).obj c) := by
    rw [← Prefunctor.comp_assoc, hp]; exact m.ι_pre_comp_brCells K' _
  have hB : (colimit.ι (elementsPoly (wedgeHoms K) p.fam) c).pre ⋙q
      (m.brCells K ⋙q (q.brMap f).words.toPrefunctor) = m.brLeg K' ((brElt f).obj c) := by
    rw [← Prefunctor.comp_assoc, m.ι_pre_comp_brCells K c]
    exact congrArg (fun π : (q.fam.obj (eltBase (wedgeHoms K) c)).Word ⥤ (q.Br K').Word =>
        m.famCells (eltBase (wedgeHoms K) c) ⋙q π.toPrefunctor)
      ((Prefunctor.pathsFunctor_comp _ _).symm.trans (congrArg Prefunctor.pathsFunctor hq))
  exact hA.trans hB.symm

end BraidPresentation.Map

end ChainCat
