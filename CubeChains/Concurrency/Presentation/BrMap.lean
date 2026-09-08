import CubeChains.Concurrency.Presentation.BrFunctor

/-!
# Concurrency/Presentation/BrMap — a map of braid presentations, lifted

A map `p ⟶ q` spells a generator of `p` by a **word** of `q` performing the same braid
(`braid_word`).  Above a chain that word lifts once and for all: it performs the generator's own
braid, so it makes the same germ step, and `germWordOf` lifts it at the run.  A germ word is its
braid word (`germWord_injective`), which is what makes the lift unique and hence the family
strictly natural in the chain.  Everything above is then the colimit's own functoriality.
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

A 0-cell of the germ slice **is** a run — no presentation enters it — so the spelling leaves the
0-cells alone.  A 1-cell is a generator of `p` making a germ step, and the comparison's word
performs that generator's braid, so it lifts to the germ word over the same run
(`germWordOf`). -/

variable {d' d : Ch Zbp}


/-- The word of `q`'s slice a 1-cell of `p`'s spells: the germ word the comparison lifts to. -/
noncomputable def sliceMap : ∀ {a b : (p.slicePoly d).V},
    ((⟨a⟩ : GenObj (p.slicePoly d).Gen) ⟶ ⟨b⟩) →
      Quiver.Path (⟨a⟩ : GenObj (q.slicePoly d).Gen) ⟨b⟩
  | _, _, .mk (i := N) e =>
      (Polygraph.coproductPre (fun N => q.germPoly (runGermChart d N)) N).mapPath
        (m.germWordOf (runGermChart d N) e)

/-- **The lifted germ word is pushed by a merge** — both sides spell the comparison's own braid
word, and a germ word is its braid word. -/
theorem germWordOf_push (f : d' ⟶ d) {N : ℕ} {u v : RunAt d' N}
    (e : p.GermGen (runGermChart d' N) u v) :
    m.germWordOf (runGermChart d N) ((p.runChartPush f N).map e)
      = (q.runChartPush f N).mapPath (m.germWordOf (runGermChart d' N) e) :=
  q.germWord_injective _
    ((m.germWord_germWordOf (runGermChart d N) ((p.runChartPush f N).map e)).trans
      ((m.germWord_germWordOf (runGermChart d' N) e).symm.trans
        (q.germWord_runChartPush f N (m.germWordOf (runGermChart d' N) e)).symm))

/-- **The spelling is strictly natural in the chain.** -/
theorem sliceMap_push (f : d' ⟶ d) : ∀ {a b : (p.slicePoly d').V}
    (e : (⟨a⟩ : GenObj (p.slicePoly d').Gen) ⟶ ⟨b⟩),
    m.sliceMap (((p.sliceRawFunctor).map f).pre.map e)
      = ((q.sliceRawFunctor).map f).pre.mapPath (m.sliceMap e)
  | _, _, .mk (i := N) e =>
      (congrArg (Polygraph.coproductPre (fun M => q.germPoly (runGermChart d M)) N).mapPath
          (m.germWordOf_push f e)).trans
        ((Prefunctor.mapPath_comp_apply (q.runChartPush f N)
            (Polygraph.coproductPre (fun M => q.germPoly (runGermChart d M)) N) _).symm.trans
          (Polygraph.descPre_mapPath (fun M => q.germPoly (runGermChart d' M))
            (fun M => q.slicePushFibre f M ≫ q.sliceIncl d M) N _).symm)

/-! ## …in the orientation the colimit route uses

`Br` is built on the *reversed* slice — a braid raises the weak order where an arrow of the
localized slice lowers it — so the spelling is read backwards, and `opPre_mapPath` carries the
naturality across. -/

/-- **`p`'s slice, spelled in `q`'s**, with words read backwards. -/
noncomputable def famCells (d : Ch Zbp) :
    GenObj (p.fam.obj d).Gen ⥤q (q.fam.obj d).Word where
  obj a := ⟨a.as⟩
  map {_ _} e := revPath (Gen := opGen (q.slicePoly d).Gen) (m.sliceMap (opHom e))

theorem famCells_push (f : d' ⟶ d) :
    (p.fam.map f).pre ⋙q m.famCells d
      = m.famCells d' ⋙q (q.fam.map f).pre.pathsFunctor.toPrefunctor :=
  Prefunctor.ext' (fun _ => rfl) fun _ _ e =>
    (congrArg (fun t => revPath (Gen := opGen (q.slicePoly d).Gen) t)
        (m.sliceMap_push f (opHom e))).trans
      (opPre_mapPath ((q.sliceRawFunctor).map f).pre (m.sliceMap (opHom e))).symm

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
theorem brCells_ιV (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a : (p.slicePoly (eltBase (wedgeHoms K) c)).V) :
    (m.brCells K).obj (ιV K p.fam c a) = ιV K q.fam c (a) :=
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
  rw [show (colimit.ι (elementsPoly (wedgeHoms K) p.fam) c).pre.obj ⟨a⟩ = ιV K p.fam c a from
      rfl, m.brCells_ιV K c a, q.at_ιV K c (a), p.at_ιV K c a]
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
  have hslice : (q.slicePresentation (eltBase (wedgeHoms K) c)).eval.map
        ((m.famCells (eltBase (wedgeHoms K) c)).map g)
      = (p.slicePresentation (eltBase (wedgeHoms K) c)).arrow g := Subsingleton.elim _ _
  have hL : (q.presentsBr K).eval.map ((m.brLeg K c).map g)
      = eqToHom (q.at_ιV K c (a)) ≫ (locEquivElements K).inverse.map
            ((colimSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).map
              ((p.slicePresentation (eltBase (wedgeHoms K) c)).arrow g))
          ≫ eqToHom (q.at_ιV K c (b)).symm :=
    (q.eval_ιWord K c ((m.famCells (eltBase (wedgeHoms K) c)).map g)).trans
      (congrArg (fun t => eqToHom (q.at_ιV K c (a)) ≫
        (locEquivElements K).inverse.map
          ((colimSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).map t)
        ≫ eqToHom (q.at_ιV K c (b)).symm) hslice)
  have hR : (p.presentsBr K).arrow ((colimit.ι (elementsPoly (wedgeHoms K) p.fam) c).pre.map g)
      = eqToHom (p.at_ιV K c a) ≫ (locEquivElements K).inverse.map
            ((colimSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).map
              ((p.slicePresentation (eltBase (wedgeHoms K) c)).arrow g))
          ≫ eqToHom (p.at_ιV K c b).symm :=
    p.arrow_ιE K c a b g
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
