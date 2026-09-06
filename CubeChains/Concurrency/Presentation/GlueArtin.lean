import CubeChains.Concurrency.Presentation.GlueVsFibration
import CubeChains.Machinery.Presentation.ColimitCells

/-!
# Concurrency/Presentation/GlueArtin — the Artin generators, spelled by glue 1-cells

`Ch(Hbp □ⁿ)[W⁻¹]` is presented twice: by the colimit of the run slices
(`presentsChainsRunColimit`) and by the base's Artin generators acting on the fibre over the run
(`hLocArtinPresentation`).  The comparison sends **generator to generator**: the `k`-th Artin
generator at the run `z` is the single glue 1-cell in the copy at `atomComp n k` carrying the
element `z` is merged from, whose two ends are the atom leg and the merge leg.

It is a bijection in both dimensions (`bijective_genQuiver`), so the two polygraphs share their
generating data and differ only in their 2-cells: the Artin relations on one side, the thinness of
each localized slice on the other.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits Localization

/-- **A 1-cell read at 0-cells its endpoints are equal to**: the transport a comparison of two
polygraphs leaves behind. -/
theorem CategoryTheory.Polygraph.Presents.arrow_homOfEq {P : Polygraph} {C : Type*} [Category C]
    (p : Presents P C) {a b a' b' : GenObj P.Gen} (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    p.arrow (Quiver.homOfEq f ha hb)
      = eqToHom (congrArg p.at' ha).symm ≫ p.arrow f ≫ eqToHom (congrArg p.at' hb) := by
  subst ha; subst hb; simp [Quiver.homOfEq]

namespace ChainCat

/-! ## The copies of the colimit polygraph

A copy is indexed by an element of `wedgeHoms K` — a chain of the base with a map into `K`, which
is what `toElements` names — and its 0-cells are the runs over that chain.  Everything here is the
colimit's universal property read on a leg; no cell of the colimit is ever examined. -/

/-- The compatibility the run slices satisfy, named once. -/
theorem runSlicePresentation_hP : ∀ {d' d : Ch Zbp} (f : d' ⟶ d),
    (runPolyFunctor.map f).functor ⋙ (runSlicePresentation d).E
      = (runSlicePresentation d').E ⋙ overMapLoc (W Zbp) f :=
  fun {_ _} f => runPoly_hP runSlicePresentation runSlicePresentation_at f

/-- **A refinement of the base moves the copy**: the element restricted along `g`, mapping to the
element it was restricted from.  Its base map is `g` on the nose, which is what makes the 0-cell
identification below definitional. -/
def eltLeg (K : BPSet) {d e : Ch Zbp} (g : d ⟶ e) (x : (wedgeHoms K).obj (op e)) :
    (op ⟨op d, (wedgeHoms K).map g.op x⟩ : ((wedgeHoms K).Elements)ᵒᵖ) ⟶ op ⟨op e, x⟩ :=
  (CategoryOfElements.homMk ⟨op e, x⟩ ⟨op d, (wedgeHoms K).map g.op x⟩ g.op rfl).op

@[simp] theorem eltLeg_base (K : BPSet) {d e : Ch Zbp} (g : d ⟶ e)
    (x : (wedgeHoms K).obj (op e)) :
    (CategoryOfElements.π (wedgeHoms K)).leftOp.map (eltLeg K g x) = g := rfl

/-- **A 0-cell of the colimit**: a run over a chain, read in the copy at an element. -/
noncomputable def glueV (K : BPSet) (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a : RunOver (eltBase (wedgeHoms K) c)) :
    GenObj (colimit (elementsPoly (wedgeHoms K) runPolyFunctor)).Gen :=
  (colimit.ι (elementsPoly (wedgeHoms K) runPolyFunctor) c).pre.obj ⟨a⟩

/-- **A 1-cell of the colimit**: a crossing inside a copy. -/
noncomputable def glueE (K : BPSet) (c : ((wedgeHoms K).Elements)ᵒᵖ)
    {a b : RunOver (eltBase (wedgeHoms K) c)}
    (g : (⟨a⟩ : GenObj (runPoly (eltBase (wedgeHoms K) c)).Gen) ⟶ ⟨b⟩) :
    glueV K c a ⟶ glueV K c b :=
  (colimit.ι (elementsPoly (wedgeHoms K) runPolyFunctor) c).pre.map g

/-- **The copies agree along an arrow of `∫X`** — the colimit's own naturality, on 0-cells. -/
theorem glueV_leg (K : BPSet) {c' c : ((wedgeHoms K).Elements)ᵒᵖ} (u : c' ⟶ c)
    (a : RunOver (eltBase (wedgeHoms K) c')) :
    glueV K c (RunOver.push ((CategoryOfElements.π (wedgeHoms K)).leftOp.map u) a)
      = glueV K c' a :=
  congrArg (fun F : Polygraph.Hom (runPoly (eltBase (wedgeHoms K) c'))
      (colimit (elementsPoly (wedgeHoms K) runPolyFunctor)) => F.pre.obj ⟨a⟩)
    (colimit.w (elementsPoly (wedgeHoms K) runPolyFunctor) u)

/-- **…and the same, on 1-cells.** -/
theorem glueE_leg (K : BPSet) {c' c : ((wedgeHoms K).Elements)ᵒᵖ} (u : c' ⟶ c)
    {a b : RunOver (eltBase (wedgeHoms K) c')}
    (g : (⟨a⟩ : GenObj (runPoly (eltBase (wedgeHoms K) c')).Gen) ⟶ ⟨b⟩) :
    glueE K c ((runPolyFunctor.map
        ((CategoryOfElements.π (wedgeHoms K)).leftOp.map u)).pre.map g)
      = Quiver.homOfEq (glueE K c' g) (glueV_leg K u a).symm (glueV_leg K u b).symm := by
  have hnat : ((elementsPoly (wedgeHoms K) runPolyFunctor).map u).pre ⋙q
      (colimit.ι (elementsPoly (wedgeHoms K) runPolyFunctor) c).pre
      = (colimit.ι (elementsPoly (wedgeHoms K) runPolyFunctor) c').pre :=
    congrArg (fun m : Polygraph.Hom ((elementsPoly (wedgeHoms K) runPolyFunctor).obj c')
      (colimit (elementsPoly (wedgeHoms K) runPolyFunctor)) => m.pre)
      (colimit.w (elementsPoly (wedgeHoms K) runPolyFunctor) u)
  exact eq_of_heq ((Prefunctor.map_heq_of_eq hnat g).trans
    (Quiver.homOfEq_heq _ _ (glueE K c' g)).symm)

/-- **The object a 0-cell of the colimit names**: its own slice object, lifted at the copy's
element.  `glueIncl_desc` computes the comparison on a leg, and that is all a generator ever
meets. -/
theorem at_glueV (K : BPSet) (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a : RunOver (eltBase (wedgeHoms K) c)) :
    (presentsChainsRunColimit K).at' (glueV K c a)
      = (locEquivElements K).inverse.obj
          ((glueSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).obj
            ((runSlicePresentation (eltBase (wedgeHoms K) c)).at' ⟨a⟩)) := by
  have h1 : (presentsChainsRunColimit K).at' (glueV K c a)
      = (locEquivElements K).inverse.obj
          ((glueInclFun (wedgeHoms K) runPolyFunctor c ⋙
            glueDesc (P := runPolyFunctor) (wedgeHoms K) (W Zbp) runSlicePresentation
              runSlicePresentation_hP).obj
              ((runPoly (eltBase (wedgeHoms K) c)).quot.obj ⟨a⟩)) := rfl
  exact h1.trans (congrArg (locEquivElements K).inverse.obj (Functor.congr_obj
    (glueIncl_desc (P := runPolyFunctor) (wedgeHoms K) (W Zbp) runSlicePresentation
      runSlicePresentation_hP c)
    ((runPoly (eltBase (wedgeHoms K) c)).quot.obj ⟨a⟩)))

/-- **…and the arrow a 1-cell names**: the arrow its own slice presentation names, lifted.  The
`eqToHom`s are `at_glueV`, which the braid does not see. -/
theorem arrow_glueE (K : BPSet) (c : ((wedgeHoms K).Elements)ᵒᵖ)
    {a b : RunOver (eltBase (wedgeHoms K) c)}
    (g : (⟨a⟩ : GenObj (runPoly (eltBase (wedgeHoms K) c)).Gen) ⟶ ⟨b⟩) :
    (presentsChainsRunColimit K).arrow (glueE K c g)
      = eqToHom (at_glueV K c a) ≫ (locEquivElements K).inverse.map
            ((glueSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).map
              ((runSlicePresentation (eltBase (wedgeHoms K) c)).arrow g))
          ≫ eqToHom (at_glueV K c b).symm := by
  have h1 : (presentsChainsRunColimit K).arrow (glueE K c g)
      = ((glueInclFun (wedgeHoms K) runPolyFunctor c ⋙
          glueDesc (P := runPolyFunctor) (wedgeHoms K) (W Zbp) runSlicePresentation
            runSlicePresentation_hP) ⋙
            (locEquivElements K).inverse).map
          ((runPoly (eltBase (wedgeHoms K) c)).quot.map g.toPath) := rfl
  rw [h1, Functor.congr_hom (congrArg (fun F => F ⋙ (locEquivElements K).inverse)
    (glueIncl_desc (P := runPolyFunctor) (wedgeHoms K) (W Zbp) runSlicePresentation
      runSlicePresentation_hP c))]
  rfl

/-! ## The copy at a run

A run is a chain of `K` all of whose beads are edges; its own copy carries it as the identity
slice object, and that 0-cell names the localized chain itself. -/

/-- The chain of `K` a run of `n` events is. -/
def runCh {K : BPSet} {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) : Ch K := ⟨𝟙^n, z⟩

/-- A run, as a 0-cell over its own chain. -/
def runOverSelf (n : ℕ) : RunOver (zObj (𝟙^n)) :=
  ⟨Over.mk (𝟙 _), fun _ hd => List.eq_of_mem_replicate hd⟩

/-- **The 0-cell of the colimit a run names**: itself, in its own copy. -/
noncomputable def glueRunV (K : BPSet) {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    GenObj (colimit (elementsPoly (wedgeHoms K) runPolyFunctor)).Gen :=
  glueV K ((toElements K).obj (runCh z)) (runOverSelf n)

theorem at_glueRunV (K : BPSet) {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (presentsChainsRunColimit K).at' (glueRunV K z)
      = (locEquivElements K).inverse.obj
          (((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q.obj
            ((toElements K).obj (runCh z))) := by
  refine (at_glueV K ((toElements K).obj (runCh z)) (runOverSelf n)).trans
    (congrArg (locEquivElements K).inverse.obj ?_)
  refine (Functor.congr_obj
    (glueSliceEval_fac (wedgeHoms K) (W Zbp) (zObj (𝟙^n)) z) (Over.mk (𝟙 _))).trans ?_
  exact congrArg (fun t => ((W Zbp).inverseImage
    (CategoryOfElements.π (wedgeHoms K)).leftOp).Q.obj (op ⟨op (zObj (𝟙^n)), t⟩))
    ((wedgeHoms K).map_id_apply (op (zObj (𝟙^n))) z)

/-- **The comparison with the localized category of elements, at a `Q`-image.** -/
noncomputable def glueUnitIso (K : BPSet) (a : Ch K) :
    (locEquivElements K).inverse.obj
        (((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q.obj
          ((toElements K).obj a))
      ≅ (W K).Q.obj a :=
  haveI : (toElements K ⋙
      ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q).IsLocalization
        (W K) :=
    Functor.IsLocalization.of_inverseImage (toElements K) _ _ (W K)
      (W_eq_inverseImage_elements K)
  (locEquivElements K).inverse.mapIso
      ((Localization.compUniqFunctor (W K).Q
        (toElements K ⋙ ((W Zbp).inverseImage
          (CategoryOfElements.π (wedgeHoms K)).leftOp).Q) (W K)).app a).symm ≪≫
    ((locEquivElements K).unitIso.app ((W K).Q.obj a)).symm

/-- **The glue route names the localized run chain.** -/
noncomputable def glueRunIso (K : BPSet) {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (presentsChainsRunColimit K).at' (glueRunV K z) ≅ (W K).Q.obj (runCh z) :=
  eqToIso (at_glueRunV K z) ≪≫ glueUnitIso K (runCh z)

/-! ## The atom's cell, as a copy

Above a run, the `k`-th atom's cell is the chain `atomComp n k`, and the run is the merge leg of
that cell.  Its chart is forced: the merges act bijectively on the fibre (`IsSegal`), so the run
determines what it was merged from. -/

section Cube

variable {n : ℕ} (k : Fin (n - 1)) (z : ⋁(𝟙^n) ⟶ Hbp.obj (□n))

/-- **The chart the `k`-th atom's cell carries above a run** — the run, un-merged across the cut.
Nothing is chosen: the merge is inverted in the localized base. -/
noncomputable def atomWitness : ⋁(atomComp n k) ⟶ Hbp.obj (□n) :=
  haveI := isIso_Q_op_of_W (W_mergeOnes n k)
  (hFibre n).map (inv (((W Zbp).op).Q.map (mergeOnes n k).op)) z

/-- **The merge leg of the cell restricts to the run.** -/
theorem mergeOnes_atomWitness : (mergeOnes n k).φ ≫ atomWitness k z = z := by
  haveI := isIso_Q_op_of_W (W_mergeOnes n k)
  have h1 : (hFibre n).map (((W Zbp).op).Q.map (mergeOnes n k).op) (atomWitness k z) = z := by
    rw [atomWitness, ← (hFibre n).map_comp_apply, IsIso.inv_hom_id, (hFibre n).map_id_apply]
  rwa [hFibre_map_Q] at h1

/-- **…and the crossing leg restricts to the run the atom acts to.** -/
theorem atomOnes_atomWitness :
    (atomOnes n k).φ ≫ atomWitness k z = (hFibre n).map (atomLoop n k) z := by
  haveI := isIso_Q_op_of_W (W_mergeOnes n k)
  have hconj : atomLoop n k
      = inv (((W Zbp).op).Q.map (mergeOnes n k).op)
          ≫ ((W Zbp).op).Q.map (atomOnes n k).op := by
    rw [atomLoop, conj,
      show runMerge (zObj (𝟙^n)) (dimSum_replicate n) = 𝟙 _ from endo_eq_id _,
      op_id, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  rw [hconj, (hFibre n).map_comp_apply, hFibre_map_Q]
  rfl

/-- The crossing leg of the atom's cell, as a 0-cell of the cell's own copy. -/
def atomRun : RunOver (zObj (atomComp n k)) := RunOver.push (atomOnes n k) (runOverSelf n)

/-- …and the merge leg. -/
noncomputable def mergeRun : RunOver (zObj (atomComp n k)) :=
  RunOver.push (mergeOnes n k) (runOverSelf n)

/-- **The two legs of the atom's cell are one crossing apart** — the cell itself is the witness,
with nothing below it. -/
theorem runStep_atom : RunStep (atomRun k) (mergeRun k) :=
  ⟨zObj (atomComp n k), atomOnes n k, mergeOnes n k, 𝟙 _,
    (permLen_crossPerm (dimSum_replicate n) rfl (atomOnes n k)).trans
      (by rw [crossPerm_atomOnes]; exact permLen_adjT k),
    W_mergeOnes n k, by simp [atomRun, RunOver.push, runOverSelf],
    by simp [mergeRun, RunOver.push, runOverSelf]⟩

/-- **A generating step of a slice is the atom's cell, pushed down**: one crossing above the run
is one atom above it, and the cell it comes from is `atomComp n k`.  The converse of
`runStep_atom`, and what makes the 1-cell dictionary surjective. -/
theorem exists_atomComp_leg {d : Ch Zbp} (hd : dimSum d.dims = n) {a b : RunOver d}
    (h : RunStep a b) :
    ∃ (k : Fin (n - 1)) (v : zObj (atomComp n k) ⟶ d),
      RunOver.push v (atomRun k) = a ∧ RunOver.push v (mergeRun k) = b := by
  obtain ⟨⟨la, ⟨⟩, ga⟩, hra⟩ := a
  obtain ⟨⟨lb, ⟨⟩, gb⟩, hrb⟩ := b
  obtain rfl : la = zObj (𝟙^n) := RunOver.left_eq hd ⟨Over.mk ga, hra⟩
  obtain rfl : lb = zObj (𝟙^n) := RunOver.left_eq hd ⟨Over.mk gb, hrb⟩
  obtain ⟨e', t, m, zz, ht, hm, hta, hmb⟩ := h
  have hta' : (t : zObj (𝟙^n) ⟶ e') ≫ zz = (ga : zObj (𝟙^n) ⟶ d) := hta
  have hmb' : (m : zObj (𝟙^n) ⟶ e') ≫ zz = (gb : zObj (𝟙^n) ⟶ d) := hmb
  have htlen : permLen (crossPerm (a := zObj (𝟙^n)) (b := e') (dimSum_replicate n) t) = 1 :=
    (permLen_crossPerm (a := zObj (𝟙^n)) (b := e') rfl (dimSum_replicate n) t).trans ht
  obtain ⟨k, hk⟩ := eq_adjT_of_permLen_eq_one htlen
  have hσa := crossPerm_comp (a := zObj (𝟙^n)) (b := e') (c := d) (dimSum_replicate n) t zz
  rw [hta', hk] at hσa
  have hσb : crossPerm (a := zObj (𝟙^n)) (b := d) (dimSum_replicate n) gb
      = crossPerm (tgtStrands (a := zObj (𝟙^n)) (b := e') t (dimSum_replicate n)) zz := by
    have h0 := crossPerm_comp (a := zObj (𝟙^n)) (b := e') (c := d) (dimSum_replicate n) m zz
    rw [hmb', crossPerm_eq_one_of_W (dimSum_replicate n) hm, mul_one] at h0
    exact h0
  have hab : crossPerm (a := zObj (𝟙^n)) (b := d) (dimSum_replicate n) ga
      = crossPerm (a := zObj (𝟙^n)) (b := d) (dimSum_replicate n) gb * adjT k := by
    rw [hσa, hσb]
  have hlena :=
    permLen_crossPerm_comp (a := zObj (𝟙^n)) (b := e') (c := d) (dimSum_replicate n) t zz
  rw [hta', hk, permLen_adjT] at hlena
  have hlenb : permLen (crossPerm (a := zObj (𝟙^n)) (b := d) (dimSum_replicate n) gb)
      = permLen (crossPerm (tgtStrands (a := zObj (𝟙^n)) (b := e') t
          (dimSum_replicate n)) zz) := congrArg permLen hσb
  have hasc : crossPerm (a := zObj (𝟙^n)) (b := d) (dimSum_replicate n) gb (adjLo k)
      < crossPerm (a := zObj (𝟙^n)) (b := d) (dimSum_replicate n) gb (adjHi k) := by
    rcases lt_trichotomy
      (crossPerm (a := zObj (𝟙^n)) (b := d) (dimSum_replicate n) gb (adjLo k))
      (crossPerm (a := zObj (𝟙^n)) (b := d) (dimSum_replicate n) gb (adjHi k)) with
      hlt | heq | hgt
    · exact hlt
    · exact absurd (congrArg Fin.val ((Equiv.injective _) heq))
        (by rw [adjLo_val, adjHi_val]; omega)
    · have hdrop := permLen_mul_adjT_of_descent (i := k) hgt
      rw [← hab] at hdrop
      omega
  have hdesc : crossPerm (a := zObj (𝟙^n)) (b := d) (dimSum_replicate n) ga (adjHi k)
      < crossPerm (a := zObj (𝟙^n)) (b := d) (dimSum_replicate n) ga (adjLo k) := by
    rw [hab, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, adjT_hi, adjT_lo]
    exact hasc
  obtain ⟨v, hmerge, hatom⟩ := exists_atom_step hd k
    (nonempty_atomComp_of_descent hd ga hdesc) (rfl : crossPerm (dimSum_replicate n) gb = _) hasc
  have hgaeq : atomOnes n k ≫ v = ga :=
    hom_ext_of_crossPerm (h := dimSum_replicate n) (hatom.trans hab.symm)
  refine ⟨k, v, Subtype.ext (congrArg Over.mk ?_), Subtype.ext (congrArg Over.mk ?_)⟩
  · simpa using hgaeq
  · simpa using hmerge

/-- **The crossing leg's 0-cell is the run its own leg restricts the chart to.** -/
theorem glueV_atomLeg (K : BPSet) (w : ⋁(atomComp n k) ⟶ K) :
    glueV K (op ⟨op (zObj (atomComp n k)), w⟩) (atomRun k)
      = glueRunV K ((atomOnes n k).φ ≫ w) :=
  glueV_leg K (eltLeg K (atomOnes n k) w) (runOverSelf n)

/-- …and the merge leg's likewise. -/
theorem glueV_mergeLeg (K : BPSet) (w : ⋁(atomComp n k) ⟶ K) :
    glueV K (op ⟨op (zObj (atomComp n k)), w⟩) (mergeRun k)
      = glueRunV K ((mergeOnes n k).φ ≫ w) :=
  glueV_leg K (eltLeg K (mergeOnes n k) w) (runOverSelf n)

/-- The copy the `k`-th atom's cell is. -/
noncomputable def atomElt : ((wedgeHoms (Hbp.obj (□n))).Elements)ᵒᵖ :=
  (toElements (Hbp.obj (□n))).obj ⟨atomComp n k, atomWitness k z⟩

/-- **The crossing leg's 0-cell is the run the atom acts to.** -/
theorem glueV_atomRun :
    glueV (Hbp.obj (□n)) (atomElt k z) (atomRun k)
      = glueRunV (Hbp.obj (□n)) ((hFibre n).map (atomLoop n k) z) :=
  (glueV_atomLeg k (Hbp.obj (□n)) (atomWitness k z)).trans
    (congrArg (glueRunV (Hbp.obj (□n))) (atomOnes_atomWitness k z))

/-- **…and the merge leg's is the run itself.** -/
theorem glueV_mergeRun :
    glueV (Hbp.obj (□n)) (atomElt k z) (mergeRun k) = glueRunV (Hbp.obj (□n)) z :=
  (glueV_mergeLeg k (Hbp.obj (□n)) (atomWitness k z)).trans
    (congrArg (glueRunV (Hbp.obj (□n))) (mergeOnes_atomWitness k z))

/-- **The chart above a run is forced** — the merge acts bijectively on the fibre. -/
theorem eq_atomWitness {w : ⋁(atomComp n k) ⟶ Hbp.obj (□n)}
    (hw : (mergeOnes n k).φ ≫ w = z) : w = atomWitness k z := by
  haveI := isIso_Q_op_of_W (W_mergeOnes n k)
  have h1 : (hFibre n).map (((W Zbp).op).Q.map (mergeOnes n k).op) w = z := by
    rw [hFibre_map_Q]; exact hw
  have h2 : (hFibre n).map (((W Zbp).op).Q.map (mergeOnes n k).op) (atomWitness k z) = z := by
    rw [hFibre_map_Q]; exact mergeOnes_atomWitness k z
  have h3 := congrArg ((hFibre n).map (inv (((W Zbp).op).Q.map (mergeOnes n k).op)))
    (h1.trans h2.symm)
  rwa [← (hFibre n).map_comp_apply, ← (hFibre n).map_comp_apply, IsIso.hom_inv_id,
    (hFibre n).map_id_apply, (hFibre n).map_id_apply] at h3

/-- **The one 1-cell of the atom's copy**: its crossing leg, one crossing above its merge leg. -/
noncomputable def atomCell :
    glueV (Hbp.obj (□n)) (atomElt k z) (atomRun k)
      ⟶ glueV (Hbp.obj (□n)) (atomElt k z) (mergeRun k) :=
  glueE (Hbp.obj (□n)) (atomElt k z)
    (⟨runStep_atom k⟩ :
      (⟨atomRun k⟩ : GenObj (runPoly (zObj (atomComp n k))).Gen) ⟶ ⟨mergeRun k⟩)

theorem arrow_atomCell :
    (presentsChainsRunColimit (Hbp.obj (□n))).arrow (atomCell k z)
      = eqToHom (at_glueV (Hbp.obj (□n)) (atomElt k z) (atomRun k)) ≫
          (locEquivElements (Hbp.obj (□n))).inverse.map
            ((glueSliceEval (wedgeHoms (Hbp.obj (□n))) (W Zbp) (zObj (atomComp n k))
              (atomWitness k z)).map
                ((runSlicePresentation (zObj (atomComp n k))).arrow
                  (⟨runStep_atom k⟩ :
                    (⟨atomRun k⟩ : GenObj (runPoly (zObj (atomComp n k))).Gen) ⟶
                      ⟨mergeRun k⟩)))
        ≫ eqToHom (at_glueV (Hbp.obj (□n)) (atomElt k z) (mergeRun k)).symm :=
  arrow_glueE _ _ _

/-- **The braid the atom's 1-cell performs is the `k`-th atom.** -/
theorem chBraid_atomCell :
    chBraid ((locEquivElements (Hbp.obj (□n))).inverse.map
        ((glueSliceEval (wedgeHoms (Hbp.obj (□n))) (W Zbp) (zObj (atomComp n k))
          (atomWitness k z)).map
            ((runSlicePresentation (zObj (atomComp n k))).arrow
              (⟨runStep_atom k⟩ :
                (⟨atomRun k⟩ : GenObj (runPoly (zObj (atomComp n k))).Gen) ⟶ ⟨mergeRun k⟩))))
      (hbpStrands _) (hbpStrands _) = posPerm (adjT k) :=
  (chBraid_glueSliceEval_runStep (Hbp.obj (□n)) (zObj (atomComp n k)) (atomWitness k z)
    ⟨runStep_atom k⟩ (e := zObj (atomComp n k)) (t := atomOnes n k) (m := mergeOnes n k)
    (z := 𝟙 _) (W_mergeOnes n k) (by simp [atomRun, RunOver.push, runOverSelf])
    (by simp [mergeRun, RunOver.push, runOverSelf]) (dimSum_replicate n) (dimSum_replicate n)
    (dimSum_atomComp n k) (hbpStrands _) (hbpStrands _)).trans
      (congrArg posPerm (crossPerm_atomOnes n k))

end Cube

/-! ## The dictionary

A 0-cell of the fibration route is a run; a 1-cell is an Artin generator acting on one.  Both go
to the copy at the atom's cell, where the run is the merge leg. -/

/-- The run a 0-cell of the fibration route carries. -/
def artinRun {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) : ⋁(𝟙^n) ⟶ Hbp.obj (□n) := x.as.2

/-- …and the 0-cell a run is. -/
def artinPt {n : ℕ} (z : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) : GenObj (hLocArtinPoly n).Gen :=
  ⟨⟨SingleObj.star (PresentedMonoid (ArtinRel n)), z⟩⟩

@[simp] theorem artinRun_artinPt {n : ℕ} (z : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) :
    artinRun (artinPt z) = z := rfl

@[simp] theorem artinPt_artinRun {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) :
    artinPt (artinRun x) = x := rfl

/-- **A generator acts by its atom.** -/
theorem artinRun_step {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    (hFibre n).map (atomLoop n e.1) (artinRun x) = artinRun y := by
  rw [← runLoop_adjT]; exact e.2

/-- **The fibration route names the localized run chain.** -/
noncomputable def artinRunIso {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) :
    ((hLocArtinPresentation n).at' x).unop ≅ (W (Hbp.obj (□n))).Q.obj (runCh (artinRun x)) :=
  haveI : (chDescent (Hbp.obj (□n)) (isSegal_H_of_symFree_repr (symFreeCube n))).IsLocalization
      (W (Hbp.obj (□n))) := isLocalization_chDescent _ _
  haveI : (CategoryOfElements.pre
      (wedgeHomsDescend (Hbp.obj (□n)) (isSegal_H_of_symFree_repr (symFreeCube n)))
      (runBase n)).IsEquivalence :=
    CategoryOfElements.isEquivalence_pre _ _
      (cover_of_strands _ n (isSegal_H_of_symFree_repr (symFreeCube n))
        (fun {_} α => hbpCubeStrands α))
  (Localization.compEquivalenceFromModelInverseIso
    (chDescent (Hbp.obj (□n)) (isSegal_H_of_symFree_repr (symFreeCube n)))
    (W (Hbp.obj (□n)))).app (runCh (artinRun x))

/-- **The 0-cell dictionary**: a run, read in its own copy. -/
noncomputable def obCell {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) :
    GenObj ((colimit
      (elementsPoly (wedgeHoms (Hbp.obj (□n))) runPolyFunctor)).op).Gen :=
  ⟨(glueRunV (Hbp.obj (□n)) (artinRun x)).as⟩

/-- **The crossing leg is the 0-cell the generator acts to.** -/
theorem genSrc {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    glueV (Hbp.obj (□n)) (atomElt e.1 (artinRun x)) (atomRun e.1)
      = glueRunV (Hbp.obj (□n)) (artinRun y) :=
  (glueV_atomRun e.1 (artinRun x)).trans
    (congrArg (glueRunV (Hbp.obj (□n))) (artinRun_step e))

/-- **…and the merge leg is the 0-cell it acts from.** -/
theorem genTgt {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    glueV (Hbp.obj (□n)) (atomElt e.1 (artinRun x)) (mergeRun e.1)
      = glueRunV (Hbp.obj (□n)) (artinRun x) :=
  glueV_mergeRun e.1 (artinRun x)

/-- **The 1-cell dictionary**: the `k`-th Artin generator at the run `z` is the single crossing in
the copy at `atomComp n k` carrying the chart `z` is merged from.  The polygraphs run in opposite
directions, so the crossing leg is the generator's *target*. -/
noncomputable def genCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    obCell x ⟶ obCell y :=
  (Quiver.homOfEq (atomCell e.1 (artinRun x)) (genSrc e) (genTgt e) :
    glueRunV (Hbp.obj (□n)) (artinRun y) ⟶ glueRunV (Hbp.obj (□n)) (artinRun x))

/-- **The 0-cells name the same object.** -/
noncomputable def thetaCell {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) :
    ((presentsChainsRunColimit (Hbp.obj (□n))).op).at' (obCell x)
      ≅ (hLocArtinPresentation n).at' x :=
  (artinRunIso x ≪≫ (glueRunIso (Hbp.obj (□n)) (artinRun x)).symm).op

/-! ## The comparison

Both sides perform the same atom, and `eq_of_chBraid_eq` is decisive: the localized chains project
faithfully to the localized base. -/

/-- **The glue spelling of a generator performs that generator's atom.** -/
theorem chBraid_genCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    chBraid ((((presentsChainsRunColimit (Hbp.obj (□n))).op).arrow (genCell e)).unop)
        (hbpStrands _) (hbpStrands _) = posPerm (adjT e.1) := by
  have h0 : (((presentsChainsRunColimit (Hbp.obj (□n))).op).arrow (genCell e)).unop
      = (presentsChainsRunColimit (Hbp.obj (□n))).arrow
          (Quiver.homOfEq (atomCell e.1 (artinRun x)) (genSrc e) (genTgt e)) :=
    congrArg Quiver.Hom.unop
      (Presents.op_arrow (presentsChainsRunColimit (Hbp.obj (□n))) (genCell e))
  rw [h0, Presents.arrow_homOfEq, arrow_atomCell]
  refine (chBraid_eqToHom_sandwich _ _ _
    (hbpStrands _) (hbpStrands _) (hbpStrands _) (hbpStrands _)).trans ?_
  exact (chBraid_eqToHom_sandwich _ _ _
    (hbpStrands _) (hbpStrands _) (hbpStrands _) (hbpStrands _)).trans
      (chBraid_atomCell e.1 (artinRun x))

/-- **…and so does the fibration route's own generator**, conjugated by the 0-cell dictionary. -/
theorem chBraid_thetaCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    chBraid (((thetaCell x).hom ≫ (hLocArtinPresentation n).arrow e ≫ (thetaCell y).inv).unop)
        (hbpStrands _) (hbpStrands _) = posPerm (adjT e.1) := by
  have hR : ((thetaCell x).hom ≫ (hLocArtinPresentation n).arrow e ≫ (thetaCell y).inv).unop
      = (thetaCell y).inv.unop ≫ ((hLocArtinPresentation n).arrow e).unop
          ≫ (thetaCell x).hom.unop := by
    rw [unop_comp, unop_comp, Category.assoc]
  have h1 : IsIso ((thetaCell y).inv.unop) := inferInstanceAs (IsIso ((thetaCell y).unop).inv)
  have h2 : IsIso ((thetaCell x).hom.unop) := inferInstanceAs (IsIso ((thetaCell x).unop).hom)
  rw [hR]
  exact (chBraid_sandwich _ h1 _ _ h2 (hbpStrands _) (hbpStrands _) (hbpStrands _)
    (hbpStrands _)).trans (chBraid_hLocArtinPresentation_arrow n e)

/-- **The dictionary names the same arrow.**  Both sides perform the `k`-th atom, and the
projection to the localized base is faithful. -/
theorem hgenCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    ((presentsChainsRunColimit (Hbp.obj (□n))).op).arrow (genCell e)
      = (thetaCell x).hom ≫ (hLocArtinPresentation n).arrow e ≫ (thetaCell y).inv :=
  Quiver.Hom.unop_inj (eq_of_chBraid_eq (isSegal_H_of_symFree_repr (symFreeCube n))
    (N := n) (hbpStrands _) (hbpStrands _)
    ((chBraid_genCell e).trans (chBraid_thetaCell e).symm))

/-- **The colimit presentation of `Ch(Hbp □ⁿ)[W⁻¹]` and the fibration one agree, generator by
generator**: a 0-cell of the fibration route is a run, read in its own copy, and its `k`-th Artin
generator is the *one* crossing of the copy at `atomComp n k`.  No word is ever chosen. -/
noncomputable def glueArtinMap (n : ℕ) :
    Presents.Map (hLocArtinPresentation n) ((presentsChainsRunColimit (Hbp.obj (□n))).op) :=
  Presents.Map.ofGenerators obCell genCell thetaCell fun {_ _} e => hgenCell e

/-- **The spelling is one letter long** — a generator goes to a generator, not to a word. -/
theorem glueArtinMap_cells {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    (glueArtinMap n).hom.cells.map e = (genCell e).toPath := rfl

/-- **…so the two polygraphs present `Ch(Hbp □ⁿ)[W⁻¹]` compatibly**: the equivalence is the one
the generator dictionary spells. -/
noncomputable def glueArtinEquiv (n : ℕ) :
    (hLocArtinPoly n).presented ≌
      ((colimit (elementsPoly (wedgeHoms (Hbp.obj (□n))) runPolyFunctor)).op).presented :=
  (glueArtinMap n).equiv

/-! ## The 0-cells biject

Surjectivity is the colimit's legs (`exists_colimit_ι_obj`) followed by the leg down to a run's own
copy; injectivity is that `PosBraid n` has no non-trivial units, so distinct runs are
non-isomorphic. -/

/-- **Every 0-cell of a copy is a run's own 0-cell** — a run over `d` is entered from its own
chain, and the leg down to it is an arrow of the elements. -/
theorem exists_glueRunV (K : BPSet) {n : ℕ} (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (hc : dimSum (eltBase (wedgeHoms K) c).dims = n)
    (a : RunOver (eltBase (wedgeHoms K) c)) :
    ∃ z : ⋁(𝟙^n) ⟶ K, glueV K c a = glueRunV K z := by
  obtain ⟨⟨l, ⟨⟩, h⟩, hrun⟩ := a
  obtain rfl : l = zObj (𝟙^n) := RunOver.left_eq hc ⟨Over.mk h, hrun⟩
  refine ⟨(wedgeHoms K).map h.op c.unop.2, Eq.trans ?_
    (glueV_leg K (eltLeg K h c.unop.2) (runOverSelf n))⟩
  exact congrArg (glueV K c) (Subtype.ext (congrArg Over.mk (Category.id_comp h).symm))

theorem surjective_obCell (n : ℕ) : Function.Surjective (obCell (n := n)) := by
  intro A
  obtain ⟨c, w, hw⟩ := Polygraph.exists_colimit_ι_obj
    (elementsPoly (wedgeHoms (Hbp.obj (□n))) runPolyFunctor) ⟨A.as⟩
  obtain ⟨z, hz⟩ := exists_glueRunV (Hbp.obj (□n)) c (hbpCubeStrands c.unop.2) w.as
  exact ⟨artinPt z, congrArg (fun v : GenObj (colimit
    (elementsPoly (wedgeHoms (Hbp.obj (□n))) runPolyFunctor)).Gen => (⟨v.as⟩ : GenObj _))
    (hz.symm.trans hw)⟩

/-- The fibre over the run, as a category of elements. -/
noncomputable abbrev hFibElt (n : ℕ) :=
  (runBase n ⋙ wedgeHomsDescend (Hbp.obj (□n))
    (isSegal_H_of_symFree_repr (symFreeCube n))).Elements

/-- The element of the fibre a 0-cell of the fibration route is. -/
noncomputable def artinElt {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) : hFibElt n :=
  ⟨(artinComponent n).at' (Polygraph.pt _ x.as.1), artinRun x⟩

/-- **Distinct runs are non-isomorphic in the fibre** — `PosBraid n` has no non-trivial units. -/
theorem artinRun_eq_of_iso {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen}
    (α : artinElt x ≅ artinElt y) : artinRun x = artinRun y := by
  haveI : IsIso (α.hom.val) := inferInstanceAs (IsIso ((CategoryOfElements.π _).map α.hom))
  have h := congrArg Quiver.Hom.unop (IsIso.hom_inv_id (f := α.hom.val))
  rw [unop_comp, unop_id, SingleObj.comp_as_mul, SingleObj.id_as_one] at h
  have hid : α.hom.val = 𝟙 _ :=
    Quiver.Hom.unop_inj ((eq_one_of_mul_eq_one h).trans (SingleObj.id_as_one (PosBraid n) _).symm)
  have hp := α.hom.property
  rw [hid] at hp
  exact (((runBase n ⋙ wedgeHomsDescend (Hbp.obj (□n))
    (isSegal_H_of_symFree_repr (symFreeCube n))).map_id_apply _ (artinRun x)).symm.trans hp)

theorem injective_obCell (n : ℕ) : Function.Injective (obCell (n := n)) := by
  intro x y hxy
  have hι : (hLocArtinPresentation n).at' x ≅ (hLocArtinPresentation n).at' y :=
    (thetaCell x).symm ≪≫
      eqToIso (congrArg ((presentsChainsRunColimit (Hbp.obj (□n))).op).at' hxy) ≪≫ thetaCell y
  set E := chLocEquivElements (Hbp.obj (□n)) n (isSegal_H_of_symFree_repr (symFreeCube n))
    (fun {_} α => hbpCubeStrands α)
  have hα : op (artinElt y) ≅ op (artinElt x) :=
    (E.counitIso.app (op (artinElt y))).symm ≪≫ E.functor.mapIso hι.unop ≪≫
      E.counitIso.app (op (artinElt x))
  have hz := artinRun_eq_of_iso hα.unop
  exact (artinPt_artinRun x).symm.trans ((congrArg artinPt hz).trans (artinPt_artinRun y))

/-- **The 0-cells of the two polygraphs biject**, generator dictionary and all. -/
theorem bijective_obCell (n : ℕ) : Function.Bijective (obCell (n := n)) :=
  ⟨injective_obCell n, surjective_obCell n⟩

/-- **A 0-cell of the colimit names its run** — the shape the 1-cell dictionary reads a copy's
chart off. -/
theorem injective_glueRunV (n : ℕ) :
    Function.Injective (glueRunV (Hbp.obj (□n)) (n := n)) := fun z z' h =>
  congrArg artinRun (injective_obCell n (a₁ := artinPt z) (a₂ := artinPt z')
    (congrArg (fun v : GenObj (colimit
      (elementsPoly (wedgeHoms (Hbp.obj (□n))) runPolyFunctor)).Gen => (⟨v.as⟩ : GenObj _)) h))

/-! ## The 1-cells biject

Surjectivity is `exists_colimit_ι_map` followed by `exists_atomComp_leg`: a crossing anywhere is
the atom's own cell pushed down, and the copy it comes from is the atom's.  Injectivity is the
braid: a generator is pinned by the atom it performs. -/

theorem surjective_genCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen}
    (e : obCell x ⟶ obCell y) : ∃ e' : x ⟶ y, genCell e' = e := by
  obtain ⟨c, w₁, w₂, g, hx, hy, he⟩ := Polygraph.exists_colimit_ι_map
    (elementsPoly (wedgeHoms (Hbp.obj (□n))) runPolyFunctor)
    (e : glueRunV (Hbp.obj (□n)) (artinRun y) ⟶ glueRunV (Hbp.obj (□n)) (artinRun x))
  obtain ⟨w₁⟩ := w₁
  obtain ⟨w₂⟩ := w₂
  have hd : dimSum (eltBase (wedgeHoms (Hbp.obj (□n))) c).dims = n := hbpCubeStrands c.unop.2
  obtain ⟨k, v, hpa, hpb⟩ := exists_atomComp_leg (n := n) hd g.down
  subst hpa
  subst hpb
  have hleg : ∀ a : RunOver (zObj (atomComp n k)),
      glueV (Hbp.obj (□n)) c (RunOver.push v a)
        = glueV (Hbp.obj (□n)) (op ⟨op (zObj (atomComp n k)),
            (wedgeHoms (Hbp.obj (□n))).map v.op c.unop.2⟩) a :=
    fun a => glueV_leg (Hbp.obj (□n)) (eltLeg (Hbp.obj (□n)) v c.unop.2) a
  have hay : (atomOnes n k).φ ≫ (wedgeHoms (Hbp.obj (□n))).map v.op c.unop.2 = artinRun y :=
    injective_glueRunV n
      ((glueV_atomLeg k (Hbp.obj (□n)) _).symm.trans ((hleg (atomRun k)).symm.trans hx))
  have hax : (mergeOnes n k).φ ≫ (wedgeHoms (Hbp.obj (□n))).map v.op c.unop.2 = artinRun x :=
    injective_glueRunV n
      ((glueV_mergeLeg k (Hbp.obj (□n)) _).symm.trans ((hleg (mergeRun k)).symm.trans hy))
  have hw2 : (wedgeHoms (Hbp.obj (□n))).map v.op c.unop.2 = atomWitness k (artinRun x) :=
    eq_atomWitness k (artinRun x) hax
  have hgen : (hFibre n).map (runLoop n (adjT k)) (artinRun x) = artinRun y := by
    rw [runLoop_adjT]
    exact (atomOnes_atomWitness k (artinRun x)).symm.trans (by rw [← hw2]; exact hay)
  obtain ⟨u, hu⟩ : ∃ u : atomElt k (artinRun x) ⟶ c,
      (CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map u = v :=
    ⟨(CategoryOfElements.homMk c.unop
      (⟨op (zObj (atomComp n k)), atomWitness k (artinRun x)⟩ :
        (wedgeHoms (Hbp.obj (□n))).Elements) v.op hw2).op, rfl⟩
  subst hu
  refine ⟨⟨k, hgen⟩, Eq.trans ?_ he⟩
  have hg : (runPolyFunctor.map ((CategoryOfElements.π
        (wedgeHoms (Hbp.obj (□n)))).leftOp.map u)).pre.map
      (⟨runStep_atom k⟩ : (⟨atomRun k⟩ : GenObj (runPoly (zObj (atomComp n k))).Gen) ⟶
        ⟨mergeRun k⟩) = g := rfl
  have hEq : (colimit.ι (elementsPoly (wedgeHoms (Hbp.obj (□n))) runPolyFunctor) c).pre.map g
      = Quiver.homOfEq (atomCell k (artinRun x))
          (glueV_leg (Hbp.obj (□n)) u (atomRun k)).symm
          (glueV_leg (Hbp.obj (□n)) u (mergeRun k)).symm := by
    rw [← hg]
    exact glueE_leg (Hbp.obj (□n)) u _
  rw [hEq]
  exact (Quiver.homOfEq_trans (atomCell k (artinRun x)) _ _ _ _).symm

theorem injective_genCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} :
    Function.Injective (genCell : (x ⟶ y) → (obCell x ⟶ obCell y)) := by
  intro e e' h
  have hb : posPerm (adjT e.1) = posPerm (adjT e'.1) :=
    (chBraid_genCell e).symm.trans
      ((congrArg (fun t : obCell x ⟶ obCell y =>
        chBraid ((((presentsChainsRunColimit (Hbp.obj (□n))).op).arrow t).unop)
          (hbpStrands _) (hbpStrands _)) h).trans (chBraid_genCell e'))
  have hp : adjT e.1 = adjT e'.1 := by
    have hh := congrArg (posPermHom n) hb
    rwa [posPermHom_posPerm, posPermHom_posPerm] at hh
  exact Subtype.ext (Fin.ext (adjT_inj hp))

theorem bijective_genCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} :
    Function.Bijective (genCell : (x ⟶ y) → (obCell x ⟶ obCell y)) :=
  ⟨injective_genCell, fun e => surjective_genCell e⟩

/-- **The generator dictionary, as a map of generating quivers.** -/
noncomputable def genQuiver (n : ℕ) :
    GenObj (hLocArtinPoly n).Gen ⥤q
      GenObj ((colimit (elementsPoly (wedgeHoms (Hbp.obj (□n))) runPolyFunctor)).op).Gen where
  obj := obCell
  map := genCell

/-- **…and it is an isomorphism of generating quivers**: the `n!` runs biject with the colimit's
0-cells, and each hom-set of Artin generators with the colimit's 1-cells there.  With
`glueArtinMap` — the same data, naming the same arrows — the two presentations of
`Ch(Hbp □ⁿ)[W⁻¹]` differ only in their 2-cells. -/
theorem bijective_genQuiver (n : ℕ) :
    Function.Bijective (genQuiver n).obj ∧
      ∀ x y : GenObj (hLocArtinPoly n).Gen,
        Function.Bijective ((genQuiver n).map : (x ⟶ y) → _) :=
  ⟨bijective_obCell n, fun _ _ => bijective_genCell⟩

end ChainCat
