import CubeChains.Concurrency.Presentation.SliceExchange
import CubeChains.Concurrency.Presentation.HAction
import CubeChains.Concurrency.Presentation.RunCells
import CubeChains.Concurrency.Presentation.ChBraid
import CubeChains.Machinery.Presentation.Comparison
import CubeChains.Machinery.Presentation.Opposite

/-!
# Concurrency/Presentation/RouteComparison — what each route's generators perform

The colimit route names one 0-cell per run of a chain and one 1-cell per *witnessed* crossing; the
fibration route names one 0-cell per element of the fibre over the run and one 1-cell per base
generator acting on it.  Each is an equivalence onto its own model of `Ch(K)[W⁻¹]`, and each model
reads to the localized base, so `chBraid_equiv_map` says what a generator performs — once per
route, with nothing transported by hand.

Both answers are the same atom: `chBraid_runGen` on the colimit side and
`chBraid_hLocArtinPresentation_arrow` on the fibration side.  Faithfulness (`eq_of_chBraid_eq`) is
what makes that decisive.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph

namespace ChainCat

/-! ## The fibration route: the fibre over the run

`chLocEquivElements` reads `Ch K[W⁻¹]` as the elements of the fibre over the run; projecting those
back to the base is the very same functor, so an arrow's braid is the base generator it carries. -/

section Fibre

variable (K : BPSet) (N : ℕ) (hS : IsSegal K.toPsh)
  (hK : ∀ {d : List ℕ+}, (⋁d ⟶ K) → dimSum d = N)

/-- The base projection, read through the fibre over the run. -/
noncomputable def chLocBaseElt : (W K).Localization ⥤ (((W Zbp).op).Localization)ᵒᵖ :=
  (chLocEquivElements K N hS hK).functor ⋙
    (CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N) ⋙
      CategoryOfElements.π (wedgeHomsDescend K hS)).op

/-- **…and it is the projection.**  `pre` is inverted and re-applied, so only its counit is
left. -/
noncomputable def chLocBaseEltIso : chLocBase K ≅ chLocBaseElt K N hS hK :=
  haveI : (chDescent K hS).IsLocalization (W K) := isLocalization_chDescent _ _
  haveI : (CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N)).IsEquivalence :=
    CategoryOfElements.isEquivalence_pre _ _ (cover_of_strands K N hS hK)
  chLocBaseModelIso K hS ≪≫
    Functor.isoWhiskerLeft (Localization.equivalenceFromModel (chDescent K hS) (W K)).functor
      (NatIso.op (Functor.isoWhiskerRight
        (CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N)).asEquivalence.counitIso
        (CategoryOfElements.π (wedgeHomsDescend K hS))))

/-- **The braid a fibration-route arrow performs is the base generator it carries.**  An arrow of
the fibre's category of elements is a braid acting on a run; read back in `Ch(K)[W⁻¹]` it performs
exactly that braid. -/
theorem chBraid_chLocEquivElements_inverse_map
    {A B : (runBase N ⋙ wedgeHomsDescend K hS).Elements} (ψ : A ⟶ B)
    (hB : dimSum (chOf ((chLocEquivElements K N hS hK).inverse.obj (op B))).dims = N)
    (hA : dimSum (chOf ((chLocEquivElements K N hS hK).inverse.obj (op A))).dims = N) :
    chBraid ((chLocEquivElements K N hS hK).inverse.map ψ.op) hB hA
      = homEquivPosBraid (dimSum_replicate N) (dimSum_replicate N) ((runBase N).map ψ.val) :=
  chBraid_equiv_map (chLocEquivElements K N hS hK) (chLocBaseEltIso K N hS hK) ψ.op hB hA
    (dimSum_replicate N) (dimSum_replicate N)

end Fibre

/-! ### At the decorated cube: a fibration-route generator names its atom -/

/-- Every chain of the decorated cube has `n` strands. -/
theorem hbpStrands {n : ℕ} (c : Ch (Hbp.obj (□n))) : dimSum c.dims = n := hbpCubeStrands c.map

/-- **The braid the `k`-th Artin generator names is the `k`-th atom.**  The fibration route's
1-cells are the base's generators acting on the fibre, and the base generator `k` is `posPerm
(adjT k)` on the nose; nothing in the transport to `Ch(Hbp □ⁿ)[W⁻¹]` disturbs it. -/
theorem chBraid_hLocArtinPresentation_arrow (n : ℕ) {x y : GenObj (hLocArtinPoly n).Gen}
    (e : x ⟶ y) :
    chBraid ((hLocArtinPresentation n).arrow e).unop
        (hbpStrands (chOf ((hLocArtinPresentation n).at' y).unop))
        (hbpStrands (chOf ((hLocArtinPresentation n).at' x).unop))
      = posPerm (adjT e.1) :=
  (chBraid_chLocEquivElements_inverse_map (Hbp.obj (□n)) n
      (isSegal_H_of_symFree_repr (symFreeCube n)) (fun {_} α => hbpCubeStrands α)
      (((artinComponent n).elements
        (runBase n ⋙ wedgeHomsDescend (Hbp.obj (□n))
          (isSegal_H_of_symFree_repr (symFreeCube n)))).arrow e)
      (hbpStrands _) (hbpStrands _)).trans
    (homEquivPosBraid_runLoop n (adjT e.1))

/-! ## The colimit route: the localized slices

The colimit route reads `Ch(K)[W⁻¹]` as the localized category of elements and each 1-cell inside a
localized slice.  Both steps project to the localized base on the nose — `elementsLift_comp_π` is
an equality — so a 1-cell's braid is read in its own slice. -/

section ColimitSide

/-- **A 1-cell of the colimit polygraph is an adjacent transposition.**  `RunStep` asks for one
crossing; a permutation with one inversion is an `adjT`. -/
theorem runStep_exists_adjT {d : Ch Zbp} {a b : RunOver d} (h : RunStep a b) :
    ∃ (e : Ch Zbp) (t : a.1.left ⟶ e) (m : b.1.left ⟶ e) (z : e ⟶ d)
      (k : Fin (dimSum a.1.left.dims - 1)),
      crossPerm rfl t = adjT k ∧ W Zbp m ∧ t ≫ z = a.1.hom ∧ m ≫ z = b.1.hom := by
  obtain ⟨e, t, m, z, ht, hm, hta, hmb⟩ := h
  obtain ⟨k, hk⟩ := eq_adjT_of_permLen_eq_one ht
  exact ⟨e, t, m, z, k, hk, hm, hta, hmb⟩

variable (K : BPSet)

/-- A chain of the base, read in the localized base. -/
noncomputable abbrev zBase : Ch Zbp ⥤ (((W Zbp).op).Localization)ᵒᵖ := ((W Zbp).op).Q.rightOp

/-- The elements of `wedgeHoms K`, read in the localized base. -/
noncomputable abbrev eltBaseRaw : ((wedgeHoms K).Elements)ᵒᵖ ⥤ (((W Zbp).op).Localization)ᵒᵖ :=
  (CategoryOfElements.π (wedgeHoms K)).leftOp ⋙ zBase

theorem eltBaseRaw_inverts :
    ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).IsInvertedBy
      (eltBaseRaw K) := by
  intro a b f hf
  haveI : IsIso ((((W Zbp).op).Q).map
      (((CategoryOfElements.π (wedgeHoms K)).leftOp.map f).op)) :=
    Localization.inverts ((W Zbp).op).Q ((W Zbp).op) _ hf
  exact inferInstanceAs (IsIso (Quiver.Hom.op ((((W Zbp).op).Q).map
    (((CategoryOfElements.π (wedgeHoms K)).leftOp.map f).op))))

/-- The localized elements, projected to the localized base. -/
noncomputable def eltLocBase :
    ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Localization ⥤
      (((W Zbp).op).Localization)ᵒᵖ :=
  Localization.Construction.lift (eltBaseRaw K) (eltBaseRaw_inverts K)

theorem eltLocBase_fac :
    ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q ⋙ eltLocBase K
      = eltBaseRaw K :=
  Localization.Construction.fac _ _

/-- **…and it is the projection.** -/
noncomputable def chLocBaseColimIso :
    chLocBase K ≅ (locEquivElements K).functor ⋙ eltLocBase K :=
  haveI : Localization.Lifting (W K).Q (W K) (chBaseRaw K)
      ((locEquivElements K).functor ⋙ eltLocBase K) :=
    ⟨Functor.isoWhiskerRight
      (Localization.compUniqFunctor (W K).Q
        (toElements K ⋙ ((W Zbp).inverseImage
          (CategoryOfElements.π (wedgeHoms K)).leftOp).Q) (W K)) (eltLocBase K) ≪≫
      eqToIso (congrArg (fun F => toElements K ⋙ F) (eltLocBase_fac K))⟩
  chLocBaseIso K _

/-- **The braid a colimit-route arrow performs is the one it performs on the elements.** -/
theorem chBraid_locEquivElements_inverse_map {N : ℕ}
    {A B : ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Localization}
    (φ : A ⟶ B)
    (hA : dimSum (chOf ((locEquivElements K).inverse.obj A)).dims = N)
    (hB : dimSum (chOf ((locEquivElements K).inverse.obj B)).dims = N)
    (hA' : dimSum (zOf ((eltLocBase K).obj A).unop).dims = N)
    (hB' : dimSum (zOf ((eltLocBase K).obj B).unop).dims = N) :
    chBraid ((locEquivElements K).inverse.map φ) hA hB
      = homEquivPosBraid hB' hA' (((eltLocBase K).map φ).unop) :=
  chBraid_equiv_map (locEquivElements K) (chLocBaseColimIso K) φ hA hB hA' hB'

/-- A slice 1-cell, projected: the cartesian lift is a section of the projection, so both descents
read a `Q`-image off the arrow underneath. -/
theorem colimSliceEval_eltLocBase_map_Q (d : Ch Zbp) (x : (wedgeHoms K).obj (op d))
    {y y' : Over d} (f : y ⟶ y') :
    (eltLocBase K).map ((colimSliceEval (wedgeHoms K) (W Zbp) d x).map
      (((W Zbp).over (X := d)).Q.map f)) = zBase.map f.left := by
  have h1 : (colimSliceEval (wedgeHoms K) (W Zbp) d x).map (((W Zbp).over (X := d)).Q.map f)
      = ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q.map
        ((elementsLift (wedgeHoms K) d x).map f) := Category.id_comp _
  have h2 : (eltLocBase K).map (((W Zbp).inverseImage
        (CategoryOfElements.π (wedgeHoms K)).leftOp).Q.map
        ((elementsLift (wedgeHoms K) d x).map f))
      = (eltBaseRaw K).map ((elementsLift (wedgeHoms K) d x).map f) := Category.id_comp _
  exact (congrArg (eltLocBase K).map h1).trans h2

/-- **The braid a colimit-route 1-cell performs in `Ch(K)[W⁻¹]` is the crossing of the square that
witnesses it**: cross the pair, then undo the merge, which performs nothing.

The slice is a poset, so `φ` is *the* arrow and no presentation of it is named: whichever family
of slice polygraphs the colimit was built from, its 1-cells perform this braid. -/
theorem chBraid_colimSliceEval {N : ℕ} (d : Ch Zbp) (x : (wedgeHoms K).obj (op d)) {a b : Over d}
    (φ : ((W Zbp).over (X := d)).Q.obj a ⟶ ((W Zbp).over (X := d)).Q.obj b)
    {e : Ch Zbp} {t : a.left ⟶ e} {m : b.left ⟶ e} {z : e ⟶ d} (hm : W Zbp m)
    (hta : t ≫ z = a.hom) (hmb : m ≫ z = b.hom)
    (ha : dimSum a.left.dims = N) (hb : dimSum b.left.dims = N) (he : dimSum e.dims = N)
    (hA : dimSum (chOf ((locEquivElements K).inverse.obj
      ((colimSliceEval (wedgeHoms K) (W Zbp) d x).obj
        (((W Zbp).over (X := d)).Q.obj a)))).dims = N)
    (hB : dimSum (chOf ((locEquivElements K).inverse.obj
      ((colimSliceEval (wedgeHoms K) (W Zbp) d x).obj
        (((W Zbp).over (X := d)).Q.obj b)))).dims = N) :
    chBraid ((locEquivElements K).inverse.map
        ((colimSliceEval (wedgeHoms K) (W Zbp) d x).map φ)) hA hB
      = posPerm (crossPerm ha t) := by
  refine (chBraid_locEquivElements_inverse_map K _ hA hB ha hb).trans ?_
  have hkey : φ ≫ ((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b ⟶ Over.mk z)
      = ((W Zbp).over (X := d)).Q.map (Over.homMk t hta : a ⟶ Over.mk z) :=
    Subsingleton.elim _ _
  have hstep : (eltLocBase K).map ((colimSliceEval (wedgeHoms K) (W Zbp) d x).map φ)
        ≫ zBase.map m = zBase.map t :=
    (congrArg (fun s => (eltLocBase K).map ((colimSliceEval (wedgeHoms K) (W Zbp) d x).map φ) ≫ s)
      (colimSliceEval_eltLocBase_map_Q K d x (Over.homMk m hmb : b ⟶ Over.mk z)).symm).trans
      ((((colimSliceEval (wedgeHoms K) (W Zbp) d x ⋙ eltLocBase K).map_comp _ _).symm.trans
        (congrArg (fun s => (eltLocBase K).map
          ((colimSliceEval (wedgeHoms K) (W Zbp) d x).map s)) hkey)).trans
        (colimSliceEval_eltLocBase_map_Q K d x (Over.homMk t hta : a ⟶ Over.mk z)))
  exact homEquivPosBraid_of_merge ha hb he hm
    (unop_comp.symm.trans (congrArg Quiver.Hom.unop hstep))

/-- **…read at objects named some other way.**  A polygraph's 0-cells name their slice objects only
up to an equation, and the braid does not see it. -/
theorem chBraid_colimSliceEval_of_eq {N : ℕ} (d : Ch Zbp) (x : (wedgeHoms K).obj (op d))
    {X Y : ((W Zbp).over (X := d)).Localization} {a b : Over d}
    (hX : X = ((W Zbp).over (X := d)).Q.obj a) (hY : Y = ((W Zbp).over (X := d)).Q.obj b)
    (φ : X ⟶ Y)
    {e : Ch Zbp} {t : a.left ⟶ e} {m : b.left ⟶ e} {z : e ⟶ d} (hm : W Zbp m)
    (hta : t ≫ z = a.hom) (hmb : m ≫ z = b.hom)
    (ha : dimSum a.left.dims = N) (hb : dimSum b.left.dims = N) (he : dimSum e.dims = N)
    (hA' : dimSum (chOf ((locEquivElements K).inverse.obj
      ((colimSliceEval (wedgeHoms K) (W Zbp) d x).obj X))).dims = N)
    (hB' : dimSum (chOf ((locEquivElements K).inverse.obj
      ((colimSliceEval (wedgeHoms K) (W Zbp) d x).obj Y))).dims = N) :
    chBraid ((locEquivElements K).inverse.map
        ((colimSliceEval (wedgeHoms K) (W Zbp) d x).map φ)) hA' hB'
      = posPerm (crossPerm ha t) := by
  subst hX
  subst hY
  exact chBraid_colimSliceEval K d x φ hm hta hmb ha hb he hA' hB'

/-! ### …hence what a 1-cell of `Br p K` performs

A 1-cell of a copy is a generator of `p` acting on a run and its two 0-cells name their own runs
(`sliceCellOver_runPt`), so the copy's own chain is the common target and the two structure maps
are the two legs.  An uncrossed source run is a merge, which performs nothing. -/

namespace BraidPresentation

variable (p : BraidPresentation)

/-- **A 1-cell of `Br p K` out of an uncrossed run performs its generator's permutation.**  The
run the generator acts *from* is the merge leg, so the whole cell performs the crossing the
generator adds. -/
theorem chBraid_runGen {N : ℕ} (c : ((wedgeHoms K).Elements)ᵒᵖ)
    {u v : RunAt (eltBase (wedgeHoms K) c) N} (s : p.S N)
    (hact : (sliceActionAt (eltBase (wedgeHoms K) c) N (p.braid s)).unop.val (some u) = some v)
    (hu : u.perm = 1)
    (hA : dimSum (chOf ((p.presentsBr K).at' (ιV K p.fam c (p.runPt v)))).dims = N)
    (hB : dimSum (chOf ((p.presentsBr K).at' (ιV K p.fam c (p.runPt u)))).dims = N) :
    chBraid ((p.presentsBr K).arrow
        (ιE K p.fam c (a := p.runPt v) (b := p.runPt u) (p.runGen s hact))) hA hB
      = posPerm (p.perm s) := by
  have ha : dimSum (v.1.1.left).dims = N := RunOver.left_dimSum v.strands v.1
  have hb : dimSum (u.1.1.left).dims = N := RunOver.left_dimSum u.strands u.1
  have hA' := (congrArg (fun X => dimSum (chOf X).dims)
    (p.at_ιV K c (p.runPt v)).symm).trans hA
  have hB' := (congrArg (fun X => dimSum (chOf X).dims)
    (p.at_ιV K c (p.runPt u)).symm).trans hB
  rw [p.arrow_ιE K c (p.runPt v) (p.runPt u) (p.runGen s hact)]
  refine (chBraid_eqToHom_sandwich _ _ _ hA hA' hB' hB).trans ?_
  refine (chBraid_colimSliceEval_of_eq K (eltBase (wedgeHoms K) c) c.unop.2
    (a := v.1.1) (b := u.1.1)
    ((slicePresentationOf_at p.base _ (p.runPt v)).trans
      (congrArg ((W Zbp).over (X := eltBase (wedgeHoms K) c)).Q.obj (p.sliceCellOver_runPt v)))
    ((slicePresentationOf_at p.base _ (p.runPt u)).trans
      (congrArg ((W Zbp).over (X := eltBase (wedgeHoms K) c)).Q.obj (p.sliceCellOver_runPt u)))
    _ (t := v.1.1.hom) (m := u.1.1.hom) (z := 𝟙 _)
    ((W_iff_crossPerm_eq_one hb u.1.1.hom).mpr hu)
    (Category.comp_id _) (Category.comp_id _) ha hb u.strands hA' hB').trans ?_
  refine congrArg posPerm ?_
  have hmul : v.perm = u.perm * p.perm s :=
    ChainCat.BraidPresentation.GermStep.mul_eq
      ((sliceActionAt_eq_some_iff (p.braid s) u v).mp hact)
  rw [show crossPerm ha v.1.1.hom = v.perm from rfl, hmul, hu, one_mul]

end BraidPresentation

end ColimitSide

end ChainCat
