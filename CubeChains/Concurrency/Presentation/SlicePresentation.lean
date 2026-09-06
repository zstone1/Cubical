import CubeChains.Concurrency.Merge.CubeThin
import CubeChains.Concurrency.Merge.WedgeLocalize
import CubeChains.Concurrency.Presentation.ElementsFibration
import CubeChains.Machinery.Presentation.Glue
import CubeChains.Concurrency.Presentation.LocPresentation

/-!
# Concurrency/Presentation/SlicePresentation — gluing the localized slices

`Ch(K)[W⁻¹]` is the localized category of elements of `wedgeHoms K` (`locEquivElements`), so a
functor of slice presentations glues to a presentation of the whole: a colimit over the elements
category, one copy per chain, glued along the arrows of `Ch K` (`presentsChainsColimit`).

The slice is *not* the elements of a functor on the localized base — the obstruction is the fibres,
not the formula (`merge_fibres_clash`) — so the family cannot be induced by descent; it is
inherited from the base instead (`Concurrency/Presentation/SliceInherit`).
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph

namespace ChainCat

instance instIsThinProd {C D : Type*} [Category C] [Category D] [Quiver.IsThin C]
    [Quiver.IsThin D] : Quiver.IsThin (C × D) :=
  fun X Y => inferInstanceAs (Subsingleton ((X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)))

/-- **The localized slice is a poset** — `locCube_isThin` bead by bead, along the splitting. -/
instance locSlice_isThin : ∀ d : List ℕ+, Quiver.IsThin ((W (⋁d)).Localization)
  | [] => locCube_isThin 0
  | n :: rest =>
      haveI := locSlice_isThin rest
      isThin_of_equiv (locChConsEquiv n rest)

/-! ## The slice of `Ch K`, for an arbitrary `K`

A chain of `K` lies over its own shape, and `toChZ K` is a discrete fibration, so the slice under
it *is* the base's slice over that shape — and `W K` is the base's class pulled back.  Both are
unconditional: the localized slice under a chain of any `K` whatever depends only on the chain's
dimension sequence, and on nothing about `K`. -/

/-- A chain lies over its own shape. -/
theorem toChZ_obj (K : BPSet) (c : Ch K) : (toChZ K).obj c = zObj c.dims := Obj.eq_of_dims rfl

/-- **The localized slice of `Ch K` under a chain is the base's under its shape.** -/
noncomputable def locOverEquivBase (K : BPSet) (c : Ch K) :
    ((W K).over (X := c)).Localization ≌ ((W Zbp).over (X := zObj c.dims)).Localization := by
  rw [W_eq_inverseImage_toChZ K]
  exact toChZ_obj K c ▸ sliceLocEquiv (toChZ K) (W Zbp) c

/-! ## Gluing the slices

One copy of the slice polygraph per chain of `K`, glued along the arrows of `Ch K` — a colimit over
the elements category, transported along `locEquivElements`. -/

/-- `W K` read on the category of elements, in the spelling the glue route uses. -/
theorem W_eq_inverseImage_elements (K : BPSet) :
    W K = ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).inverseImage
      (toElements K) := by
  ext a b f
  rw [W_eq_inverseImage_toChZ]
  rfl

/-- **`Ch(K)[W⁻¹]` is the localized category of elements**: `toElements K` is an equivalence and
carries one class to the other, so it is a localization too (`of_inverseImage`). -/
noncomputable def locEquivElements (K : BPSet) :
    (W K).Localization ≌
      ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Localization :=
  haveI : (toElements K ⋙
      ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q).IsLocalization (W K) :=
    Functor.IsLocalization.of_inverseImage (toElements K) _ _ (W K)
      (W_eq_inverseImage_elements K)
  Localization.uniq (W K).Q
    (toElements K ⋙ ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q) (W K)

/-- An object of `Ch Zbp` is its own shape. -/
theorem eq_zObj (d : Ch Zbp) : zObj d.dims = d := Obj.eq_of_dims rfl

/-- **The localized slice over any chain of the base is a poset** — `locSlice_isThin`, read through
`locOverEquivWedge`. -/
instance locOver_isThin (d : Ch Zbp) :
    Quiver.IsThin (((W Zbp).over (X := d)).Localization) :=
  eq_zObj d ▸ isThin_of_equiv (locOverEquivWedge d.dims).symm

/-- **`Ch(K)[W⁻¹]` is presented by the colimit of the slice presentations, for every `K`.**  The
slices being posets is supplied here; the caller brings a functor of slice presentations
(`P`, `hP`) whose 0-cells are a skeleton of each localized slice (`R`). -/
noncomputable def presentsChainsColimit (K : BPSet) {P : Ch Zbp ⥤ Polygraph.{0, 0, 0}}
    (p : ∀ d : Ch Zbp, Presents (P.obj d) (((W Zbp).over (X := d)).Localization))
    (hP : ∀ {d' d : Ch Zbp} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc (W Zbp) f)
    (R : SliceSkeleton (W Zbp) p) :
    Presents (Limits.colimit (elementsPoly (wedgeHoms K) P)) ((W K).Localization) :=
  (presentsSliceColimit (wedgeHoms K) (W Zbp) p hP locOver_isThin R).transport
    (locEquivElements K).symm


/-! ## The cells of the colimit

A copy is indexed by an element of `wedgeHoms K` — a chain of the base with a map into `K` — and
its cells are that chain's slice polygraph's.  Everything here is the colimit's universal property
read on a leg; no cell of the colimit is ever examined. -/

section Cells

variable (K : BPSet) (P : Ch Zbp ⥤ Polygraph.{0, 0, 0})

/-- **A refinement of the base moves the copy**: the element restricted along `g`, mapping to the
element it was restricted from.  Its base map is `g` on the nose, which is what makes the 0-cell
identification below definitional. -/
def eltLeg {d e : Ch Zbp} (g : d ⟶ e) (x : (wedgeHoms K).obj (op e)) :
    (op ⟨op d, (wedgeHoms K).map g.op x⟩ : ((wedgeHoms K).Elements)ᵒᵖ) ⟶ op ⟨op e, x⟩ :=
  (CategoryOfElements.homMk ⟨op e, x⟩ ⟨op d, (wedgeHoms K).map g.op x⟩ g.op rfl).op

@[simp] theorem eltLeg_base {d e : Ch Zbp} (g : d ⟶ e) (x : (wedgeHoms K).obj (op e)) :
    (CategoryOfElements.π (wedgeHoms K)).leftOp.map (eltLeg K g x) = g := rfl

/-- **A 0-cell of the colimit**: a 0-cell of a copy. -/
noncomputable def glueV (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a : (P.obj (eltBase (wedgeHoms K) c)).V) :
    GenObj (Limits.colimit (elementsPoly (wedgeHoms K) P)).Gen :=
  (Limits.colimit.ι (elementsPoly (wedgeHoms K) P) c).pre.obj ⟨a⟩

/-- **A 1-cell of the colimit**: a 1-cell inside a copy. -/
noncomputable def glueE (c : ((wedgeHoms K).Elements)ᵒᵖ)
    {a b : (P.obj (eltBase (wedgeHoms K) c)).V}
    (g : (⟨a⟩ : GenObj (P.obj (eltBase (wedgeHoms K) c)).Gen) ⟶ ⟨b⟩) :
    glueV K P c a ⟶ glueV K P c b :=
  (Limits.colimit.ι (elementsPoly (wedgeHoms K) P) c).pre.map g

/-- **The copies agree along an arrow of `∫X`** — the colimit's own naturality, on 0-cells. -/
theorem glueV_leg {c' c : ((wedgeHoms K).Elements)ᵒᵖ} (u : c' ⟶ c)
    (a : (P.obj (eltBase (wedgeHoms K) c')).V) :
    glueV K P c ((P.map ((CategoryOfElements.π (wedgeHoms K)).leftOp.map u)).pre.obj ⟨a⟩).as
      = glueV K P c' a :=
  congrArg (fun F : Polygraph.Hom (P.obj (eltBase (wedgeHoms K) c'))
      (Limits.colimit (elementsPoly (wedgeHoms K) P)) => F.pre.obj ⟨a⟩)
    (Limits.colimit.w (elementsPoly (wedgeHoms K) P) u)

/-- **…and the same, on 1-cells.** -/
theorem glueE_leg {c' c : ((wedgeHoms K).Elements)ᵒᵖ} (u : c' ⟶ c)
    {a b : (P.obj (eltBase (wedgeHoms K) c')).V}
    (g : (⟨a⟩ : GenObj (P.obj (eltBase (wedgeHoms K) c')).Gen) ⟶ ⟨b⟩) :
    glueE K P c ((P.map ((CategoryOfElements.π (wedgeHoms K)).leftOp.map u)).pre.map g)
      = Quiver.homOfEq (glueE K P c' g) (glueV_leg K P u a).symm (glueV_leg K P u b).symm := by
  have hnat : ((elementsPoly (wedgeHoms K) P).map u).pre ⋙q
      (Limits.colimit.ι (elementsPoly (wedgeHoms K) P) c).pre
      = (Limits.colimit.ι (elementsPoly (wedgeHoms K) P) c').pre :=
    congrArg (fun m : Polygraph.Hom ((elementsPoly (wedgeHoms K) P).obj c')
      (Limits.colimit (elementsPoly (wedgeHoms K) P)) => m.pre)
      (Limits.colimit.w (elementsPoly (wedgeHoms K) P) u)
  exact eq_of_heq ((Prefunctor.map_heq_of_eq hnat g).trans
    (Quiver.homOfEq_heq _ _ (glueE K P c' g)).symm)

/-- **A transported 1-cell is the transport of its 1-cell** — `glueE` is a prefunctor. -/
theorem glueE_homOfEq (c : ((wedgeHoms K).Elements)ᵒᵖ)
    {a b a' b' : (P.obj (eltBase (wedgeHoms K) c)).V}
    (g : (⟨a⟩ : GenObj (P.obj (eltBase (wedgeHoms K) c)).Gen) ⟶ ⟨b⟩)
    (ha : (⟨a⟩ : GenObj (P.obj (eltBase (wedgeHoms K) c)).Gen) = ⟨a'⟩)
    (hb : (⟨b⟩ : GenObj (P.obj (eltBase (wedgeHoms K) c)).Gen) = ⟨b'⟩) :
    glueE K P c (Quiver.homOfEq g ha hb)
      = Quiver.homOfEq (glueE K P c g)
          (congrArg (Limits.colimit.ι (elementsPoly (wedgeHoms K) P) c).pre.obj ha)
          (congrArg (Limits.colimit.ι (elementsPoly (wedgeHoms K) P) c).pre.obj hb) := by
  obtain rfl : a = a' := congrArg GenObj.as ha
  obtain rfl : b = b' := congrArg GenObj.as hb
  rfl

variable (p : ∀ d : Ch Zbp, Presents (P.obj d) (((W Zbp).over (X := d)).Localization))
  (hP : ∀ {d' d : Ch Zbp} (f : d' ⟶ d),
    (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc (W Zbp) f)
  (R : SliceSkeleton (W Zbp) p)

/-- **The object a 0-cell of the colimit names**: its own slice object, lifted at the copy's
element.  `glueIncl_desc` computes the comparison on a leg, and that is all a cell ever meets. -/
theorem at_glueV (c : ((wedgeHoms K).Elements)ᵒᵖ) (a : (P.obj (eltBase (wedgeHoms K) c)).V) :
    (presentsChainsColimit K p hP R).at' (glueV K P c a)
      = (locEquivElements K).inverse.obj
          ((glueSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).obj
            ((p (eltBase (wedgeHoms K) c)).at' ⟨a⟩)) := by
  have h1 : (presentsChainsColimit K p hP R).at' (glueV K P c a)
      = (locEquivElements K).inverse.obj
          ((glueInclFun (wedgeHoms K) P c ⋙
            glueDesc (P := P) (wedgeHoms K) (W Zbp) p hP).obj
              ((P.obj (eltBase (wedgeHoms K) c)).quot.obj ⟨a⟩)) := rfl
  exact h1.trans (congrArg (locEquivElements K).inverse.obj (Functor.congr_obj
    (glueIncl_desc (P := P) (wedgeHoms K) (W Zbp) p hP c)
    ((P.obj (eltBase (wedgeHoms K) c)).quot.obj ⟨a⟩)))

/-- **…and the arrow a 1-cell names**: the arrow its own slice presentation names, lifted.  The
`eqToHom`s are `at_glueV`, which the braid does not see. -/
theorem arrow_glueE (c : ((wedgeHoms K).Elements)ᵒᵖ)
    {a b : (P.obj (eltBase (wedgeHoms K) c)).V}
    (g : (⟨a⟩ : GenObj (P.obj (eltBase (wedgeHoms K) c)).Gen) ⟶ ⟨b⟩) :
    (presentsChainsColimit K p hP R).arrow (glueE K P c g)
      = eqToHom (at_glueV K P p hP R c a) ≫ (locEquivElements K).inverse.map
            ((glueSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).map
              ((p (eltBase (wedgeHoms K) c)).arrow g))
          ≫ eqToHom (at_glueV K P p hP R c b).symm := by
  have h1 : (presentsChainsColimit K p hP R).arrow (glueE K P c g)
      = ((glueInclFun (wedgeHoms K) P c ⋙
          glueDesc (P := P) (wedgeHoms K) (W Zbp) p hP) ⋙
            (locEquivElements K).inverse).map
          ((P.obj (eltBase (wedgeHoms K) c)).quot.map g.toPath) := rfl
  rw [h1, Functor.congr_hom (congrArg (fun F => F ⋙ (locEquivElements K).inverse)
    (glueIncl_desc (P := P) (wedgeHoms K) (W Zbp) p hP c))]
  rfl

end Cells

/-! ## Why the slice presentations are not induced from the base

A presentation of a category induces one of the category of elements of any functor on it
(`Presents.elements`).  Gluing would be parametric in the base that way if the localized slice were
a category of elements over the *localized* base.  It is not. -/

theorem one_mem_boundaries_ones : (1 : ℕ) ∈ boundaries (𝟙^2) := by
  rw [show (𝟙^2 : List ℕ+) = [1, 1] from rfl, boundaries_cons, boundaries_singleton]
  decide

theorem one_not_mem_boundaries_two : (1 : ℕ) ∉ boundaries ([2] : List ℕ+) := by
  rw [boundaries_singleton]; decide

/-- **The square does not refine the run**: arrows only ever add cuts, and `1` is a boundary of
`[1,1]` but not of `[2]`. -/
theorem isEmpty_hom_two_ones : IsEmpty (zObj ([2] : List ℕ+) ⟶ zObj (𝟙^2)) := by
  rw [← not_nonempty_iff, nonempty_hom_iff]
  rintro ⟨-, hsub⟩
  exact one_not_mem_boundaries_two (hsub one_mem_boundaries_ones)

theorem dimSum_two : BPSet.dimSum ((zObj ([2] : List ℕ+)).dims) = 2 := dimSum_single 2

/-- **The slice's fibre presheaf does not invert the merges.**  `Over d` is the category of
elements of `Hom(-, d)`; for that to descend to the localized base the merges would have to act
bijectively on it, and precomposition along the merge `1∨1 ⟶ 2` maps an *empty* hom-set onto a
nonempty one. -/
theorem hom_presheaf_not_inverts_merge :
    ∃ (a b : Ch Zbp) (w : a ⟶ b), W Zbp w ∧
      ¬ Function.Surjective (fun y : b ⟶ zObj (𝟙^2) => w ≫ y) := by
  refine ⟨zObj (𝟙^2), zObj [2], runMerge (zObj [2]) dimSum_two,
    W_runMerge (zObj [2]) dimSum_two, fun hsurj => ?_⟩
  obtain ⟨y, -⟩ := hsurj (𝟙 _)
  exact isEmpty_hom_two_ones.elim y

/-- **The localized slice is not the elements of a functor that descends to the localized base.**
A functor on the localized base sends an inverted arrow to a *bijection*; `Over.forget d` is a
discrete fibration before localizing — which is exactly why `Over d` is the elements category of
`Hom(-, d)` — and it cannot stay one after, because the merge below is inverted while its two
fibres over `d = 1∨1` are `∅` and `{𝟙}`.  The obstruction is the fibres, not the formula, so no
choice of *descending* functor escapes it.

**What this does not settle.**  It refutes one route to parameterizing the slice presentations —
descent along the projection to the base — and nothing more.  In particular it says nothing about
parameterizing somewhere else: `slicePolyFunctor` is parametric in an arbitrary presentation of the
base and asks no functor to descend, because `sliceFibre` is built on the runs at the base and
`Presents.elements` is applied there.  Do not read a two-theorem split out of this. -/
theorem merge_fibres_clash :
    W Zbp (runMerge (zObj ([2] : List ℕ+)) dimSum_two) ∧
      IsEmpty (zObj ([2] : List ℕ+) ⟶ zObj (𝟙^2)) ∧
      Nonempty (zObj (𝟙^2) ⟶ zObj (𝟙^2)) :=
  ⟨W_runMerge _ dimSum_two, isEmpty_hom_two_ones, ⟨𝟙 _⟩⟩

end ChainCat
