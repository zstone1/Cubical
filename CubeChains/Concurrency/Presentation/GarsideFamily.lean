import CubeChains.Concurrency.Presentation.GarsideRuns

/-!
# Concurrency/Presentation/GarsideFamily — the product family, and the colimit it presents

The slice polygraph over `d` is the product of its beads' Dehornoy germs (`garsideSliceIso`), so
the germ family transports onto `garsidePolyList d.dims`.  What makes the transported family
usable is that the *wedge* route names the same slice object (`garsideSlice_naming`): the
comparison `hP` is then an equality of functors, and the colimit of the wedge presentations
presents `Ch(K)[W⁻¹]`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits

namespace ChainCat

variable {d' d : Ch Zbp}

/-! ## The family -/

/-- **One Dehornoy germ per bead, functorially in the chain** — the germ-on-runs family, read
through `garsideSliceIso`. -/
noncomputable def garsideRawFam : Ch Zbp ⥤ Polygraph.{0, 0, 0} where
  obj d := garsidePolyList d.dims
  map {d' d} f := (garsideSliceIso d').inv ≫ germBP.slicePush f ≫ (garsideSliceIso d).hom
  map_id d := by
    rw [germBP.slicePush_id, Category.id_comp, Iso.inv_hom_id]
  map_comp {_ d' _} f g := by
    rw [germBP.slicePush_comp, Category.assoc, Category.assoc, Category.assoc,
      ← Category.assoc (garsideSliceIso d').hom, Iso.hom_inv_id, Category.id_comp,
      ← Category.assoc, ← Category.assoc]

@[simp] theorem garsideRawFam_obj (d : Ch Zbp) : garsideRawFam.obj d = garsidePolyList d.dims :=
  rfl

/-- **The family, in the orientation the colimit route consumes.** -/
noncomputable def garsideFam : Ch Zbp ⥤ Polygraph.{0, 0, 0} :=
  garsideRawFam ⋙ Polygraph.opFunctor

/-- **The slice presentation, in that orientation.** -/
noncomputable def garsideSlicePresentation (d : Ch Zbp) :
    Presents (garsideFam.obj d) (((W Zbp).over (X := d)).Localization) :=
  ((garsideSlicePresents d).op).transport (opOpEquivalence _)

/-- **A 0-cell names the run it came from**, `garsideSlice_naming` read the right way up. -/
theorem garsideSlicePresentation_at (d : Ch Zbp) (b : (germBP.slicePoly d).V) :
    (garsideSlicePresentation d).at' ⟨((garsideSliceIso d).hom.pre.obj ⟨b⟩).as⟩
      = ((W Zbp).over (X := d)).Q.obj (germBP.sliceCellOver b) :=
  congrArg Opposite.unop (garsideSlice_naming d b)

/-- **A merge pushes the run inside the tuple** — the transport is conjugation, so the two
comparisons cancel. -/
theorem garsideRawFam_map_hom (f : d' ⟶ d) (b : (germBP.slicePoly d').V) :
    (garsideRawFam.map f).pre.obj ((garsideSliceIso d').hom.pre.obj ⟨b⟩)
      = (garsideSliceIso d).hom.pre.obj ⟨germBP.slicePushV f b⟩ := by
  change (garsideSliceIso d).hom.pre.obj ((germBP.slicePush f).pre.obj
      ((garsideSliceIso d').inv.pre.obj ((garsideSliceIso d').hom.pre.obj ⟨b⟩))) = _
  rw [show (garsideSliceIso d').inv.pre.obj ((garsideSliceIso d').hom.pre.obj ⟨b⟩) = ⟨b⟩ from
    congrArg (fun m : germBP.slicePoly d' ⟶ germBP.slicePoly d' => m.pre.obj ⟨b⟩)
      (garsideSliceIso d').hom_inv_id]
  rfl

/-- **The wedge presentations are compatible with the base**: a 0-cell names the run it is, and
pushing it is `Over.map`.  Only the naming is asked — `hP_of_naming`, on `locOver_isThin`. -/
theorem garsideSlice_hP (f : d' ⟶ d) :
    (garsideFam.map f).functor ⋙ (garsideSlicePresentation d).E
      = (garsideSlicePresentation d').E ⋙ overMapLoc (W Zbp) f :=
  hP_of_naming (W Zbp) garsideSlicePresentation (fun {d' d} f z => by
    obtain ⟨⟨a⟩⟩ := z
    obtain ⟨b, rfl⟩ : ∃ b, ((garsideSliceIso d').hom.pre.obj ⟨b⟩).as = a :=
      ⟨((garsideSliceIso d').inv.pre.obj ⟨a⟩).as,
        congrArg GenObj.as (congrArg
          (fun m : garsidePolyList d'.dims ⟶ garsidePolyList d'.dims => m.pre.obj ⟨a⟩)
          (garsideSliceIso d').inv_hom_id)⟩
    change (garsideSlicePresentation d).at'
        ⟨((garsideRawFam.map f).pre.obj ((garsideSliceIso d').hom.pre.obj ⟨b⟩)).as⟩
      = (overMapLoc (W Zbp) f).obj ((garsideSlicePresentation d').at'
          ⟨((garsideSliceIso d').hom.pre.obj ⟨b⟩).as⟩)
    rw [garsideRawFam_map_hom, garsideSlicePresentation_at, garsideSlicePresentation_at,
      germBP.sliceCellOver_push]
    exact (overMapLoc_obj (W Zbp) f _).symm) f

/-! ## The colimit -/

/-- **The Garside polygraph of `K`**: one copy of the beads' germs per chain, glued along the
arrows. -/
noncomputable def garsidePoly (K : BPSet) : Polygraph.{0, 0, 0} :=
  Limits.colimit (elementsPoly (wedgeHoms K) garsideFam)

/-- **…and it presents `Ch(K)[W⁻¹]`**, with no hypothesis on `K`. -/
noncomputable def garsidePresents (K : BPSet) :
    Presents (garsidePoly K) ((W K).Localization) :=
  presentsChainsColimit K garsideSlicePresentation fun {_ _} f => garsideSlice_hP f

/-- **The Garside polygraph of `□ⁿ` presents the right weak Bruhat order on `Sₙ`, read
backwards.** -/
noncomputable def garsideCube (n : ℕ) : Presents (garsidePoly (□n)) ((WeakOrder n)ᵒᵖ) :=
  (garsidePresents (□n)).transport (locCubeWeakOrder n)

/-- **The germ family is the bead family**, naturally in the chain. -/
noncomputable def garsideRawFamIso : germBP.sliceRawFunctor ≅ garsideRawFam :=
  NatIso.ofComponents garsideSliceIso fun {d' d} f => by
    change germBP.slicePush f ≫ (garsideSliceIso d).hom
      = (garsideSliceIso d').hom ≫ ((garsideSliceIso d').inv ≫
          germBP.slicePush f ≫ (garsideSliceIso d).hom)
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- **…so the cell dictionary's colimit is the Garside polygraph.**  `RunCells` reads the cells on
the left, where a 0-cell *is* a run. -/
noncomputable def runPolyIso (K : BPSet) : runPoly K ≅ garsidePoly K :=
  HasColimit.isoOfNatIso (Functor.isoWhiskerLeft (CategoryOfElements.π (wedgeHoms K)).leftOp
    (Functor.isoWhiskerRight garsideRawFamIso Polygraph.opFunctor))

end ChainCat
