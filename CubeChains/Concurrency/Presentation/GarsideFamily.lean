import CubeChains.Concurrency.Presentation.Dehornoy
import CubeChains.Concurrency.Presentation.SlicePresentation

/-!
# Concurrency/Presentation/GarsideFamily — the bead family, and the colimit it presents

The Garside polygraph of a chain is the germ of its beads' orders, and a **merge** acts on it by
pushing the run a tuple names (`beadFunctor`): `taut` is a functor, so `garsideRawFam` is one with
nothing to check beyond `beadFunctor_id` and `beadFunctor_comp`.

What makes the family usable is that a 0-cell *names* the run it is (`garsideSlicePresents_at`,
definitional at every step of the wedge splitting), and pushing it is `Over.map` — so the comparison
`hP` is an equality of functors (`hP_of_naming`, on `locOver_isThin`) and the colimit of the slice
presentations presents `Ch(K)[W⁻¹]`, with no hypothesis on `K`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits

namespace ChainCat

variable {d' d : Ch Zbp}

/-! ## The family -/

/-- **One Dehornoy germ per bead, functorially in the chain.** -/
noncomputable def garsideRawFam : Ch Zbp ⥤ Polygraph.{0, 0, 0} where
  obj d := garsidePolyList d.dims
  map f := tautMap (beadFunctor f)
  map_id d := by rw [beadFunctor_id, tautMap_id]; rfl
  map_comp f g := by rw [beadFunctor_comp, tautMap_comp]; rfl

/-- **The family, in the orientation the colimit route consumes** — a braid *raises* the weak order
where an arrow of the localized slice lowers it. -/
noncomputable def garsideFam : Ch Zbp ⥤ Polygraph.{0, 0, 0} :=
  garsideRawFam ⋙ Polygraph.opFunctor

/-- **The slice presentation, in that orientation.** -/
noncomputable def garsideSlicePresentation (d : Ch Zbp) :
    Presents (garsideFam.obj d) (((W Zbp).over (X := d)).Localization) :=
  ((garsideSlicePresents d).op).transport (opOpEquivalence _)

/-- **A 0-cell names the run it came from**, `garsideSlicePresents_at` read the right way up. -/
theorem garsideSlicePresentation_at (d : Ch Zbp) (x : wedgeOrder d.dims) :
    (garsideSlicePresentation d).at' ⟨x⟩
      = ((W Zbp).over (X := d)).Q.obj (wedgeRunOver d x).1 :=
  congrArg Opposite.unop (garsideSlicePresents_at d x)

/-- **The slice presentations are compatible with the base**: a 0-cell names the run it is, and
pushing it is `Over.map`.  Only the naming is asked — `hP_of_naming`, on `locOver_isThin`. -/
theorem garsideSlice_hP (f : d' ⟶ d) :
    (garsideFam.map f).functor ⋙ (garsideSlicePresentation d).E
      = (garsideSlicePresentation d').E ⋙ overMapLoc (W Zbp) f :=
  hP_of_naming (W Zbp) garsideSlicePresentation (fun {d' d} f z => by
    obtain ⟨⟨x⟩⟩ := z
    change (garsideSlicePresentation d).at' ⟨beadMap f x⟩
      = (overMapLoc (W Zbp) f).obj ((garsideSlicePresentation d').at' ⟨x⟩)
    rw [garsideSlicePresentation_at, garsideSlicePresentation_at, wedgeRunOver_beadMap]
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

end ChainCat
