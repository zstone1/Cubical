import CubeChains.FinalBraid.SalBraidTope

/-!
# FinalBraid/WallCrossing — the Salvetti wall-crossing law

The **naturality half of STEP E** of `Sal(braidCOM n) ≌ Int(Lines(cube n))`: for a refinement
`f : y ⟶ x` in `RefineObj (cube n).init (cube n).final` (`y` finer than `x`) and a chamber tuple
`L` on `x`, the tope of the restricted chambers factors through the wall-crossing law

```
braidSign (heightOf y ((RefineLines n).map f.op L))
    = comp (braidSign (covectorHeight y)) (braidSign (heightOf x L)).
```

**Layer:** FinalBraid.  **Imports:** `FinalBraid/SalBraidTope`.  Not part of the default
`CubeChains` target.
-/

open CategoryTheory Opposite CubeChain StdCube SignType

namespace FinalBraid

open SignVec

variable {n : ℕ}
variable {x y : RefineObj (BPSet.cube n).init (BPSet.cube n).final}

/-! ## Abbreviations for the two side conditions of `□ⁿ` -/

/-- The wedge map induced by a refinement `f : y ⟶ x`, as a `BPSet` morphism. -/
noncomputable abbrev rwm (f : y ⟶ x) :
    BPSet.serialWedge (y.cubes.map (·.1)) ⟶ BPSet.serialWedge (x.cubes.map (·.1)) :=
  refineWedgeMap (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n) f

/-- The underlying presheaf map `φ` of `(cubeChainRefineEquiv n).functor.map f`. -/
theorem functor_map_φ (f : y ⟶ x) :
    ((cubeChainRefineEquiv n).functor.map f).φ = rwm f := rfl

theorem refineLines_map_apply (f : y ⟶ x) (L : (RefineLines n).obj (op x))
    (i : Fin ((cubeChainRefineEquiv n).functor.obj y).dims.length) :
    (RefineLines n).map f.op L i
      = (L (blockIdx (rwm f).hom i)).restrict
          (faceEmb (blockFace (rwm f).hom i)) (faceEmb (blockFace (rwm f).hom i)).injective := by
  rfl

/-! ## Index bridges -/

/-- The `Fin`-cast of a chain index into the dimension-list index. -/
abbrev yc (j : Fin y.cubes.length) : Fin (y.cubes.map (·.1)).length :=
  j.cast (by rw [List.length_map])

/-- The descent map of `y` (a monomorphism), as a presheaf map. -/
noncomputable abbrev descHom (y : RefineObj (BPSet.cube n).init (BPSet.cube n).final) :
    (BPSet.serialWedge (y.cubes.map (·.1))).toPsh ⟶ (BPSet.cube n).toPsh :=
  (refineToWedgeObj y).map.hom

theorem descHom_mono (y : RefineObj (BPSet.cube n).init (BPSet.cube n).final) :
    Mono (descHom y) :=
  descent_mono (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n) (refineToWedgeObj y)

theorem descHom_app_injective (y : RefineObj (BPSet.cube n).init (BPSet.cube n).final) (m : ℕ) :
    Function.Injective ((descHom y).app (op (Box.ob m))) :=
  have := descHom_mono y
  (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app _).mp this (op (Box.ob m)))

/-- `rwm f` composed with `x`'s descent is `y`'s descent (presheaf level). -/
theorem rwm_hom_comp_descHom (f : y ⟶ x) :
    (rwm f).hom ≫ descHom x = descHom y := by
  have h := refineWedgeMap_w (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n) f
  have := congrArg BPSet.Hom.hom h
  rwa [BPSet.comp_hom] at this

/-! ## Item 1 — the block factorisation square -/

/-- Dimension bridge: the `yc j`-th entry of a chain's dimension list is the `j`-th bead's dim. -/
theorem dimGet {z : RefineObj (BPSet.cube n).init (BPSet.cube n).final} (j : Fin z.cubes.length) :
    (z.cubes.map (·.1)).get (yc j) = (z.cubes.get j).1 := by
  simp [yc]

/-- The block restriction of a chain's descent map is the Yoneda classifier of the `j`-th bead. -/
theorem ι_comp_descHom (z : RefineObj (BPSet.cube n).init (BPSet.cube n).final)
    (j : Fin z.cubes.length) :
    BPSet.serialWedge.ι (z.cubes.map (·.1)) (yc j) ≫ descHom z
      = eqToHom (congrArg (fun m : ℕ+ => (BPSet.cube (m : ℕ)).toPsh) (dimGet j))
        ≫ yonedaEquiv.symm (z.cubes.get j).2 :=
  ι_comp_wedgeDesc (BPSet.cube n).init (BPSet.cube n).final z.cubes z.isChain j

/-- The face inclusion `f.incl j`, bridged by the dimension `eqToHom`s to have the
`dims`-indexed source/target objects used by the serial-wedge inclusions. -/
noncomputable def gbridge (f : y ⟶ x) (j : Fin y.cubes.length) :=
  eqToHom (congrArg Box.ob (congrArg (·.val) (dimGet j)))
    ≫ f.incl j
    ≫ eqToHom (congrArg Box.ob (congrArg (·.val) (dimGet (f.refinement j)).symm))

/-- **Item 1 — the block factorisation.**  For a refinement `f : y ⟶ x` (`y` finer), the `j`-th
block inclusion of `y`, followed by the induced wedge map `φ = rwm f`, factors through the
`(f.refinement j)`-th block of `x` via the recorded face inclusion `f.incl j` (bridged by the
dimension `eqToHom`s). -/
theorem refineWedgeMap_block_factor (f : y ⟶ x) (j : Fin y.cubes.length) :
    BPSet.serialWedge.ι (y.cubes.map (·.1)) (yc j) ≫ (rwm f).hom
      = yoneda.map (gbridge f j)
        ≫ BPSet.serialWedge.ι (x.cubes.map (·.1)) (yc (f.refinement j)) := by
  unfold gbridge
  haveI := descHom_mono x
  rw [← cancel_mono (descHom x)]
  erw [Category.assoc, rwm_hom_comp_descHom, ι_comp_descHom y j]
  erw [Category.assoc, ι_comp_descHom x (f.refinement j)]
  rw [f.inclSpec j, ← yonedaEquiv_symm_naturality_left]
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  erw [Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

/-- **Item 2 — the block index.**  The `j`-th `y`-block lands in the `(f.refinement j)`-th
`x`-block under `φ = rwm f`. -/
theorem blockIdx_rwm (f : y ⟶ x) (j : Fin y.cubes.length) :
    blockIdx (rwm f).hom (yc j) = yc (f.refinement j) :=
  (blockIdx_eq_of_factor (rwm f).hom (yc j) (yc (f.refinement j)) (gbridge f j)
    (refineWedgeMap_block_factor f j)).symm

/-- **Item 3 — the restriction rule.**  The chamber the restricted tuple puts on `y`-bead `j`
is the chamber on `x`-bead `f.refinement j`, restricted along `gbridge f j`'s free-coordinate
embedding. -/
theorem linesRestrict_apply (f : y ⟶ x) (L : (RefineLines n).obj (op x))
    (j : Fin y.cubes.length) :
    (RefineLines n).map f.op L (yc j)
      = (L (yc (f.refinement j))).restrict (faceEmb (gbridge f j))
          (faceEmb (gbridge f j)).injective := by
  rw [refineLines_map_apply]
  exact restrict_factor (rwm f).hom (yc j) (yc (f.refinement j)) (gbridge f j)
    (refineWedgeMap_block_factor f j) L

/-! ## Item 4 — the free-coordinate embeddings compose -/

/-- `toStar` intertwines a cube-map pullback with the iterated-face map (replica of the sibling
`BraidFaceEquiv.toStar_map_op`, kept self-contained here). -/
theorem toStar_map_op {dy dx : ℕ} (φ : Box.ob dy ⟶ Box.ob dx)
    (c : (BPSet.cube n).toPsh.cells dx) :
    toStar ((BPSet.cube n).toPsh.map φ.op c)
      = StdCube.app (K := StdCube.stdPre n) (toStar c)
          (toStar (φ : (BPSet.cube dx).toPsh.cells dy)) := by
  have h : (BPSet.cube n).toPsh.map φ.op c
      = ((BPSet.cube n).toPsh.cubeMap c).app (op (Box.ob dy)) φ := by
    rw [PrecubicalSet.cubeMap]
    exact (yonedaEquiv_symm_app_apply c (op (Box.ob dy)) φ).symm
  rw [h, toStar_cubeMap_app]

/-- **Item 4b — the geometric core.**  The `j`-th `y`-bead's free directions embed (via
`f.incl j`) into the `(f.refinement j)`-th `x`-bead's free directions, compatibly with the
coordinate maps `nones`. -/
theorem nones_incl (f : y ⟶ x) (j : Fin y.cubes.length) (b : Fin ((y.cubes.get j).1 : ℕ)) :
    nones (toStar (y.cubes.get j).2) b
      = nones (toStar (x.cubes.get (f.refinement j)).2) (faceEmb (f.incl j) b) := by
  have hspec := congrArg toStar (f.inclSpec j)
  rw [toStar_map_op] at hspec
  rw [hspec, nones_app]
  rfl

/-- The free-coordinate embedding of a dimension `eqToHom` is the corresponding `Fin.cast`. -/
theorem faceEmb_eqToHom {a a' : ℕ} (h : a = a') (u : Fin a) :
    faceEmb (eqToHom (congrArg Box.ob h)) u = Fin.cast h u := by
  subst h
  simp only [Fin.cast_eq_self]
  exact faceEmb_id a u

/-- **Item 4a — `gbridge`'s embedding is `f.incl j`'s, up to the dimension `Fin.cast`s.** -/
theorem faceEmb_gbridge (f : y ⟶ x) (j : Fin y.cubes.length)
    (u : Fin (((cubeChainRefineEquiv n).functor.obj y).dims.get (yc j))) :
    Fin.cast (dseqGetNat x (f.refinement j)) (faceEmb (gbridge f j) u)
      = faceEmb (f.incl j) (Fin.cast (dseqGetNat y j) u) := by
  apply Fin.ext
  unfold gbridge
  rw [faceEmb_comp, faceEmb_comp, faceEmb_eqToHom (congrArg (·.val) (dimGet j)),
    faceEmb_eqToHom (congrArg (·.val) (dimGet (f.refinement j)).symm)]
  simp only [Fin.val_cast]
  rfl

/-- **Item 4 (assembled).**  The chamber directions of the restricted chamber, pushed to the
`x`-bead coordinates, are `f.incl j`'s images — i.e. the same coordinates. -/
theorem nones_gbridge (f : y ⟶ x) (j : Fin y.cubes.length)
    (u : Fin (((cubeChainRefineEquiv n).functor.obj y).dims.get (yc j))) :
    nones (toStar (x.cubes.get (f.refinement j)).2)
        (Fin.cast (dseqGetNat x (f.refinement j)) (faceEmb (gbridge f j) u))
      = nones (toStar (y.cubes.get j).2) (Fin.cast (dseqGetNat y j) u) := by
  rw [faceEmb_gbridge, ← nones_incl]

/-! ## Item 5 — block containment -/

/-- **Item 5 — a `y`-block is contained in its target `x`-block.** -/
theorem blockOf_subset (f : y ⟶ x) (j : Fin y.cubes.length) :
    blockOf y j ⊆ blockOf x (f.refinement j) := by
  intro p hp
  obtain ⟨b, rfl⟩ : ∃ b, nones (toStar (y.cubes.get j).2) b = p :=
    ⟨nonesIdx (toStar (y.cubes.get j).2) p hp, nones_nonesIdx _ _ hp⟩
  rw [nones_incl f j]
  exact nones_mem _ _

/-- **Item 5 (corollary).**  A coordinate of `y`-block `j` has `x`-block index `f.refinement j`. -/
theorem blockIndex_of_mem (f : y ⟶ x) (j : Fin y.cubes.length) {p : Fin n}
    (hp : p ∈ blockOf y j) : blockIndex x p = f.refinement j :=
  blockIndex_unique x (blockOf_subset f j hp)

/-! ## Item 6 — the wall-crossing law -/

/-- The chamber-direction index of `p` in `y`-bead `j` maps, under `gbridge`'s embedding, to the
chamber-direction index of `p` in `x`-bead `f.refinement j`: the two describe the *same*
coordinate `p`. -/
theorem faceEmb_cast_eq (f : y ⟶ x) (j : Fin y.cubes.length) {p : Fin n}
    (hp : p ∈ blockOf y j) (hp' : p ∈ blockOf x (f.refinement j)) :
    faceEmb (gbridge f j)
        (Fin.cast (dseqGetNat y j).symm (nonesIdx (toStar (y.cubes.get j).2) p hp))
      = Fin.cast (dseqGetNat x (f.refinement j)).symm
          (nonesIdx (toStar (x.cubes.get (f.refinement j)).2) p hp') := by
  apply Fin.cast_injective (dseqGetNat x (f.refinement j))
  apply (nones (toStar (x.cubes.get (f.refinement j)).2)).injective
  rw [nones_gbridge]
  change nones (toStar (y.cubes.get j).2) (nonesIdx (toStar (y.cubes.get j).2) p hp)
     = nones (toStar (x.cubes.get (f.refinement j)).2)
         (nonesIdx (toStar (x.cubes.get (f.refinement j)).2) p hp')
  rw [nones_nonesIdx, nones_nonesIdx]

/-- **Item 6 — the same-block core.**  For two coordinates in the same `y`-block (hence the same
`x`-block), the restricted and un-restricted height covectors give the same sign: both reduce to
the *same* chamber comparison `(L (f.refinement j)).lt`. -/
theorem same_block_sign (f : y ⟶ x) (L : (RefineLines n).obj (op x)) (j : Fin y.cubes.length)
    {p q : Fin n} (hp : p ∈ blockOf y j) (hq : q ∈ blockOf y j) (hpq : p ≠ q) :
    SignType.sign (heightOf y ((RefineLines n).map f.op L) p
        - heightOf y ((RefineLines n).map f.op L) q)
      = SignType.sign (heightOf x L p - heightOf x L q) := by
  have hp' : p ∈ blockOf x (f.refinement j) := blockOf_subset f j hp
  have hq' : q ∈ blockOf x (f.refinement j) := blockOf_subset f j hq
  set rL := (RefineLines n).map f.op L with hrLdef
  rw [sign_sub_of_ne (fun h => hpq (heightOf_injective y rL h)),
      sign_sub_of_ne (fun h => hpq (heightOf_injective x L h))]
  suffices h : (heightOf y rL p < heightOf y rL q) ↔ (heightOf x L p < heightOf x L q) by
    by_cases hc : heightOf y rL p < heightOf y rL q
    · rw [if_pos hc, if_pos (h.mp hc)]
    · rw [if_neg hc, if_neg (fun hcx => hc (h.mpr hcx))]
  set ap := nonesIdx (toStar (y.cubes.get j).2) p hp with hapdef
  set aq := nonesIdx (toStar (y.cubes.get j).2) q hq with haqdef
  set a'p := nonesIdx (toStar (x.cubes.get (f.refinement j)).2) p hp' with ha'pdef
  set a'q := nonesIdx (toStar (x.cubes.get (f.refinement j)).2) q hq' with ha'qdef
  have hyp : heightOf y rL p = (n : ℤ) * (j : ℤ)
      + chamberRank (rL (Fin.cast (dseqLen y).symm j)) (Fin.cast (dseqGetNat y j).symm ap) := by
    conv_lhs => rw [show p = nones (toStar (y.cubes.get j).2) ap from (nones_nonesIdx _ _ hp).symm]
    exact heightOf_nones y rL j ap
  have hyq : heightOf y rL q = (n : ℤ) * (j : ℤ)
      + chamberRank (rL (Fin.cast (dseqLen y).symm j)) (Fin.cast (dseqGetNat y j).symm aq) := by
    conv_lhs => rw [show q = nones (toStar (y.cubes.get j).2) aq from (nones_nonesIdx _ _ hq).symm]
    exact heightOf_nones y rL j aq
  have hxp : heightOf x L p = (n : ℤ) * ((f.refinement j) : ℤ)
      + chamberRank (L (Fin.cast (dseqLen x).symm (f.refinement j)))
          (Fin.cast (dseqGetNat x (f.refinement j)).symm a'p) := by
    conv_lhs => rw [show p = nones (toStar (x.cubes.get (f.refinement j)).2) a'p from
      (nones_nonesIdx _ _ hp').symm]
    exact heightOf_nones x L (f.refinement j) a'p
  have hxq : heightOf x L q = (n : ℤ) * ((f.refinement j) : ℤ)
      + chamberRank (L (Fin.cast (dseqLen x).symm (f.refinement j)))
          (Fin.cast (dseqGetNat x (f.refinement j)).symm a'q) := by
    conv_lhs => rw [show q = nones (toStar (x.cubes.get (f.refinement j)).2) a'q from
      (nones_nonesIdx _ _ hq').symm]
    exact heightOf_nones x L (f.refinement j) a'q
  rw [hyp, hyq, hxp, hxq, add_lt_add_iff_left, add_lt_add_iff_left,
    chamberRank_lt_iff, chamberRank_lt_iff]
  have hlr : rL (Fin.cast (dseqLen y).symm j)
      = (L (yc (f.refinement j))).restrict (faceEmb (gbridge f j))
          (faceEmb (gbridge f j)).injective := linesRestrict_apply f L j
  rw [hlr, Chamber.restrict_lt, hapdef, haqdef, ha'pdef, ha'qdef]
  refine iff_of_eq (congrArg₂ (L (yc (f.refinement j))).lt ?_ ?_)
  · exact faceEmb_cast_eq f j hp hp'
  · exact faceEmb_cast_eq f j hq hq'

/-- **THE WALL-CROSSING LAW (naturality of the tope↔chamber bijection).**  For a refinement
`f : y ⟶ x` (`y` finer than `x`) and a chamber tuple `L` on `x`, the tope of the restricted
chambers on `y` is the Salvetti composite `comp (covectorHeight y) (heightOf x L)`: across blocks
the finer covector `covectorHeight y` decides the sign (`faceLE_covectorHeight_heightOf`), within a
block both sides reduce to the same chamber comparison (`same_block_sign`). -/
theorem wall_crossing (f : y ⟶ x) (L : (RefineLines n).obj (op x)) :
    braidSign (heightOf y ((RefineLines n).map f.op L))
      = comp (braidSign (covectorHeight y)) (braidSign (heightOf x L)) := by
  funext e
  change braidSign (heightOf y ((RefineLines n).map f.op L)) e
      = if braidSign (covectorHeight y) e = 0 then braidSign (heightOf x L) e
        else braidSign (covectorHeight y) e
  by_cases hz : braidSign (covectorHeight y) e = 0
  · -- same-block case
    rw [if_pos hz]
    have hbeq : blockIndex y e.1.1 = blockIndex y e.1.2 := by
      have hc := (braidSign_zero_iff (covectorHeight y) e).mp hz
      simp only [covectorHeight] at hc
      exact Fin.ext (by exact_mod_cast hc)
    have hp : e.1.1 ∈ blockOf y (blockIndex y e.1.1) := blockIndex_mem y e.1.1
    have hq : e.1.2 ∈ blockOf y (blockIndex y e.1.1) := (mem_block_iff y).mpr hbeq.symm
    rw [braidSign_apply, braidSign_apply]
    exact same_block_sign f L (blockIndex y e.1.1) hp hq (ne_of_lt e.2)
  · -- cross-block case
    rw [if_neg hz]
    have h4 := faceLE_covectorHeight_heightOf y ((RefineLines n).map f.op L)
    rw [faceLE_braidSign_iff_refinesTies] at h4
    exact h4 e ((braidSign_ne_zero_iff _ e).mp hz)

end FinalBraid
