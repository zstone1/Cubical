import CubeChains.Concurrency.Presentation.CubePresentation
import CubeChains.Concurrency.Merge.WedgeLocalize
import CubeChains.Machinery.Presentation.Product
import CubeChains.Concurrency.Presentation.ElementsFibration
import CubeChains.Machinery.Presentation.GlueOn
import CubeChains.Concurrency.Presentation.LocPresentation
import CubeChains.Concurrency.Presentation.CubeChartWeakOrder

/-!
# Concurrency/Presentation/SlicePresentation — the localized slices, and gluing them

`Ch (⋁d)[W⁻¹]` splits as a **product over the beads** (`locChConsEquiv`), so the presentation is
`Presents.prod` iterated (`beadPresentation`): one factor per bead, plus the product's
`interchange` 2-cells saying atoms in different beads commute.  The induction takes *any* family of
cube presentations, so it serves both the atom steps (`slicePresentation`) and an arbitrary
presentation of the base (`sliceLocPresentation`).  `Presents.ofThin` would also apply
(`locSlice_isThin`) but would quotient by every parallel pair, losing those relations.

Gluing the slices needs a set every chain maps **into**, and arrows run finer ⟶ coarser: the
maximal chains generate (`generating_maximalChains`), the runs do not (`generating_isRun_iff`).
The slice is *not* the elements of a functor on the localized base — the obstruction is the fibres,
not the formula (`merge_fibres_clash`) — so that one route to inducing the family fails.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph

universe u

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

/-- **The polygraph of a shape**: one factor per bead, the copies commuting by the product's
`interchange`.  The trailing `□0` the recursion leaves is a one-object factor with no generators.
`Q` is *any* family of polygraphs for the localized cubes — which is what makes the slice inherit
whatever the cube inherits.

`Polygraph.{u, u}`, not `Polygraph.{w, u}`: `Polygraph.prod` lands in
`Polygraph.{max wp wq up uq, max up uq}`, so it **grows the 1-cell universe** unless the two agree,
and the recursion below would change type at every cons.  Both families used here are
`Polygraph.{0, 0}`, so the restriction is invisible — until someone brings a base presentation at
unequal universes. -/
def beadPoly (Q : ℕ → Polygraph.{u, u}) : List ℕ+ → Polygraph.{u, u}
  | [] => Q 0
  | n :: rest => Polygraph.prod (Q (n : ℕ)) (beadPoly Q rest)

/-- **`Ch (⋁d)[W⁻¹]` is presented, bead by bead.**  `Presents.prod` on the polygraphs,
`locChConsEquiv` on the categories; the induction step is one line, `Presents.prod` being
hypothesis-free. -/
noncomputable def beadPresentation {Q : ℕ → Polygraph.{u, u}}
    (q : ∀ m : ℕ, Presents (Q m) ((W (□m)).Localization)) :
    ∀ d : List ℕ+, Presents (beadPoly Q d) ((W (⋁d)).Localization)
  | [] => q 0
  | n :: rest => ((q (n : ℕ)).prod (beadPresentation q rest)).transport (locChConsEquiv n rest)

/-- **…and so is the slice of the base over that shape** — `overEquivWedgeChains` is on the nose,
so this is the same polygraph read through `locOverEquivWedge`. -/
noncomputable def overBeadPresentation {Q : ℕ → Polygraph.{u, u}}
    (q : ∀ m : ℕ, Presents (Q m) ((W (□m)).Localization)) (d : List ℕ+) :
    Presents (beadPoly Q d) (((W Zbp).over (X := zObj d)).Localization) :=
  (beadPresentation q d).transport (locOverEquivWedge d).symm

/-! ### The two families

The atom steps present each localized cube outright (`cubePresentation`, via thinness); an
arbitrary presentation `p` of the base presents it too (`cubeLocPresentation`), and *that* one is
parametric.  The bead induction is run once and instantiated at each. -/

/-- The atom-step polygraph of a shape. -/
def slicePoly : List ℕ+ → Polygraph.{0, 0} := beadPoly fun m => Polygraph.thin (CubeStep m)

noncomputable def slicePresentation (d : List ℕ+) :
    Presents (slicePoly d) ((W (⋁d)).Localization) :=
  beadPresentation cubePresentation d

noncomputable def overSlicePresentation (d : List ℕ+) :
    Presents (slicePoly d) (((W Zbp).over (X := zObj d)).Localization) :=
  overBeadPresentation cubePresentation d

/-- **The localized slice, presented parametrically in the base.**  `p` is an arbitrary
presentation of `Ch Zbp[W⁻¹]`; the cube inherits it through `cubeLocPresentation`, and the bead
induction carries it to every shape. -/
noncomputable def sliceLocPresentation {P : Polygraph.{u, u}}
    (p : Presents P (((W Zbp).op).Localization)) (d : List ℕ+) :
    Presents (beadPoly (fun m => cubeChartPoly m p) d) ((W (⋁d)).Localization) :=
  beadPresentation (fun m => cubeLocPresentation m p) d

/-! ## The slice of `Ch K`, for an arbitrary `K`

A chain of `K` lies over its own shape, and `toChZ K` is a discrete fibration, so the slice under
it *is* the base's slice over that shape — and `W K` is the base's class pulled back.  Both are
unconditional, so a chain of any `K` whatever has its localized slice presented by the polygraph of
its dimension sequence, and by nothing about `K`. -/

/-- A chain lies over its own shape. -/
theorem toChZ_obj (K : BPSet) (c : Ch K) : (toChZ K).obj c = zObj c.dims := Obj.eq_of_dims rfl

/-- **The localized slice of `Ch K` under a chain is the base's under its shape.** -/
noncomputable def locOverEquivBase (K : BPSet) (c : Ch K) :
    ((W K).over (X := c)).Localization ≌ ((W Zbp).over (X := zObj c.dims)).Localization := by
  rw [W_eq_inverseImage_toChZ K]
  exact toChZ_obj K c ▸ sliceLocEquiv (toChZ K) (W Zbp) c

/-- **The localized slice of `Ch K` under any chain is presented, for every `K`** — by the
polygraph of the chain's dimension sequence, with no hypothesis on `K`.  This is where the glue
family consumes the slices, so it is stated for an arbitrary bead family: at `cubePresentation` it
is the atom steps, at `fun m => cubeLocPresentation m p` it is parametric in the base. -/
noncomputable def chOverBeadPresentation {Q : ℕ → Polygraph.{u, u}}
    (q : ∀ m : ℕ, Presents (Q m) ((W (□m)).Localization)) (K : BPSet) (c : Ch K) :
    Presents (beadPoly Q c.dims) (((W K).over (X := c)).Localization) :=
  (overBeadPresentation q c.dims).transport (locOverEquivBase K c).symm

noncomputable def chOverSlicePresentation (K : BPSet) (c : Ch K) :
    Presents (slicePoly c.dims) (((W K).over (X := c)).Localization) :=
  chOverBeadPresentation cubePresentation K c

/-! ## Gluing the slices

`GlueOn` wants a set of chains that every chain maps **into**.  Arrows run finer ⟶ coarser, so that
set is the maximal chains — and it is emphatically not the runs, which sit at the other end. -/

/-- `W K` read on the category of elements, in the spelling `presentsGlueOn` uses. -/
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

/-- The 0-cell of the glued polygraph that a chain names. -/
def chGlueV {K : BPSet} (a : Ch K) : GlueV (wedgeHoms K) := ⟨zObj a.dims, a.map⟩

theorem elt_chGlueV {K : BPSet} (a : Ch K) :
    elt (wedgeHoms K) (chGlueV a) = (toElements K).obj a := rfl

/-- **The maximal chains generate**, for every `K` and with no hypothesis on it: coarsening
terminates (`exists_hom_maximal`) and `toElements K` is an equivalence. -/
theorem generating_maximalChains (K : BPSet) :
    Generating (wedgeHoms K) (chGlueV '' MaximalChains K) := by
  intro c
  obtain ⟨s, hs, ⟨g⟩⟩ := exists_hom_maximal ((toElements K).objPreimage c)
  exact ⟨chGlueV s, ⟨s, hs, rfl⟩,
    ⟨((toElements K).objObjPreimageIso c).inv ≫ (toElements K).map g⟩⟩

/-- **Generation over the runs holds exactly when every chain is a run** — `Generating` needs an
arrow *into* the set, and nothing coarsens onto a run (`eq_of_hom_isRun`). -/
theorem generating_isRun_iff (K : BPSet) :
    Generating (wedgeHoms K) (chGlueV '' {a : Ch K | IsRun K a}) ↔ ∀ a : Ch K, IsRun K a := by
  constructor
  · intro h a
    obtain ⟨v, hv, ⟨u⟩⟩ := h ((toElements K).obj a)
    obtain ⟨s, hs, rfl⟩ := hv
    obtain ⟨g, -⟩ := (toElements K).map_surjective u
    obtain rfl := eq_of_hom_isRun g hs
    exact hs
  · intro h c
    exact ⟨chGlueV ((toElements K).objPreimage c), ⟨_, h _, rfl⟩,
      ⟨((toElements K).objObjPreimageIso c).inv⟩⟩

/-- …so already at the base the runs are not a generating set: the one-bead chain on two events
maps into no run. -/
theorem not_generating_isRun :
    ¬ Generating (wedgeHoms Zbp) (chGlueV '' {a : Ch Zbp | IsRun Zbp a}) := by
  rw [generating_isRun_iff]
  intro h
  exact absurd (h (zObj (topDims 2)) ⟨2, by omega⟩ (by simp [topDims])) (by decide)

/-- An object of `Ch Zbp` is its own shape. -/
theorem eq_zObj (d : Ch Zbp) : zObj d.dims = d := Obj.eq_of_dims rfl

/-- **The localized slice over any chain of the base is a poset** — `locSlice_isThin`, read through
`locOverEquivWedge`. -/
instance locOver_isThin (d : Ch Zbp) :
    Quiver.IsThin (((W Zbp).over (X := d)).Localization) :=
  eq_zObj d ▸ isThin_of_equiv (locOverEquivWedge d.dims).symm

/-- **`Ch(K)[W⁻¹]` is presented by gluing the slice presentations over the maximal chains.**  Both
geometric hypotheses are discharged here — the maximal chains generate and the slices are posets —
so what is left is a functor of slice presentations (`P`, `hP`) and the canonical run over each
slice object (`R`). -/
noncomputable def presentsChainsGlueOn (K : BPSet) {P : Ch Zbp ⥤ Polygraph.{w', u'}}
    (L : SliceLabels P)
    (p : ∀ d : Ch Zbp, Presents (P.obj d) (((W Zbp).over (X := d)).Localization))
    (hL : ∀ (d : Ch Zbp) (a : (P.obj d).V),
      (p d).at' ⟨a⟩ = Localization.Construction.objEquiv (W Zbp).over (L.ob d a))
    (hP : ∀ {d' d : Ch Zbp} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc (W Zbp) f)
    (R : SliceRetract L (W Zbp)) :
    Presents (glueOn (wedgeHoms K) L (chGlueV '' MaximalChains K)) ((W K).Localization) :=
  (presentsGlueOn (wedgeHoms K) L _ (W Zbp) p hL hP locOver_isThin R
    (generating_maximalChains K)).transport (locEquivElements K).symm


/-! ## Why the slice presentations are not induced from the base

A presentation of a category induces one of the category of elements of any functor on it
(`Presents.elements`), which is what makes `cubeChartPresentation` parametric in an arbitrary
spelling of the base.  Gluing would be parametric the same way if the localized slice were a
category of elements over the *localized* base.  It is not. -/

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
parameterizing somewhere else: `cubeChartPresentation` is parametric in an arbitrary presentation of
the base and asks no functor to descend, because `cubeFibre` is built on run-charts at the base and
`Presents.elements` is applied there.  Do not read a two-theorem split out of this. -/
theorem merge_fibres_clash :
    W Zbp (runMerge (zObj ([2] : List ℕ+)) dimSum_two) ∧
      IsEmpty (zObj ([2] : List ℕ+) ⟶ zObj (𝟙^2)) ∧
      Nonempty (zObj (𝟙^2) ⟶ zObj (𝟙^2)) :=
  ⟨W_runMerge _ dimSum_two, isEmpty_hom_two_ones, ⟨𝟙 _⟩⟩

end ChainCat
