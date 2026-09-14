import CubeChains.Concurrency.Presentation.RunArrows
import CubeChains.Concurrency.Presentation.BeadOrder

/-!
# Concurrency/Presentation/TopRefinement — the two runs a chain spans

A chain is entered by one merge out of a run (`bottomRun`, `bottomHom`); its greatest refinement is
that merge run backwards inside every bead — the **complement** (`Run.compl`):

    (bottomRun e).chain ──bottomHom──▸ e ◂──topOf.2── (topOf e).1.chain

`topOf` is a function of `e` alone, so "this refinement is the greatest one" (`IsTop`) is the
equation `wedgeRun f = (wedgeRun (bottomHom e)).compl`.  The weak order is graded bead by bead, so a
length recognises it too (`isTop_iff_permLen`) — which is what lets the Artin comparison name the
greatest cut by a Coxeter length.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat

variable {K : BPSet}

/-! ## A chain whose shape is a run is its own run -/

theorem eltRestrict_id (c : (chCutPoly K).V) : eltRestrict c (𝟙 (shOf c)) = c :=
  congrArg (fun t => (⟨shOf c, t⟩ : (chCutPoly K).V))
    (by rw [op_id, Functor.map_id_apply])

/-- **A chain is its own run exactly when its shape is one** — the merge onto it is an
endomorphism, and a reindexing that leaves the shape alone therefore reflects the condition. -/
theorem eltRep_eq_self_iff (c : (chCutPoly K).V) : eltRep c = c ↔ zRep (shOf c) = shOf c :=
  ⟨fun h => congrArg (fun z : (chCutPoly K).V => shOf z) h, fun hz =>
    (eltRestrict_eq_of_W c hz (W_zRunMerge (shOf c)) (MorphismProperty.id_mem _ _)).trans
      (eltRestrict_id c)⟩

/-- …read at a named strand count. -/
theorem eltRep_eq_self {N : ℕ} {c : (chCutPoly K).V} (h : shOf c = zObj (𝟙^N)) : eltRep c = c := by
  have hd : dimSum (shOf c).dims = N := by rw [h]; exact dimSum_replicate N
  refine (eltRep_eq_self_iff c).mpr ?_
  change zObj (𝟙^(dimSum (shOf c).dims)) = shOf c
  rw [hd, h]

/-- **A chain its own run merges onto has an all-ones shape.** -/
theorem shOf_eq_ones_of_eltRep {M : ℕ} {c : (chCutPoly K).V} (h : eltRep c = c)
    (hM : dimSum (shOf c).dims = M) : shOf c = zObj (𝟙^M) :=
  (congrArg (fun s : (chCutPoly K).V => shOf s) h).symm.trans
    (congrArg (fun n => zObj (𝟙^n)) hM)

/-- **The 0-cells of the contraction are exactly the runs** — both sides say the shape is all
edges. -/
theorem eltRep_eq_self_iff_isRun (c : (chCutPoly K).V) : eltRep c = c ↔ IsRun Zbp (shOf c) :=
  ⟨fun h _ hd => List.eq_of_mem_replicate
      (congrArg ChainCat.Obj.dims (shOf_eq_ones_of_eltRep h rfl) ▸ hd),
    fun h => eltRep_eq_self (N := (shOf c).dims.length)
      (Obj.eq_of_dims (List.eq_replicate_of_mem h))⟩

namespace Paper

/-! ## A chain, and the run below it -/

/-- The 0-cell of the lifted cut polygraph a chain names. -/
def chV (a : Ch K) : (chCutPoly K).V := ⟨zObj a.dims, a.map⟩

@[simp] theorem vChain_chV (a : Ch K) : vChain (chV a) = a := rfl

/-- **A 0-cell of the contraction is a run** — it is its own merge, so its shape is all ones. -/
theorem isRun_vChain (U : (chCollapse K).V) : IsRun K (vChain U.1) :=
  (eltRep_eq_self_iff_isRun U.1).mp U.2

/-- The run a 0-cell of the contraction names. -/
def runOfV (U : (chCollapse K).V) : Run K := ⟨vChain U.1, isRun_vChain U⟩

/-- **A run is its own run** — its shape is all ones, and the merge out of that shape is the
identity. -/
theorem eltRep_chV (X : Run K) : eltRep (chV X.chain) = chV X.chain :=
  eltRep_eq_self (N := X.dims.length) (Obj.eq_of_dims (List.eq_replicate_of_mem X.ones))

/-- The 0-cell of the contraction a run names. -/
def vOfRun (X : Run K) : (chCollapse K).V := ⟨chV X.chain, eltRep_chV X⟩

/-- **A 0-cell is the shape it sits over, carrying its map** — the only transport the `Ch K`↔`∫F`
comparison pays, and it is definitional in the fibre. -/
theorem chV_vChain (z : (chCutPoly K).V) : chV (vChain z) = z :=
  Sigma.ext (Obj.eq_of_dims rfl) HEq.rfl

/-- **The 0-cells are the runs** — the comparison in dimension zero. -/
def runEquiv (K : BPSet) : Run K ≃ (chCollapse K).V where
  toFun := vOfRun
  invFun := runOfV
  left_inv _ := rfl
  right_inv U := Subtype.ext (chV_vChain U.1)

/-- **The run a chain is merged into from.** -/
noncomputable def bottomRun (a : Ch K) : Run K := runOfV ⟨eltRep (chV a), eltRep_idem _⟩

/-- **A run is the run below itself.** -/
theorem bottomRun_self (X : Run K) : bottomRun X.chain = X :=
  Run.ext (congrArg vChain (eltRep_chV X))

/-- **A merge does not change the run below.** -/
theorem bottomRun_eq_of_W {c d : Ch K} (u : c ⟶ d) (hu : W K u) : bottomRun d = bottomRun c :=
  Run.ext (congrArg vChain (eltRep_eq_of_W (a := chV d) (b := chV c) u hu).symm)

/-- **A merge out of a run names the run below its target.** -/
theorem eq_bottomRun_of_W {X : Run K} {a : Ch K} (m : X.chain ⟶ a) (hm : W K m) :
    bottomRun a = X := (bottomRun_eq_of_W m hm).trans (bottomRun_self X)

/-- **The merge a chain is entered by** from the run below it. -/
noncomputable def bottomHom (a : Ch K) : (bottomRun a).chain ⟶ a := runMergeK (chV a)

theorem W_bottomHom (a : Ch K) : W K (bottomHom a) := W_runMergeK (chV a)

/-! ## The greatest refinement out of a run

A refinement of `e` out of a run *is* a run of `⋁e.dims` — the source's classifying map is forced to
`φ ≫ e.map` — so the two readings are inverse (`wedgeRun`, `ofWedgeRun`).  The greatest refinement
is the merge below `e` run backwards inside every bead, `Run.compl`. -/

/-- A refinement out of a run, as a run of the target's wedge. -/
def wedgeRun {X : Run K} {e : Ch K} (f : X.chain ⟶ e) : Run (⋁e.dims) :=
  ⟨⟨X.dims, Hom.φ f⟩, X.ones⟩

/-- …and back: the run it refines `e` by, with the refinement. -/
def ofWedgeRun (e : Ch K) (r : Run (⋁e.dims)) : Σ X : Run K, X.chain ⟶ e :=
  ⟨⟨⟨r.dims, r.chain.map ≫ e.map⟩, r.ones⟩, ⟨r.chain.map, rfl⟩⟩

@[simp] theorem wedgeRun_ofWedgeRun (e : Ch K) (r : Run (⋁e.dims)) :
    wedgeRun (ofWedgeRun e r).2 = r := rfl

/-- **A refinement out of a run recovers the pair** — its source's classifying map is forced, so
`wedgeRun` and `ofWedgeRun` are inverse. -/
theorem ofWedgeRun_wedgeRun {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    ofWedgeRun e (wedgeRun f) = ⟨X, f⟩ := by
  obtain ⟨⟨Xd, Xm⟩, Xp⟩ := X
  obtain ⟨φ, hw⟩ := f
  revert Xp
  dsimp only
  intro Xp φ hw
  subst hw
  rfl

/-- **The crossing permutation of a refinement out of a run**, on the target's own events. -/
noncomputable def runCross {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    Perm (Fin (dimSum e.dims)) := crossPerm (dimSum_eq_of_hom f) f

/-- …read at the base, where the bead order lives. -/
theorem runCross_zHom {X : Run K} {e : Ch K} (f : X.chain ⟶ e)
    (h : dimSum X.dims = dimSum e.dims) :
    crossPerm (a := zObj X.dims) h (zHom (Hom.φ f)) = runCross f :=
  crossPerm_eq_of_φ _ rfl

/-- **A refinement out of a run is one of the target's runs.** -/
theorem runSet_runCross {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    RunSet (zObj e.dims) (dimSum e.dims) (runCross f) :=
  runSet_iff_exists_wedgeHom.mpr
    ⟨X.dims, X.ones, dimSum_eq_of_hom f, Hom.φ f, runCross_zHom f (dimSum_eq_of_hom f)⟩

/-- **The capacity bounds a refinement out of a run** — it is one of the target's runs, and a run
over a shape inverts at most the pairs its beads hold. -/
theorem permLen_crossPerm_le_crossCap {X : Run K} {e : Ch K} (f : X.chain ⟶ e) {N : ℕ}
    (h : dimSum X.chain.dims = N) : permLen (crossPerm h f) ≤ crossCap e.dims :=
  (permLen_crossPerm (dimSum_eq_of_hom f) h f).trans_le (permLen_le_crossCap (runSet_runCross f))

/-- **A crossing refinement onto a degree-one chain crosses exactly one pair** — the target holds
one concurrent pair and no more, and a refinement that crosses none is a merge. -/
theorem permLen_crossPerm_eq_one {X : Run K} {e : Ch K} (f : X.chain ⟶ e) (he : degree e = 1)
    (hf : ¬ W K f) {N : ℕ} (h : dimSum X.chain.dims = N) : permLen (crossPerm h f) = 1 := by
  have hle := (permLen_crossPerm_le_crossCap f h).trans_eq (crossCap_eq_one_of_degree he)
  have hne : permLen (crossPerm h f) ≠ 0 := fun h0 =>
    hf ((W_iff_flat f).mpr ((crossPerm_eq_one_iff_flat h f).mp (eq_one_of_permLen_eq_zero _ h0)))
  omega

/-- **A merge in front crosses nothing**, so it leaves the crossing permutation alone. -/
theorem runCross_W_comp {X Y : Run K} {e : Ch K} {u : X.chain ⟶ Y.chain} (hu : W K u)
    (f : Y.chain ⟶ e) : runCross (u ≫ f) = runCross f :=
  (crossPerm_comp (dimSum_eq_of_hom (u ≫ f)) u f).trans (by
    rw [crossPerm_eq_one_of_W _ hu, mul_one]
    exact rfl)

/-- **Two refinements out of runs that cross alike name one run of the wedge** — a chain map is its
wedge map, and the crossing pins that. -/
theorem wedgeRun_eq_of_runCross_eq {e : Ch K} {X Y : Run K} {f : X.chain ⟶ e} {g : Y.chain ⟶ e}
    (h : runCross f = runCross g) : wedgeRun f = wedgeRun g := by
  obtain ⟨⟨Xd, Xm⟩, Xp⟩ := X
  obtain ⟨⟨Yd, Ym⟩, Yp⟩ := Y
  obtain rfl : Xd = Yd :=
    ones_eq_of_dimSum_eq Xp Yp ((dimSum_eq_of_hom f).trans (dimSum_eq_of_hom g).symm)
  have hd : dimSum Xd = dimSum e.dims := dimSum_eq_of_hom f
  have hbase : zHom (Hom.φ f) = zHom (Hom.φ g) :=
    hom_ext_of_crossPerm (h := hd)
      ((runCross_zHom f hd).trans (h.trans (runCross_zHom g hd).symm))
  exact Run.ext (congrArg (fun φ => (⟨Xd, φ⟩ : Ch (⋁e.dims))) (congrArg ChainCat.Hom.φ hbase))

/-- **A chain is entered by one merge out of a run** — merges cross nothing, and a refinement out of
a run is pinned by what it crosses. -/
theorem wedgeRun_eq_of_W {e : Ch K} {X Y : Run K} {f : X.chain ⟶ e} {g : Y.chain ⟶ e}
    (hf : W K f) (hg : W K g) : wedgeRun f = wedgeRun g :=
  wedgeRun_eq_of_runCross_eq
    ((show runCross f = 1 from crossPerm_eq_one_of_W _ hf).trans
      (show runCross g = 1 from crossPerm_eq_one_of_W _ hg).symm)

/-- **The greatest refinement of a chain out of a run**: the merge below it, run backwards inside
every bead. -/
noncomputable def topOf (e : Ch K) : Σ X : Run K, X.chain ⟶ e :=
  ofWedgeRun e (wedgeRun (bottomHom e)).compl

/-- **The run a chain's greatest refinement comes out of.**  The two runs a chain spans:
`bottomRun` crosses nothing, `topRun` crosses as much as the chain allows. -/
noncomputable abbrev topRun (e : Ch K) : Run K := (topOf e).1

@[simp] theorem wedgeRun_topOf (e : Ch K) :
    wedgeRun (topOf e).2 = (wedgeRun (bottomHom e)).compl := wedgeRun_ofWedgeRun e _

/-- **Codimension is degree, out of a run.** -/
theorem codim_topOf (e : Ch K) : codim (topOf e).2 = degree e := by
  change degree e - degree (topOf e).1.chain = degree e
  rw [(isRun_iff_degree_eq_zero _).mp (topOf e).1.property, Nat.sub_zero]

/-- **The greatest refinement crosses**, as soon as there is anything to cross: the complement fixes
only the shapes with nothing to reverse (`Run.compl_ne`), and a chain is entered by one merge.  So
the two factorisations a degree-two object reads spell a relation, not `w = w`. -/
theorem not_W_topOf (e : Ch K) (he : degree e ≠ 0) : ¬ W K (topOf e).2 := fun hW =>
  Run.compl_ne (wedgeRun (bottomHom e)) he
    ((wedgeRun_topOf e).symm.trans (wedgeRun_eq_of_W hW (W_bottomHom e)))

/-! ## The greatest refinement, as a condition on a refinement

`topOf` is a function of the chain alone, so "this refinement is the greatest one" is an equation of
pairs — equivalently, the two readings being inverse, an equation of runs of `⋁e.dims`: the
refinement's run is the **complement** of the merge the chain is entered by. -/

/-- **A refinement is its target's greatest one** — it comes out of a run, and the pair it makes is
`topOf`'s. -/
def IsTop {a e : Ch K} (f : a ⟶ e) : Prop := ∃ h : IsRun K a, topOf e = ⟨⟨a, h⟩, f⟩

/-- …read at a named run, where the existential is redundant. -/
theorem isTop_iff_eq {X : Run K} {e : Ch K} (f : X.chain ⟶ e) : IsTop f ↔ topOf e = ⟨X, f⟩ :=
  ⟨fun h => h.2, fun h => ⟨X.property, h⟩⟩

/-- **…and it is the complement of the merge below**, `wedgeRun` and `ofWedgeRun` being inverse. -/
theorem isTop_iff_wedgeRun {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    IsTop f ↔ wedgeRun f = (wedgeRun (bottomHom e)).compl := by
  rw [isTop_iff_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (congrArg (fun t : Σ Y : Run K, Y.chain ⟶ e => wedgeRun t.2) h).symm.trans
      (wedgeRun_topOf e)
  · exact (congrArg (ofWedgeRun e) h.symm).trans (ofWedgeRun_wedgeRun f)

/-- Two `(run, refinement)` pairs agree once their runs do and the refinements agree after the
renaming that identifies them. -/
private theorem top_eq {e : Ch K} (t : Σ X : Run K, X.chain ⟶ e) {X : Run K} (h : t.1 = X)
    {f : X.chain ⟶ e} (hf : t.2 = eqToHom (congrArg Run.chain h) ≫ f) : t = ⟨X, f⟩ := by
  obtain ⟨R, g⟩ := t
  subst h
  simpa using hf

/-- **`topOf`'s own refinement, read at another name for its run, is the greatest one** — the
renaming cancels, and `IsTop` sees nothing else. -/
theorem isTop_eqToHom_comp {e : Ch K} {X : Run K} (h : (topOf e).1 = X) :
    IsTop (eqToHom (congrArg Run.chain h.symm) ≫ (topOf e).2) :=
  ⟨X.property, top_eq (topOf e) h (by
    rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp])⟩

/-- **The run a greatest refinement comes out of** — `IsTop` names it. -/
theorem IsTop.fst_eq {X : Run K} {e : Ch K} {f : X.chain ⟶ e} (hf : IsTop f) : (topOf e).1 = X :=
  congrArg Sigma.fst hf.2

/-- **There is only one greatest refinement** out of a given run — both are `topOf`'s. -/
theorem IsTop.hom_eq {X : Run K} {e : Ch K} {f g : X.chain ⟶ e} (hf : IsTop f) (hg : IsTop g) :
    f = g :=
  eq_of_heq (Sigma.mk.inj_iff.mp (hf.2.symm.trans hg.2)).2

/-- **`W` is a condition on the wedge map** — so it is the same upstairs and at the base. -/
theorem W_zHom_iff {a b : Ch K} (f : a ⟶ b) : W Zbp (zHom (Hom.φ f)) ↔ W K f :=
  (W_iff_flat _).trans (W_iff_flat f).symm

/-- **A chain and its shape are entered by one run of the wedge** — both merges are merges out of
runs onto the same wedge map, and `W` sees nothing else. -/
theorem wedgeRun_bottomHom_zObj (e : Ch K) :
    wedgeRun (bottomHom (zObj e.dims)) = wedgeRun (bottomHom e) :=
  wedgeRun_eq_of_W (X := bottomRun (zObj e.dims))
    (Y := ⟨zObj (bottomRun e).dims, (bottomRun e).property⟩)
    (f := bottomHom (zObj e.dims)) (g := zHom (Hom.φ (bottomHom e)))
    (W_bottomHom _) ((W_zHom_iff (bottomHom e)).mpr (W_bottomHom e))

/-- **…and so being the greatest refinement is the same upstairs and at the base**, `wedgeRun`
reading the wedge map and nothing else. -/
theorem isTop_iff_zHom {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    IsTop f ↔ IsTop (zHom (Hom.φ f)) := by
  rw [isTop_iff_wedgeRun (X := X) f,
    isTop_iff_wedgeRun (X := (⟨zObj X.dims, X.ones⟩ : Run Zbp)) (zHom (Hom.φ f)),
    wedgeRun_bottomHom_zObj]
  exact Iff.rfl

/-! ## …and it is the reversal in every bead

The merge below a chain crosses nothing, so its wedge run is the least tuple's; the complement
carries that to the greatest tuple's, whose crossing is the block sum `blockTop`. -/

/-- **A tuple's own run crosses the tuple.** -/
theorem runCross_ofWedgeRun_tupleRun (e : Ch K) (x : wedgeOrder e.dims) :
    runCross (ofWedgeRun e (tupleRun e.dims x)).2 = blockSum e.dims x :=
  (runCross_zHom (ofWedgeRun e (tupleRun e.dims x)).2
      (dimSum_eq_of_hom (ofWedgeRun e (tupleRun e.dims x)).2)).symm.trans
    (crossPerm_wedgeRunChain e.dims x _)

/-- **The merge below a chain is its least tuple's run.** -/
theorem wedgeRun_bottomHom (e : Ch K) :
    wedgeRun (bottomHom e) = tupleRun e.dims (blockBot e.dims) :=
  (wedgeRun_eq_of_runCross_eq
      ((show runCross (bottomHom e) = 1 from crossPerm_eq_one_of_W _ (W_bottomHom e)).trans
        ((runCross_ofWedgeRun_tupleRun e (blockBot e.dims)).trans
          (blockSum_blockBot e.dims)).symm)).trans
    (wedgeRun_ofWedgeRun e _)

/-- **…so the greatest refinement is the greatest tuple's run.** -/
theorem topOf_eq_ofWedgeRun (e : Ch K) :
    topOf e = ofWedgeRun e (tupleRun e.dims (blockTop e.dims)) :=
  congrArg (ofWedgeRun e)
    ((congrArg Run.compl (wedgeRun_bottomHom e)).trans (compl_tupleRun_blockBot e.dims))

/-- **The greatest refinement crosses the greatest tuple.** -/
theorem runCross_topOf (e : Ch K) : runCross (topOf e).2 = blockSum e.dims (blockTop e.dims) :=
  (congrArg (fun t : Σ X : Run K, X.chain ⟶ e => runCross t.2) (topOf_eq_ofWedgeRun e)).trans
    (runCross_ofWedgeRun_tupleRun e (blockTop e.dims))

/-- …so it attains the capacity. -/
theorem permLen_runCross_topOf (e : Ch K) :
    permLen (runCross (topOf e).2) = crossCap e.dims :=
  (congrArg permLen (runCross_topOf e)).trans (permLen_blockSum_blockTop e.dims)

/-- **The greatest refinement is the only one that attains the capacity** — the weak order is graded
in every bead, so the reversals are where the capacity is reached and nowhere else.  The `mpr`
direction is what lets a length recognise the greatest refinement across two targets, where the runs
themselves cannot be compared. -/
theorem isTop_iff_permLen {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    IsTop f ↔ permLen (runCross f) = crossCap e.dims :=
  ⟨fun hf =>
      (congrArg (fun t : Σ Y : Run K, Y.chain ⟶ e => permLen (runCross t.2)) hf.2).symm.trans
        (permLen_runCross_topOf e),
   fun hf => (isTop_iff_wedgeRun f).mpr
    ((wedgeRun_eq_of_runCross_eq
        ((eq_blockSum_blockTop_of_permLen e.dims (runSet_runCross f) hf).trans
          (runCross_topOf e).symm)).trans (wedgeRun_topOf e))⟩

/-! ## Degree one -/

/-- **At degree one there is only one crossing refinement out of the run** — `eq_atomOnes`: the
shape is an atom's cell (`exists_atomComp`), and at that cell a non-merge is the atom. -/
theorem eq_of_not_W_deg_one {d : List ℕ+} (hd : ∀ x ∈ d, x = 1) {c : Ch Zbp}
    (hdeg : degree c = 1) {u v : zObj d ⟶ c} (hu : ¬ W Zbp u) (hv : ¬ W Zbp v) : u = v := by
  obtain ⟨n, rfl⟩ : ∃ n, d = 𝟙^n := ⟨d.length, List.eq_replicate_iff.mpr ⟨rfl, hd⟩⟩
  have hcod : codim u = 1 := by
    change degree c - degree (zObj (𝟙^n)) = 1
    rw [hdeg, (degree_eq_zero_iff (zObj (𝟙^n))).mpr fun x hx => List.eq_of_mem_replicate hx,
      Nat.sub_zero]
  obtain ⟨k, rfl⟩ := exists_atomComp u hcod
  rw [eq_atomOnes hu, eq_atomOnes hv]

/-- **…and so it names one run of the wedge** — the degree-one twin of `wedgeRun_eq_of_W`. -/
theorem wedgeRun_eq_of_not_W {e : Ch K} (he : degree e = 1) {X Y : Run K}
    {f : X.chain ⟶ e} {g : Y.chain ⟶ e} (hf : ¬ W K f) (hg : ¬ W K g) :
    wedgeRun f = wedgeRun g := by
  obtain ⟨⟨Xd, Xm⟩, Xp⟩ := X
  obtain ⟨⟨Yd, Ym⟩, Yp⟩ := Y
  obtain rfl : Xd = Yd :=
    ones_eq_of_dimSum_eq Xp Yp ((dimSum_eq_of_hom f).trans (dimSum_eq_of_hom g).symm)
  have hbase : zHom (Hom.φ f) = zHom (Hom.φ g) :=
    eq_of_not_W_deg_one Xp (c := zObj e.dims) he
      (fun h => hf ((W_zHom_iff f).mp h)) (fun h => hg ((W_zHom_iff g).mp h))
  exact Run.ext (congrArg (fun φ => (⟨Xd, φ⟩ : Ch (⋁e.dims))) (congrArg ChainCat.Hom.φ hbase))

/-- **At degree one a crossing refinement out of a given run is unique** — `eq_of_not_W_deg_one` at
the base, and a chain map is its wedge map. -/
theorem hom_eq_of_not_W_deg_one {e : Ch K} (he : degree e = 1) {X : Run K} {f g : X.chain ⟶ e}
    (hf : ¬ W K f) (hg : ¬ W K g) : f = g := by
  have h0 : zHom f.φ = zHom g.φ :=
    eq_of_not_W_deg_one X.ones (c := zObj e.dims) he
      (fun h => hf ((W_zHom_iff f).mp h)) (fun h => hg ((W_zHom_iff g).mp h))
  exact hom_ext' (((zHom_φ f.φ).symm.trans (congrArg ChainCat.Hom.φ h0)).trans (zHom_φ g.φ))

/-- **At degree one the greatest refinement is the only crossing one.**  So a degree-one object
carries a 1-cell with nothing beside it: the merge names one end, the complement the other. -/
theorem topOf_fst_eq_of_not_W {e : Ch K} (he : degree e = 1) {X : Run K} {f : X.chain ⟶ e}
    (hf : ¬ W K f) : (topOf e).1 = X :=
  ((isTop_iff_wedgeRun f).mpr
    ((wedgeRun_eq_of_not_W he hf (not_W_topOf e (by rw [he]; exact one_ne_zero))).trans
      (wedgeRun_topOf e))).fst_eq

end Paper

end ChainCat
