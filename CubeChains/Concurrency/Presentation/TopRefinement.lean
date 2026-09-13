import CubeChains.Concurrency.Presentation.RunArrows
import CubeChains.Concurrency.Presentation.BeadOrder
import CubeChains.Concurrency.Executions.Complement

/-!
# Concurrency/Presentation/TopRefinement — the two runs a chain spans

A chain is entered by one merge out of a run (`bottomRun`, `bottomHom`) and refined by one greatest
refinement out of a run (`topOf`, the reversal inside every bead):

    (bottomRun e).chain ──bottomHom──▸ e ◂──topOf.2── (topOf e).1.chain

`topOf` is a function of `e` alone, so "this refinement is the greatest one" is an equation of pairs
(`IsTop`); the weak order is graded bead by bead, so it is also the numerical statement that the
refinement attains the crossing capacity (`isTop_iff_permLen`).
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
theorem isRun_vChain (U : (chContraction K).V) : IsRun K (vChain U.1) :=
  (eltRep_eq_self_iff_isRun U.1).mp U.2

/-- The run a 0-cell of the contraction names. -/
def runOfV (U : (chContraction K).V) : Run K := ⟨vChain U.1, isRun_vChain U⟩

/-- **A run is its own run** — its shape is all ones, and the merge out of that shape is the
identity. -/
theorem eltRep_chV (X : Run K) : eltRep (chV X.chain) = chV X.chain :=
  eltRep_eq_self (N := X.dims.length) (Obj.eq_of_dims (List.eq_replicate_of_mem X.ones))

/-- The 0-cell of the contraction a run names. -/
def vOfRun (X : Run K) : (chContraction K).V := ⟨chV X.chain, eltRep_chV X⟩

/-- **A 0-cell is the shape it sits over, carrying its map** — the only transport the `Ch K`↔`∫F`
comparison pays, and it is definitional in the fibre. -/
theorem chV_vChain (z : (chCutPoly K).V) : chV (vChain z) = z :=
  Sigma.ext (Obj.eq_of_dims rfl) HEq.rfl

/-- **The 0-cells are the runs** — the comparison in dimension zero. -/
def runEquiv (K : BPSet) : Run K ≃ (chContraction K).V where
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
`φ ≫ e.map` — and a run of a wedge crosses one permutation per bead (`blockSum`).  The greatest
refinement is the reversal in every bead (`blockTop`): `crossCap` bounds every crossing and the weak
order is graded bead by bead, so nothing else crosses that much. -/

/-- A refinement out of a run, as a run of the target's wedge. -/
def wedgeRun {X : Run K} {e : Ch K} (f : X.chain ⟶ e) : Run (⋁e.dims) :=
  ⟨⟨X.dims, Hom.φ f⟩, X.ones⟩

/-- …and back: the run it refines `e` by, with the refinement. -/
def ofWedgeRun (e : Ch K) (r : Run (⋁e.dims)) : Σ X : Run K, X.chain ⟶ e :=
  ⟨⟨⟨r.dims, r.chain.map ≫ e.map⟩, r.ones⟩, ⟨r.chain.map, rfl⟩⟩

@[simp] theorem wedgeRun_ofWedgeRun (e : Ch K) (r : Run (⋁e.dims)) :
    wedgeRun (ofWedgeRun e r).2 = r := rfl

/-- **A refinement out of a run recovers the run** — its source's classifying map is forced. -/
theorem ofWedgeRun_wedgeRun_fst {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    (ofWedgeRun e (wedgeRun f)).1 = X :=
  Run.ext (congrArg (fun m => (⟨X.dims, m⟩ : Ch K)) f.w)

/-- A run refining a chain has the chain's events as its beads. -/
theorem Run.dims_eq_of_hom {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    X.dims = 𝟙^(dimSum e.dims) :=
  List.eq_replicate_iff.mpr
    ⟨by rw [← dimSum_eq_length_of_ones X.ones]; exact dimSum_eq_of_hom f, X.ones⟩

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

/-- **The capacity bounds every refinement out of a run.** -/
theorem permLen_runCross_le {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    permLen (runCross f) ≤ crossCap e.dims := by
  have hd : dimSum X.dims = dimSum e.dims := dimSum_eq_of_hom f
  have hbound : permLen (crossPerm (a := zObj X.dims) hd (zHom (Hom.φ f))) ≤ crossCap e.dims :=
    permLen_crossPerm_le_crossCap e.dims (zHom (Hom.φ f)) rfl hd
  exact (congrArg permLen (runCross_zHom f hd).symm).trans_le hbound

/-- **A renaming is a merge** — `subst`, and the identity is one. -/
theorem W_eqToHom {a b : Ch K} (h : a = b) : W K (eqToHom h) := by
  subst h
  rw [eqToHom_refl]
  exact MorphismProperty.id_mem _ _

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
  obtain ⟨n, rfl⟩ : ∃ n, Xd = 𝟙^n := ⟨Xd.length, List.eq_replicate_iff.mpr ⟨rfl, Xp⟩⟩
  obtain ⟨m, rfl⟩ : ∃ m, Yd = 𝟙^m := ⟨Yd.length, List.eq_replicate_iff.mpr ⟨rfl, Yp⟩⟩
  obtain rfl : n = m := by
    have h1 := dimSum_eq_of_hom f
    have h2 := dimSum_eq_of_hom g
    rw [show dimSum (𝟙^n : List ℕ+) = n from dimSum_replicate n] at h1
    rw [show dimSum (𝟙^m : List ℕ+) = m from dimSum_replicate m] at h2
    omega
  have hd : dimSum (𝟙^n : List ℕ+) = dimSum e.dims := dimSum_eq_of_hom f
  have hbase : zHom (Hom.φ f) = zHom (Hom.φ g) :=
    hom_ext_of_crossPerm (h := hd)
      ((runCross_zHom f hd).trans (h.trans (runCross_zHom g hd).symm))
  exact Run.ext (congrArg (fun φ => (⟨𝟙^n, φ⟩ : Ch (⋁e.dims))) (congrArg ChainCat.Hom.φ hbase))

/-- The greatest run of a wedge: the reversal in every bead. -/
noncomputable def topWedgeRun (l : List ℕ+) : Run (⋁l) :=
  ⟨wedgeRunChain l (blockTop l), wedgeRunChain_ones l (blockTop l)⟩

/-- **The greatest refinement of a chain out of a run.** -/
noncomputable def topOf (e : Ch K) : Σ X : Run K, X.chain ⟶ e := ofWedgeRun e (topWedgeRun e.dims)

/-- **The run a chain's greatest refinement comes out of.**  The two runs a chain spans:
`bottomRun` crosses nothing, `topRun` crosses as much as the chain allows. -/
noncomputable abbrev topRun (e : Ch K) : Run K := (topOf e).1

/-- …and that refinement. -/
noncomputable abbrev topHom (e : Ch K) : (topRun e).chain ⟶ e := (topOf e).2

/-- **Codimension is degree, out of a run.** -/
theorem codim_topOf (e : Ch K) : codim (topOf e).2 = degree e := by
  change degree e - degree (topOf e).1.chain = degree e
  rw [(isRun_iff_degree_eq_zero _).mp (topOf e).1.property, Nat.sub_zero]

/-- **The greatest refinement crosses the greatest tuple.** -/
theorem runCross_topOf (e : Ch K) : runCross (topOf e).2 = blockSum e.dims (blockTop e.dims) :=
  (runCross_zHom (topOf e).2 (dimSum_eq_of_hom (topOf e).2)).symm.trans
    (crossPerm_wedgeRunChain e.dims (blockTop e.dims) _)

/-- …so it attains the capacity. -/
theorem permLen_runCross_topOf (e : Ch K) :
    permLen (runCross (topOf e).2) = crossCap e.dims :=
  (congrArg permLen (runCross_topOf e)).trans (permLen_blockSum_blockTop e.dims)

/-- **A refinement as long as the capacity crosses what the greatest one crosses** — the weak order
is graded, so the capacity is attained only at the reversals. -/
theorem runCross_eq_of_permLen {X : Run K} {e : Ch K} {f : X.chain ⟶ e}
    (hf : permLen (runCross f) = crossCap e.dims) : runCross f = runCross (topOf e).2 :=
  (eq_blockSum_blockTop_of_permLen e.dims (runSet_runCross f) hf).trans (runCross_topOf e).symm

/-- **…and so it comes out of the same run.** -/
theorem topOf_fst_eq_of_permLen {X : Run K} {e : Ch K} {f : X.chain ⟶ e}
    (hf : permLen (runCross f) = crossCap e.dims) : (topOf e).1 = X :=
  (congrArg (fun r => (ofWedgeRun e r).1)
      (wedgeRun_eq_of_runCross_eq (f := (topOf e).2) (g := f)
        (runCross_eq_of_permLen hf).symm)).trans (ofWedgeRun_wedgeRun_fst f)

/-- **A reversal to make** — a shape with a bead of more than one dimension has capacity. -/
theorem crossCap_ne_zero_of_degree_ne_zero {e : Ch K} (he : degree e ≠ 0) :
    crossCap e.dims ≠ 0 := fun h0 =>
  he ((degree_eq_zero_iff e).mpr (crossCap_eq_zero_iff.mp h0))

/-- **The greatest refinement crosses**, as soon as there is anything to cross: it attains the
capacity, and only an all-edges shape has none.  So the two factorisations a degree-two object reads
spell a relation, not `w = w`. -/
theorem not_W_topOf (e : Ch K) (he : degree e ≠ 0) : ¬ W K (topOf e).2 := fun hW =>
  crossCap_ne_zero_of_degree_ne_zero he
    ((permLen_runCross_topOf e).symm.trans
      ((congrArg permLen
        (crossPerm_eq_one_of_W (dimSum_eq_of_hom (topOf e).2) hW)).trans permLen_one))

/-! ## The greatest refinement, as a condition on a refinement

`topOf` is a function of the chain alone, so "this refinement is the greatest one" is an equation of
pairs.  The capacity bounds every refinement out of a run (`permLen_runCross_le`) and is attained
only at the reversals, so the equation is also the numerical statement that it is attained. -/

/-- **A refinement is its target's greatest one** — it comes out of a run, and the pair it makes is
`topOf`'s. -/
def IsTop {a e : Ch K} (f : a ⟶ e) : Prop := ∃ h : IsRun K a, topOf e = ⟨⟨a, h⟩, f⟩

/-- Two `(run, refinement)` pairs agree once their runs do and the refinements agree after the
renaming that identifies them. -/
private theorem top_eq {e : Ch K} (t : Σ X : Run K, X.chain ⟶ e) {X : Run K} (h : t.1 = X)
    {f : X.chain ⟶ e} (hf : t.2 = eqToHom (congrArg Run.chain h) ≫ f) : t = ⟨X, f⟩ := by
  obtain ⟨R, g⟩ := t
  subst h
  simpa using hf

/-- …and a crossing length read off a pair travels along such an equation. -/
private theorem permLen_of_top_eq {e : Ch K} (t : Σ X : Run K, X.chain ⟶ e)
    (ht : permLen (runCross t.2) = crossCap e.dims) {X : Run K} {f : X.chain ⟶ e}
    (hf : t = ⟨X, f⟩) : permLen (runCross f) = crossCap e.dims := by
  subst hf; exact ht

/-- **The greatest refinement is the one attaining the capacity** — `runCross_eq_of_permLen` plus
`hom_ext_of_crossPerm`, a refinement out of a run being its crossing permutation. -/
theorem isTop_iff_permLen {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    IsTop f ↔ permLen (runCross f) = crossCap e.dims := by
  refine ⟨fun hf => permLen_of_top_eq (topOf e) (permLen_runCross_topOf e) hf.2, fun hf => ?_⟩
  refine ⟨X.property, top_eq (topOf e) (topOf_fst_eq_of_permLen hf) ?_⟩
  exact hom_ext_of_crossPerm (h := dimSum_eq_of_hom (topOf e).2)
    ((runCross_eq_of_permLen hf).symm.trans (runCross_W_comp (W_eqToHom _) f).symm)

/-- …read without naming the run, which `IsTop` carries itself. -/
theorem IsTop.permLen_eq {a e : Ch K} {f : a ⟶ e} (hf : IsTop f) :
    permLen (crossPerm (dimSum_eq_of_hom f) f) = crossCap e.dims :=
  (isTop_iff_permLen (X := ⟨a, hf.1⟩) f).mp hf

/-- **There is only one greatest refinement** out of a given run. -/
theorem IsTop.hom_eq {X : Run K} {e : Ch K} {f g : X.chain ⟶ e} (hf : IsTop f) (hg : IsTop g) :
    f = g :=
  hom_ext_of_crossPerm (h := dimSum_eq_of_hom f)
    ((runCross_eq_of_permLen hf.permLen_eq).trans (runCross_eq_of_permLen hg.permLen_eq).symm)

/-- **`W` is a condition on the wedge map** — so it is the same upstairs and at the base. -/
theorem W_zHom_iff {a b : Ch K} (f : a ⟶ b) : W Zbp (zHom (Hom.φ f)) ↔ W K f :=
  (W_iff_monotone_coordMap _).trans (W_iff_monotone_coordMap f).symm

/-- **…and so is being the greatest refinement**, the crossing permutation being read there. -/
theorem isTop_zHom {a e : Ch K} {f : a ⟶ e} (hf : IsTop f) : IsTop (zHom (Hom.φ f)) :=
  (isTop_iff_permLen (X := ⟨zObj a.dims, hf.1⟩) _).mpr
    ((congrArg permLen (runCross_zHom (X := ⟨a, hf.1⟩) f (dimSum_eq_of_hom f))).trans
      hf.permLen_eq)

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
  obtain ⟨n, rfl⟩ : ∃ n, Xd = 𝟙^n := ⟨Xd.length, List.eq_replicate_iff.mpr ⟨rfl, Xp⟩⟩
  obtain ⟨m, rfl⟩ : ∃ m, Yd = 𝟙^m := ⟨Yd.length, List.eq_replicate_iff.mpr ⟨rfl, Yp⟩⟩
  obtain rfl : n = m := by
    have h1 := dimSum_eq_of_hom f
    have h2 := dimSum_eq_of_hom g
    rw [show dimSum (𝟙^n : List ℕ+) = n from dimSum_replicate n] at h1
    rw [show dimSum (𝟙^m : List ℕ+) = m from dimSum_replicate m] at h2
    omega
  have hbase : zHom (Hom.φ f) = zHom (Hom.φ g) :=
    eq_of_not_W_deg_one (fun x hx => List.eq_of_mem_replicate hx) (c := zObj e.dims) he
      (fun h => hf ((W_zHom_iff f).mp h)) (fun h => hg ((W_zHom_iff g).mp h))
  exact Run.ext (congrArg (fun φ => (⟨𝟙^n, φ⟩ : Ch (⋁e.dims)))
    (congrArg ChainCat.Hom.φ hbase))

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
  (congrArg (fun r => (ofWedgeRun e r).1)
      (wedgeRun_eq_of_not_W he (not_W_topOf e (by rw [he]; exact one_ne_zero)) hf)).trans
    (ofWedgeRun_wedgeRun_fst f)

end Paper

end ChainCat
