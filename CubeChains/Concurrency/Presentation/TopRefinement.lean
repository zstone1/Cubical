import CubeChains.Concurrency.Presentation.SliceRuns
import CubeChains.Concurrency.Executions.Complement

/-!
# Concurrency/Presentation/TopRefinement — the two runs a chain spans

A chain is entered by one merge out of a run (`bottomRun`, `bottomHom`); its greatest refinement is
that merge run backwards inside every bead — the **complement** (`Run.compl`):

    (bottomRun e).chain ──bottomHom──▸ e ◂──topOf.2── (topOf e).1.chain

`topOf` is a function of `e` alone, and a run and its complement split the shape's capacity, so a
crossing length recognises the greatest refinement (`isTop_iff_permLen`). -/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat

variable {K : BPSet}

namespace Paper

/-! ## A refinement out of a run

A refinement of `e` out of a run *is* a run of `⋁e.dims` — the source's classifying map is forced to
`φ ≫ e.map` — so the two readings are inverse (`wedgeRun`, `ofWedgeRun`).  Both runs a chain spans
are read off this bijection: the merge below it, and that merge run backwards inside every bead
(`Run.compl`). -/

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

/-- **A refinement out of a run crosses what its run of the target's wedge does** — both read the
same wedge map. -/
theorem cross_wedgeRun {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    (wedgeRun f).cross = runCross f := runCross_zHom f _

/-- **The capacity bounds a refinement out of a run** — it is one of the target's runs, and a run
inverts at most the pairs the target's beads hold. -/
theorem permLen_crossPerm_le_crossCap {X : Run K} {e : Ch K} (f : X.chain ⟶ e) {N : ℕ}
    (h : dimSum X.chain.dims = N) : permLen (crossPerm h f) ≤ crossCap e.dims :=
  (permLen_crossPerm (dimSum_eq_of_hom f) h f).trans_le
    ((congrArg permLen (cross_wedgeRun f)).symm.trans_le (permLen_cross_le_crossCap (wedgeRun f)))

/-- **A crossing refinement onto a degree-one chain crosses exactly one pair** — the target holds
one concurrent pair and no more, and a refinement that crosses none is a merge. -/
theorem permLen_crossPerm_eq_one {X : Run K} {e : Ch K} (f : X.chain ⟶ e) (he : degree e = 1)
    (hf : ¬ W K f) {N : ℕ} (h : dimSum X.chain.dims = N) : permLen (crossPerm h f) = 1 := by
  have hle := (permLen_crossPerm_le_crossCap f h).trans_eq (crossCap_eq_one_of_degree he)
  have hne : permLen (crossPerm h f) ≠ 0 := fun h0 =>
    hf ((W_iff_crossPerm_eq_one h f).mpr (eq_one_of_permLen_eq_zero _ h0))
  omega

/-- **Two refinements out of runs that cross alike name one run of the wedge** — a chain map is its
wedge map, and the crossing pins that. -/
theorem wedgeRun_eq_of_runCross_eq {e : Ch K} {X Y : Run K} {f : X.chain ⟶ e} {g : Y.chain ⟶ e}
    (h : runCross f = runCross g) : wedgeRun f = wedgeRun g :=
  Run.cross_injective ((cross_wedgeRun f).trans (h.trans (cross_wedgeRun g).symm))

/-- **A chain is entered by one merge out of a run** — merges cross nothing, and a refinement out of
a run is pinned by what it crosses. -/
theorem wedgeRun_eq_of_W {e : Ch K} {X Y : Run K} {f : X.chain ⟶ e} {g : Y.chain ⟶ e}
    (hf : W K f) (hg : W K g) : wedgeRun f = wedgeRun g :=
  wedgeRun_eq_of_runCross_eq
    ((show runCross f = 1 from crossPerm_eq_one_of_W _ hf).trans
      (show runCross g = 1 from crossPerm_eq_one_of_W _ hg).symm)

/-! ## The least refinement out of a run

The run on a chain's own events merges onto it in exactly one way downstairs
(`existsUnique_W_ones`), and `W` sees only the wedge map (`W_iff_of_φ`), so the merge and its
source are functions of the chain over every `K`.  Uniqueness is `bottomOf_eq_of_W`, and the three
readings below are its `Sigma.fst` at the identity, at a composite, and as it stands. -/

/-- **The run a chain is entered from, with its merge**: the run on the chain's own events, mapped
in by the base merge out of it. -/
noncomputable def bottomOf (a : Ch K) : Σ X : Run K, X.chain ⟶ a :=
  ofWedgeRun a ⟨⟨𝟙^(dimSum a.dims), Hom.φ (runMerge (N := dimSum a.dims) (zObj a.dims) rfl)⟩,
    fun _ hd => List.eq_of_mem_replicate hd⟩

/-- **The run a chain is merged into from.** -/
noncomputable def bottomRun (a : Ch K) : Run K := (bottomOf a).1

/-- **The merge a chain is entered by** from the run below it. -/
noncomputable def bottomHom (a : Ch K) : (bottomRun a).chain ⟶ a := (bottomOf a).2

theorem W_bottomHom (a : Ch K) : W K (bottomHom a) :=
  (W_iff_of_φ (f := bottomHom a) (f' := runMerge (N := dimSum a.dims) (zObj a.dims) rfl) rfl).mpr
    (W_runMerge _ _)

/-- **A chain is entered by one merge out of a run** — merges cross nothing, and a refinement out of
a run is pinned by what it crosses, so any merge out of a run *is* the pair below. -/
theorem bottomOf_eq_of_W {X : Run K} {a : Ch K} {m : X.chain ⟶ a} (hm : W K m) :
    bottomOf a = ⟨X, m⟩ :=
  (ofWedgeRun_wedgeRun (bottomHom a)).symm.trans
    ((congrArg (ofWedgeRun a) (wedgeRun_eq_of_W (W_bottomHom a) hm)).trans
      (ofWedgeRun_wedgeRun m))

/-- **A merge out of a run names the run below its target.** -/
theorem eq_bottomRun_of_W {X : Run K} {a : Ch K} (m : X.chain ⟶ a) (hm : W K m) :
    bottomRun a = X := congrArg Sigma.fst (bottomOf_eq_of_W hm)

/-- **A run is the run below itself.** -/
theorem bottomRun_self (X : Run K) : bottomRun X.chain = X :=
  eq_bottomRun_of_W (𝟙 X.chain) (MorphismProperty.id_mem _ _)

/-- **A merge does not change the run below.** -/
theorem bottomRun_eq_of_W {c d : Ch K} (u : c ⟶ d) (hu : W K u) : bottomRun d = bottomRun c :=
  eq_bottomRun_of_W (bottomHom c ≫ u) ((W K).comp_mem _ _ (W_bottomHom c) hu)

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

/-- **The run a greatest refinement comes out of** — `IsTop` names it. -/
theorem IsTop.fst_eq {X : Run K} {e : Ch K} {f : X.chain ⟶ e} (hf : IsTop f) : (topOf e).1 = X :=
  congrArg Sigma.fst hf.2

/-- **There is only one greatest refinement** out of a given run — both are `topOf`'s. -/
theorem IsTop.hom_eq {X : Run K} {e : Ch K} {f g : X.chain ⟶ e} (hf : IsTop f) (hg : IsTop g) :
    f = g :=
  eq_of_heq (Sigma.mk.inj_iff.mp (hf.2.symm.trans hg.2)).2

/-- **`W` is a condition on the wedge map** — so it is the same upstairs and at the base. -/
theorem W_zHom_iff {a b : Ch K} (f : a ⟶ b) : W Zbp (zHom (Hom.φ f)) ↔ W K f :=
  W_iff_of_φ rfl

/-! ## …and it is the longest run over the shape

The merge below a chain crosses nothing, so a run over the chain's shape and its complement split
the capacity (`permLen_cross_add_compl`): the complement attains it, and nothing else does. -/

/-- **The merge below a chain crosses nothing.** -/
theorem cross_wedgeRun_bottomHom (e : Ch K) : (wedgeRun (bottomHom e)).cross = 1 :=
  (cross_wedgeRun (bottomHom e)).trans (crossPerm_eq_one_of_W _ (W_bottomHom e))

/-- **The greatest refinement attains the capacity** — its run is the complement of one crossing
nothing, so it takes the whole of the shape's capacity. -/
theorem permLen_runCross_topOf (e : Ch K) :
    permLen (runCross (topOf e).2) = crossCap e.dims := by
  have hL := permLen_cross_add_compl e.dims (wedgeRun (bottomHom e))
  rw [cross_wedgeRun_bottomHom, permLen_one] at hL
  rw [← cross_wedgeRun, wedgeRun_topOf]
  omega

/-- **The greatest refinement is the only one that attains the capacity** — a run's complement takes
what the run leaves, so the capacity is reached exactly when the complement crosses nothing.  The
`mpr` direction is what lets a length recognise the greatest refinement across two targets, where
the runs themselves cannot be compared. -/
theorem isTop_iff_permLen {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    IsTop f ↔ permLen (runCross f) = crossCap e.dims :=
  ⟨fun hf =>
      (congrArg (fun t : Σ Y : Run K, Y.chain ⟶ e => permLen (runCross t.2)) hf.2).symm.trans
        (permLen_runCross_topOf e),
   fun hf => (isTop_iff_wedgeRun f).mpr
    (eq_compl_of_permLen (cross_wedgeRun_bottomHom e)
      ((congrArg permLen (cross_wedgeRun f)).trans hf))⟩

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
