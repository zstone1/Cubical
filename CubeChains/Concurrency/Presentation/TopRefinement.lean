import CubeChains.Concurrency.Presentation.RunAtoms

/-!
# Concurrency/Presentation/TopRefinement — the two runs a chain spans

A refinement out of a run is a run of the target's wedge, so a run-arrow into a chain's shape names
a run over the chain.  The shape's merge names the run below it and the shape's longest run the
run at its top:

    (bottomRun e).chain ──bottomHom──▸ e ◂──topHom── (topRun e).chain

Both are functions of the shape alone, so a map of `K` carries them on the nose. -/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat

variable {K : BPSet}

namespace Paper

/-! ## A refinement out of a run

A refinement of `e` out of a run *is* a run of `⋁e.dims` — the source's classifying map is forced to
`φ ≫ e.map` — so the two readings are inverse (`wedgeRun`, `ofWedgeRun`). -/

/-- A refinement out of a run, as a run of the target's wedge. -/
def wedgeRun {X : Run K} {e : Ch K} (f : X.chain ⟶ e) : Run (⋁e.dims) :=
  ⟨⟨X.dims, Hom.φ f⟩, X.ones⟩

/-- …and back: the run it refines `e` by, with the refinement. -/
def ofWedgeRun (e : Ch K) (r : Run (⋁e.dims)) : Σ X : Run K, X.chain ⟶ e :=
  ⟨⟨⟨r.dims, r.chain.map ≫ e.map⟩, r.ones⟩, ⟨r.chain.map, rfl⟩⟩

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

/-- **`W` is a condition on the wedge map** — so it is the same upstairs and at the base. -/
theorem W_zHom_iff {a b : Ch K} (f : a ⟶ b) : W Zbp (zHom (Hom.φ f)) ↔ W K f :=
  W_iff_of_φ rfl

/-- **Two merges out of runs name one run of the wedge** — the runs have the same events, and at
the base a merge is pinned by its endpoints. -/
theorem wedgeRun_eq_of_W {e : Ch K} {X Y : Run K} {f : X.chain ⟶ e} {g : Y.chain ⟶ e}
    (hf : W K f) (hg : W K g) : wedgeRun f = wedgeRun g := by
  obtain ⟨⟨Xd, Xm⟩, Xp⟩ := X
  obtain ⟨⟨Yd, Ym⟩, Yp⟩ := Y
  obtain rfl : Xd = Yd :=
    ones_eq_of_dimSum_eq Xp Yp ((dimSum_eq_of_hom f).trans (dimSum_eq_of_hom g).symm)
  exact Run.ext (congrArg (fun φ => (⟨Xd, φ⟩ : Ch (⋁e.dims)))
    (congrArg ChainCat.Hom.φ (eq_of_W ((W_zHom_iff f).mpr hf) ((W_zHom_iff g).mpr hg))))

/-! ## The run below a chain

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

/-- **A chain is entered by one merge out of a run** — any merge out of a run *is* the pair
below. -/
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

/-! ## The run at the top of a chain -/

/-- **The longest run over a chain, with its refinement**: the shape's longest run, read over the
chain. -/
noncomputable def topOf (a : Ch K) : Σ X : Run K, X.chain ⟶ a :=
  ofWedgeRun a ⟨⟨𝟙^(dimSum a.dims), Hom.φ (shapeTop (N := dimSum a.dims) (zObj a.dims) rfl).arr⟩,
    fun _ hd => List.eq_of_mem_replicate hd⟩

/-- **The run at the top of a chain.** -/
noncomputable def topRun (a : Ch K) : Run K := (topOf a).1

/-- **The refinement a chain's top run makes.** -/
noncomputable def topHom (a : Ch K) : (topRun a).chain ⟶ a := (topOf a).2

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

/-- **At degree one a crossing refinement out of a given run is unique** — `eq_of_not_W_deg_one` at
the base, and a chain map is its wedge map. -/
theorem hom_eq_of_not_W_deg_one {e : Ch K} (he : degree e = 1) {X : Run K} {f g : X.chain ⟶ e}
    (hf : ¬ W K f) (hg : ¬ W K g) : f = g := by
  have h0 : zHom f.φ = zHom g.φ :=
    eq_of_not_W_deg_one X.ones (c := zObj e.dims) he
      (fun h => hf ((W_zHom_iff f).mp h)) (fun h => hg ((W_zHom_iff g).mp h))
  exact hom_ext' (((zHom_φ f.φ).symm.trans (congrArg ChainCat.Hom.φ h0)).trans (zHom_φ g.φ))

end Paper

end ChainCat
