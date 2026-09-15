import CubeChains.Concurrency.Presentation.RunAtoms

/-!
# Concurrency/Presentation/TopRefinement — the two runs a chain spans

A run over a chain's shape names a run over the chain (`shapeRun`).  The shape's merge names the
run below it and the shape's longest run the run at its top:

    (bottomRun e).chain ──bottomHom──▸ e ◂──topHom── (topRun e).chain

Both are functions of the shape alone, so a map of `K` carries them on the nose. -/

open CategoryTheory Opposite BPSet CubeChains Equiv

namespace ChainCat

variable {K : BPSet}

namespace Paper

/-! ## The runs over a chain

A run over a chain's shape, composed with the chain's classifying map, is a run over the chain.
The shape is all it sees, so a climb is the same term over every `K`. -/

/-- The wedge map a refinement of shapes carries. -/
abbrev zPhi {p q : List ℕ+} (r : zObj p ⟶ zObj q) : ⋁p ⟶ ⋁q := Hom.φ r

/-- The run over a chain a run over its shape names. -/
def shapeRun (e : Ch K) {N : ℕ} (σ : zObj (𝟙^N) ⟶ zObj e.dims) : Run K :=
  ⟨⟨𝟙^N, zPhi σ ≫ e.map⟩, fun _ hd => List.eq_of_mem_replicate hd⟩

/-- …with the refinement it makes. -/
def shapeHom (e : Ch K) {N : ℕ} (σ : zObj (𝟙^N) ⟶ zObj e.dims) : (shapeRun e σ).chain ⟶ e :=
  ⟨zPhi σ, rfl⟩

/-- **The run a chain is merged into from.** -/
noncomputable def bottomRun (a : Ch K) : Run K := shapeRun a (runMerge (zObj a.dims) rfl)

/-- **The merge a chain is entered by** from the run below it. -/
noncomputable def bottomHom (a : Ch K) : (bottomRun a).chain ⟶ a := shapeHom a _

/-- **The run at the top of a chain**: its shape's longest run. -/
noncomputable def topRun (a : Ch K) : Run K := shapeRun a (shapeTop (zObj a.dims) rfl)

/-- **The refinement a chain's top run makes.** -/
noncomputable def topHom (a : Ch K) : (topRun a).chain ⟶ a := shapeHom a _

/-- The run below a chain, at any count of its events. -/
theorem bottomRun_eq_shapeRun (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N) :
    bottomRun e = shapeRun e (runMerge _ hN) := by
  subst hN; rfl

/-- The run at the top of a chain, at any count of its events. -/
theorem topRun_eq_shapeRun (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N) :
    topRun e = shapeRun e (shapeTop _ hN) := by
  subst hN; rfl

theorem W_bottomHom (a : Ch K) : W K (bottomHom a) :=
  (W_iff_of_φ (f := bottomHom a) (f' := runMerge (zObj a.dims) rfl) rfl).mpr (W_runMerge _ _)

/-! ## A refinement carries the runs along

A run over the source, composed with the refinement's shape, is a run over the target — the same
run.  Merges out of the run being unique, a merge does not move the run below. -/

/-- **A run over a refinement's source is the run over its target it composes to.** -/
theorem shapeRun_comp {c d : Ch K} (u : c ⟶ d) {N : ℕ} (σ : zObj (𝟙^N) ⟶ zObj c.dims) :
    shapeRun d (σ ≫ baseMap u) = shapeRun c σ :=
  Run.ext (congrArg (fun m => (⟨𝟙^N, m⟩ : Ch K))
    ((Category.assoc (zPhi σ) (zPhi (baseMap u)) d.map).trans (congrArg (zPhi σ ≫ ·) u.w)))

/-- **A merge does not change the run below** — the source's merge, composed, is the target's. -/
theorem bottomRun_eq_of_W {c d : Ch K} (u : c ⟶ d) (hu : W K u) : bottomRun d = bottomRun c :=
  (bottomRun_eq_shapeRun d (dimSum_eq_of_hom u).symm).trans ((congrArg (shapeRun d)
    (eq_runMerge _ ((W Zbp).comp_mem _ _ (W_runMerge _ _)
      ((W_iff_of_φ (f := baseMap u) (f' := u) rfl).mpr hu)))).symm.trans (shapeRun_comp u _))

/-- **A run is the run below itself** — out of the run into itself the merge is the identity. -/
theorem bottomRun_self (X : Run K) : bottomRun X.chain = X := by
  obtain ⟨⟨d, m⟩, hd⟩ := X
  obtain ⟨n, rfl⟩ : ∃ n, d = 𝟙^n := ⟨d.length, List.eq_replicate_iff.mpr ⟨rfl, hd⟩⟩
  refine (bottomRun_eq_shapeRun _ (dimSum_replicate n)).trans (Run.ext ?_)
  rw [← eq_runMerge _ (MorphismProperty.id_mem _ (zObj (𝟙^n)))]
  exact congrArg (fun m' => (⟨𝟙^n, m'⟩ : Ch K)) (Category.id_comp m)

end Paper

end ChainCat
