import CubeChains.Concurrency.Presentation.SlicePresentation

/-!
# Concurrency/Presentation/SliceFunctor — the slice polygraph, functorial in the base

`presentsChainsGlue` wants a functor `Ch Zbp ⥤ Polygraph` whose `d`-th value presents the
localized slice over `d`.  Indexing its 0-cells by the **slice itself** — the runs over `d`, with
`P.map f := Over.map f` — makes both functor laws `rfl`: composition in `Ch Zbp` is strictly
associative and unital, and a 1-cell carries no data at all.  It is the *property* of being one
crossing apart, and postcomposing a witnessing square with `f` is the whole of `P.map` on 1-cells.

The labels are then the identity, so `SliceLabels.map_ob` — the equality the overlaps need — is
`rfl`.

Two namespace traps, each a build: inside `namespace ChainCat` bare `Hom` is `ChainCat.Hom` (the
`Ch K` morphisms), so `Polygraph.Hom` must be spelled; and bare `Functor.ext` is core Lean's
`Functor` typeclass, failing with a `LawfulFunctor` unification error, so
`CategoryTheory.Functor.ext` must be spelled.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph

namespace ChainCat

/-- The runs over a chain: the 0-cells of the slice polygraph. -/
def RunOver (d : Ch Zbp) : Type := {u : Over d // IsRun Zbp u.left}

/-- Postcomposition; it does not touch the source, so the run condition survives untouched. -/
def RunOver.push {d' d : Ch Zbp} (f : d' ⟶ d) (u : RunOver d') : RunOver d :=
  ⟨(Over.map f).obj u.1, u.2⟩

/-- **One crossing undone**: `a` and `b` agree after `a` crosses a single pair and `b` merges.
A *property*, not data — the position is already pinned by the two 0-cells, and carrying it would
be what stops `runPolyFunctor`'s laws from being `rfl`. -/
def RunStep {d : Ch Zbp} (a b : RunOver d) : Prop :=
  ∃ (e : Ch Zbp) (t : a.1.left ⟶ e) (m : b.1.left ⟶ e) (z : e ⟶ d),
    permLen (crossPerm rfl t) = 1 ∧ W Zbp m ∧ t ≫ z = a.1.hom ∧ m ≫ z = b.1.hom

/-- **The step survives postcomposition** — the same square, read further down.  This is the whole
of `P.map` on 1-cells; no crossing permutation is touched. -/
theorem RunStep.push {d' d : Ch Zbp} (f : d' ⟶ d) {a b : RunOver d'} (h : RunStep a b) :
    RunStep (RunOver.push f a) (RunOver.push f b) := by
  obtain ⟨e, t, m, z, ht, hm, ha, hb⟩ := h
  exact ⟨e, t, m, z ≫ f, ht, hm,
    (Category.assoc t z f).symm.trans (congrArg (fun w => w ≫ f) ha),
    (Category.assoc m z f).symm.trans (congrArg (fun w => w ≫ f) hb)⟩

/-- The slice polygraph: 0-cells the runs over `d`, 1-cells the single crossings, and every
parallel pair related — the localized slice is a poset, so there is no word problem. -/
def runPoly (d : Ch Zbp) : Polygraph :=
  Polygraph.thin fun a b : RunOver d => PLift (RunStep a b)

def runPre {d' d : Ch Zbp} (f : d' ⟶ d) :
    GenObj (runPoly d').Gen ⥤q GenObj (runPoly d).Gen where
  obj a := ⟨RunOver.push f a.as⟩
  map e := ⟨e.down.push f⟩

def runMap {d' d : Ch Zbp} (f : d' ⟶ d) : Polygraph.Hom (runPoly d') (runPoly d) :=
  Polygraph.thinMap (runPre f)

/-- **The slice polygraph is functorial in the base.**  `Over.map` is strictly functorial on
`Ch Zbp` — composition there is associative and unital on the nose — and a 1-cell carries no data,
so both laws are `rfl` on the 1-cells, hence `thin_hom_ext`. -/
def runPolyFunctor : Ch Zbp ⥤ Polygraph where
  obj := runPoly
  map := runMap
  map_id _ := Polygraph.thin_hom_ext rfl
  map_comp _ _ := Polygraph.thin_hom_ext rfl

/-! ## Compatibility with the base

`hP` is an *equality* of functors, which is what walled the product indexing.  Here it costs
nothing: the localized slice is a poset, so the equality is one of objects, and on objects
`overMapLoc` is `Over.map` (`overMapLoc_obj`) — exactly what the 0-cells already are. -/

/-- **The 0-cells name their own slice objects**, so labelling is the identity and `map_ob` is
`rfl` — the equality the span identification needs, with nothing to transport. -/
def runLabels : SliceLabels runPolyFunctor where
  ob _ a := a.1
  map_ob _ _ := rfl

/-- **The slice presentations are compatible with the base**, for any family naming its 0-cells by
the slice objects they are — no hypothesis on the family beyond `hL`. -/
theorem runPoly_hP
    (p : ∀ d : Ch Zbp, Presents (runPoly d) (((W Zbp).over (X := d)).Localization))
    (hL : ∀ (d : Ch Zbp) (a : RunOver d),
      (p d).at' ⟨a⟩ = Localization.Construction.objEquiv ((W Zbp).over (X := d)) a.1)
    {d' d : Ch Zbp} (f : d' ⟶ d) :
    (runPolyFunctor.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc (W Zbp) f := by
  fapply CategoryTheory.Functor.ext
  · rintro ⟨⟨a⟩⟩
    change (p d).at' ⟨RunOver.push f a⟩ = (overMapLoc (W Zbp) f).obj ((p d').at' ⟨a⟩)
    rw [hL d _, hL d' _, overMapLoc_obj]
    rfl
  · intro _ _ _
    exact Subsingleton.elim _ _

end ChainCat
