import CubeChains.Concurrency.Presentation.GermWeakOrder
import CubeChains.Concurrency.Presentation.SliceRunSet
import CubeChains.Concurrency.Merge.CubeWeakEquiv
import CubeChains.Machinery.Presentation.Coproduct
import CubeChains.Machinery.Presentation.Opposite

/-!
# Concurrency/Presentation/SliceGerm — the slice polygraph is a down-set

The runs over `d` are down-closed in the right weak order (`runSet_down`), so they *are* a
`WeakDownset`, and the germ presentation applies to them with no absorbing point and no `Option`:
`slicePoly p d` is one germ per strand count, and `slicePresents p d` presents the localized slice
over `d` read backwards.

Two things the strand count decides.  The down-set lives at one count, so the polygraph is a
**coproduct** over the counts, and a merge is the coproduct of the down-sets' pushes — which is what
keeps the family *strictly* functorial in `d`, `slicePush_id` and `slicePush_comp` being
`Sigma.hom_ext` and nothing else.  And every count but `d`'s own is empty, which is why the
coproduct of the down-sets' orders is the single localized slice (`sliceLocEquiv`).

A merge left-translates a germ step (`germStep_push`), so it is a map of down-sets, and
`Polygraph.comapOver` carries it: the 2-cells are `p`'s own and do not move, only the words above
them.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv Polygraph

namespace ChainCat

variable {d' d : Ch Zbp} {N : ℕ}

/-! ## The runs over a chain, as a down-set -/

/-- **The runs over `d` on `N` events, as a down-set** — named by their crossing permutations,
which is injective, and down-closed by the exchange. -/
noncomputable def runDownset (d : Ch Zbp) (N : ℕ) : WeakDownset N where
  carrier := RunAt d N
  perm := RunAt.perm
  perm_injective := RunAt.perm_injective
  mem_of_le := fun {u _} h => runSet_down ⟨u, rfl⟩ h

/-! ### …and where it sits in the whole weak order

Every shape on `N` events is coarsened by the one-bead shape `[N]` (`exists_W_to_top`), whose runs
are *all* of `Perm (Fin N)`; the runs over any shape are a down-set there (`runSet_down`).  So
the runs of every shape sit in one weak order, and along a **merge** the map between them is
the inclusion of down-sets.

It is **only** along a merge.  A general refinement left-translates by its crossing
(`RunAt.push_perm`), so the family is a diagram of translations, not of inclusions — which is why
`slicePushFibre` below is `comapOver`, carried by `germProj` being *constant* on 0-cells, and not a
restriction map. -/

/-- **The one-bead shape's runs are every permutation** — its down-set is the whole weak order. -/
theorem runSet_topDims (N : ℕ) (σ : Perm (Fin N)) : RunSet (zObj (topDims N)) N σ :=
  ⟨⟨⟨Over.mk ((onesTopEquiv N).symm σ), fun _ hd => List.eq_of_mem_replicate hd⟩,
      dimSum_replicate N⟩,
    crossPerm_onesTopEquiv_symm N σ⟩

/-- **A merge includes one down-set in the next** — it crosses nothing, so moves no point. -/
theorem runSet_of_W {d' d : Ch Zbp} {f : d' ⟶ d} (hf : W Zbp f) {σ : Perm (Fin N)}
    (h : RunSet d' N σ) : RunSet d N σ := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨RunAt.push f u, by
    rw [RunAt.push_perm f u.strands u, crossPerm_eq_one_of_W u.strands hf, one_mul]⟩

/-! ## The localized slice is the down-set's order

A braid raises the weak order where an arrow of the localized slice lowers it, so the two are
opposite.  Nothing else separates them: both are thin, the runs are a skeleton of the slice
(`exists_runOver_iso`), and every rise is realised by the simple that names the gap. -/

instance isThin_sigma {ι : Type*} (C : ι → Type*) [∀ i, Category (C i)]
    [∀ i, Quiver.IsThin (C i)] : Quiver.IsThin (Σ i, C i) := by
  rintro ⟨i, x⟩ ⟨j, y⟩
  refine ⟨?_⟩
  rintro ⟨f⟩ ⟨g⟩
  exact congrArg (fun h => Sigma.SigmaHom.mk h) (Subsingleton.elim f g)

/-- A run over `d` names an object of the localized slice, backwards. -/
noncomputable def runLocFibre (d : Ch Zbp) (N : ℕ) :
    (runDownset d N).Order ⥤ (((W Zbp).over (X := d)).Localization)ᵒᵖ where
  obj u := op (((W Zbp).over (X := d)).Q.obj (u : RunAt d N).1.1)
  map {u v} h :=
    (nonempty_locOver_hom_of_le (u : RunAt d N).strands (v : RunAt d N).1 (u : RunAt d N).1
      (leOfHom h)).some.op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- **The localized slice over `d` is the runs over `d`, in the weak order, read backwards** — one
down-set per strand count, and every count but `d`'s own is empty. -/
noncomputable def sliceLocFunctor (d : Ch Zbp) :
    (Σ N : ℕ, (runDownset d N).Order) ⥤ (((W Zbp).over (X := d)).Localization)ᵒᵖ :=
  Sigma.desc (runLocFibre d)

instance sliceLocFunctor_faithful (d : Ch Zbp) : (sliceLocFunctor d).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance sliceLocFunctor_full (d : Ch Zbp) : (sliceLocFunctor d).Full where
  map_surjective {X Y} f := by
    obtain ⟨N, u⟩ := X
    obtain ⟨M, v⟩ := Y
    have hu : dimSum d.dims = N := RunAt.strands (u : RunAt d N)
    have hv : dimSum d.dims = M := RunAt.strands (v : RunAt d M)
    obtain rfl : M = N := hv.symm.trans hu
    exact ⟨Sigma.SigmaHom.mk (homOfLE (weakOver_le_of_loc_hom hu f.unop)),
      Subsingleton.elim _ _⟩

instance sliceLocFunctor_essSurj (d : Ch Zbp) : (sliceLocFunctor d).EssSurj where
  mem_essImage X := by
    obtain ⟨y, hy⟩ := Localization.Construction.exists_Q_obj ((W Zbp).over (X := d)) X.unop
    obtain ⟨a, ⟨i⟩⟩ := exists_runOver_iso (d := d) (N := dimSum d.dims) rfl y
    exact ⟨⟨dimSum d.dims, (⟨a, RunOver.left_dimSum rfl a⟩ : RunAt d (dimSum d.dims))⟩,
      ⟨(i ≪≫ eqToIso hy).op.symm ≪≫ eqToIso (Opposite.op_unop X)⟩⟩

instance sliceLocFunctor_isEquivalence (d : Ch Zbp) : (sliceLocFunctor d).IsEquivalence := { }

/-- **…as an equivalence.** -/
noncomputable def sliceLocEquiv (d : Ch Zbp) :
    (Σ N : ℕ, (runDownset d N).Order) ≌ (((W Zbp).over (X := d)).Localization)ᵒᵖ :=
  (sliceLocFunctor d).asEquivalence

namespace BraidPresentation

variable (p : BraidPresentation)

/-! ## The slice polygraph -/

/-- **The slice polygraph over `d`**: `p`'s germ on the runs over `d`, one down-set per count.
0-cells the runs, 1-cells the generators of `p` making a germ step between two of them, 2-cells the
relations of `p` holding there. -/
noncomputable def slicePoly (d : Ch Zbp) : Polygraph.{0, 0, 0} :=
  Polygraph.coprod fun N => p.germPoly (runDownset d N)

/-- **…presenting the localized slice over `d`, read backwards.**  No `Option`, no absorbing point,
and no choice: the runs are a down-set, which is exactly what the germ asks of its points. -/
noncomputable def slicePresents (d : Ch Zbp) :
    Presents (p.slicePoly d) ((((W Zbp).over (X := d)).Localization)ᵒᵖ) :=
  (Presents.coproduct fun N => p.dehornoy (runDownset d N)).transport (sliceLocEquiv d)

/-- The strand-`N` germ, included in the slice polygraph. -/
noncomputable def sliceIncl (d : Ch Zbp) (N : ℕ) : p.germPoly (runDownset d N) ⟶ p.slicePoly d :=
  Polygraph.coprodι (fun M => p.germPoly (runDownset d M)) N

/-- …on the generating quivers. -/
noncomputable def slicePre (d : Ch Zbp) (N : ℕ) :
    GenObj (p.GermGen (runDownset d N)) ⥤q GenObj (p.slicePoly d).Gen := (p.sliceIncl d N).pre

instance slicePre_faithful (d : Ch Zbp) (N : ℕ) : (p.slicePre d N).pathsFunctor.Faithful :=
  Polygraph.coprod_pathsFunctor_faithful (fun M => p.germPoly (runDownset d M)) N

theorem slicePre_full (d : Ch Zbp) (N : ℕ) : (p.slicePre d N).pathsFunctor.Full :=
  Polygraph.coprod_pathsFunctor_full (fun M => p.germPoly (runDownset d M)) N

/-! ## …functorially in `d`

A merge left-translates a germ step, so it is a map of down-sets over a fixed strand count, and
`comapOver` carries it with the 2-cells untouched. -/

/-- **A merge is a map of down-sets**: it left-translates every germ step. -/
def runGermPush (f : d' ⟶ d) (N : ℕ) :
    GenObj (p.GermGen (runDownset d' N)) ⥤q GenObj (p.GermGen (runDownset d N)) where
  obj x := ⟨RunAt.push f x.as⟩
  map e := ⟨e.1, germStep_push f e.2⟩

/-- …hence a map of the germs there. -/
noncomputable def slicePushFibre (f : d' ⟶ d) (N : ℕ) :
    p.germPoly (runDownset d' N) ⟶ p.germPoly (runDownset d N) :=
  Polygraph.comapOver (p.germProj (runDownset d N)) (p.runGermPush f N)

theorem slicePushFibre_id (d : Ch Zbp) (N : ℕ) :
    p.slicePushFibre (𝟙 d) N = 𝟙 (p.germPoly (runDownset d N)) :=
  Polygraph.Hom.ext' rfl fun _ => heq_of_eq (Polygraph.ComapRel.ext
    (Prefunctor.mapPath_id _) (Prefunctor.mapPath_id _) rfl)

theorem slicePushFibre_comp {d'' : Ch Zbp} (f : d'' ⟶ d') (g : d' ⟶ d) (N : ℕ) :
    p.slicePushFibre (f ≫ g) N = p.slicePushFibre f N ≫ p.slicePushFibre g N :=
  Polygraph.Hom.ext' rfl fun α => heq_of_eq (Polygraph.ComapRel.ext
    (Prefunctor.mapPath_comp_apply (p.runGermPush f N) (p.runGermPush g N) α.src)
    (Prefunctor.mapPath_comp_apply (p.runGermPush f N) (p.runGermPush g N) α.tgt) rfl)

/-- **Pushing a germ word leaves the braid word it spells alone** — a merge moves the runs, never
the generators. -/
theorem germWord_runGermPush (f : d' ⟶ d) (N : ℕ)
    {x y : GenObj (p.GermGen (runDownset d' N))} (w : Quiver.Path x y) :
    p.germWord (runDownset d N) ((p.runGermPush f N).mapPath w)
      = p.germWord (runDownset d' N) w := by
  induction w with
  | nil => rfl
  | cons w e ih =>
      change Quiver.Path.cons (p.germWord (runDownset d N) ((p.runGermPush f N).mapPath w)) _
        = Quiver.Path.cons (p.germWord (runDownset d' N) w) _
      rw [ih]
      rfl

/-- **A merge, on the whole slice polygraph** — one down-set at a time. -/
noncomputable def slicePush (f : d' ⟶ d) : p.slicePoly d' ⟶ p.slicePoly d :=
  Polygraph.coprodDescHom _ fun N => p.slicePushFibre f N ≫ p.sliceIncl d N

@[simp] theorem sliceIncl_push (f : d' ⟶ d) (N : ℕ) :
    p.sliceIncl d' N ≫ p.slicePush f = p.slicePushFibre f N ≫ p.sliceIncl d N :=
  Polygraph.coprodι_comp_descHom _ _ N

theorem slicePush_id (d : Ch Zbp) : p.slicePush (𝟙 d) = 𝟙 (p.slicePoly d) :=
  Polygraph.coprod_hom_ext _ fun N => by
    change p.sliceIncl d N ≫ p.slicePush (𝟙 d) = p.sliceIncl d N ≫ 𝟙 (p.slicePoly d)
    rw [p.sliceIncl_push, p.slicePushFibre_id d N, Category.id_comp, Category.comp_id]

theorem slicePush_comp {d'' : Ch Zbp} (f : d'' ⟶ d') (g : d' ⟶ d) :
    p.slicePush (f ≫ g) = p.slicePush f ≫ p.slicePush g :=
  Polygraph.coprod_hom_ext _ fun N => by
    change p.sliceIncl d'' N ≫ p.slicePush (f ≫ g)
      = p.sliceIncl d'' N ≫ p.slicePush f ≫ p.slicePush g
    rw [← Category.assoc, p.sliceIncl_push f N, p.sliceIncl_push, p.slicePushFibre_comp f g N,
      Category.assoc, ← p.sliceIncl_push g N, Category.assoc]

/-- **The slice polygraph, functorially in `d`** — the strand count is data in a 0-cell, so a
merge moves nothing but the run. -/
noncomputable def sliceRawFunctor : Ch Zbp ⥤ Polygraph.{0, 0, 0} where
  obj := p.slicePoly
  map f := p.slicePush f
  map_id := p.slicePush_id
  map_comp := p.slicePush_comp

/-- **The slice family**, in the orientation the colimit route consumes: a braid *raises* the weak
order where an arrow of the localized slice lowers it. -/
noncomputable def fam : Ch Zbp ⥤ Polygraph.{0, 0, 0} := p.sliceRawFunctor ⋙ Polygraph.opFunctor

/-- **The slice presentation, in that orientation.** -/
noncomputable def slicePresentation (d : Ch Zbp) :
    Presents (p.fam.obj d) (((W Zbp).over (X := d)).Localization) :=
  ((p.slicePresents d).op).transport (opOpEquivalence _)

/-- **`Ch(□n)[W⁻¹]` presented by `p`'s germ**, with no `Option` anywhere in the construction — the
one-bead shape, where every permutation is a run. -/
noncomputable def germPresentsCube (n : ℕ) :
    Presents (p.germPoly (WeakDownset.top n)).op ((W (□n)).Localization) :=
  (p.dehornoyTop n).op.transport (locCubeWeakOrder n).symm

end BraidPresentation

end ChainCat
