import CubeChains.Concurrency.Presentation.BeadRuns
import CubeChains.Concurrency.Presentation.GermProduct
import CubeChains.Concurrency.Presentation.SliceInherit

/-!
# Concurrency/Presentation/GarsidePresentation — `Ch(K)[W⁻¹]` from the Dehornoy germ

One derivation, six steps.  `Ch(K)[W⁻¹]` is the colimit of its localized slices (1); a slice is the
germ on the runs over its chain, uniformly in the chain (2); at one cube every permutation is a run,
so the slice is the Dehornoy germ of `Sₙ` (3); over a concatenation the runs are the block sums, so
the slice is the **categorical** product of the halves' (4) — not the tensor, which carries no merge
(`isEmpty_beadHom_pair_two`).  The family is then a functor whose slice comparison is an equality of
functors (5), so the colimit of the presentations presents the colimit (6).

Steps 3 and 4 are proved here; the rest is applied where it stands.
-/

open CategoryTheory Opposite BPSet CubeChains Polygraph Limits

namespace ChainCat

/-! ## 0. The Dehornoy germ

`germPoly` at the whole weak order: 0-cells the permutations, 1-cells the simples `s` with
`permLen x + permLen s = permLen (x * s)`, 2-cells `s·t ↦ s * t` where the lengths add, and `1 ↦ ε`.
The one polygraph whose cells are named here; everything below is a general construction applied to
it. -/

/-- The Garside germ of the braid monoid on `n` strands. -/
noncomputable def dehornoyPoly (n : ℕ) : Polygraph.{0, 0, 0} :=
  germBP.germPoly (WeakDownset.top n)

/-! ## 1. `Ch(K)[W⁻¹]` is the colimit of its localized slices

`presentsChainsColimit` (`Concurrency/Presentation/SlicePresentation`), applied unchanged: one copy
of the slice polygraph per element of `wedgeHoms K`, glued along the arrows of `Ch K`. -/

/-! ## 2. …and a localized slice is the germ on the runs over its chain

`germBP.slicePresentation` (`Concurrency/Presentation/SliceGerm`), applied unchanged: the runs over
a chain are down-closed in the right weak order, so they are a `WeakDownset` and the germ applies
there.  The arrow action left-translates a run by the crossing of the merge — one rule for every
arrow, with no bead index in it. -/

/-! ## 3. At one cube the slice is `dehornoyPoly n`

Every permutation of the axes is a run over a one-bead shape (`runSet_single`), so the run down-set
names the whole weak order and `germPolyCongr` identifies the two germs — an isomorphism of
polygraphs, with no localized category in it.  `Set.range (runDownset d N).perm` **is**
`{σ | RunSet d N σ}` definitionally, so a description of the runs is already one of a range. -/

/-- The strand count is 0-cell data, so the coproduct over counts is its one non-empty leg. -/
private noncomputable def sliceFibreIso {d : Ch Zbp} {N : ℕ} (h : dimSum d.dims = N) :
    germBP.germPoly (runDownset d N) ≅ germBP.slicePoly d :=
  Polygraph.coprodιIso (fun M => germBP.germPoly (runDownset d M)) N
    fun _ hM => ⟨fun u => hM ((RunAt.strands u).symm.trans h)⟩

private theorem range_runDownset_single (n : ℕ+) :
    Set.range (runDownset (zObj [n]) (n : ℕ)).perm = Set.range (WeakDownset.top (n : ℕ)).perm :=
  Set.ext fun σ => ⟨fun _ => ⟨σ, rfl⟩, fun _ => runSet_single n σ⟩

/-- **The slice at one cube is the Dehornoy germ** — every permutation of the axes is a run, a
one-bead shape being the coarsest chain on its events. -/
noncomputable def sliceCube (n : ℕ+) : germBP.slicePoly (zObj [n]) ≅ dehornoyPoly (n : ℕ) :=
  (sliceFibreIso (d := zObj [n]) (dimSum_single n)).symm ≪≫
    germBP.germPolyCongr (range_runDownset_single n)

/-! ## 4. Over a concatenation the slice is the categorical product

`runSet_append` (`Concurrency/Presentation/BeadRuns`) makes the runs over a concatenation the block
sums of the runs over the halves, so the down-set is `WeakDownset.prod`; `germProdIso` makes its
germ the **categorical** product.  It is the product and not the tensor because the tensor of the
same two beads carries no merge at all (`isEmpty_beadHom_pair_two`). -/

private theorem range_runDownset_append (d d' : List ℕ+) :
    Set.range (runDownset (zObj (d ++ d')) (dimSum d + dimSum d')).perm
      = Set.range ((runDownset (zObj d) (dimSum d)).prod
          (runDownset (zObj d') (dimSum d'))).perm := by
  ext σ
  constructor
  · intro h
    obtain ⟨_, _, ⟨u, rfl⟩, ⟨v, rfl⟩, rfl⟩ := (runSet_append rfl rfl σ).mp h
    exact ⟨(u, v), rfl⟩
  · rintro ⟨⟨u, v⟩, rfl⟩
    exact (runSet_append rfl rfl _).mpr ⟨u.perm, v.perm, ⟨u, rfl⟩, ⟨v, rfl⟩, rfl⟩

/-- **The slice over a concatenation is the product of the slices** — the block-sum down-set is the
product down-set, and its germ is the categorical product. -/
noncomputable def sliceConcat (d d' : List ℕ+) :
    germBP.slicePoly (zObj (d ++ d'))
      ≅ germBP.slicePoly (zObj d) ⨯ germBP.slicePoly (zObj d') :=
  (sliceFibreIso (d := zObj (d ++ d')) (dimSum_append d d')).symm ≪≫
    germBP.germPolyCongr (range_runDownset_append d d') ≪≫
    GarsideGerm.germProdIso _ _ ≪≫
    Limits.prod.mapIso (sliceFibreIso (d := zObj d) (N := dimSum d) rfl)
      (sliceFibreIso (d := zObj d') (N := dimSum d') rfl)

/-! ## 5. The family is a functor, and the slice comparison is an equality

`germBP.fam` and `slicePoly_hP` (`Concurrency/Presentation/SliceInherit`), applied unchanged: a
0-cell names its own slice object and a merge moves it by `Over.map`, so the comparison is an
equality of functors, its morphism half being `locOver_isThin`. -/

/-! ## 6. The colimit of the slice presentations presents the colimit

`germBP.presentsBr` (`Concurrency/Presentation/SliceInherit`), which is 1 fed by 5. -/

/-- The Garside polygraph of `K`: one copy of the germ per chain, glued along the arrows. -/
noncomputable def garsidePoly (K : BPSet) : Polygraph.{0, 0, 0} := germBP.Br K

/-- **…and it presents `Ch(K)[W⁻¹]`**, with no hypothesis on `K`. -/
noncomputable def garsidePresents (K : BPSet) :
    Presents (garsidePoly K) ((W K).Localization) :=
  germBP.presentsBr K

end ChainCat
