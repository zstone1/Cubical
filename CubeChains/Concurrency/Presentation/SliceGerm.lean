import CubeChains.Concurrency.Presentation.GermWeakOrder
import CubeChains.Concurrency.Presentation.SliceFibre
import CubeChains.Concurrency.Merge.CubeWeakEquiv
import CubeChains.Machinery.Presentation.Opposite

/-!
# Concurrency/Presentation/SliceGerm — the slice is the germ, cut to a down-set

The runs over `d` are **down-closed** in the right weak order (`weakDown_runSet`), and a down-set
of a poset is convex outright.  So `Presents.restrict` cuts `dehornoy` down to them with no
absorbing point and no `Option`: `sliceGermPresents` is the slice presentation, stated and proved
in germ vocabulary.

`locOverRuns` is what ties it to `Ch Zbp`: `weakOverLoc` is fully faithful, and its essential image
is exactly the runs' classes, so the localized slice *is* the down-set, read backwards.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv Polygraph

namespace ChainCat

variable {d : Ch Zbp} {N : ℕ}

/-! ## The runs, as a convex subcategory of the weak order -/

/-- The permutations `d`'s blocks allow, as a property of the weak order. -/
def RunProp (d : Ch Zbp) (N : ℕ) : ObjectProperty (WeakOrder N) :=
  fun x => RunSet d N (WeakOrder.perm x)

/-- **The runs over `d` are convex** — they are down-closed, and in a poset a factorisation
through `z` puts `z` below the upper end.  This is the convexity `Presents.restrict` asks for, with
no absorbing point anywhere. -/
theorem convex_runProp (d : Ch Zbp) (N : ℕ) : (RunProp d N).Convex :=
  fun _ hb _ g => weakDown_runSet d N hb (WeakOrder.le_def.mp (leOfHom g))

/-- A run over `d` names a `RunProp`-object. -/
theorem runProp_of_runAt (u : RunAt d N) : RunProp d N (WeakOrder.of u.perm) := ⟨u, rfl⟩

/-! ## The slice polygraph, `Option`-free -/

variable (p : BraidPresentation)

/-- **The slice polygraph over `d`**: `p`'s germ, cut to the runs over `d`.  0-cells the runs,
1-cells the generators of `p` making a germ step between two of them, 2-cells the relations of `p`
holding there. -/
noncomputable def sliceGermPoly (d : Ch Zbp) (N : ℕ) : Polygraph.{0, 0, 0} :=
  (p.dehornoy N).restrictPoly (RunProp d N)

/-- **…presenting the runs over `d` in the weak order.** -/
noncomputable def sliceGermPresents (d : Ch Zbp) (N : ℕ) :
    Presents (sliceGermPoly p d N) (RunProp d N).FullSubcategory :=
  (p.dehornoy N).restrict (RunProp d N) (convex_runProp d N)

/-! ## …and the down-set is the localized slice

`weakOverLoc` is fully faithful; below, its essential image is pinned to the runs, so it
corestricts to an equivalence.  Every object of the slice is entered from a run by a merge
(`exists_runOver_iso`), and the localization inverts that merge, so the two have the same class. -/

/-- **The class of an object of the localized slice is a run's** — the merge from its own run is
in `W`. -/
theorem runProp_weakOver (hd : dimSum d.dims = N) (y : Over d) :
    RunProp d N (weakOver hd y) := by
  obtain ⟨a, ⟨i⟩⟩ := exists_runOver_iso hd y
  refine ⟨⟨a, RunOver.left_dimSum hd a⟩, ?_⟩
  have h : weakOver hd y = weakOver hd a.1 :=
    WeakOrder.eq_of_iso ((weakOverLoc hd).mapIso i).unop
  change WeakOrder.perm (weakOver hd a.1) = WeakOrder.perm (weakOver hd y)
  rw [h]

theorem runProp_leftOp (hd : dimSum d.dims = N)
    (X : (((W Zbp).over (X := d)).Localization)ᵒᵖ) :
    RunProp d N ((weakOverLoc hd).leftOp.obj X) := by
  obtain ⟨x⟩ := X
  obtain ⟨y, rfl⟩ := Localization.Construction.exists_Q_obj _ x
  exact runProp_weakOver hd y

/-- **The localized slice over `d` is the runs over `d`, in the weak order, read backwards.**  With
this, `sliceGermPresents` presents the localized slice and no `Option` is spent anywhere. -/
noncomputable def locOverRuns (hd : dimSum d.dims = N) :
    (((W Zbp).over (X := d)).Localization)ᵒᵖ ≌ (RunProp d N).FullSubcategory :=
  haveI hff := (Functor.FullyFaithful.ofFullyFaithful (weakOverLoc hd)).leftOp
  haveI : (weakOverLoc hd).leftOp.Full := hff.full
  haveI : (weakOverLoc hd).leftOp.Faithful := hff.faithful
  haveI : ((RunProp d N).lift (weakOverLoc hd).leftOp (runProp_leftOp hd)).EssSurj :=
    { mem_essImage := fun Z => by
        obtain ⟨o, ho⟩ := Z
        obtain ⟨u, hu⟩ := ho
        obtain rfl : WeakOrder.of u.perm = o := by rw [hu, WeakOrder.of_perm]
        exact ⟨op (((W Zbp).over (X := d)).Q.obj u.1.1), ⟨eqToIso rfl⟩⟩ }
  haveI : ((RunProp d N).lift (weakOverLoc hd).leftOp (runProp_leftOp hd)).IsEquivalence := { }
  ((RunProp d N).lift (weakOverLoc hd).leftOp (runProp_leftOp hd)).asEquivalence

/-- **The slice presentation, `Option`-free**: `p`'s germ cut to the runs over `d` presents the
localized slice over `d`. -/
noncomputable def sliceGermPresentsLoc (hd : dimSum d.dims = N) :
    Presents (sliceGermPoly p d N) ((((W Zbp).over (X := d)).Localization)ᵒᵖ) :=
  (sliceGermPresents p d N).transport (locOverRuns hd).symm

/-- **`Ch(□n)[W⁻¹]` presented by `p`'s germ**, with no `Option` anywhere in the construction — the
one-bead shape, where every permutation is a run. -/
noncomputable def germPresentsCube (n : ℕ) :
    Presents (p.germPoly n).op ((W (□n)).Localization) :=
  (p.dehornoy n).op.transport (locCubeWeakOrder n).symm

end ChainCat
