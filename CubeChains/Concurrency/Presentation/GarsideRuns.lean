import CubeChains.Concurrency.Presentation.GarsidePresentation

/-!
# Concurrency/Presentation/GarsideRuns — what the wedge route names

The wedge route's 0-cells are tuples of bead permutations, and the object one of them names is the
beads' own runs, concatenated (`wedgeRunChain`).  Read in the slice that is a run over the chain,
whose crossing permutation is the block sum — so the wedge route and the germ-on-runs route name
the same slice object, which is what an equality of naming functors needs.
-/

open CategoryTheory CategoryTheory.MonoidalCategory Opposite BPSet CubeChains CubeChain Polygraph
  Limits

namespace ChainCat

/-! ## The chain a tuple of bead permutations names -/

/-- **The beads' own runs, concatenated** — the chain of `⋁l` a point of `topList l` names. -/
noncomputable def wedgeRunChain : (l : List ℕ+) → (topList l).carrier → Ch (⋁l)
  | [] => fun x => (runAt x).chain
  | n :: rest => fun x =>
      (chConcat (□(n : ℕ)) (⋁rest)).obj ((runAt x.1).chain, wedgeRunChain rest x.2)

/-- **The wedge splitting names the concatenated runs** — `locCubeWeakOrder` bead by bead and
`locChConsEquiv` at every junction, both of which compute on a `Q`-image. -/
theorem wedgeLocOrder_functor_obj : ∀ (l : List ℕ+) (x : (topList l).Order),
    (wedgeLocOrder l).functor.obj x = op ((W (⋁l)).Q.obj (wedgeRunChain l x))
  | [], _ => rfl
  | n :: rest, x =>
      congrArg (fun y : ((W (⋁rest)).Localization)ᵒᵖ =>
          (consLocOrder n rest).functor.obj
            (op ((W (□(n : ℕ))).Q.obj (runAt x.1).chain), y))
        (wedgeLocOrder_functor_obj rest x.2)

/-! ## …and the polygraph's 0-cells are the tuples

Every step of `garsideWedgePresents` is read *forwards* — `ofPolyIso_at'` at each isomorphism of
polygraphs — so no `Iso.inv` is unfolded and the naming reduces to `wedgeLocOrder`. -/

variable {n : ℕ} {a b : ℕ}

/-- A germ 0-cell names its own point. -/
theorem dehornoy_at (C : WeakDownset n) (x : C.carrier) :
    (germBP.dehornoy C).at' ⟨x⟩ = (x : C.Order) := rfl

/-- **A pair of points names the pair of orders** — the block-sum germ read as the product. -/
theorem dehornoyProd_at (C₁ : WeakDownset a) (C₂ : WeakDownset b) (x : (C₁.prod C₂).carrier) :
    (GarsideGerm.dehornoyProd C₁ C₂).at'
        ((GarsideGerm.germProdIso C₁ C₂).hom.pre.obj ⟨x⟩)
      = WeakDownset.prodBlocks (C₁ := C₁) (C₂ := C₂) x :=
  congrArg (WeakDownset.orderProd C₁ C₂).functor.obj
    (Presents.ofPolyIso_at' (germBP.dehornoy (C₁.prod C₂))
      (GarsideGerm.germProdIso C₁ C₂) ⟨x⟩)

/-- **The beads' germs, multiplied, name what the wedge splitting names.** -/
theorem garsideWedgePresents_at : ∀ (l : List ℕ+) (x : (topList l).carrier),
    (garsideWedgePresents l).at' ((garsideListIso l).hom.pre.obj ⟨x⟩)
      = (wedgeLocOrder l).functor.obj x
  | [], _ => rfl
  | n :: rest, x => by
      refine Eq.trans (congrArg
        ((((WeakDownset.orderTop (n : ℕ)).trans (cubeLocOrder (n : ℕ))).prod
          (wedgeLocOrder rest)).trans (consLocOrder n rest)).functor.obj
        ((Presents.ofPolyIso_at' _ (Limits.prod.mapIso (Iso.refl (dehornoyPoly (n : ℕ)))
          (garsideListIso rest)) _).trans (dehornoyProd_at _ _ x))) rfl

/-! ## The concatenated runs, read in the slice

A bead's run is a chain over its own cube; the junction glues them by `chConcat`, and `crossPerm`
is monoidal there.  The head bead's top chain is `[n]` only for `n` positive, which is the one
place `ℕ+` is destructured. -/

/-- The one-bead chain of a positive-dimensional cube. -/
def beadTop (n : ℕ+) : Ch (□(n : ℕ)) := ⟨[n], (serialWedge1 n).hom⟩

/-- A wedge's own shape, classified by the identity. -/
def wedgeTop (l : List ℕ+) : Ch (⋁l) := ⟨l, 𝟙 (⋁l)⟩

/-- Every chain of a cube refines its one bead. -/
def toBeadTop {n : ℕ+} (A : Ch (□(n : ℕ))) : A ⟶ beadTop n :=
  ⟨A.map ≫ (serialWedge1 n).inv, by
    change (A.map ≫ (serialWedge1 n).inv) ≫ (serialWedge1 n).hom = A.map
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩

/-- …and every chain of a wedge refines its shape. -/
def toWedgeTop {l : List ℕ+} (B : Ch (⋁l)) : B ⟶ wedgeTop l := ⟨B.map, Category.comp_id _⟩

/-- The one bead *is* the coarsest chain, so refining it is the crossing. -/
theorem crossPerm_toBeadTop {n : ℕ+} (A : Ch (□(n : ℕ))) (h : dimSum A.dims = (n : ℕ)) :
    crossPerm h (toBeadTop A) = cross A := by
  obtain ⟨_ | k, hn⟩ := n
  · exact absurd hn (by omega)
  · rfl

/-- **A bead and a tail concatenate to the identity** — the monoidal triangle, `⋁[]` being the
unit. -/
theorem concatChainMap_beadTop (n : ℕ+) (rest : List ℕ+) :
    concatChainMap (□(n : ℕ)) (⋁rest) (beadTop n) (wedgeTop rest) = 𝟙 (⋁(n :: rest)) := by
  have htri : (serialWedge1 n).hom ⊗ₘ 𝟙 (⋁rest) = (serialWedgeAppend [n] rest).hom :=
    (MonoidalCategory.tensorHom_id (serialWedge1 n).hom (⋁rest)).trans
      (MonoidalCategory.triangle (□(n : ℕ)) (⋁rest)).symm
  change (serialWedgeAppend [n] rest).inv ≫ ((serialWedge1 n).hom ⊗ₘ 𝟙 (⋁rest)) = 𝟙 _
  rw [htri]
  exact Iso.inv_hom_id _

/-- …so a concatenation's classifying map is its own refinement of the two tops. -/
theorem concatHomφ_toTop {n : ℕ+} {rest : List ℕ+} (A : Ch (□(n : ℕ))) (B : Ch (⋁rest)) :
    concatHomφ (toBeadTop A) (toWedgeTop B) = concatChainMap (□(n : ℕ)) (⋁rest) A B := by
  have h := concatHomφ_w (toBeadTop A) (toWedgeTop B)
  rw [concatChainMap_beadTop] at h
  exact (Category.comp_id _).symm.trans h

/-- **The crossing of a junction is the block sum** — `crossPerm_chConcat`, read on the classifying
map of the concatenation rather than on a refinement. -/
theorem crossPerm_zHom_concatChainMap {n : ℕ+} {rest : List ℕ+}
    (A : Ch (□(n : ℕ))) (B : Ch (⋁rest)) {p q : ℕ}
    (hA : dimSum A.dims = p) (hB : dimSum B.dims = q)
    (h : dimSum (A.dims ++ B.dims) = p + q) :
    crossPerm (a := zObj (A.dims ++ B.dims)) h
        (zHom (e := n :: rest) (concatChainMap (□(n : ℕ)) (⋁rest) A B))
      = permSum p q (crossPerm hA (toBeadTop A), crossPerm hB (toWedgeTop B)) := by
  subst hA
  subst hB
  refine Eq.trans ?_ (crossPerm_chConcat (ab := (A, B)) (ab' := (beadTop n, wedgeTop rest))
    (toBeadTop A, toWedgeTop B))
  exact crossPerm_eq_of_φ h (concatHomφ_toTop A B).symm

/-- **A tuple names an all-edges chain** — every bead of every bead's run is an edge. -/
theorem wedgeRunChain_ones : ∀ (l : List ℕ+) (x : (topList l).carrier),
    ∀ y ∈ (wedgeRunChain l x).dims, y = 1
  | [], x => fun y hy =>
      List.eq_of_mem_replicate (by rw [← run_dims (runAt x)]; exact hy)
  | n :: rest, x => fun y hy =>
      (List.mem_append.mp hy).elim
        (fun hy => List.eq_of_mem_replicate (by rw [← run_dims (runAt x.1)]; exact hy))
        (fun hy => wedgeRunChain_ones rest x.2 y hy)

/-- **…whose crossing permutation is the block sum of the beads'.** -/
theorem crossPerm_wedgeRunChain : ∀ (l : List ℕ+) (x : (topList l).carrier)
    (h : dimSum (wedgeRunChain l x).dims = dimSum l),
    crossPerm (a := zObj (wedgeRunChain l x).dims) h
        (zHom (e := l) (wedgeRunChain l x).map) = (topList l).perm x
  | [], _, _ => Equiv.ext fun i => i.elim0
  | n :: rest, x, h => by
      have hB : dimSum (wedgeRunChain rest x.2).dims = dimSum rest :=
        serialWedge_dimSum_eq (wedgeRunChain rest x.2).map
      have htail : crossPerm hB (toWedgeTop (wedgeRunChain rest x.2))
          = crossPerm (a := zObj (wedgeRunChain rest x.2).dims) hB
            (zHom (e := rest) (wedgeRunChain rest x.2).map) := crossPerm_eq_of_φ _ rfl
      refine Eq.trans (crossPerm_zHom_concatChainMap (n := n) (rest := rest)
        (runAt x.1).chain (wedgeRunChain rest x.2) (dimSum_dims_cube _) hB h) ?_
      rw [crossPerm_toBeadTop, cross_runAt, htail, crossPerm_wedgeRunChain rest x.2]
      rfl

/-! ## The tuple's run, and what the two routes name -/

/-- **The run over `d` a tuple of bead permutations names.** -/
noncomputable def wedgeRunOver (d : Ch Zbp) (x : (topList d.dims).carrier) :
    RunAt d (dimSum d.dims) :=
  ⟨⟨(wedgeChainsToOver d).obj (wedgeRunChain d.dims x), wedgeRunChain_ones d.dims x⟩,
    serialWedge_dimSum_eq (wedgeRunChain d.dims x).map⟩

/-- …crossing the block sum of the beads' permutations. -/
theorem wedgeRunOver_perm (d : Ch Zbp) (x : (topList d.dims).carrier) :
    (wedgeRunOver d x).perm = (topList d.dims).perm x :=
  (crossPerm_eq_of_φ _ rfl).trans (crossPerm_wedgeRunChain d.dims x _)

/-- **The wedge route names that run.** -/
theorem garsideSlicePresents_at (d : Ch Zbp) (x : (topList d.dims).carrier) :
    (garsideSlicePresents d).at' ((garsideListIso d.dims).hom.pre.obj ⟨x⟩)
      = op (((W Zbp).over (X := d)).Q.obj (wedgeRunOver d x).1.1) :=
  congrArg ((locOverEquivWedge d).op.symm).functor.obj
    ((garsideWedgePresents_at d.dims x).trans (wedgeLocOrder_functor_obj d.dims x))

/-! ## The runs over a chain are the tuples

One inclusion is `wedgeRunOver` and needs no induction; the other is `runSet_append` at every
junction, with `runSet_single` releasing the head bead. -/

/-- **Every run over a shape is a tuple of bead permutations.** -/
theorem runSet_topList : ∀ (l : List ℕ+) {σ : Equiv.Perm (Fin (dimSum l))},
    RunSet (zObj l) (dimSum l) σ → ∃ x : (topList l).carrier, (topList l).perm x = σ
  | [], σ, _ => ⟨σ, rfl⟩
  | n :: rest, σ, h => by
      obtain ⟨_, _, -, h₂, rfl⟩ := (runSet_append (dl := [n]) (dr := rest) rfl rfl σ).mp h
      obtain ⟨y, rfl⟩ := runSet_topList rest h₂
      exact ⟨(_, y), rfl⟩

/-- **The permutations `d`'s blocks allow are the block sums of its beads'.** -/
theorem range_runDownset_topList (d : Ch Zbp) :
    Set.range (runDownset d (dimSum d.dims)).perm = Set.range (topList d.dims).perm := by
  have hz : ∀ σ, RunSet d (dimSum d.dims) σ → RunSet (zObj d.dims) (dimSum d.dims) σ := by
    rw [eq_zObj d]; exact fun _ h => h
  refine Set.ext fun σ => ⟨fun h => ?_, ?_⟩
  · obtain ⟨u, rfl⟩ := h
    exact runSet_topList d.dims (hz _ ⟨u, rfl⟩)
  · rintro ⟨x, rfl⟩
    exact ⟨wedgeRunOver d x, wedgeRunOver_perm d x⟩

/-- **The slice polygraph is the beads' germs, multiplied.** -/
noncomputable def garsideSliceIso (d : Ch Zbp) :
    germBP.slicePoly d ≅ garsidePolyList d.dims :=
  (sliceFibreIso (d := d) (N := dimSum d.dims) rfl).symm ≪≫
    germBP.germPolyCongr (range_runDownset_topList d) ≪≫ garsideListIso d.dims

/-- **The beads of a concatenation are the beads of its halves** — `sliceConcat` at the two
shapes, which is where the runs split. -/
noncomputable def garsidePolyListAppend (l l' : List ℕ+) :
    garsidePolyList (l ++ l') ≅ garsidePolyList l ⨯ garsidePolyList l' :=
  (garsideSliceIso (zObj (l ++ l'))).symm ≪≫ sliceConcat l l' ≪≫
    Limits.prod.mapIso (garsideSliceIso (zObj l)) (garsideSliceIso (zObj l'))

/-- **The two routes name the same slice object** — the wedge route's tuple and the germ route's
run have one crossing permutation, and a run is pinned by it (`RunAt.perm_injective`). -/
theorem garsideSlice_naming (d : Ch Zbp) (a : (germBP.slicePoly d).V) :
    (garsideSlicePresents d).at' ((garsideSliceIso d).hom.pre.obj ⟨a⟩)
      = op (((W Zbp).over (X := d)).Q.obj (germBP.sliceCellOver a)) := by
  obtain ⟨u, rfl⟩ := germBP.exists_runPt_of_strands (rfl : dimSum d.dims = dimSum d.dims) a
  have hinv : (sliceFibreIso (d := d) (N := dimSum d.dims) rfl).inv.pre.obj
      ⟨germBP.runPt u⟩ = ⟨u⟩ :=
    congrArg (fun m : germBP.germPoly (runDownset d (dimSum d.dims)) ⟶
        germBP.germPoly (runDownset d (dimSum d.dims)) => m.pre.obj ⟨u⟩)
      (sliceFibreIso (d := d) (N := dimSum d.dims) rfl).hom_inv_id
  have hcell : (garsideSliceIso d).hom.pre.obj ⟨germBP.runPt u⟩
      = (garsideListIso d.dims).hom.pre.obj
        ⟨WeakDownset.equivOfRangeEq (range_runDownset_topList d) u⟩ :=
    congrArg (fun z => (garsideListIso d.dims).hom.pre.obj
      ((germBP.germPolyCongr (range_runDownset_topList d)).hom.pre.obj z)) hinv
  rw [hcell, garsideSlicePresents_at, germBP.sliceCellOver_runPt]
  exact congrArg (fun v : RunAt d (dimSum d.dims) =>
      op (((W Zbp).over (X := d)).Q.obj v.1.1))
    (RunAt.perm_injective ((wedgeRunOver_perm d _).trans
      (WeakDownset.perm_equivOfRangeEq (range_runDownset_topList d) u)))

end ChainCat
