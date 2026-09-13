import CubeChains.Concurrency.Presentation.BeadRuns
import CubeChains.Concurrency.Grading.CodimTwo

/-!
# Concurrency/Presentation/BeadOrder — the beads' permutations, and the merge's action on them

`wedgeOrder l` is one right weak order per bead, multiplied — the 0-cells a shape's Garside
polygraph carries.  `blockSum` reads a tuple as one permutation of the events, injectively and
order-reflectingly, and the tuple's own chain (`wedgeRunOver`) is the **run** crossing it: its
beads' runs, concatenated.  That identification is a bijection onto the runs, so a merge acts by
postcomposing the run — `crossPerm f * blockSum x` on the labels — and functoriality is the
crossing's cocycle law with no bead index in it.

The event count is carried as a parameter with its equation (`RunAt d N`), never transported: a
merge preserves it only propositionally, and the run itself does not see it at all.
-/

open CategoryTheory CategoryTheory.MonoidalCategory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

variable {N : ℕ}

/-! ## The order -/

/-- **One right weak order per bead, multiplied.** -/
def wedgeOrder : List ℕ+ → Type
  | [] => WeakOrder 0
  | n :: rest => WeakOrder (n : ℕ) × wedgeOrder rest

/-- The bead order is a **product of categories**, not the product order's category: a 1-cell is one
rise per bead, which is what `taut` must see for the germ to split over a junction. -/
instance instCategoryWedgeOrder : ∀ l : List ℕ+, Category.{0} (wedgeOrder l)
  | [] => inferInstanceAs (Category (WeakOrder 0))
  | n :: rest =>
      letI := instCategoryWedgeOrder rest
      inferInstanceAs (Category (WeakOrder (n : ℕ) × wedgeOrder rest))

instance isThin_wedgeOrder : ∀ l : List ℕ+, Quiver.IsThin (wedgeOrder l)
  | [] => fun x y => Preorder.subsingleton_hom (α := WeakOrder 0) x y
  | n :: rest =>
      letI := instCategoryWedgeOrder rest
      letI := isThin_wedgeOrder rest
      inferInstanceAs (Quiver.IsThin (WeakOrder (n : ℕ) × wedgeOrder rest))

/-- **The empty shape has one tuple** — there is nothing to permute. -/
theorem wedgeOrder_nil_eq (x y : wedgeOrder []) : x = y := Equiv.ext fun i => i.elim0

/-- Thinness, applied rather than searched for: inside a recursion on the shape the instance's index
is a variable and instance search will not find it. -/
theorem wedgeOrder_hom_eq {l : List ℕ+} {x y : wedgeOrder l} (e e' : x ⟶ y) : e = e' :=
  (isThin_wedgeOrder l x y).allEq e e'

/-! ## The block sum

A tuple's label is the permutation of the events it performs, bead by bead. -/

/-- **The permutation of the events a tuple performs** — its beads', juxtaposed. -/
def blockSum : (l : List ℕ+) → wedgeOrder l → Perm (Fin (dimSum l))
  | [] => fun _ => 1
  | n :: rest => fun x => permSum (n : ℕ) (dimSum rest) (WeakOrder.perm x.1, blockSum rest x.2)

/-- **A tuple is pinned by its block sum.** -/
theorem blockSum_injective : ∀ l : List ℕ+, Function.Injective (blockSum l)
  | [] => fun _ _ _ => wedgeOrder_nil_eq _ _
  | n :: rest => fun x y h => by
      have h' := permSum_injective h
      have ha : WeakOrder.perm x.1 = WeakOrder.perm y.1 :=
        congrArg (fun p : Perm (Fin (n : ℕ)) × Perm (Fin (dimSum rest)) => p.1) h'
      have hb : blockSum rest x.2 = blockSum rest y.2 :=
        congrArg (fun p : Perm (Fin (n : ℕ)) × Perm (Fin (dimSum rest)) => p.2) h'
      exact Prod.ext ha (blockSum_injective rest hb)

/-- **A tuple rises exactly when its block sum does** — one rise per bead on the left, one
comparison of block sums on the right; `weakOrder_permSum_le_iff` at every junction. -/
theorem nonempty_hom_iff_blockSum_le : ∀ (l : List ℕ+) (x y : wedgeOrder l),
    Nonempty (x ⟶ y) ↔ WeakOrder.of (blockSum l x) ≤ WeakOrder.of (blockSum l y)
  | [], x, y =>
      iff_of_true ⟨eqToHom (wedgeOrder_nil_eq x y)⟩
        (le_of_eq (congrArg WeakOrder.of (congrArg (blockSum []) (wedgeOrder_nil_eq x y))))
  | n :: rest, x, y => by
      constructor
      · rintro ⟨e⟩
        exact (weakOrder_permSum_le_iff _ _ _ _).mpr
          ⟨leOfHom e.1, (nonempty_hom_iff_blockSum_le rest x.2 y.2).mp ⟨e.2⟩⟩
      · intro hxy
        obtain ⟨h₁, h₂⟩ := (weakOrder_permSum_le_iff _ _ _ _).mp hxy
        exact ⟨(homOfLE h₁, ((nonempty_hom_iff_blockSum_le rest x.2 y.2).mpr h₂).some)⟩

/-! ## The greatest tuple

The reversal in every bead; `crossCap` is its length. -/

/-- **The greatest tuple**: the reversal in every bead. -/
def blockTop : (l : List ℕ+) → wedgeOrder l
  | [] => (⊤ : WeakOrder 0)
  | _ :: rest => (⊤, blockTop rest)

/-- The reversal is the greatest bead. -/
@[simp] theorem perm_top (n : ℕ) : WeakOrder.perm (⊤ : WeakOrder n) = Fin.revPerm := rfl

/-- The block sum splits at a junction — stated at the spelling `dimSum (n :: rest)` the tuple's
type carries, which is where `permLen_permSum` cannot fire on the nose. -/
theorem permLen_blockSum_cons (n : ℕ+) (rest : List ℕ+) (x : wedgeOrder (n :: rest)) :
    permLen (blockSum (n :: rest) x)
      = permLen (WeakOrder.perm x.1) + permLen (blockSum rest x.2) := permLen_permSum _ _

/-- **The greatest tuple attains the capacity.** -/
theorem permLen_blockSum_blockTop : ∀ l : List ℕ+,
    permLen (blockSum l (blockTop l)) = crossCap l
  | [] => by rw [blockSum, permLen_one, crossCap_nil]
  | n :: rest => by
      have hcons : permLen (blockSum (n :: rest) (blockTop (n :: rest)))
          = permLen (Fin.revPerm : Perm (Fin (n : ℕ)))
            + permLen (blockSum rest (blockTop rest)) :=
        permLen_blockSum_cons n rest (blockTop (n :: rest))
      rw [hcons, crossCap_cons, permLen_blockSum_blockTop rest]

/-! ## …and it is a run's crossing permutation

The tuple's own chain is the beads' runs, concatenated; `crossPerm` is monoidal over the junctions,
so the chain crosses the block sum. -/

/-- **The beads' own runs, concatenated** — the chain of `⋁l` a tuple names. -/
noncomputable def wedgeRunChain : (l : List ℕ+) → wedgeOrder l → Ch (⋁l)
  | [] => fun x => (wordRun (WeakOrder.perm x)).chain
  | n :: rest => fun x =>
      (chConcat (□(n : ℕ)) (⋁rest)).obj ((wordRun (WeakOrder.perm x.1)).chain,
        wedgeRunChain rest x.2)

/-- **A tuple names an all-edges chain** — every bead of every bead's run is an edge. -/
theorem wedgeRunChain_ones : ∀ (l : List ℕ+) (x : wedgeOrder l),
    ∀ y ∈ (wedgeRunChain l x).dims, y = 1
  | [], x => (wordRun (WeakOrder.perm x)).ones
  | _ :: rest, x => isRun_chConcat (wordRun (WeakOrder.perm x.1))
      ⟨wedgeRunChain rest x.2, wedgeRunChain_ones rest x.2⟩

/-- **A chain of `□n` crosses at the base what it crosses in the cube** — `serialWedge1` *is* the
coarsest chain's classifying map, so the base refinement is `toCubeTop` in another spelling. -/
theorem cross_eq_crossPerm_zHom {n : ℕ+} (A : Ch (□(n : ℕ))) (h : dimSum A.dims = (n : ℕ)) :
    crossPerm (a := zObj A.dims) h (zHom (e := [n]) (A.map ≫ (serialWedge1 n).inv)) = cross A := by
  obtain ⟨_ | k, hn⟩ := n
  · exact absurd hn (by omega)
  · exact crossPerm_eq_of_φ h rfl

/-- **The crossing of a junction is the block sum** — `crossPerm_zHom_concat` at the classifying map
of a concatenation, whose two halves are the head bead read in its own one-bead wedge (the monoidal
triangle, `⋁[]` being the unit) and the tail read by its own classifying map. -/
theorem crossPerm_zHom_concatChainMap {n : ℕ+} {rest : List ℕ+}
    (A : Ch (□(n : ℕ))) (B : Ch (⋁rest)) {q : ℕ} (hB : dimSum B.dims = q)
    (h : dimSum (A.dims ++ B.dims) = (n : ℕ) + q) :
    crossPerm (a := zObj (A.dims ++ B.dims)) h
        (zHom (e := n :: rest) (concatChainMap (□(n : ℕ)) (⋁rest) A B))
      = permSum (n : ℕ) q (cross A, crossPerm (a := zObj B.dims) hB (zHom (e := rest) B.map)) := by
  have htri : (serialWedge1 n).hom ⊗ₘ 𝟙 (⋁rest) = serialWedgeAppendHom [n] rest :=
    (MonoidalCategory.tensorHom_id (serialWedge1 n).hom (⋁rest)).trans
      (MonoidalCategory.triangle (□(n : ℕ)) (⋁rest)).symm
  have hcomp : ((A.map ≫ (serialWedge1 n).inv) ⊗ₘ B.map)
      ≫ ((serialWedge1 n).hom ⊗ₘ 𝟙 (⋁rest)) = A.map ⊗ₘ B.map := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Category.comp_id]
  have hmap : concatHomφ (zHom (e := [n]) (A.map ≫ (serialWedge1 n).inv))
      (zHom (e := rest) B.map) = concatChainMap (□(n : ℕ)) (⋁rest) A B :=
    (congrArg (fun t => (serialWedgeAppend A.dims B.dims).inv
        ≫ (((A.map ≫ (serialWedge1 n).inv) ⊗ₘ B.map) ≫ t)) htri.symm).trans
      (congrArg (fun t => (serialWedgeAppend A.dims B.dims).inv ≫ t) hcomp)
  refine Eq.trans (crossPerm_eq_of_φ (db := [n] ++ rest) h
    (g' := zHom (concatHomφ (zHom (e := [n]) (A.map ≫ (serialWedge1 n).inv))
      (zHom (e := rest) B.map))) hmap.symm) ?_
  exact (crossPerm_zHom_concat _ _ (dimSum_dims_cube A) hB h).trans
    (congrArg (fun σ => permSum (n : ℕ) q
        (σ, crossPerm (a := zObj B.dims) hB (zHom (e := rest) B.map)))
      (cross_eq_crossPerm_zHom A (dimSum_dims_cube A)))

/-- **…whose crossing permutation is the block sum.** -/
theorem crossPerm_wedgeRunChain : ∀ (l : List ℕ+) (x : wedgeOrder l)
    (h : dimSum (wedgeRunChain l x).dims = dimSum l),
    crossPerm (a := zObj (wedgeRunChain l x).dims) h
        (zHom (e := l) (wedgeRunChain l x).map) = blockSum l x
  | [], _, _ => Equiv.ext fun i => i.elim0
  | n :: rest, x, h => by
      have hB : dimSum (wedgeRunChain rest x.2).dims = dimSum rest :=
        serialWedge_dimSum_eq (wedgeRunChain rest x.2).map
      have hblk : blockSum (n :: rest) x
          = permSum (n : ℕ) (dimSum rest) (WeakOrder.perm x.1, blockSum rest x.2) := rfl
      refine Eq.trans (crossPerm_zHom_concatChainMap (n := n) (rest := rest)
        (wordRun (WeakOrder.perm x.1)).chain (wedgeRunChain rest x.2) hB h) ?_
      rw [hblk, cross_wordRun, crossPerm_wedgeRunChain rest x.2]

/-! ## The capacity bounds a tuple

The tuple's own chain is a refinement of the shape, so `permLen_crossPerm_le_crossCap` bounds it;
the order is graded in every bead, so only the reversals attain the bound. -/

/-- **The capacity bounds a tuple's length** — the bound on every refinement, read at the tuple's
own chain. -/
theorem permLen_blockSum_le (l : List ℕ+) (x : wedgeOrder l) :
    permLen (blockSum l x) ≤ crossCap l :=
  (congrArg permLen (crossPerm_wedgeRunChain l x
      (serialWedge_dimSum_eq (wedgeRunChain l x).map))).symm.trans_le
    (permLen_crossPerm_le_crossCap l (zHom (e := l) (wedgeRunChain l x).map) rfl _)

/-- **The greatest tuple is the only one of its length** — the order is graded in every bead. -/
theorem eq_blockTop_of_permLen : ∀ (l : List ℕ+) (x : wedgeOrder l),
    permLen (blockSum l x) = crossCap l → x = blockTop l
  | [], x, _ => wedgeOrder_nil_eq x (blockTop [])
  | n :: rest, x, h => by
      rw [permLen_blockSum_cons n rest x, crossCap_cons] at h
      have h₁ := permLen_le_revPerm (WeakOrder.perm x.1)
      have h₂ := permLen_blockSum_le rest x.2
      rw [show blockTop (n :: rest) = ((⊤ : WeakOrder (n : ℕ)), blockTop rest) from rfl]
      exact Prod.ext
        (WeakOrder.eq_of_le_of_permLen_eq (le_top (a := x.1)) (by rw [perm_top]; omega))
        (eq_blockTop_of_permLen rest x.2 (by omega))

/-! ## The tuples are the runs -/

/-- **The run over `d` a tuple names** — the event count is not part of it. -/
noncomputable def wedgeRunOver (d : Ch Zbp) (x : wedgeOrder d.dims) : RunOver d :=
  ⟨(wedgeChainsToOver d).obj (wedgeRunChain d.dims x), wedgeRunChain_ones d.dims x⟩

/-- …crossing the block sum, at `d`'s own event count. -/
theorem perm_wedgeRunOver (d : Ch Zbp) (x : wedgeOrder d.dims) :
    RunOver.perm rfl (wedgeRunOver d x) = blockSum d.dims x :=
  (crossPerm_eq_of_φ _ rfl).trans (crossPerm_wedgeRunChain d.dims x _)

/-- **Every run over a shape is a tuple's** — `runSet_append` at every junction, with
`runSet_single` releasing the head bead. -/
theorem exists_blockSum : ∀ (l : List ℕ+) {σ : Perm (Fin (dimSum l))},
    RunSet (zObj l) (dimSum l) σ → ∃ x : wedgeOrder l, blockSum l x = σ
  | [], σ, _ => ⟨WeakOrder.of σ, Equiv.ext fun i => i.elim0⟩
  | n :: rest, σ, h => by
      obtain ⟨σ₁, σ₂, -, h₂, rfl⟩ :=
        (runSet_append (dl := [n]) (dr := rest) (dimSum_single n) rfl σ).mp h
      obtain ⟨y, rfl⟩ := exists_blockSum rest h₂
      exact ⟨(WeakOrder.of σ₁, y), rfl⟩

/-- **…and every tuple's block sum is a run's crossing permutation.** -/
theorem runSet_blockSum (l : List ℕ+) (x : wedgeOrder l) :
    RunSet (zObj l) (dimSum l) (blockSum l x) :=
  ⟨⟨wedgeRunOver (zObj l) x, RunOver.left_dimSum rfl _⟩, perm_wedgeRunOver (zObj l) x⟩

/-- **A run as long as the capacity crosses the greatest tuple** — so a shape has exactly one
greatest run, and it is the reversal in every bead. -/
theorem eq_blockSum_blockTop_of_permLen (l : List ℕ+) {σ : Perm (Fin (dimSum l))}
    (hσ : RunSet (zObj l) (dimSum l) σ) (h : permLen σ = crossCap l) :
    σ = blockSum l (blockTop l) := by
  obtain ⟨x, rfl⟩ := exists_blockSum l hσ
  rw [eq_blockTop_of_permLen l x h]

theorem wedgeRunOver_injective (d : Ch Zbp) : Function.Injective (wedgeRunOver d) := fun x y h =>
  blockSum_injective d.dims
    (((perm_wedgeRunOver d x).symm.trans (congrArg (RunOver.perm rfl) h)).trans
      (perm_wedgeRunOver d y))

theorem wedgeRunOver_surjective (d : Ch Zbp) : Function.Surjective (wedgeRunOver d) := by
  intro u
  have hz : ∀ σ, RunSet d (dimSum d.dims) σ → RunSet (zObj d.dims) (dimSum d.dims) σ := by
    rw [eq_zObj d]; exact fun _ h => h
  obtain ⟨x, hx⟩ := exists_blockSum d.dims
    (hz _ ⟨⟨u, RunOver.left_dimSum rfl u⟩, rfl⟩)
  exact ⟨x, RunOver.perm_injective rfl ((perm_wedgeRunOver d x).trans hx)⟩

/-- **The tuples over a chain are its runs** — at any naming of the event count, the run itself
carrying none. -/
noncomputable def beadEquiv (d : Ch Zbp) (h : dimSum d.dims = N) : wedgeOrder d.dims ≃ RunAt d N :=
  Equiv.ofBijective (fun x => ⟨wedgeRunOver d x, RunOver.left_dimSum h _⟩)
    ⟨fun _ _ hxy => wedgeRunOver_injective d (congrArg Subtype.val hxy),
      fun u => (wedgeRunOver_surjective d u.1).imp fun _ hx => Subtype.ext hx⟩

/-- **A tuple rises exactly when the run it names does** — the count is a variable, so `subst`
replaces it by `d`'s own and no relabelling of `Fin` is left to carry. -/
theorem beadEquiv_le_iff (d : Ch Zbp) (h : dimSum d.dims = N) (x y : wedgeOrder d.dims) :
    Nonempty (x ⟶ y)
      ↔ WeakOrder.of (beadEquiv d h x).perm ≤ WeakOrder.of (beadEquiv d h y).perm := by
  subst h
  have hx : (beadEquiv d rfl x).perm = blockSum d.dims x := perm_wedgeRunOver d x
  have hy : (beadEquiv d rfl y).perm = blockSum d.dims y := perm_wedgeRunOver d y
  rw [hx, hy]
  exact nonempty_hom_iff_blockSum_le d.dims x y

/-! ## The merge's action -/

variable {d' d : Ch Zbp}

/-- **A merge postcomposes the run a tuple names** — the run is the geometry, the label follows. -/
noncomputable def beadMap (f : d' ⟶ d) (x : wedgeOrder d'.dims) : wedgeOrder d.dims :=
  (beadEquiv d (dimSum_eq_of_hom f).symm).symm (RunAt.push f (beadEquiv d' rfl x))

@[simp] theorem wedgeRunOver_beadMap (f : d' ⟶ d) (x : wedgeOrder d'.dims) :
    wedgeRunOver d (beadMap f x) = RunOver.push f (wedgeRunOver d' x) :=
  congrArg Subtype.val ((beadEquiv d (dimSum_eq_of_hom f).symm).apply_symm_apply _)

/-- **…so it pushes the run at any naming of the count.** -/
theorem beadEquiv_beadMap (f : d' ⟶ d) (h : dimSum d.dims = N) (h' : dimSum d'.dims = N)
    (x : wedgeOrder d'.dims) :
    beadEquiv d h (beadMap f x) = RunAt.push f (beadEquiv d' h' x) :=
  Subtype.ext (wedgeRunOver_beadMap f x)

/-- **The label is left-translated by the merge's own crossing** — `crossPerm φ * blockSum x`, with
the beads' crossings assembled by `crossPerm_chConcat`. -/
theorem perm_beadMap (f : d' ⟶ d) (h : dimSum d.dims = N) (h' : dimSum d'.dims = N)
    (x : wedgeOrder d'.dims) :
    (beadEquiv d h (beadMap f x)).perm = crossPerm h' f * (beadEquiv d' h' x).perm :=
  (congrArg RunAt.perm (beadEquiv_beadMap f h h' x)).trans
    (RunAt.push_perm f h' (beadEquiv d' h' x))

theorem beadMap_id (d : Ch Zbp) (x : wedgeOrder d.dims) : beadMap (𝟙 d) x = x :=
  wedgeRunOver_injective d ((wedgeRunOver_beadMap (𝟙 d) x).trans
    (Subtype.ext (congrArg Over.mk (Category.comp_id _))))

theorem beadMap_comp {d'' : Ch Zbp} (f : d'' ⟶ d') (g : d' ⟶ d) (x : wedgeOrder d''.dims) :
    beadMap (f ≫ g) x = beadMap g (beadMap f x) := by
  refine wedgeRunOver_injective d ?_
  rw [wedgeRunOver_beadMap, wedgeRunOver_beadMap, wedgeRunOver_beadMap]
  exact Subtype.ext (congrArg Over.mk (Category.assoc _ _ _).symm)

/-- **A merge carries a rise to a rise** — `RunAt.push_le_push`, read through the identification of
the tuples with the runs. -/
theorem nonempty_hom_beadMap (f : d' ⟶ d) {x y : wedgeOrder d'.dims} (e : x ⟶ y) :
    Nonempty (beadMap f x ⟶ beadMap f y) := by
  refine (beadEquiv_le_iff d (dimSum_eq_of_hom f).symm _ _).mpr ?_
  rw [beadEquiv_beadMap f (dimSum_eq_of_hom f).symm rfl x,
    beadEquiv_beadMap f (dimSum_eq_of_hom f).symm rfl y]
  exact RunAt.push_le_push f ((beadEquiv_le_iff d' rfl x y).mp ⟨e⟩)

/-- **…hence a functor of the bead orders.** -/
noncomputable def beadFunctor (f : d' ⟶ d) : wedgeOrder d'.dims ⥤ wedgeOrder d.dims where
  obj := beadMap f
  map e := (nonempty_hom_beadMap f e).some
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem beadFunctor_id (d : Ch Zbp) : beadFunctor (𝟙 d) = 𝟭 (wedgeOrder d.dims) :=
  CategoryTheory.Functor.ext (beadMap_id d) fun _ _ _ => Subsingleton.elim _ _

theorem beadFunctor_comp {d'' : Ch Zbp} (f : d'' ⟶ d') (g : d' ⟶ d) :
    beadFunctor (f ≫ g) = beadFunctor f ⋙ beadFunctor g :=
  CategoryTheory.Functor.ext (beadMap_comp f g) fun _ _ _ => Subsingleton.elim _ _

end ChainCat
