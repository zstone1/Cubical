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

The event count is carried as a parameter with its equation (`RunOver.perm h`), never transported:
a merge preserves it only propositionally, and the run itself does not see it at all.
-/

open CategoryTheory CategoryTheory.MonoidalCategory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

variable {N M : ℕ}

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

A tuple's label is the permutation of the events it performs, bead by bead.  Reading it at another
naming of the count conjugates by a relabelling of `Fin`, which the weak order does not see
(`weakOrder_of_permCongr_le_iff`). -/

/-- **The permutation of the events a tuple performs** — its beads', juxtaposed. -/
def blockSum : (l : List ℕ+) → wedgeOrder l → Perm (Fin (dimSum l))
  | [] => fun _ => 1
  | n :: rest => fun x => permSum (n : ℕ) (dimSum rest) (WeakOrder.perm x.1, blockSum rest x.2)

@[simp] theorem blockSum_cons (n : ℕ+) (rest : List ℕ+) (x : wedgeOrder (n :: rest)) :
    blockSum (n :: rest) x
      = permSum (n : ℕ) (dimSum rest) (WeakOrder.perm x.1, blockSum rest x.2) := rfl

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

/-- **A block sum rises exactly when every bead does** — neither bead can borrow a crossing from
another (`permLen_permSum`), so the comparison splits. -/
theorem weakOrder_permSum_le_iff {m n : ℕ} (p₁ q₁ : Perm (Fin m)) (p₂ q₂ : Perm (Fin n)) :
    WeakOrder.of (permSum m n (p₁, p₂)) ≤ WeakOrder.of (permSum m n (q₁, q₂))
      ↔ WeakOrder.of p₁ ≤ WeakOrder.of q₁ ∧ WeakOrder.of p₂ ≤ WeakOrder.of q₂ := by
  have key : (permSum m n (p₁, p₂))⁻¹ * permSum m n (q₁, q₂)
      = permSum m n (p₁⁻¹ * q₁, p₂⁻¹ * q₂) := by
    rw [← map_inv, ← map_mul]; rfl
  have h₁ := permLen_mul_le p₁ (p₁⁻¹ * q₁)
  have h₂ := permLen_mul_le p₂ (p₂⁻¹ * q₂)
  rw [mul_inv_cancel_left] at h₁ h₂
  simp only [WeakOrder.le_def, WeakOrder.perm_of, key, permLen_permSum]
  omega

/-- **…so a tuple rises exactly when its block sum does** — one rise per bead on the left, one
comparison of block sums on the right. -/
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

The reversal in every bead.  `crossCap` is its length, and the weak order is graded bead by bead, so
it is the *only* tuple of that length — which is what pins a shape's greatest run. -/

/-- **The greatest tuple**: the reversal in every bead. -/
def blockTop : (l : List ℕ+) → wedgeOrder l
  | [] => (⊤ : WeakOrder 0)
  | _ :: rest => (⊤, blockTop rest)

@[simp] theorem blockTop_fst (n : ℕ+) (rest : List ℕ+) :
    (blockTop (n :: rest)).1 = (⊤ : WeakOrder (n : ℕ)) := rfl

@[simp] theorem blockTop_snd (n : ℕ+) (rest : List ℕ+) :
    (blockTop (n :: rest)).2 = blockTop rest := rfl

/-- The reversal is the greatest bead. -/
@[simp] theorem perm_top (n : ℕ) : WeakOrder.perm (⊤ : WeakOrder n) = Fin.revPerm := rfl

/-- The block sum splits at a junction — stated at the spelling `dimSum (n :: rest)` the tuple's
type carries, which is where `permLen_permSum` cannot fire on the nose. -/
theorem permLen_blockSum_cons (n : ℕ+) (rest : List ℕ+) (x : wedgeOrder (n :: rest)) :
    permLen (blockSum (n :: rest) x)
      = permLen (WeakOrder.perm x.1) + permLen (blockSum rest x.2) := permLen_permSum _ _

/-- **The capacity bounds a tuple's length** — nothing beats a reversal in any bead. -/
theorem permLen_blockSum_le : ∀ (l : List ℕ+) (x : wedgeOrder l),
    permLen (blockSum l x) ≤ crossCap l
  | [], _ => by rw [blockSum, permLen_one, crossCap_nil]
  | n :: rest, x => by
      rw [permLen_blockSum_cons n rest x, crossCap_cons]
      exact Nat.add_le_add (permLen_le_revPerm _) (permLen_blockSum_le rest x.2)

/-- **…and the greatest tuple attains it.** -/
theorem permLen_blockSum_blockTop : ∀ l : List ℕ+,
    permLen (blockSum l (blockTop l)) = crossCap l
  | [] => by rw [blockSum, permLen_one, crossCap_nil]
  | n :: rest => by
      rw [permLen_blockSum_cons n rest (blockTop (n :: rest)), blockTop_fst, blockTop_snd,
        perm_top, crossCap_cons, permLen_blockSum_blockTop rest]

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

/-! ## …and it is a run's crossing permutation

The tuple's own chain is the beads' runs, concatenated; `crossPerm` is monoidal over the junctions,
so the chain crosses the block sum. -/

/-- **The beads' own runs, concatenated** — the chain of `⋁l` a tuple names. -/
noncomputable def wedgeRunChain : (l : List ℕ+) → wedgeOrder l → Ch (⋁l)
  | [] => fun x => (runAt (WeakOrder.perm x)).chain
  | n :: rest => fun x =>
      (chConcat (□(n : ℕ)) (⋁rest)).obj ((runAt (WeakOrder.perm x.1)).chain,
        wedgeRunChain rest x.2)

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
theorem wedgeRunChain_ones : ∀ (l : List ℕ+) (x : wedgeOrder l),
    ∀ y ∈ (wedgeRunChain l x).dims, y = 1
  | [], x => fun y hy =>
      List.eq_of_mem_replicate (by rw [← run_dims (runAt (WeakOrder.perm x))]; exact hy)
  | n :: rest, x => fun y hy =>
      (List.mem_append.mp hy).elim
        (fun hy => List.eq_of_mem_replicate
          (by rw [← run_dims (runAt (WeakOrder.perm x.1))]; exact hy))
        (fun hy => wedgeRunChain_ones rest x.2 y hy)

/-- **…whose crossing permutation is the block sum.** -/
theorem crossPerm_wedgeRunChain : ∀ (l : List ℕ+) (x : wedgeOrder l)
    (h : dimSum (wedgeRunChain l x).dims = dimSum l),
    crossPerm (a := zObj (wedgeRunChain l x).dims) h
        (zHom (e := l) (wedgeRunChain l x).map) = blockSum l x
  | [], _, _ => Equiv.ext fun i => i.elim0
  | n :: rest, x, h => by
      have hB : dimSum (wedgeRunChain rest x.2).dims = dimSum rest :=
        serialWedge_dimSum_eq (wedgeRunChain rest x.2).map
      have htail : crossPerm hB (toWedgeTop (wedgeRunChain rest x.2))
          = crossPerm (a := zObj (wedgeRunChain rest x.2).dims) hB
            (zHom (e := rest) (wedgeRunChain rest x.2).map) := crossPerm_eq_of_φ _ rfl
      refine Eq.trans (crossPerm_zHom_concatChainMap (n := n) (rest := rest)
        (runAt (WeakOrder.perm x.1)).chain (wedgeRunChain rest x.2)
        (dimSum_dims_cube _) hB h) ?_
      rw [crossPerm_toBeadTop, cross_runAt, htail, crossPerm_wedgeRunChain rest x.2]
      rfl

/-! ## The tuples are the runs -/

/-- **The run over `d` a tuple names** — the event count is not part of it. -/
noncomputable def wedgeRunOver (d : Ch Zbp) (x : wedgeOrder d.dims) : RunOver d :=
  ⟨(wedgeChainsToOver d).obj (wedgeRunChain d.dims x), wedgeRunChain_ones d.dims x⟩

/-- …crossing the block sum, read at any naming of the event count. -/
theorem perm_wedgeRunOver (d : Ch Zbp) (h : dimSum d.dims = dimSum d.dims)
    (x : wedgeOrder d.dims) :
    RunOver.perm h (wedgeRunOver d x) = blockSum d.dims x :=
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
  ⟨⟨wedgeRunOver (zObj l) x, RunOver.left_dimSum rfl _⟩, perm_wedgeRunOver (zObj l) rfl x⟩

/-- **A run as long as the capacity crosses the greatest tuple** — so a shape has exactly one
greatest run, and it is the reversal in every bead. -/
theorem eq_blockSum_blockTop_of_permLen (l : List ℕ+) {σ : Perm (Fin (dimSum l))}
    (hσ : RunSet (zObj l) (dimSum l) σ) (h : permLen σ = crossCap l) :
    σ = blockSum l (blockTop l) := by
  obtain ⟨x, rfl⟩ := exists_blockSum l hσ
  rw [eq_blockTop_of_permLen l x h]

theorem wedgeRunOver_injective (d : Ch Zbp) : Function.Injective (wedgeRunOver d) := fun x y h =>
  blockSum_injective d.dims
    (((perm_wedgeRunOver d rfl x).symm.trans (congrArg (RunOver.perm rfl) h)).trans
      (perm_wedgeRunOver d rfl y))

theorem wedgeRunOver_surjective (d : Ch Zbp) : Function.Surjective (wedgeRunOver d) := by
  intro u
  have hz : ∀ σ, RunSet d (dimSum d.dims) σ → RunSet (zObj d.dims) (dimSum d.dims) σ := by
    rw [eq_zObj d]; exact fun _ h => h
  obtain ⟨x, hx⟩ := exists_blockSum d.dims
    (hz _ ⟨⟨u, RunOver.left_dimSum rfl u⟩, rfl⟩)
  exact ⟨x, RunOver.perm_injective rfl ((perm_wedgeRunOver d rfl x).trans hx)⟩

/-- **The tuples over a chain are its runs** — at any naming of the event count, the run itself
carrying none. -/
noncomputable def beadEquiv (d : Ch Zbp) (h : dimSum d.dims = N) : wedgeOrder d.dims ≃ RunAt d N :=
  Equiv.ofBijective (fun x => ⟨wedgeRunOver d x, RunOver.left_dimSum h _⟩)
    ⟨fun _ _ hxy => wedgeRunOver_injective d (congrArg Subtype.val hxy),
      fun u => (wedgeRunOver_surjective d u.1).imp fun _ hx => Subtype.ext hx⟩

@[simp] theorem beadEquiv_val (d : Ch Zbp) (h : dimSum d.dims = N) (x : wedgeOrder d.dims) :
    (beadEquiv d h x).1 = wedgeRunOver d x := rfl

/-! ## …and the recount between two namings

A run's crossing permutation is read at a named count, and two namings differ by a relabelling of
`Fin`: lengths and gaps go along, so the weak order does not see it. -/

theorem weakOrder_of_permCongr_le_iff {m k : ℕ} (e : m = k) (σ τ : Perm (Fin m)) :
    WeakOrder.of ((finCongr e).permCongr σ) ≤ WeakOrder.of ((finCongr e).permCongr τ)
      ↔ WeakOrder.of σ ≤ WeakOrder.of τ := by
  have hmul : ((finCongr e).permCongr σ)⁻¹ * (finCongr e).permCongr τ
      = (finCongr e).permCongr (σ⁻¹ * τ) := by
    rw [← Equiv.permCongrHom_coe (finCongr e), ← map_inv, ← map_mul]
  rw [WeakOrder.le_def, WeakOrder.le_def, WeakOrder.perm_of, WeakOrder.perm_of, WeakOrder.perm_of,
    WeakOrder.perm_of, hmul, permLen_permCongr_finCongr, permLen_permCongr_finCongr,
    permLen_permCongr_finCongr]

theorem weakOrder_perm_recount {d : Ch Zbp} (h : dimSum d.dims = N) (h' : dimSum d.dims = M)
    (u v : RunOver d) :
    WeakOrder.of (RunOver.perm h' u) ≤ WeakOrder.of (RunOver.perm h' v)
      ↔ WeakOrder.of (RunOver.perm h u) ≤ WeakOrder.of (RunOver.perm h v) := by
  rw [RunOver.perm, RunOver.perm, crossPerm_recount (RunOver.left_dimSum h u)
      (RunOver.left_dimSum h' u), crossPerm_recount (RunOver.left_dimSum h v)
      (RunOver.left_dimSum h' v)]
  exact weakOrder_of_permCongr_le_iff _ _ _

/-- **A tuple rises exactly when the run it names does.** -/
theorem beadEquiv_le_iff (d : Ch Zbp) (h : dimSum d.dims = N) (x y : wedgeOrder d.dims) :
    Nonempty (x ⟶ y)
      ↔ WeakOrder.of (beadEquiv d h x).perm ≤ WeakOrder.of (beadEquiv d h y).perm := by
  rw [show (beadEquiv d h x).perm = RunOver.perm h (wedgeRunOver d x) from
      congrArg (fun k : dimSum d.dims = N => RunOver.perm k (wedgeRunOver d x))
        (Subsingleton.elim _ _),
    show (beadEquiv d h y).perm = RunOver.perm h (wedgeRunOver d y) from
      congrArg (fun k : dimSum d.dims = N => RunOver.perm k (wedgeRunOver d y))
        (Subsingleton.elim _ _),
    weakOrder_perm_recount rfl h, perm_wedgeRunOver, perm_wedgeRunOver]
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

/-- **A merge carries a rise to a rise** — its crossings are new above every run
(`RunAt.push_permLen`), so the translation preserves length-additivity. -/
theorem nonempty_hom_beadMap (f : d' ⟶ d) {x y : wedgeOrder d'.dims} (e : x ⟶ y) :
    Nonempty (beadMap f x ⟶ beadMap f y) := by
  have hle := (beadEquiv_le_iff d' rfl x y).mp ⟨e⟩
  refine (beadEquiv_le_iff d (dimSum_eq_of_hom f).symm _ _).mpr ?_
  rw [perm_beadMap f (dimSum_eq_of_hom f).symm rfl x,
    perm_beadMap f (dimSum_eq_of_hom f).symm rfl y]
  have key : ∀ u : RunAt d' (dimSum d'.dims),
      permLen (crossPerm (rfl : dimSum d'.dims = dimSum d'.dims) f * u.perm)
        = permLen (crossPerm (rfl : dimSum d'.dims = dimSum d'.dims) f) + permLen u.perm :=
    fun u => by
      rw [← RunAt.push_perm f rfl u, RunAt.push_permLen f rfl u]; omega
  refine WeakOrder.le_def.mpr ?_
  have h₁ := key (beadEquiv d' rfl x)
  have h₂ := key (beadEquiv d' rfl y)
  have hgap : (crossPerm (rfl : dimSum d'.dims = dimSum d'.dims) f * (beadEquiv d' rfl x).perm)⁻¹
      * (crossPerm (rfl : dimSum d'.dims = dimSum d'.dims) f * (beadEquiv d' rfl y).perm)
      = ((beadEquiv d' rfl x).perm)⁻¹ * (beadEquiv d' rfl y).perm := by
    group
  rw [WeakOrder.le_def] at hle
  simp only [WeakOrder.perm_of] at hle ⊢
  rw [hgap]
  omega

/-- **…hence a functor of the bead orders.** -/
noncomputable def beadFunctor (f : d' ⟶ d) : wedgeOrder d'.dims ⥤ wedgeOrder d.dims where
  obj := beadMap f
  map e := (nonempty_hom_beadMap f e).some
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp] theorem beadFunctor_obj (f : d' ⟶ d) (x : wedgeOrder d'.dims) :
    (beadFunctor f).obj x = beadMap f x := rfl

theorem beadFunctor_id (d : Ch Zbp) : beadFunctor (𝟙 d) = 𝟭 (wedgeOrder d.dims) :=
  CategoryTheory.Functor.ext (beadMap_id d) fun _ _ _ => Subsingleton.elim _ _

theorem beadFunctor_comp {d'' : Ch Zbp} (f : d'' ⟶ d') (g : d' ⟶ d) :
    beadFunctor (f ≫ g) = beadFunctor f ⋙ beadFunctor g :=
  CategoryTheory.Functor.ext (beadMap_comp f g) fun _ _ _ => Subsingleton.elim _ _

end ChainCat
