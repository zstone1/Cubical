import CubeChains.Concurrency.Presentation.BeadRuns
import CubeChains.Concurrency.Grading.CodimTwo
import CubeChains.Concurrency.Executions.Complement
import CubeChains.Concurrency.Merge.CubeCrossing

/-!
# Concurrency/Presentation/BeadOrder — the beads' permutations, and the run they name

`wedgeOrder l` is one right weak order per bead.  `blockSum` reads a tuple as one permutation of the
events, and the tuple's own chain (`wedgeRunChain`) is the **run** crossing it: its beads' runs,
concatenated.  The capacity bounds the block sum, and only the reversal in every bead attains it —
which is what makes the greatest run a shape's complement of the least.
-/

open CategoryTheory CategoryTheory.MonoidalCategory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

/-! ## The order -/

/-- **One right weak order per bead, multiplied.** -/
def wedgeOrder : List ℕ+ → Type
  | [] => WeakOrder 0
  | n :: rest => WeakOrder (n : ℕ) × wedgeOrder rest

/-- **The empty shape has one tuple** — there is nothing to permute. -/
theorem wedgeOrder_nil_eq (x y : wedgeOrder []) : x = y := Equiv.ext fun i => i.elim0

/-! ## The block sum

A tuple's label is the permutation of the events it performs, bead by bead. -/

/-- **The permutation of the events a tuple performs** — its beads', juxtaposed. -/
def blockSum : (l : List ℕ+) → wedgeOrder l → Perm (Fin (dimSum l))
  | [] => fun _ => 1
  | n :: rest => fun x => permSum (n : ℕ) (dimSum rest) (WeakOrder.perm x.1, blockSum rest x.2)

/-! ## The greatest tuple

The reversal in every bead; `crossCap` is its length. -/

/-- **The greatest tuple**: the reversal in every bead. -/
def blockTop : (l : List ℕ+) → wedgeOrder l
  | [] => (⊤ : WeakOrder 0)
  | _ :: rest => (⊤, blockTop rest)

/-- The reversal is the greatest bead. -/
@[simp] theorem perm_top (n : ℕ) : WeakOrder.perm (⊤ : WeakOrder n) = Fin.revPerm := rfl

/-- **The least tuple**: the identity in every bead. -/
def blockBot : (l : List ℕ+) → wedgeOrder l
  | [] => WeakOrder.of 1
  | _ :: rest => (WeakOrder.of 1, blockBot rest)

/-- **The least tuple crosses nothing.** -/
theorem blockSum_blockBot : ∀ l : List ℕ+, blockSum l (blockBot l) = 1
  | [] => rfl
  | n :: rest => by
      change permSum (n : ℕ) (dimSum rest) (1, blockSum rest (blockBot rest)) = 1
      rw [blockSum_blockBot rest]
      exact map_one _

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
      rw [hcons, crossCap_cons, permLen_blockSum_blockTop rest, permLen_revPerm]

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

/-! ### …read bead by bead

A tuple's chain is a **run** of `⋁l`, so it has two readings: the tuple, and the beads' own runs
(`runProj`).  Comparing them once here is what makes the complement — reversal in every bead —
the passage from the least tuple to the greatest. -/

/-- **The run of `⋁l` a tuple names.** -/
noncomputable def tupleRun (l : List ℕ+) (x : wedgeOrder l) : Run (⋁l) :=
  ⟨wedgeRunChain l x, wedgeRunChain_ones l x⟩

/-- **A run of a wedge is its beads** — `runConcat_runSplit` at every junction. -/
theorem run_eq_of_runProj : ∀ (l : List ℕ+) {r s : Run (⋁l)},
    (∀ i, runProj r i = runProj s i) → r = s
  | [], r, s, _ => run_cube0_eq r s
  | n :: rest, r, s, h => by
      have h0 : (runSplit (consAltitude n rest) r).1 = (runSplit (consAltitude n rest) s).1 := by
        have hz := h 0
        rwa [runProj_zero, runProj_zero] at hz
      have h1 : (runSplit (consAltitude n rest) r).2 = (runSplit (consAltitude n rest) s).2 :=
        run_eq_of_runProj rest fun j => by
          have hs := h j.succ
          rwa [runProj_succ, runProj_succ] at hs
      exact ((runConcat_runSplit (consAltitude n rest) r).symm.trans
          (congrArg (runConcat (□(n : ℕ)) (⋁rest)).obj (Prod.ext h0 h1))).trans
        (runConcat_runSplit (consAltitude n rest) s)

/-- **Bead `i` of the least tuple's run runs the bead's axes in order.** -/
theorem runProj_tupleRun_blockBot : ∀ (l : List ℕ+) (i : Fin l.length),
    runProj (tupleRun l (blockBot l)) i = wordRun 1
  | [], i => i.elim0
  | n :: rest, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact runProj_concat_zero n rest (wordRun 1) (tupleRun rest (blockBot rest))
      · exact (runProj_concat_succ n rest (wordRun 1) (tupleRun rest (blockBot rest)) j).trans
          (runProj_tupleRun_blockBot rest j)

/-- **…and bead `i` of the greatest tuple's run runs them backwards.** -/
theorem runProj_tupleRun_blockTop : ∀ (l : List ℕ+) (i : Fin l.length),
    runProj (tupleRun l (blockTop l)) i = wordRun Fin.revPerm
  | [], i => i.elim0
  | n :: rest, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact runProj_concat_zero n rest (wordRun Fin.revPerm) (tupleRun rest (blockTop rest))
      · exact (runProj_concat_succ n rest (wordRun Fin.revPerm)
            (tupleRun rest (blockTop rest)) j).trans (runProj_tupleRun_blockTop rest j)

/-- **The greatest tuple's run is the least one's complement** — reversal in every bead
(`runProj_compl`), and reversing the order a bead fires its axes in is `Fin.revPerm`. -/
theorem compl_tupleRun_blockBot (l : List ℕ+) :
    (tupleRun l (blockBot l)).compl = tupleRun l (blockTop l) :=
  run_eq_of_runProj l fun i => by
    rw [runProj_compl, runProj_tupleRun_blockBot, rev_wordRun, one_mul,
      runProj_tupleRun_blockTop]

/-- **…and at degree zero the complement fixes every run** — each bead is an edge, so there is
nothing to reverse.  With `Run.compl_ne` this is the "exactly" its docstring claims. -/
theorem Run.compl_eq_self {l : List ℕ+} (r : Run (⋁l)) (hl : BPSet.degree l = 0) : r.compl = r :=
  run_eq_of_runProj l fun i => by
    have h1 : ((l.get i : ℕ)) = 1 :=
      congrArg (fun x : ℕ+ => (x : ℕ)) ((BPSet.degree_eq_zero_iff l).mp hl _ (List.get_mem l i))
    refine (runPermEquiv _).injective (Equiv.ext fun x => Fin.ext ?_)
    have h2 := (runPermEquiv _ (runProj r.compl i) x).isLt
    have h3 := (runPermEquiv _ (runProj r i) x).isLt
    omega

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

A crossing is a set of pairs, so a bead inverts at most the pairs it holds (`permLen_le_choose`);
the order is graded in every bead, so only the reversals attain the bound. -/

/-- **The capacity bounds a tuple's length** — the one-bead bound, summed over the junctions. -/
theorem permLen_blockSum_le : ∀ (l : List ℕ+) (x : wedgeOrder l),
    permLen (blockSum l x) ≤ crossCap l
  | [], _ => by rw [blockSum, permLen_one]; exact Nat.zero_le _
  | n :: rest, x => by
      rw [permLen_blockSum_cons n rest x, crossCap_cons]
      exact Nat.add_le_add (permLen_le_choose _) (permLen_blockSum_le rest x.2)

/-- **The greatest tuple is the only one of its length** — the order is graded in every bead. -/
theorem eq_blockTop_of_permLen : ∀ (l : List ℕ+) (x : wedgeOrder l),
    permLen (blockSum l x) = crossCap l → x = blockTop l
  | [], x, _ => wedgeOrder_nil_eq x (blockTop [])
  | n :: rest, x, h => by
      rw [permLen_blockSum_cons n rest x, crossCap_cons] at h
      have h₁ := permLen_le_choose (WeakOrder.perm x.1)
      have h₂ := permLen_blockSum_le rest x.2
      rw [show blockTop (n :: rest) = ((⊤ : WeakOrder (n : ℕ)), blockTop rest) from rfl]
      exact Prod.ext
        (WeakOrder.eq_of_le_of_permLen_eq (le_top (a := x.1))
          (by rw [perm_top, permLen_revPerm]; omega))
        (eq_blockTop_of_permLen rest x.2 (by omega))

/-! ## The tuples are the runs -/

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

/-- **The capacity bounds every run over a shape** — a run is a tuple, and a tuple is bounded bead
by bead. -/
theorem permLen_le_crossCap {l : List ℕ+} {σ : Perm (Fin (dimSum l))}
    (hσ : RunSet (zObj l) (dimSum l) σ) : permLen σ ≤ crossCap l := by
  obtain ⟨x, rfl⟩ := exists_blockSum l hσ
  exact permLen_blockSum_le l x

/-- **A run as long as the capacity crosses the greatest tuple** — so a shape has exactly one
greatest run, and it is the reversal in every bead. -/
theorem eq_blockSum_blockTop_of_permLen (l : List ℕ+) {σ : Perm (Fin (dimSum l))}
    (hσ : RunSet (zObj l) (dimSum l) σ) (h : permLen σ = crossCap l) :
    σ = blockSum l (blockTop l) := by
  obtain ⟨x, rfl⟩ := exists_blockSum l hσ
  rw [eq_blockTop_of_permLen l x h]

end ChainCat
