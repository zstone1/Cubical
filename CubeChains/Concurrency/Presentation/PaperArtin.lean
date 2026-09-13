import CubeChains.Concurrency.Presentation.PaperPoly
import CubeChains.Concurrency.Presentation.ArtinDegreeZero

/-!
# Concurrency/Presentation/PaperArtin — at the base the paper's cells are Artin's

A run of `Zbp` is its strand count, so a cell of `Paper.poly Zbp` is a loop and the object it
carries is the only datum on either side:

    Run Zbp ────────────▸ ℕ                                   0-cells
    Cell 1 ──obj──▸ RunAtom N ───▸ Fin (N−1)                   1-cells, the generators
    Cell 2 ──obj──▸ RunSquare N ─▸ AtomPair N ─▸ artinBP.Rel N  2-cells, the relations

A 2-cell's object is one bead of dimension three, or two of dimension two: hexagon and square.
-/

open CategoryTheory CategoryTheory.Polygraph BPSet CubeChains

namespace ChainCat.Paper

/-! ## A run of the base is its strand count -/

/-- The run on `N` events at the base. -/
def zRun (N : ℕ) : Run Zbp := ⟨zObj (𝟙^N), fun _ hd => List.eq_of_mem_replicate hd⟩

@[simp] theorem zRun_chain (N : ℕ) : (zRun N).chain = zObj (𝟙^N) := rfl

@[simp] theorem dimSum_zRun (N : ℕ) : dimSum (zRun N).dims = N := dimSum_replicate N

/-- **A run of the base is the run on its own events** — the shape is all edges and the classifying
map is forced. -/
theorem eq_zRun (X : Run Zbp) : X = zRun (dimSum X.dims) :=
  Run.ext ((degree_eq_zero_iff_eq_run X.chain).mp ((isRun_iff_degree_eq_zero _).mp X.property))

/-- **…so the 0-cells are the strand counts.** -/
def zRunEquiv : Run Zbp ≃ ℕ where
  toFun X := dimSum X.dims
  invFun := zRun
  left_inv X := (eq_zRun X).symm
  right_inv := dimSum_replicate

/-- **The run below a chain of the base is the run on the chain's events.** -/
theorem bottomRun_eq_zRun (a : Ch Zbp) : bottomRun a = zRun (dimSum a.dims) :=
  (eq_zRun (bottomRun a)).trans (congrArg zRun (dimSum_eq_of_hom (bottomHom a)))

/-- **…and so is the run its greatest refinement comes out of.** -/
theorem topRun_eq_zRun (a : Ch Zbp) : (topOf a).1 = zRun (dimSum a.dims) :=
  (eq_zRun (topOf a).1).trans (congrArg zRun (dimSum_eq_of_hom (topOf a).2))

/-- **A cell of the base is a loop** — both its ends are the run on its object's events. -/
theorem Cell.ends_eq {n : ℕ} {X Y : Run Zbp} (α : Cell n X Y) : X = Y :=
  ((α.below.symm.trans (bottomRun_eq_zRun α.obj)).trans (topRun_eq_zRun α.obj).symm).trans α.top

/-- **A cell's object has the events of its ends.** -/
theorem Cell.dimSum_obj {n : ℕ} {X Y : Run Zbp} (α : Cell n X Y) :
    dimSum α.obj.dims = dimSum X.dims :=
  (dimSum_eq_of_hom (bottomHom α.obj)).symm.trans
    (congrArg (fun Z : Run Zbp => dimSum Z.dims) α.below)

/-! ## The 1-cells are the cuts out of the run -/

/-- **The cut a degree-one object is** — its greatest refinement, which at degree one is the only
crossing one. -/
noncomputable def runAtomOfGen {N : ℕ} (α : Gen (zRun N) (zRun N)) : RunAtom N :=
  ⟨α.obj, α.hom, α.codim_hom, α.not_W_hom one_ne_zero⟩

/-- …and the degree-one object a cut out of the run is. -/
def genOfRunAtom {N : ℕ} (a : RunAtom N) : Gen (zRun N) (zRun N) where
  obj := a.tgt
  degree_obj := a.degree_tgt
  below := (bottomRun_eq_zRun a.tgt).trans (congrArg zRun a.strands)
  top := topOf_fst_eq_of_not_W (X := zRun N) (f := a.cut) a.degree_tgt a.not_merge

/-- **The 1-cells at `N` strands are the cuts out of the run** — hence, by `runAtomEquiv`, Artin's
`N−1` generators. -/
noncomputable def genRunAtomEquiv (N : ℕ) : Gen (zRun N) (zRun N) ≃ RunAtom N where
  toFun := runAtomOfGen
  invFun := genOfRunAtom
  left_inv _ := Cell.ext rfl
  right_inv _ := RunAtom.ext_tgt rfl

/-! ## The 2-cells are the degree-two objects above it -/

/-- **The degree-two shape a 2-cell is.** -/
def runSquareOfCell {N : ℕ} (α : Cell 2 (zRun N) (zRun N)) : RunSquare N :=
  ⟨α.obj, α.dimSum_obj.trans (dimSum_zRun N), α.degree_obj⟩

/-- …and the 2-cell a degree-two shape is. -/
def cellOfRunSquare {N : ℕ} (s : RunSquare N) : Cell 2 (zRun N) (zRun N) where
  obj := s.apex
  degree_obj := s.degree_apex
  below := (bottomRun_eq_zRun s.apex).trans (congrArg zRun s.strands)
  top := (topRun_eq_zRun s.apex).trans (congrArg zRun s.strands)

/-- **The 2-cells at `N` strands are the degree-two shapes on `N` events.** -/
def cellRunSquareEquiv (N : ℕ) : Cell 2 (zRun N) (zRun N) ≃ RunSquare N where
  toFun := runSquareOfCell
  invFun := cellOfRunSquare
  left_inv _ := Cell.ext rfl
  right_inv _ := rfl

/-- **A 2-cell's object is one bead of dimension three, or two beads of dimension two** — the
hexagon's shape and the square's, the rest of the beads edges, and the capacity tells them apart. -/
theorem cell_species {N : ℕ} (α : Cell 2 (zRun N) (zRun N)) :
    ((∃ l r : List ℕ+, (zRun N).dims = l ++ 1 :: 1 :: 1 :: r ∧ α.obj.dims = l ++ 3 :: r)
        ∧ crossCap α.obj.dims = 3)
      ∨ ((∃ l m r : List ℕ+, (zRun N).dims = l ++ 1 :: 1 :: (m ++ 1 :: 1 :: r) ∧
          α.obj.dims = l ++ 2 :: (m ++ 2 :: r)) ∧ crossCap α.obj.dims = 2) :=
  crossCap_of_codim_eq_two α.hom (degree_ones N) α.codim_hom

/-! ## …which is Artin's presentation -/

/-- **A 2-cell is a pair of cuts** — adjacent for the hexagon, apart for the square
(`AtomPair.adj_or_apart`). -/
noncomputable def cellAtomPairEquiv (N : ℕ) : Cell 2 (zRun N) (zRun N) ≃ AtomPair N :=
  (cellRunSquareEquiv N).trans (runSquareEquiv N).symm

/-- **A 2-cell's object is the chain its two cuts share.** -/
theorem obj_eq_pairChain {N : ℕ} (α : Cell 2 (zRun N) (zRun N)) :
    α.obj = pairChain N (cellAtomPairEquiv N α).lo (cellAtomPairEquiv N α).hi
      (cellAtomPairEquiv N α).ne :=
  (congrArg RunSquare.apex ((runSquareEquiv N).apply_symm_apply (runSquareOfCell α))).symm

/-- **A 2-cell's object drops exactly the two junctions its cuts name** — the species, as a
statement about `boundaries`. -/
theorem boundaries_obj {N : ℕ} (α : Cell 2 (zRun N) (zRun N)) :
    boundaries α.obj.dims = Finset.range (N + 1) \
      {((cellAtomPairEquiv N α).lo : ℕ) + 1, ((cellAtomPairEquiv N α).hi : ℕ) + 1} :=
  (congrArg (fun c : Ch Zbp => boundaries c.dims) (obj_eq_pairChain α)).trans
    (boundaries_pairChain _)

/-- **The two cuts are adjacent exactly when the object has a bead of dimension three** — the
hexagon drops two consecutive junctions, the square two with a gap, and a bead of three is the only
one with three crossings to make. -/
theorem cell_adj_iff {N : ℕ} (α : Cell 2 (zRun N) (zRun N)) :
    ((cellAtomPairEquiv N α).hi : ℕ) = ((cellAtomPairEquiv N α).lo : ℕ) + 1
      ↔ (3 : ℕ+) ∈ α.obj.dims := by
  have hlo := (cellAtomPairEquiv N α).lo.isLt
  have hhi := (cellAtomPairEquiv N α).hi.isLt
  have hlt := (cellAtomPairEquiv N α).lt
  constructor
  · intro h
    have hsh : α.obj.dims
        = 𝟙^((cellAtomPairEquiv N α).lo : ℕ) ++ (3 : ℕ+) ::
            𝟙^(N - ((cellAtomPairEquiv N α).lo : ℕ) - 3) := by
      refine boundaries_injective ?_
      rw [boundaries_obj α, boundaries_three_bead]
      ext t
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hsh]
    simp
  · intro h3
    obtain ⟨s, t, hst⟩ := List.append_of_mem h3
    have hcap : 3 ≤ crossCap α.obj.dims := by
      have h : permLen (Fin.revPerm : Equiv.Perm (Fin ((3 : ℕ+) : ℕ))) = 3 := by decide
      rw [hst, crossCap_append, crossCap_cons]
      omega
    obtain ⟨⟨l, r, hsrc, hobj⟩, -⟩ | ⟨-, hcap2⟩ := cell_species α
    · have hsub : ∀ x ∈ l ++ (1 : ℕ+) :: 1 :: 1 :: r, x = (1 : ℕ+) := by
        rw [← hsrc]
        exact fun x hx => List.eq_of_mem_replicate hx
      obtain ⟨p, rfl⟩ : ∃ p, l = 𝟙^p :=
        ⟨l.length, List.eq_replicate_of_mem fun x hx => hsub x (by simp [hx])⟩
      obtain ⟨q, rfl⟩ : ∃ q, r = 𝟙^q :=
        ⟨r.length, List.eq_replicate_of_mem fun x hx => hsub x (by simp [hx])⟩
      have hlen : p + 3 + q = N := by
        have h : (𝟙^N : List ℕ+).length = (𝟙^p ++ (1 : ℕ+) :: 1 :: 1 :: 𝟙^q).length :=
          congrArg List.length hsrc
        simp only [List.length_replicate, List.length_append, List.length_cons] at h
        omega
      have hb : Finset.range (N + 1) \
            {((cellAtomPairEquiv N α).lo : ℕ) + 1, ((cellAtomPairEquiv N α).hi : ℕ) + 1}
          = Finset.range (N + 1) \ {p + 1, p + 2} := by
        refine (boundaries_obj α).symm.trans ?_
        rw [hobj, boundaries_three_bead, hlen]
      have hsubr : ({p + 1, p + 2} : Finset ℕ) ⊆ Finset.range (N + 1) := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_range]
        omega
      have hpair := eq_of_sdiff_range (cellAtomPairEquiv N α).junctions_subset hsubr hb
      have h1 := (Finset.ext_iff.mp hpair (((cellAtomPairEquiv N α).lo : ℕ) + 1)).mp (by simp)
      have h2 := (Finset.ext_iff.mp hpair (((cellAtomPairEquiv N α).hi : ℕ) + 1)).mp (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
      omega
    · omega

/-- **The 1-cells are Artin's generators.** -/
noncomputable def genArtinEquiv (N : ℕ) : Gen (zRun N) (zRun N) ≃ artinBP.S N :=
  (genRunAtomEquiv N).trans (runAtomEquiv N).symm

/-- **The 2-cells are Artin's relations**, one per pair of cuts. -/
noncomputable def relArtinEquiv (N : ℕ) : Cell 2 (zRun N) (zRun N) ≃ artinBP.Rel N :=
  (cellAtomPairEquiv N).trans (artinRelEquiv N)

end ChainCat.Paper
