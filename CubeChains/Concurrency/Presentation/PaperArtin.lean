import CubeChains.Concurrency.Presentation.PaperPresents
import CubeChains.Concurrency.Presentation.ArtinDegreeZero

/-!
# Concurrency/Presentation/PaperArtin — at the base the paper's polygraph is Artin's

A run of `Zbp` is its strand count, so a cell of `Paper.poly Zbp` is a loop and the object it
carries is the only datum on either side:

    Run Zbp ────────────▸ ℕ                                   0-cells
    Cell 1 ──obj──▸ RunAtom N ───▸ Fin (N−1)                   1-cells, the generators
    Cell 2 ──obj──▸ RunSquare N ─▸ AtomPair N ─▸ artinBP.Rel N  2-cells, the relations

A 2-cell's object is one bead of dimension three, or two of dimension two: hexagon and square.  Its
two words are the relation's two sides letter for letter — the first leg is the atom it cuts, the
second the climb its conjugate spells — which is `paperArtinIso`.
-/

universe w u' w₂

open CategoryTheory CategoryTheory.Polygraph BPSet CubeChains Equiv

/-! ## A cell-for-cell morphism of polygraphs is invertible

Everything the inverse has to do is read back along the three bijections; its two boundary laws are
the morphism's own, read through faithfulness on words (`pathsFunctor_faithful'`). -/

namespace CategoryTheory.Polygraph

section Iso

variable {P Q : Polygraph.{w, u', w₂}} (F : Hom P Q) (hobj : Function.Bijective F.pre.obj)
  (hmap : ∀ x y : GenObj P.Gen, Function.Bijective (F.pre.map : (x ⟶ y) → _))
  (htwo : ∀ x y : GenObj P.Gen, Function.Bijective (F.two : P.Rel x y → _))

/-- The 0-cell a 0-cell of the target is the image of. -/
private noncomputable def backObj (x : GenObj Q.Gen) : GenObj P.Gen :=
  (Equiv.ofBijective _ hobj).symm x

private theorem obj_backObj (x : GenObj Q.Gen) : F.pre.obj (backObj F hobj x) = x :=
  (Equiv.ofBijective _ hobj).apply_symm_apply x

private theorem backObj_obj (x : GenObj P.Gen) : backObj F hobj (F.pre.obj x) = x :=
  (Equiv.ofBijective _ hobj).symm_apply_apply x

/-- …and the 1-cell a 1-cell is. -/
private noncomputable def backMap {x y : GenObj Q.Gen} (e : x ⟶ y) :
    backObj F hobj x ⟶ backObj F hobj y :=
  (Equiv.ofBijective _ (hmap (backObj F hobj x) (backObj F hobj y))).symm
    (Quiver.homOfEq e (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm)

private theorem map_backMap {x y : GenObj Q.Gen} (e : x ⟶ y) :
    F.pre.map (backMap F hobj hmap e)
      = Quiver.homOfEq e (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm :=
  (Equiv.ofBijective _ (hmap _ _)).apply_symm_apply _

/-- The generating quiver, read back. -/
private noncomputable def backPre : GenObj Q.Gen ⥤q GenObj P.Gen where
  obj := backObj F hobj
  map := backMap F hobj hmap

private theorem backPre_comp_pre : backPre F hobj hmap ⋙q F.pre = 𝟭q _ :=
  Prefunctor.ext_homOfEq (obj_backObj F hobj) fun _ _ e => map_backMap F hobj hmap e

private theorem map_homOfEq {x y x' y' : GenObj P.Gen} (hx : x = x') (hy : y = y') (e : x ⟶ y) :
    F.pre.map (Quiver.homOfEq e hx hy)
      = Quiver.homOfEq (F.pre.map e) (congrArg F.pre.obj hx) (congrArg F.pre.obj hy) := by
  subst hx; subst hy; rfl

private theorem pre_comp_backPre : F.pre ⋙q backPre F hobj hmap = 𝟭q _ := by
  refine Prefunctor.ext_homOfEq (backObj_obj F hobj) fun x y e => ?_
  exact (hmap _ _).1 ((map_backMap F hobj hmap (F.pre.map e)).trans
    (map_homOfEq F (backObj_obj F hobj x).symm (backObj_obj F hobj y).symm e).symm)

/-- …and the 2-cell a 2-cell is. -/
private noncomputable def backTwo {x y : GenObj Q.Gen} (β : Q.Rel x y) :
    P.Rel (backObj F hobj x) (backObj F hobj y) :=
  (Equiv.ofBijective _ (htwo (backObj F hobj x) (backObj F hobj y))).symm
    (cellCongr Q.Rel (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm β)

private theorem two_backTwo {x y : GenObj Q.Gen} (β : Q.Rel x y) :
    F.two (backTwo F hobj htwo β)
      = cellCongr Q.Rel (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm β :=
  (Equiv.ofBijective _ (htwo _ _)).apply_symm_apply _

private theorem src_cellCongr {x y x' y' : GenObj Q.Gen} (hx : x = x') (hy : y = y')
    (β : Q.Rel x y) : Q.src (cellCongr Q.Rel hx hy β) = cellCongr Quiver.Path hx hy (Q.src β) := by
  subst hx; subst hy; rfl

private theorem tgt_cellCongr {x y x' y' : GenObj Q.Gen} (hx : x = x') (hy : y = y')
    (β : Q.Rel x y) : Q.tgt (cellCongr Q.Rel hx hy β) = cellCongr Quiver.Path hx hy (Q.tgt β) := by
  subst hx; subst hy; rfl

private theorem mapPath_of_eq {V : Type*} [Quiver V] {W : Type*} [Quiver W] {φ ψ : V ⥤q W}
    (h : φ = ψ) {x y : V} (w : Quiver.Path x y) :
    φ.mapPath w = cellCongr Quiver.Path (congrArg (fun π : V ⥤q W => π.obj x) h).symm
      (congrArg (fun π : V ⥤q W => π.obj y) h).symm (ψ.mapPath w) := by
  subst h; rfl

private theorem back_src {x y : GenObj Q.Gen} (β : Q.Rel x y) :
    P.src (backTwo F hobj htwo β) = (backPre F hobj hmap).mapPath (Q.src β) := by
  haveI := pathsFunctor_faithful' F hobj hmap
  have h1 : F.pre.mapPath (P.src (backTwo F hobj htwo β))
      = cellCongr Quiver.Path (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm (Q.src β) :=
    (F.src_two (backTwo F hobj htwo β)).symm.trans
      ((congrArg Q.src (two_backTwo F hobj htwo β)).trans (src_cellCongr _ _ β))
  have h2 : F.pre.mapPath ((backPre F hobj hmap).mapPath (Q.src β))
      = cellCongr Quiver.Path (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm (Q.src β) :=
    (Prefunctor.mapPath_comp_apply (backPre F hobj hmap) F.pre (Q.src β)).symm.trans
      ((mapPath_of_eq (backPre_comp_pre F hobj hmap) (Q.src β)).trans
        (congrArg (cellCongr Quiver.Path _ _) (Prefunctor.mapPath_id (Q.src β))))
  exact F.pre.pathsFunctor.map_injective (h1.trans h2.symm)

private theorem back_tgt {x y : GenObj Q.Gen} (β : Q.Rel x y) :
    P.tgt (backTwo F hobj htwo β) = (backPre F hobj hmap).mapPath (Q.tgt β) := by
  haveI := pathsFunctor_faithful' F hobj hmap
  have h1 : F.pre.mapPath (P.tgt (backTwo F hobj htwo β))
      = cellCongr Quiver.Path (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm (Q.tgt β) :=
    (F.tgt_two (backTwo F hobj htwo β)).symm.trans
      ((congrArg Q.tgt (two_backTwo F hobj htwo β)).trans (tgt_cellCongr _ _ β))
  have h2 : F.pre.mapPath ((backPre F hobj hmap).mapPath (Q.tgt β))
      = cellCongr Quiver.Path (obj_backObj F hobj x).symm (obj_backObj F hobj y).symm (Q.tgt β) :=
    (Prefunctor.mapPath_comp_apply (backPre F hobj hmap) F.pre (Q.tgt β)).symm.trans
      ((mapPath_of_eq (backPre_comp_pre F hobj hmap) (Q.tgt β)).trans
        (congrArg (cellCongr Quiver.Path _ _) (Prefunctor.mapPath_id (Q.tgt β))))
  exact F.pre.pathsFunctor.map_injective (h1.trans h2.symm)

/-- The morphism, read back. -/
private noncomputable def back : Hom Q P where
  pre := backPre F hobj hmap
  two := backTwo F hobj htwo
  src_two := back_src F hobj hmap htwo
  tgt_two := back_tgt F hobj hmap htwo

private theorem two_cellCongr {x y x' y' : GenObj P.Gen} (hx : x = x') (hy : y = y')
    (γ : P.Rel x y) : F.two (cellCongr P.Rel hx hy γ)
      = cellCongr Q.Rel (congrArg F.pre.obj hx) (congrArg F.pre.obj hy) (F.two γ) := by
  subst hx; subst hy; rfl

private theorem backTwo_two {x y : GenObj P.Gen} (α : P.Rel x y) :
    cellCongr P.Rel (backObj_obj F hobj x) (backObj_obj F hobj y)
      (backTwo F hobj htwo (F.two α)) = α := by
  refine (htwo x y).1 ?_
  rw [two_cellCongr, two_backTwo, cellCongr_trans]
  exact cellCongr_self Q.Rel _ _ (F.two α)

/-- **A morphism bijective in every dimension is an isomorphism.** -/
noncomputable def isoOfBijective : P ≅ Q where
  hom := F
  inv := back F hobj hmap htwo
  hom_inv_id := Hom.ext' (pre_comp_backPre F hobj hmap) fun α =>
    (cellCongr_heq P.Rel (backObj_obj F hobj _) (backObj_obj F hobj _) _).symm.trans
      (heq_of_eq (backTwo_two F hobj htwo α))
  inv_hom_id := Hom.ext' (backPre_comp_pre F hobj hmap) fun β =>
    (heq_of_eq (two_backTwo F hobj htwo β)).trans (cellCongr_heq Q.Rel _ _ β)

end Iso

end CategoryTheory.Polygraph

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

theorem zRun_injective : Function.Injective zRun := zRunEquiv.symm.injective

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

/-- **The 1-cells are Artin's generators.** -/
noncomputable def genArtinEquiv (N : ℕ) : Gen (zRun N) (zRun N) ≃ artinBP.S N :=
  (genRunAtomEquiv N).trans (runAtomEquiv N).symm

/-- The 1-cell at the run whose object is the `k`-th atom's shape. -/
noncomputable def atomGen (N : ℕ) (k : Fin (N - 1)) : Gen (zRun N) (zRun N) :=
  genOfRunAtom (runAtom N k)

@[simp] theorem obj_atomGen (N : ℕ) (k : Fin (N - 1)) :
    (atomGen N k).obj = zObj (atomComp N k) := rfl

@[simp] theorem genArtinEquiv_symm (N : ℕ) (k : Fin (N - 1)) :
    (genArtinEquiv N).symm k = atomGen N k := rfl

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

/-- **A 2-cell is a pair of cuts** — adjacent for the hexagon, apart for the square
(`AtomPair.adj_or_apart`). -/
noncomputable def cellAtomPairEquiv (N : ℕ) : Cell 2 (zRun N) (zRun N) ≃ AtomPair N :=
  (cellRunSquareEquiv N).trans (runSquareEquiv N).symm

/-- **The 2-cells are Artin's relations**, one per pair of cuts. -/
noncomputable def relArtinEquiv (N : ℕ) : Cell 2 (zRun N) (zRun N) ≃ artinBP.Rel N :=
  (cellAtomPairEquiv N).trans (artinRelEquiv N)

/-- **A 2-cell's object is one bead of dimension three, or two beads of dimension two** — the
hexagon's shape and the square's, the rest of the beads edges, and the capacity tells them apart. -/
theorem cell_species {N : ℕ} (α : Cell 2 (zRun N) (zRun N)) :
    ((∃ l r : List ℕ+, (zRun N).dims = l ++ 1 :: 1 :: 1 :: r ∧ α.obj.dims = l ++ 3 :: r)
        ∧ crossCap α.obj.dims = 3)
      ∨ ((∃ l m r : List ℕ+, (zRun N).dims = l ++ 1 :: 1 :: (m ++ 1 :: 1 :: r) ∧
          α.obj.dims = l ++ 2 :: (m ++ 2 :: r)) ∧ crossCap α.obj.dims = 2) :=
  crossCap_of_codim_eq_two α.hom (degree_ones N) α.codim_hom

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

/-- **Adjacent cuts share one bead of three** — the hexagon's shape, read off `boundaries`. -/
theorem dims_obj_of_adj {N : ℕ} (α : Cell 2 (zRun N) (zRun N))
    (hadj : ((cellAtomPairEquiv N α).hi : ℕ) = ((cellAtomPairEquiv N α).lo : ℕ) + 1) :
    α.obj.dims = 𝟙^((cellAtomPairEquiv N α).lo : ℕ) ++ (3 : ℕ+)
      :: 𝟙^(N - ((cellAtomPairEquiv N α).lo : ℕ) - 3) := by
  have hlo := (cellAtomPairEquiv N α).lo.isLt
  have hhi := (cellAtomPairEquiv N α).hi.isLt
  refine boundaries_injective ?_
  rw [boundaries_obj α, boundaries_three_bead]
  ext t
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  omega

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
    rw [dims_obj_of_adj α h]
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

/-! ## The word a cut reads, letter by letter

`cutWord` conjugates a cut onto the runs: out of a run it is the atom itself, and otherwise the
climb of atoms `genClimb` picks.  A climb is pinned by its length (`Climb.eq_cons_nil`), so at
length one and two the word is forced — which is all the two species need. -/

variable {K : BPSet}

/-- A 1-cell, read as a one-letter word. -/
noncomputable abbrev genWord {X Y : Run K} (α : Gen X Y) : Quiver.Path (runPt X) (runPt Y) :=
  (Polygraph.cell (P := poly K) α).toPath

/-- **A letter is its object**, read at other names for its two ends. -/
theorem genWord_congr {X Y X' Y' : Run K} (hx : X = X') (hy : Y = Y')
    {α : Gen X Y} {β : Gen X' Y'} (h : α.obj = β.obj) :
    readAt hx hy (genWord α) = genWord β := by
  subst hx; subst hy
  exact congrArg (fun γ : Gen X Y => genWord γ) (Cell.ext h)

theorem readAt_cons {X Y Z X' Y' Z' : Run K} (hx : X = X') (hy : Y = Y') (hz : Z = Z')
    (p : Quiver.Path (runPt X) (runPt Y)) {L : Gen Y Z} {L' : Gen Y' Z'} (hL : L.obj = L'.obj) :
    readAt hx hz (p.cons L) = (readAt hx hy p).cons L' := by
  subst hx; subst hy; subst hz
  exact congrArg (fun M : Gen Y Z => p.cons M) (Cell.ext hL)

theorem readAt_trans {X Y X' Y' X'' Y'' : Run K} (hx : X = X') (hy : Y = Y') (hx' : X' = X'')
    (hy' : Y' = Y'') (p : Quiver.Path (runPt X) (runPt Y)) :
    readAt hx' hy' (readAt hx hy p) = readAt (hx.trans hx') (hy.trans hy') p := by
  subst hx; subst hy; subst hx'; subst hy'; rfl

/-- **A cut out of a run reads as one letter** — the kept 1-cell is the object it lands on. -/
theorem cutWord_of_run {X : Run K} {e : Ch K} (he : degree e = 1) {u : X.chain ⟶ e}
    (hu : codim u = 1) (hW : ¬ W K u) :
    cutWord u hu = readAt rfl (bottomRun_self X).symm (genWord (genOfHom he hW)) := by
  have hrc : RunCut (chGenOf u hu hW) := eltRep_chV X
  have h1 : cutWord u hu = runPre.mapPath
      ((keptCell (P := (chContraction K).poly) RunCut (chGenOf u hu hW) hrc).toPath) := by
    rw [cutWord, dif_neg hW,
      keptWord_congr _ (runCellWord_self (chGenOf u hu hW) hrc) _
        (Quiver.Path.all_toPath.mpr hrc), keptWord_toPath _ _ hrc]
    exact rfl
  refine h1.trans ((Prefunctor.mapPath_toPath runPre _).trans ?_)
  exact (genWord_congr (α := genOfHom he hW) (β := genOfRunCut (chGenOf u hu hW) hrc)
    rfl (bottomRun_self X).symm (obj_genOfRunCut _ hrc).symm).symm

/-- The word of 1-cells a climb of atoms spells, read on the runs. -/
noncomputable def climbWord {N : ℕ} {z : (chCutPoly K).V} {a b : RunPerm N z}
    (R : Climb (runDescents N z).perm a b) :
    Quiver.Path (runPt (runOfV (runObj a))) (runPt (runOfV (runObj b))) :=
  runPre.mapPath (keptWord (P := (chContraction K).poly) RunCut (climbPath R) (all_climbPath R))

theorem climbWord_nil {N : ℕ} {z : (chCutPoly K).V} {a : RunPerm N z} :
    climbWord (Climb.nil : Climb (runDescents N z).perm a a) = Quiver.Path.nil := rfl

/-- The 1-cell an ascent's atom is, read on the runs. -/
noncomputable abbrev ascGen {N : ℕ} {z : (chCutPoly K).V} {a b : RunPerm N z}
    (e : Ascent (runDescents N z).perm a b) : Gen (runOfV (runObj a)) (runOfV (runObj b)) :=
  genOfRunCut (ascAtom e) (runCut_ascAtom e)

theorem climbWord_cons {N : ℕ} {z : (chCutPoly K).V} {a b v : RunPerm N z}
    (R : Climb (runDescents N z).perm a b) (e : Ascent (runDescents N z).perm b v) :
    climbWord (R.cons e) = (climbWord R).cons (ascGen e) := rfl

private theorem keptWord_cellCongr {P : Polygraph} {T : ∀ {a b : P.V}, P.Gen a b → Prop}
    {x y x' y' : GenObj P.Gen} (hx : x = x') (hy : y = y') (w : Quiver.Path x y)
    (hw : Quiver.Path.All (fun ⦃_ _⦄ e => T e) w)
    (hw' : Quiver.Path.All (fun ⦃_ _⦄ e => T e) (cellCongr Quiver.Path hx hy w)) :
    keptWord T (cellCongr Quiver.Path hx hy w) hw'
      = cellCongr Quiver.Path (congrArg (fun z : GenObj P.Gen => (⟨z.as⟩ : GenObj (keptGen T))) hx)
          (congrArg (fun z : GenObj P.Gen => (⟨z.as⟩ : GenObj (keptGen T))) hy)
          (keptWord T w hw) := by
  subst hx; subst hy; rfl

/-- **A cut that does not start at a run reads as its climb.** -/
theorem cutWord_eq_climbWord {c d : Ch K} {u : c ⟶ d} (hu : codim u = 1) (hW : ¬ W K u)
    (hrc : ¬ RunCut (chGenOf u hu hW)) :
    cutWord u hu = readAt (congrArg runOfV (Subtype.ext (runObj_runBot_gen (chGenOf u hu hW))))
      (congrArg runOfV (Subtype.ext (runObj_genTop (chGenOf u hu hW))))
      (climbWord (genClimb (chGenOf u hu hW))) := by
  have e1 : runCellWord (chGenOf u hu hW)
      = cellCongr Quiver.Path
          (congrArg (chContraction K).poly.pt (Subtype.ext (runObj_runBot_gen (chGenOf u hu hW))))
          (congrArg (chContraction K).poly.pt (Subtype.ext (runObj_genTop (chGenOf u hu hW))))
          (climbPath (genClimb (chGenOf u hu hW))) := by
    rw [runCellWord, dif_neg hrc]
  have e2 : cutWord u hu = runPre.mapPath
      (keptWord (P := (chContraction K).poly) RunCut (runCellWord (chGenOf u hu hW))
        (all_runCellWord (chGenOf u hu hW))) := by
    rw [cutWord, dif_neg hW]
    exact rfl
  refine e2.trans ?_
  refine Eq.trans (congrArg runPre.mapPath
    ((keptWord_congr _ e1 _ ((Quiver.Path.all_cellCongr _ _ _).mpr
      (all_climbPath (genClimb (chGenOf u hu hW))))).trans
      (keptWord_cellCongr _ _ _ (all_climbPath (genClimb (chGenOf u hu hW))) _))) ?_
  exact Prefunctor.mapPath_cellCongr runPre _ _ _

/-- **A cut whose source has a bead does not start at a run.** -/
theorem not_runCut_of_degree_ne_zero {c d : Ch K} {u : c ⟶ d} (hu : codim u = 1) (hW : ¬ W K u)
    (hc : degree c ≠ 0) : ¬ RunCut (chGenOf u hu hW) := fun hrc => by
  have h0 : shOf (chV c) = zObj (𝟙^(dimSum c.dims)) := shOf_eq_ones_of_eltRep hrc rfl
  exact hc ((degree_eq_zero_iff c).mpr fun x hx =>
    List.eq_of_mem_replicate (congrArg ChainCat.Obj.dims h0 ▸ hx))

/-- **A climb of length two is two ascents** — the middle is the climb's own. -/
private theorem climb_eq_cons_cons {n : ℕ} {V : Type} {p : V → Perm (Fin n)}
    (hp : Function.Injective p) {w v : V} (R : Climb p w v)
    (h : permLen (p v) = permLen (p w) + 2) :
    ∃ (b : V) (f₁ : Ascent p w b) (f₂ : Ascent p b v), R = (Climb.nil.cons f₁).cons f₂ := by
  cases R with
  | nil => exact absurd h (by omega)
  | cons R e =>
      obtain ⟨f₁, rfl⟩ := Climb.eq_cons_nil hp R (by have := e.permLen_eq; omega)
      exact ⟨_, f₁, e, rfl⟩

/-- **A pair of adjacent transpositions is read off the permutation it multiplies to**, at whichever
strand count. -/
private theorem idx_eq_of_permCongr {M N : ℕ} (h : N = M) {m : Fin (M - 1)} {j : Fin (N - 1)}
    (hmj : adjT m = (finCongr h).permCongr (adjT j)) : (m : ℕ) = (j : ℕ) := by
  subst h
  exact congrArg Fin.val (adjT_injective hmj)

private theorem idx_pair_eq_of_permCongr {M N : ℕ} (h : N = M) {a b : Fin (M - 1)}
    {i j : Fin (N - 1)} (hij : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1)
    (hab : adjT a * adjT b = (finCongr h).permCongr (adjT i * adjT j))
    (hdesc : (adjT a * adjT b) (adjHi b) < (adjT a * adjT b) (adjLo b)) :
    (a : ℕ) = (i : ℕ) ∧ (b : ℕ) = (j : ℕ) := by
  subst h
  have h0 : adjT a * adjT b = adjT i * adjT j := hab
  obtain rfl : b = j := eq_of_descent_adjT_mul_adjT hij (h0 ▸ hdesc)
  refine ⟨congrArg Fin.val (adjT_injective ?_), rfl⟩
  have h1 := congrArg (fun σ : Perm (Fin N) => σ * adjT b) h0
  simpa only [mul_assoc, adjT_mul_self, mul_one] using h1

/-- **A cut whose conjugated crossing is a single atom spells one letter**, dropping that atom's
junction. -/
theorem cutWord_eq_letter {c d : Ch K} {u : c ⟶ d} (hu : codim u = 1) (hW : ¬ W K u)
    (hdeg : degree c ≠ 0) {N : ℕ} (hc : dimSum c.dims = N) {j : Fin (N - 1)}
    (hτ : crossPerm hc u = adjT j) :
    ∃ β : Gen (bottomRun d) (bottomRun c),
      cutWord u hu = genWord β ∧
        boundaries β.obj.dims = Finset.range (N + 1) \ {(j : ℕ) + 1} := by
  have hrc : ¬ RunCut (chGenOf u hu hW) := not_runCut_of_degree_ne_zero hu hW hdeg
  have hM : dimSum c.dims = vCount (chGenOf u hu hW).dom := dimSum_eq_of_hom u
  have hNM : N = vCount (chGenOf u hu hW).dom := hc.symm.trans hM
  have hperm : (genTop (chGenOf u hu hW)).1 = (finCongr hNM).permCongr (adjT j) := by
    refine (val_eq_crossPerm (genCut (chGenOf u hu hW)) hM (arr_runOf _).symm).trans ?_
    refine Eq.trans (crossPerm_eq_of_φ (g := genCut (chGenOf u hu hW)) (g' := u) hM rfl) ?_
    rw [crossPerm_recount hc hM u, hτ]
  have hlen : permLen (genTop (chGenOf u hu hW)).1 = 1 := by
    rw [hperm, permLen_permCongr_finCongr, permLen_adjT]
  obtain ⟨e, hR⟩ := Climb.eq_cons_nil
    (runDescents (vCount (chGenOf u hu hW).dom) (chGenOf u hu hW).dom).perm_inj
    (genClimb (chGenOf u hu hW))
    (by rw [runDescents_perm, runDescents_perm, runBot_val, permLen_one, hlen])
  have hstep : (genTop (chGenOf u hu hW)).1 = adjT e.idx := by simpa using e.perm_eq
  have hidx : (e.idx : ℕ) = (j : ℕ) := idx_eq_of_permCongr hNM (hstep.symm.trans hperm)
  refine ⟨cellCongr (Cell 1)
    (congrArg runOfV (Subtype.ext (runObj_runBot_gen (chGenOf u hu hW))))
    (congrArg runOfV (Subtype.ext (runObj_genTop (chGenOf u hu hW)))) (ascGen e), ?_, ?_⟩
  · rw [cutWord_eq_climbWord hu hW hrc, hR, climbWord_cons, climbWord_nil]
    exact genWord_congr _ _ (obj_cellCongr _ _ _).symm
  · rw [obj_cellCongr, obj_genOfRunCut,
      show (vChain (ascAtom e).dom).dims = atomComp (vCount (chGenOf u hu hW).dom) e.idx from rfl,
      boundaries_atomComp, hidx, ← hNM]

/-- **…and one whose conjugated crossing is a consecutive pair spells two.** -/
theorem cutWord_eq_letters {c d : Ch K} {u : c ⟶ d} (hu : codim u = 1) (hW : ¬ W K u)
    (hdeg : degree c ≠ 0) {N : ℕ} (hc : dimSum c.dims = N) {i j : Fin (N - 1)}
    (hij : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1)
    (hτ : crossPerm hc u = adjT i * adjT j) :
    ∃ (Z : Run K) (β₁ : Gen (bottomRun d) Z) (β₂ : Gen Z (bottomRun c)),
      cutWord u hu = (genWord β₁).comp (genWord β₂) ∧
        boundaries β₁.obj.dims = Finset.range (N + 1) \ {(i : ℕ) + 1} ∧
        boundaries β₂.obj.dims = Finset.range (N + 1) \ {(j : ℕ) + 1} := by
  have hrc : ¬ RunCut (chGenOf u hu hW) := not_runCut_of_degree_ne_zero hu hW hdeg
  have hM : dimSum c.dims = vCount (chGenOf u hu hW).dom := dimSum_eq_of_hom u
  have hNM : N = vCount (chGenOf u hu hW).dom := hc.symm.trans hM
  have hperm : (genTop (chGenOf u hu hW)).1
      = (finCongr hNM).permCongr (adjT i * adjT j) := by
    refine (val_eq_crossPerm (genCut (chGenOf u hu hW)) hM (arr_runOf _).symm).trans ?_
    refine Eq.trans (crossPerm_eq_of_φ (g := genCut (chGenOf u hu hW)) (g' := u) hM rfl) ?_
    rw [crossPerm_recount hc hM u, hτ]
  have hlen : permLen (genTop (chGenOf u hu hW)).1 = 2 := by
    rw [hperm, permLen_permCongr_finCongr,
      permLen_mul_adjT (adjT_ascent_of_ne (by omega : (j : ℕ) ≠ (i : ℕ))), permLen_adjT]
  obtain ⟨b, e₁, e₂, hR⟩ := climb_eq_cons_cons
    (runDescents (vCount (chGenOf u hu hW).dom) (chGenOf u hu hW).dom).perm_inj
    (genClimb (chGenOf u hu hW)) (by simpa using hlen)
  have hb : b.1 = adjT e₁.idx := by simpa using e₁.perm_eq
  have htop : (genTop (chGenOf u hu hW)).1 = adjT e₁.idx * adjT e₂.idx := by
    have h2 := e₂.perm_eq
    rw [runDescents_perm, runDescents_perm, hb] at h2
    exact h2
  obtain ⟨hi₁, hi₂⟩ := idx_pair_eq_of_permCongr hNM hij (htop.symm.trans hperm)
    (by rw [← htop]; simpa using e₂.descent)
  have hx : runOfV (runObj (runBot (chGenOf u hu hW).dom rfl)) = bottomRun d :=
    congrArg runOfV (Subtype.ext (runObj_runBot_gen (chGenOf u hu hW)))
  have hy : runOfV (runObj (genTop (chGenOf u hu hW))) = bottomRun c :=
    congrArg runOfV (Subtype.ext (runObj_genTop (chGenOf u hu hW)))
  refine ⟨runOfV (runObj b), cellCongr (Cell 1) hx rfl (ascGen e₁),
    cellCongr (Cell 1) rfl hy (ascGen e₂), ?_, ?_, ?_⟩
  · have h1 : cutWord u hu = readAt hx hy ((genWord (ascGen e₁)).comp (genWord (ascGen e₂))) := by
      rw [cutWord_eq_climbWord hu hW hrc, hR, climbWord_cons, climbWord_cons, climbWord_nil]
      exact rfl
    refine h1.trans ((cellCongr_comp (congrArg runPt hx) rfl (congrArg runPt hy)
      (genWord (ascGen e₁)) (genWord (ascGen e₂))).symm.trans ?_)
    exact congrArg₂ Quiver.Path.comp (genWord_congr hx rfl (obj_cellCongr hx rfl (ascGen e₁)).symm)
      (genWord_congr rfl hy (obj_cellCongr rfl hy (ascGen e₂)).symm)
  · rw [obj_cellCongr, obj_genOfRunCut,
      show (vChain (ascAtom e₁).dom).dims
        = atomComp (vCount (chGenOf u hu hW).dom) e₁.idx from rfl,
      boundaries_atomComp, hi₁, ← hNM]
  · rw [obj_cellCongr, obj_genOfRunCut,
      show (vChain (ascAtom e₂).dom).dims
        = atomComp (vCount (chGenOf u hu hW).dom) e₂.idx from rfl,
      boundaries_atomComp, hi₂, ← hNM]

/-! ## The two words a 2-cell reads

A 2-cell's refinement is the greatest cut out of the run onto its object, so it inverts both
junctions it drops (`descent_of_nonempty_atomComp`) and its crossing is the pair's longest word.
Factoring at either junction, the atom is the word's last letter and the rest is what the other cut
conjugates to — one letter at cuts apart, two at consecutive ones. -/

theorem factorWords_eq {X : Run K} {b : Ch K} {u : X.chain ⟶ b} (hu : codim u = 2) {ε : Bool}
    {F : OneCut u} (hF : (oneCutEquivBool u hu).symm ε = F) :
    factorWords u hu ε = readAt rfl (bottomRun_self X)
      ((cutWord F.1.snd (F.codim_snd hu)).comp (cutWord F.1.fst F.2)) := by
  subst hF; rfl

variable {N : ℕ} (α : Cell 2 (zRun N) (zRun N))

theorem cutsOf_cell_hom : cutsOf α.hom
    = {((cellAtomPairEquiv N α).lo : ℕ) + 1, ((cellAtomPairEquiv N α).hi : ℕ) + 1} := by
  rw [cutsOf, show ((zRun N).chain).dims = 𝟙^N from rfl, boundaries_ones, boundaries_obj α,
    Finset.sdiff_sdiff_eq_self (cellAtomPairEquiv N α).junctions_subset]

theorem permLen_crossPerm_cell_hom :
    permLen (crossPerm (dimSum_replicate N) α.hom) = crossCap α.obj.dims :=
  (permLen_crossPerm (dimSum_eq_of_hom α.hom) (dimSum_replicate N) α.hom).trans
    (permLen_runCross_hom α)

/-- **Either cut of a 2-cell is parabolic in its object** — it drops that junction. -/
theorem nonempty_atomComp_obj {k : Fin (N - 1)}
    (hk : (k : ℕ) = ((cellAtomPairEquiv N α).lo : ℕ)
      ∨ (k : ℕ) = ((cellAtomPairEquiv N α).hi : ℕ)) :
    Nonempty (zObj (atomComp N k) ⟶ α.obj) := by
  refine nonempty_hom_iff.mpr ⟨?_, ?_⟩
  · rw [zObj_dims, dimSum_atomComp]
    exact (α.dimSum_obj.trans (dimSum_zRun N)).symm
  · rw [zObj_dims, boundaries_atomComp, boundaries_obj α]
    intro t ht
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at ht
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨ht.1, fun hc => ht.2 ?_⟩
    rcases hk with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- **…so the 2-cell's crossing inverts it.** -/
theorem descent_cell_hom {k : Fin (N - 1)}
    (hk : (k : ℕ) = ((cellAtomPairEquiv N α).lo : ℕ)
      ∨ (k : ℕ) = ((cellAtomPairEquiv N α).hi : ℕ)) :
    crossPerm (dimSum_replicate N) α.hom (adjHi k)
      < crossPerm (dimSum_replicate N) α.hom (adjLo k) :=
  descent_of_nonempty_atomComp (permLen_crossPerm_cell_hom α) (nonempty_atomComp_obj α hk)

theorem crossCap_obj_of_adj (hadj : ((cellAtomPairEquiv N α).hi : ℕ)
      = ((cellAtomPairEquiv N α).lo : ℕ) + 1) : crossCap α.obj.dims = 3 := by
  have h3 : permLen (Fin.revPerm : Perm (Fin ((3 : ℕ+) : ℕ))) = 3 := by decide
  rw [dims_obj_of_adj α hadj, crossCap_append, crossCap_cons, crossCap_replicate_one,
    crossCap_replicate_one, h3]

theorem crossCap_obj_of_apart (hfar : ((cellAtomPairEquiv N α).lo : ℕ) + 1
      < ((cellAtomPairEquiv N α).hi : ℕ)) : crossCap α.obj.dims = 2 :=
  crossCap_eq_two_of_cuts_apart α.hom α.codim_hom (cutsOf_cell_hom α) (by omega)

/-- **At consecutive cuts the 2-cell's crossing is their braid word.** -/
theorem crossPerm_cell_hom_of_adj (hadj : ((cellAtomPairEquiv N α).hi : ℕ)
      = ((cellAtomPairEquiv N α).lo : ℕ) + 1) :
    crossPerm (dimSum_replicate N) α.hom
      = adjT (cellAtomPairEquiv N α).lo * adjT (cellAtomPairEquiv N α).hi
        * adjT (cellAtomPairEquiv N α).lo :=
  eq_braid_of_descents hadj (descent_cell_hom α (Or.inl rfl)) (descent_cell_hom α (Or.inr rfl))
    ((permLen_crossPerm_cell_hom α).trans (crossCap_obj_of_adj α hadj))

/-- **…and at cuts apart their commuting product.** -/
theorem crossPerm_cell_hom_of_apart (hfar : ((cellAtomPairEquiv N α).lo : ℕ) + 1
      < ((cellAtomPairEquiv N α).hi : ℕ)) :
    crossPerm (dimSum_replicate N) α.hom
      = adjT (cellAtomPairEquiv N α).hi * adjT (cellAtomPairEquiv N α).lo :=
  eq_adjT_mul_adjT_of_descents hfar (descent_cell_hom α (Or.inl rfl))
    (descent_cell_hom α (Or.inr rfl))
    ((permLen_crossPerm_cell_hom α).trans (crossCap_obj_of_apart α hfar))

/-- **The greatest cut factored at one of its two junctions** — the atom goes first. -/
theorem exists_leg_cell {k : Fin (N - 1)}
    (hk : (k : ℕ) = ((cellAtomPairEquiv N α).lo : ℕ)
      ∨ (k : ℕ) = ((cellAtomPairEquiv N α).hi : ℕ)) :
    ∃ w : zObj (atomComp N k) ⟶ α.obj, atomOnes N k ≫ w = α.hom := by
  have hd : dimSum α.obj.dims = N := α.dimSum_obj.trans (dimSum_zRun N)
  obtain ⟨r, hr⟩ := exists_run_mul_adjT hd α.hom (descent_cell_hom α hk)
  obtain ⟨w, hw⟩ := exists_leg k hd (nonempty_atomComp_obj α hk)
    (adjT_ascent_of_descent (descent_cell_hom α hk)) hr
  refine ⟨w, hom_ext_of_crossPerm (h := dimSum_replicate N) ?_⟩
  rw [crossPerm_comp, hw, crossPerm_atomOnes, mul_assoc, adjT_mul_self, mul_one]
  exact rfl

theorem codim_leg_cell {k : Fin (N - 1)} {w : zObj (atomComp N k) ⟶ α.obj}
    (hw : atomOnes N k ≫ w = α.hom) : codim w = 1 := by
  have h : codim α.hom = codim (atomOnes N k) + codim w := hw ▸ codim_comp (atomOnes N k) w
  have h2 : codim α.hom = 2 := α.codim_hom
  rw [codim_atomOnes] at h
  omega

/-- **The second leg crosses what the first one leaves.** -/
theorem crossPerm_leg_cell {k : Fin (N - 1)} {w : zObj (atomComp N k) ⟶ α.obj}
    (hw : atomOnes N k ≫ w = α.hom) :
    crossPerm (dimSum_atomComp N k) w = crossPerm (dimSum_replicate N) α.hom * adjT k := by
  have h : crossPerm (dimSum_replicate N) (atomOnes N k ≫ w)
      = crossPerm (dimSum_atomComp N k) w * adjT k :=
    (crossPerm_comp (dimSum_replicate N) (atomOnes N k) w).trans
      (congrArg (fun σ => crossPerm (dimSum_atomComp N k) w * σ) (crossPerm_atomOnes N k))
  rw [hw] at h
  exact ((congrArg (fun σ => σ * adjT k) h).trans
    (by rw [mul_assoc, adjT_mul_self, mul_one])).symm

theorem not_W_leg_cell {k j : Fin (N - 1)} {w : zObj (atomComp N k) ⟶ α.obj}
    (hτ : crossPerm (dimSum_atomComp N k) w = adjT j) : ¬ W Zbp w := fun hW =>
  adjT_ne_one j (hτ.symm.trans (crossPerm_eq_one_of_W _ hW))

theorem not_W_leg_cell_pair {k i j : Fin (N - 1)} {w : zObj (atomComp N k) ⟶ α.obj}
    (hne : (i : ℕ) ≠ (j : ℕ)) (hτ : crossPerm (dimSum_atomComp N k) w = adjT i * adjT j) :
    ¬ W Zbp w := fun hW =>
  adjT_mul_adjT_ne_one hne (hτ.symm.trans (crossPerm_eq_one_of_W _ hW))

/-- The factorisation of a 2-cell's refinement whose first cut is the `k`-th atom. -/
def cellOneCut {k : Fin (N - 1)} {w : zObj (atomComp N k) ⟶ α.obj}
    (hw : atomOnes N k ≫ w = α.hom) : OneCut α.hom :=
  ⟨⟨zObj (atomComp N k), atomOnes N k, w, hw⟩, codim_atomOnes N k⟩

/-- **The two cuts of a 2-cell are consecutive junctions exactly when its pair is adjacent.** -/
theorem cutsAdjacent_cell_hom_iff : CutsAdjacent α.hom
    ↔ ((cellAtomPairEquiv N α).hi : ℕ) = ((cellAtomPairEquiv N α).lo : ℕ) + 1 := by
  have hlt := (cellAtomPairEquiv N α).lt
  have hhi := (cellAtomPairEquiv N α).hi.isLt
  constructor
  · intro hadj
    by_contra hne
    have hu : ((cellAtomPairEquiv N α).lo : ℕ) + 2 ∈ boundaries ((zRun N).chain).dims := by
      rw [show ((zRun N).chain).dims = 𝟙^N from rfl, boundaries_ones, Finset.mem_range]
      omega
    exact hadj (((cellAtomPairEquiv N α).lo : ℕ) + 1) (by rw [cutsOf_cell_hom α]; simp)
      (((cellAtomPairEquiv N α).hi : ℕ) + 1) (by rw [cutsOf_cell_hom α]; simp)
      (((cellAtomPairEquiv N α).lo : ℕ) + 2) hu ⟨by omega, by omega⟩
  · intro hadj s hs t ht u hu
    rw [cutsOf_cell_hom α, Finset.mem_insert, Finset.mem_singleton] at hs ht
    rintro ⟨h1, h2⟩
    omega

/-- **The factorisation at the lower cut is the `false` side at consecutive cuts and the `true` side
at cuts apart.** -/
theorem oneCutEquivBool_cell {wlo : zObj (atomComp N (cellAtomPairEquiv N α).lo) ⟶ α.obj}
    {whi : zObj (atomComp N (cellAtomPairEquiv N α).hi) ⟶ α.obj}
    (hlo : atomOnes N (cellAtomPairEquiv N α).lo ≫ wlo = α.hom)
    (hhi : atomOnes N (cellAtomPairEquiv N α).hi ≫ whi = α.hom) :
    (CutsAdjacent α.hom →
        oneCutEquivBool α.hom α.codim_hom (cellOneCut α hlo) = false ∧
          oneCutEquivBool α.hom α.codim_hom (cellOneCut α hhi) = true) ∧
      (¬ CutsAdjacent α.hom →
        oneCutEquivBool α.hom α.codim_hom (cellOneCut α hlo) = true ∧
          oneCutEquivBool α.hom α.codim_hom (cellOneCut α hhi) = false) := by
  refine oneCutEquivBool_of_lt α.codim_hom ?_
  rw [coe_oneCutEquivCuts (cellOneCut α hlo) (cutsOf_atomOnes N _),
    coe_oneCutEquivCuts (cellOneCut α hhi) (cutsOf_atomOnes N _)]
  have := (cellAtomPairEquiv N α).lt
  omega

/-- **A 2-cell's word at the factorisation whose first cut is the `k`-th atom** — that atom is the
word's last letter. -/
theorem cellWords_eq_cons {k : Fin (N - 1)} {w : zObj (atomComp N k) ⟶ α.obj}
    (hw : atomOnes N k ≫ w = α.hom) {ε : Bool}
    (hε : oneCutEquivBool α.hom α.codim_hom (cellOneCut α hw) = ε) :
    cellWords α ε
      = (readAt α.below ((bottomRun_eq_zRun (zObj (atomComp N k))).trans
          (congrArg zRun (dimSum_atomComp N k)))
          (cutWord w (codim_leg_cell α hw))).cons (atomGen N k) := by
  have hm : bottomRun (zObj (atomComp N k)) = zRun N :=
    (bottomRun_eq_zRun (zObj (atomComp N k))).trans (congrArg zRun (dimSum_atomComp N k))
  have hq : cutWord (atomOnes N k) (codim_atomOnes N k)
      = genWord (cellCongr (Cell 1) rfl (bottomRun_self (zRun N)).symm
          (genOfHom (degree_atomComp N k) (not_W_atomOnes N k))) :=
    (cutWord_of_run (degree_atomComp N k) (codim_atomOnes N k) (not_W_atomOnes N k)).trans
      (genWord_congr rfl (bottomRun_self (zRun N)).symm (obj_cellCongr _ _ _).symm)
  have hF : (oneCutEquivBool α.hom α.codim_hom).symm ε = cellOneCut α hw :=
    (oneCutEquivBool α.hom α.codim_hom).injective ((Equiv.apply_symm_apply _ ε).trans hε.symm)
  have hfw : factorWords α.hom α.codim_hom ε
      = readAt rfl (bottomRun_self (zRun N))
          ((cutWord w (codim_leg_cell α hw)).comp
            (cutWord (atomOnes N k) (codim_atomOnes N k))) :=
    factorWords_eq α.codim_hom hF
  refine Eq.trans (congrArg (readAt α.below (rfl : zRun N = zRun N)) (hfw.trans
    (congrArg (readAt rfl (bottomRun_self (zRun N)))
      (congrArg (Quiver.Path.comp (cutWord w (codim_leg_cell α hw))) hq)))) ?_
  refine Eq.trans (congrArg (readAt α.below (rfl : zRun N = zRun N))
    (readAt_cons rfl hm (bottomRun_self (zRun N)) (cutWord w (codim_leg_cell α hw))
      (L' := atomGen N k) (obj_cellCongr _ _ _))) ?_
  refine Eq.trans (readAt_cons α.below (rfl : zRun N = zRun N) (rfl : zRun N = zRun N)
    (readAt rfl hm (cutWord w (codim_leg_cell α hw))) (L' := atomGen N k) rfl) ?_
  exact congrArg (fun t : Quiver.Path (runPt (zRun N)) (runPt (zRun N)) => t.cons (atomGen N k))
    (readAt_trans rfl hm α.below rfl (cutWord w (codim_leg_cell α hw)))

theorem eq_zObj_atomComp_of_boundaries {A : Ch Zbp} {j : Fin (N - 1)}
    (h : boundaries A.dims = Finset.range (N + 1) \ {(j : ℕ) + 1}) : A = zObj (atomComp N j) :=
  Obj.eq_of_dims (boundaries_injective (h.trans (boundaries_atomComp N j).symm))

theorem degree_atomComp_ne_zero (N : ℕ) (k : Fin (N - 1)) :
    degree (zObj (atomComp N k)) ≠ 0 := by rw [degree_atomComp]; exact one_ne_zero

/-- **The word a 2-cell's factorisation reads when its second leg crosses a single atom.** -/
theorem cellWords_eq_two {k j : Fin (N - 1)} {w : zObj (atomComp N k) ⟶ α.obj}
    (hw : atomOnes N k ≫ w = α.hom) (hτ : crossPerm (dimSum_atomComp N k) w = adjT j) {ε : Bool}
    (hε : oneCutEquivBool α.hom α.codim_hom (cellOneCut α hw) = ε) :
    cellWords α ε = (Quiver.Path.nil.cons (atomGen N j)).cons (atomGen N k) := by
  have hm : bottomRun (zObj (atomComp N k)) = zRun N :=
    (bottomRun_eq_zRun (zObj (atomComp N k))).trans (congrArg zRun (dimSum_atomComp N k))
  obtain ⟨β, hword, hb⟩ := cutWord_eq_letter (codim_leg_cell α hw) (not_W_leg_cell α hτ)
    (degree_atomComp_ne_zero N k) (dimSum_atomComp N k) hτ
  refine (cellWords_eq_cons α hw hε).trans (congrArg
    (fun t : Quiver.Path (runPt (zRun N)) (runPt (zRun N)) => t.cons (atomGen N k)) ?_)
  exact (congrArg (readAt α.below hm) hword).trans
    (genWord_congr α.below hm (eq_zObj_atomComp_of_boundaries hb))

/-- …and when it crosses a consecutive pair. -/
theorem cellWords_eq_three {k i j : Fin (N - 1)} {w : zObj (atomComp N k) ⟶ α.obj}
    (hw : atomOnes N k ≫ w = α.hom)
    (hij : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1)
    (hτ : crossPerm (dimSum_atomComp N k) w = adjT i * adjT j) {ε : Bool}
    (hε : oneCutEquivBool α.hom α.codim_hom (cellOneCut α hw) = ε) :
    cellWords α ε
      = ((Quiver.Path.nil.cons (atomGen N i)).cons (atomGen N j)).cons (atomGen N k) := by
  have hm : bottomRun (zObj (atomComp N k)) = zRun N :=
    (bottomRun_eq_zRun (zObj (atomComp N k))).trans (congrArg zRun (dimSum_atomComp N k))
  obtain ⟨Z, β₁, β₂, hword, hb₁, hb₂⟩ := cutWord_eq_letters (codim_leg_cell α hw)
    (not_W_leg_cell_pair α (by omega) hτ) (degree_atomComp_ne_zero N k)
    (dimSum_atomComp N k) hij hτ
  have hZ : Z = zRun N := (Cell.ends_eq β₁).symm.trans α.below
  refine (cellWords_eq_cons α hw hε).trans (congrArg
    (fun t : Quiver.Path (runPt (zRun N)) (runPt (zRun N)) => t.cons (atomGen N k)) ?_)
  refine ((congrArg (readAt α.below hm) hword).trans ?_)
  refine Eq.trans (cellCongr_comp (congrArg runPt α.below) (congrArg runPt hZ)
    (congrArg runPt hm) (genWord β₁) (genWord β₂)).symm ?_
  exact congrArg₂ Quiver.Path.comp
    (genWord_congr (β := atomGen N i) α.below hZ (eq_zObj_atomComp_of_boundaries hb₁))
    (genWord_congr (β := atomGen N j) hZ hm (eq_zObj_atomComp_of_boundaries hb₂))

/-- **A 2-cell at cuts apart reads the square's two words.** -/
theorem cellWords_of_apart (hfar : ((cellAtomPairEquiv N α).lo : ℕ) + 1
      < ((cellAtomPairEquiv N α).hi : ℕ)) :
    cellWords α false = (Quiver.Path.nil.cons (atomGen N (cellAtomPairEquiv N α).lo)).cons
        (atomGen N (cellAtomPairEquiv N α).hi) ∧
      cellWords α true = (Quiver.Path.nil.cons (atomGen N (cellAtomPairEquiv N α).hi)).cons
        (atomGen N (cellAtomPairEquiv N α).lo) := by
  obtain ⟨wlo, hlo⟩ := exists_leg_cell α (Or.inl rfl)
  obtain ⟨whi, hhi⟩ := exists_leg_cell α (Or.inr rfl)
  have hσ := crossPerm_cell_hom_of_apart α hfar
  have hnadj : ¬ CutsAdjacent α.hom := fun h => by
    have := (cutsAdjacent_cell_hom_iff α).mp h
    omega
  obtain ⟨hblo, hbhi⟩ := (oneCutEquivBool_cell α hlo hhi).2 hnadj
  have hτlo : crossPerm (dimSum_atomComp N (cellAtomPairEquiv N α).lo) wlo
      = adjT (cellAtomPairEquiv N α).hi := by
    rw [crossPerm_leg_cell α hlo, hσ, mul_assoc, adjT_mul_self, mul_one]
  have hτhi : crossPerm (dimSum_atomComp N (cellAtomPairEquiv N α).hi) whi
      = adjT (cellAtomPairEquiv N α).lo := by
    rw [crossPerm_leg_cell α hhi, hσ,
      ← adjT_comm (cellAtomPairEquiv N α).lo (cellAtomPairEquiv N α).hi hfar,
      mul_assoc, adjT_mul_self, mul_one]
  exact ⟨cellWords_eq_two α hhi hτhi hbhi, cellWords_eq_two α hlo hτlo hblo⟩

/-- **…and at consecutive cuts the hexagon's.** -/
theorem cellWords_of_adj (hadj : ((cellAtomPairEquiv N α).hi : ℕ)
      = ((cellAtomPairEquiv N α).lo : ℕ) + 1) :
    cellWords α false = ((Quiver.Path.nil.cons (atomGen N (cellAtomPairEquiv N α).lo)).cons
          (atomGen N (cellAtomPairEquiv N α).hi)).cons (atomGen N (cellAtomPairEquiv N α).lo) ∧
      cellWords α true = ((Quiver.Path.nil.cons (atomGen N (cellAtomPairEquiv N α).hi)).cons
          (atomGen N (cellAtomPairEquiv N α).lo)).cons (atomGen N (cellAtomPairEquiv N α).hi) := by
  obtain ⟨wlo, hlo⟩ := exists_leg_cell α (Or.inl rfl)
  obtain ⟨whi, hhi⟩ := exists_leg_cell α (Or.inr rfl)
  have hσ := crossPerm_cell_hom_of_adj α hadj
  obtain ⟨hblo, hbhi⟩ :=
    (oneCutEquivBool_cell α hlo hhi).1 ((cutsAdjacent_cell_hom_iff α).mpr hadj)
  have hτlo : crossPerm (dimSum_atomComp N (cellAtomPairEquiv N α).lo) wlo
      = adjT (cellAtomPairEquiv N α).lo * adjT (cellAtomPairEquiv N α).hi := by
    rw [crossPerm_leg_cell α hlo, hσ,
      mul_assoc (adjT (cellAtomPairEquiv N α).lo * adjT (cellAtomPairEquiv N α).hi),
      adjT_mul_self, mul_one]
  have hτhi : crossPerm (dimSum_atomComp N (cellAtomPairEquiv N α).hi) whi
      = adjT (cellAtomPairEquiv N α).hi * adjT (cellAtomPairEquiv N α).lo := by
    rw [crossPerm_leg_cell α hhi, hσ,
      adjT_braid (cellAtomPairEquiv N α).lo (cellAtomPairEquiv N α).hi hadj,
      mul_assoc (adjT (cellAtomPairEquiv N α).hi * adjT (cellAtomPairEquiv N α).lo),
      adjT_mul_self, mul_one]
  exact ⟨cellWords_eq_three α hlo (Or.inl hadj) hτlo hblo,
    cellWords_eq_three α hhi (Or.inr hadj) hτhi hbhi⟩

/-! ## …which is Artin's presentation -/

/-- **Consecutive cuts spell the hexagon**, in the order the pair is given. -/
theorem artinWords_of_adj {N : ℕ} (p : AtomPair N) (hadj : (p.hi : ℕ) = (p.lo : ℕ) + 1) :
    artinWords p = (FreeMonoid.of p.lo * FreeMonoid.of p.hi * FreeMonoid.of p.lo,
      FreeMonoid.of p.hi * FreeMonoid.of p.lo * FreeMonoid.of p.hi) := by
  unfold artinWords
  rw [if_pos hadj]
  rfl

/-- **…and cuts apart the square.** -/
theorem artinWords_of_apart {N : ℕ} (p : AtomPair N) (hfar : (p.lo : ℕ) + 1 < (p.hi : ℕ)) :
    artinWords p = (FreeMonoid.of p.lo * FreeMonoid.of p.hi,
      FreeMonoid.of p.hi * FreeMonoid.of p.lo) := by
  unfold artinWords
  rw [if_neg (by omega : ¬ ((p.hi : ℕ) = (p.lo : ℕ) + 1))]
  rfl

/-- The strand-`N` leg of the Artin polygraph, read on the cells of the paper's. -/
noncomputable def artinLegPre (N : ℕ) :
    GenObj (artinBP.P N).Gen ⥤q GenObj (Gen (K := Zbp)) where
  obj _ := runPt (zRun N)
  map g := atomGen N g

theorem artinLegPre_mapPath_three (N : ℕ) (a b c : Fin (N - 1)) :
    (artinLegPre N).mapPath (MonoidPoly.path (rels := ArtinRel N)
        (FreeMonoid.of a * FreeMonoid.of b * FreeMonoid.of c))
      = ((Quiver.Path.nil.cons (atomGen N a)).cons (atomGen N b)).cons (atomGen N c) := by
  rw [MonoidPoly.path_mul, MonoidPoly.path_mul, MonoidPoly.path_of, MonoidPoly.path_of,
    MonoidPoly.path_of]
  exact rfl

theorem artinLegPre_mapPath_two (N : ℕ) (a b : Fin (N - 1)) :
    (artinLegPre N).mapPath (MonoidPoly.path (rels := ArtinRel N)
        (FreeMonoid.of a * FreeMonoid.of b))
      = (Quiver.Path.nil.cons (atomGen N a)).cons (atomGen N b) := by
  rw [MonoidPoly.path_mul, MonoidPoly.path_of, MonoidPoly.path_of]
  exact rfl

/-- **A 2-cell's two words are its pair's Artin relation**, spelled in the atoms. -/
theorem cellWords_eq_artinWords (ε : Bool) :
    cellWords α ε = (artinLegPre N).mapPath (MonoidPoly.path (rels := ArtinRel N)
      (cond ε (artinWords (cellAtomPairEquiv N α)).2 (artinWords (cellAtomPairEquiv N α)).1)) := by
  rcases (cellAtomPairEquiv N α).adj_or_apart with hadj | hfar
  · refine Eq.trans ?_ (congrArg (fun l => (artinLegPre N).mapPath
      (MonoidPoly.path (rels := ArtinRel N) (cond ε l.2 l.1)))
      (artinWords_of_adj (cellAtomPairEquiv N α) hadj).symm)
    cases ε
    · exact ((cellWords_of_adj α hadj).1).trans (artinLegPre_mapPath_three N _ _ _).symm
    · exact ((cellWords_of_adj α hadj).2).trans (artinLegPre_mapPath_three N _ _ _).symm
  · refine Eq.trans ?_ (congrArg (fun l => (artinLegPre N).mapPath
      (MonoidPoly.path (rels := ArtinRel N) (cond ε l.2 l.1)))
      (artinWords_of_apart (cellAtomPairEquiv N α) hfar).symm)
    cases ε
    · exact ((cellWords_of_apart α hfar).1).trans (artinLegPre_mapPath_two N _ _).symm
    · exact ((cellWords_of_apart α hfar).2).trans (artinLegPre_mapPath_two N _ _).symm

/-- **The strand-`N` leg of the Artin polygraph is the paper's cells there** — generator to
generator, relation to relation, word for word. -/
noncomputable def artinLegHom (N : ℕ) : artinBP.P N ⟶ poly Zbp where
  pre := artinLegPre N
  two β := (relArtinEquiv N).symm β
  src_two β := (cellWords_eq_artinWords ((relArtinEquiv N).symm β) false).trans
    (congrArg (fun γ : artinBP.Rel N => (artinLegPre N).mapPath ((artinBP.P N).src γ))
      ((relArtinEquiv N).apply_symm_apply β))
  tgt_two β := (cellWords_eq_artinWords ((relArtinEquiv N).symm β) true).trans
    (congrArg (fun γ : artinBP.Rel N => (artinLegPre N).mapPath ((artinBP.P N).tgt γ))
      ((relArtinEquiv N).apply_symm_apply β))

/-- **The Artin polygraph's cells are the paper's at the base**, leg by leg. -/
noncomputable def artinHom : artinBP.poly ⟶ poly Zbp :=
  Polygraph.coprodDescHom artinBP.P artinLegHom

/-- **The 0-cells are the strand counts either way.** -/
noncomputable def artinObjEquiv : GenObj artinBP.poly.Gen ≃ GenObj (Gen (K := Zbp)) where
  toFun A := runPt (zRun A.as.1)
  invFun x := ⟨⟨dimSum x.as.dims, ()⟩⟩
  left_inv A := GenObj.ext (Sigma.ext (dimSum_zRun A.as.1) (by rfl))
  right_inv x := GenObj.ext (eq_zRun x.as).symm

theorem artinHom_obj_bijective : Function.Bijective artinHom.pre.obj :=
  artinObjEquiv.bijective

/-- **The 1-cells at one strand count are its generators, and there are none across counts.** -/
theorem artinHom_map_bijective (A B : GenObj artinBP.poly.Gen) :
    Function.Bijective (artinHom.pre.map : (A ⟶ B) → _) := by
  obtain ⟨⟨M, x⟩⟩ := A
  obtain ⟨⟨M', y⟩⟩ := B
  by_cases hM : M = M'
  · subst hM
    refine ⟨fun e e' h => ?_, fun β => ⟨CoprodGen.mk (genArtinEquiv M β), ?_⟩⟩
    · cases e with
      | mk g =>
          cases e' with
          | mk g' => exact congrArg CoprodGen.mk ((genArtinEquiv M).symm.injective h)
    · exact (genArtinEquiv M).symm_apply_apply β
  · refine ⟨fun e e' h => ?_, fun β => ?_⟩
    · cases e with
      | mk g => exact absurd rfl hM
    · exact absurd (zRun_injective (Cell.ends_eq β)) hM

/-- **…and so are the 2-cells.** -/
theorem artinHom_two_bijective (A B : GenObj artinBP.poly.Gen) :
    Function.Bijective (artinHom.two : artinBP.poly.Rel A B → _) := by
  obtain ⟨⟨M, x⟩⟩ := A
  obtain ⟨⟨M', y⟩⟩ := B
  by_cases hM : M = M'
  · subst hM
    refine ⟨fun γ γ' h => ?_, fun α => ⟨CoprodRel.mk (relArtinEquiv M α), ?_⟩⟩
    · cases γ with
      | @mk _ x₁ y₁ β =>
          cases γ' with
          | @mk _ x₂ y₂ β' =>
              obtain rfl : x₁ = x₂ := GenObj.ext rfl
              obtain rfl : y₁ = y₂ := GenObj.ext rfl
              exact congrArg CoprodRel.mk ((relArtinEquiv M).symm.injective h)
    · exact (relArtinEquiv M).symm_apply_apply α
  · refine ⟨fun γ γ' h => ?_, fun α => ?_⟩
    · cases γ with
      | mk β => exact absurd rfl hM
    · exact absurd (zRun_injective (Cell.ends_eq α)) hM

/-- **At the base the paper's polygraph is Artin's** — cell for cell, word for word. -/
noncomputable def paperArtinIso : poly Zbp ≅ artinBP.poly :=
  (Polygraph.isoOfBijective artinHom artinHom_obj_bijective artinHom_map_bijective
    artinHom_two_bijective).symm

end ChainCat.Paper
