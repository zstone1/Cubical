import CubeChains.Concurrency.Presentation.ElementsFibration
import CubeChains.Concurrency.Grading.TopBead
import CubeChains.Concurrency.Merge.MergeBraid
import CubeChains.Concurrency.Complexification.ChStarSym
import CubeChains.Concurrency.Executions.ExecData
import CubeChains.Concurrency.Complexification.SymOverRun
import CubeChains.Concurrency.Complexification.SymRun

/-!
# Concurrency/Complexification/RunClassifier — the run object, and why `Hbp` is not a product

`Hbp Zbp ≅ runBp` classifies runs bead by bead, and a merge *destroys* run data: the two orders
on a square restrict to the single order on its edges.  So neither the run factor nor the
undecorated cube inverts a merge, and the `desym` bijection
`(⋁d ⟶ Hbp K) ≃ (⋁d ⟶ K.prod runBp)` cannot be natural in `d` without killing
`InvertsMerges (Hbp K)` for every `K`.  The twist is what repairs it.
-/

open CategoryTheory Opposite BPSet CubeChain ChainCat

namespace CubeChains

/-! ## A wedge map into a one-vertex target is its beads

With a single vertex the junction conditions are vacuous, so *any* cube list is a chain: the
beads are free. -/

/-- Over a one-vertex target every cube list is a chain. -/
theorem isCubeChain_of_subsingleton (X : BPSet) [Subsingleton (X.cells 0)] :
    ∀ (l : List (Σ n : ℕ+, X.cells (n : ℕ))) (u v : X.cells 0), IsCubeChain u l v
  | [], u, v => Subsingleton.elim u v
  | ⟨_, _⟩ :: tl, _, v => ⟨Subsingleton.elim _ _, isCubeChain_of_subsingleton X tl _ v⟩

/-- The wedge map with prescribed beads. -/
def ofCells {X : BPSet} [Subsingleton (X.cells 0)] (d : List ℕ+) (r : Beads X.toPsh d) :
    ⋁d ⟶ X :=
  wedgeDescHom r (isCubeChain_of_subsingleton X r.toList _ _)

@[simp] theorem bead_ofCells {X : BPSet} [Subsingleton (X.cells 0)] (d : List ℕ+)
    (r : Beads X.toPsh d) (i : Fin d.length) : bead d (ofCells d r) i = r i :=
  congrFun (beadCell_wedgeDescHom r _) i

/-- The one-bead wedge map on a prescribed cell. -/
def ofCell {X : BPSet} [Subsingleton (X.cells 0)] (m : ℕ+) (c : X.cells (m : ℕ)) : ⋁[m] ⟶ X :=
  ofCells [m] (Fin.cases c fun i => i.elim0)

@[simp] theorem bead_ofCell {X : BPSet} [Subsingleton (X.cells 0)] (m : ℕ+)
    (c : X.cells (m : ℕ)) : bead [m] (ofCell m c) 0 = c := bead_ofCells _ _ 0

/-- **A one-bead wedge map into a one-vertex target is a cell.** -/
def oneBeadEquivCell {X : BPSet} [Subsingleton (X.cells 0)] (m : ℕ+) :
    (⋁[m] ⟶ X) ≃ X.cells (m : ℕ) where
  toFun α := bead [m] α 0
  invFun := ofCell m
  left_inv α := wedgeMap_ext_bead fun i => by
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact bead_ofCell m (bead [m] α 0)
  right_inv := bead_ofCell m

theorem ofCell_injective {X : BPSet} [Subsingleton (X.cells 0)] (m : ℕ+) :
    Function.Injective (ofCell (X := X) m) := (oneBeadEquivCell m).symm.injective

/-- An edge has a single order, so a run of an all-edges wedge is no data. -/
theorem subsingleton_runs_of_ones {d : List ℕ+} (h : ∀ x ∈ d, x = 1) :
    Subsingleton (⋁d ⟶ runBp) := by
  have hcell : ∀ n : ℕ, n = 1 → Subsingleton (runBp.cells n) := by
    rintro n rfl
    exact ⟨fun r s => (runPermEquiv 1).injective (Subsingleton.elim _ _)⟩
  exact ⟨fun u v => wedgeMap_ext_bead fun i =>
    (hcell _ (congrArg PNat.val (h _ (List.get_mem d i)))).elim _ _⟩

/-! ## A merge destroys run data

`Hom(⋁[1,1], runBp)` is a point and `Hom(⋁[2], runBp)` has two elements, so the merge
`⋁[1,1] ⟶ ⋁[2]` cannot act invertibly. -/

/-- The square carries two orders; its edges carry one. -/
theorem runCell_two_ne :
    ((runPermEquiv 2).symm 1 : runBp.cells 2) ≠ (runPermEquiv 2).symm (Equiv.swap 0 1) :=
  fun hc => absurd ((runPermEquiv 2).symm.injective hc) (by decide)

/-- The merge `⋁[1,1] ⟶ ⋁[1+1]` acts bijectively as soon as `K` inverts the merges. -/
theorem bijective_merge11_of_invertsMerges {K : BPSet} (h : InvertsMerges K) :
    Function.Bijective (fun u : ⋁[(1 : ℕ+) + 1] ⟶ K =>
      Hom.φ (mergeHom ([] : List ℕ+) [] 1 1) ≫ u) :=
  (isIso_iff_bijective _).mp (h (mergeHom ([] : List ℕ+) [] 1 1).op (W_mergeHom [] [] 1 1))

/-- **The run object does not invert the merges** — the square's two orders restrict to the same
order on its edges. -/
theorem not_invertsMerges_runBp : ¬ InvertsMerges runBp := fun h => by
  have hsub : Subsingleton (⋁([(1 : ℕ+), 1]) ⟶ runBp) :=
    subsingleton_runs_of_ones (by decide)
  exact runCell_two_ne
    (ofCell_injective _ ((bijective_merge11_of_invertsMerges h).1 (hsub.elim _ _)))

/-! ## The decorated point is the run object -/

instance : Subsingleton ((Hbp.obj Zbp).cells 0) :=
  ⟨fun _ _ => Prod.ext (Equiv.ext fun i => i.elim0) (Subsingleton.elim _ _)⟩

/-- **`Hbp Zbp` is the run object**: a decorated point is an order on its axes, and both sides
have a single vertex, so the bi-pointing costs nothing. -/
def HbpZIsoRun : Hbp.obj Zbp ≅ runBp where
  hom := (homEquivPsh _ runBp).symm HZIsoRun.hom
  inv := (homEquivPsh _ (Hbp.obj Zbp)).symm HZIsoRun.inv
  hom_inv_id := hom_ext HZIsoRun.hom_inv_id
  inv_hom_id := hom_ext HZIsoRun.inv_hom_id

/-- `InvertsMerges` sees `K` only through `wedgeHoms`, hence only up to isomorphism. -/
theorem invertsMerges_of_iso {K L : BPSet} (e : K ≅ L) (h : InvertsMerges K) :
    InvertsMerges L :=
  (MorphismProperty.IsInvertedBy.iff_of_iso ((W Zbp).op)
    (F₁ := wedgeHoms K) (F₂ := wedgeHoms L)
    (Functor.isoWhiskerLeft serialWedgeInclusion.op (yoneda.mapIso e))).mp h

/-- **The decorated point does not invert the merges** — merging forgets which axis went first. -/
theorem not_invertsMerges_Hbp_Zbp : ¬ InvertsMerges (Hbp.obj Zbp) := fun h =>
  not_invertsMerges_runBp (invertsMerges_of_iso HbpZIsoRun h)

/-! ## Nor does the undecorated cube

`runBp` fails *injectivity* — two orders on the square, one on its edges.  `□²` fails
*surjectivity* the other way round: one 2-cell, but two runs to hit.  This is the whole reason `H`
is in the picture. -/

/-- A run of `□²` has dimension sequence `[1, 1]`. -/
private theorem dims_wordChain_two (w : Equiv.Perm (Fin 2)) : (wordChain w).dims = [1, 1] := by
  have : (wordChain w).dims = 𝟙^2 :=
    (eq_replicate_of_ones (ones_wordChain w)).trans (by rw [length_wordChain])
  simpa using this

/-- The two runs of `□²`, as maps out of `⋁[1,1]`. -/
private def runMapTwo (w : Equiv.Perm (Fin 2)) : ⋁[(1 : ℕ+), 1] ⟶ □2 :=
  ⋁≡(dims_wordChain_two w).symm ≫ (wordChain w).map

private theorem chain_runMapTwo (w : Equiv.Perm (Fin 2)) :
    (⟨[1, 1], runMapTwo w⟩ : Ch (□2)) = wordChain w :=
  Obj.mk_eq_mk (dims_wordChain_two w).symm rfl

/-- A chain of `□²` with a single bead is determined: there is only one 2-cell with the right
endpoints. -/
private theorem subsingleton_topMapTwo (z z' : ⋁[(1 + 1 : ℕ+)] ⟶ □2) : z = z' := by
  have h : (⟨[(1 + 1 : ℕ+)], z⟩ : Ch (□2)) = ⟨[(1 + 1 : ℕ+)], z'⟩ :=
    eq_of_beadOf fun q => by
      rw [Nat.lt_one_iff.mp (beadOf (⟨[(1 + 1 : ℕ+)], z⟩ : Ch (□2)) q).isLt,
        Nat.lt_one_iff.mp (beadOf (⟨[(1 + 1 : ℕ+)], z'⟩ : Ch (□2)) q).isLt]
  obtain ⟨hd, hz⟩ := Obj.eq_mk_of_eq h
  rw [hz]
  exact (Category.id_comp z').symm

/-- **The cube alone does not invert the merges.** -/
theorem not_invertsMerges_cube_two : ¬ InvertsMerges (□2) := fun h => by
  obtain ⟨z, hz⟩ := (bijective_merge11_of_invertsMerges h).2 (runMapTwo 1)
  obtain ⟨z', hz'⟩ := (bijective_merge11_of_invertsMerges h).2 (runMapTwo (Equiv.swap 0 1))
  have hch : wordChain (1 : Equiv.Perm (Fin 2)) = wordChain (Equiv.swap 0 1) := by
    rw [← chain_runMapTwo, ← chain_runMapTwo, ← hz, ← hz', subsingleton_topMapTwo z z']
  have h0 : (((1 : Equiv.Perm (Fin 2)).symm 0 : Fin 2) : ℕ)
      = (((Equiv.swap (0 : Fin 2) 1).symm 0 : Fin 2) : ℕ) := by
    rw [← beadOf_wordChain, ← beadOf_wordChain, hch]
  rw [show ((1 : Equiv.Perm (Fin 2)).symm) = 1 from rfl] at h0
  simp at h0

/-! ## The merge that separates the two restrictions

`⋁[2, 1] ⟶ ⋁[3]` merges a square onto the axes `{0, 1}`.  The cyclic order `0 ↦ 1 ↦ 2 ↦ 0`
increases on `{0, 1}`; its inverse decreases there. -/

/-- The cyclic order on three axes. -/
private def cyc3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- The axes `{0, 1}` of `▫3`. -/
private def low2 : Fin 2 → Fin 3 := fun i => ⟨(i : ℕ), by omega⟩

private theorem monotone_cyc3 : Monotone fun i => cyc3 (low2 i) := by decide

private theorem not_monotone_cyc3_inv : ¬ Monotone fun i => cyc3⁻¹ (low2 i) := by decide

/-- The bead merge `⋁[2, 1] ⟶ ⋁[3]`, as a bare wedge map. -/
private def merge21 : ⋁[(2 : ℕ+), 1] ⟶ ⋁[(3 : ℕ+)] := Hom.φ (mergeHom ([] : List ℕ+) [] 2 1)

private theorem pos_merge21 (e : beadEvent [(2 : ℕ+), 1]) :
    (pos (coordMap merge21 e) : ℕ) = (pos e : ℕ) :=
  pos_coordMap_splicePhi_cubeMerge [] [] 2 1 e

/-- The merge's first bead is the face on the axes `{0, 1}`. -/
private theorem exists_face_merge21 :
    ∃ f : ▫2 ⟶ ▫3, ιᵂ [(2 : ℕ+), 1] 0 ≫ merge21.hom = yoneda.map f ≫ ιᵂ [(3 : ℕ+)] 0
      ∧ ∀ k : Fin 2, faceEmb f k = low2 k := by
  obtain ⟨j, f, hfac⟩ : ∃ (j : Fin ([(3 : ℕ+)] : List ℕ+).length)
      (f : ▫((([(2 : ℕ+), 1] : List ℕ+).get 0 : ℕ)) ⟶ ▫((([(3 : ℕ+)] : List ℕ+).get j : ℕ))),
      ιᵂ [(2 : ℕ+), 1] 0 ≫ merge21.hom = yoneda.map f ≫ ιᵂ [(3 : ℕ+)] j :=
    ⟨_, _, blockFace_spec merge21.hom 0⟩
  obtain rfl : j = 0 := Fin.fin_one_eq_zero j
  refine ⟨f, hfac, fun k => Fin.ext ?_⟩
  have h := pos_merge21 ⟨0, k⟩
  rw [coordMap_of_factor merge21 0 0 f hfac k, pos_cons_zero, pos_cons_zero] at h
  exact h

/-- The cyclic run of `⋁[3]`. -/
private def cycRun : ⋁[(3 : ℕ+)] ⟶ runBp := ofCell 3 ((runPermEquiv 3).symm cyc3)

private theorem runPermEquiv_bead_cycRun :
    runPermEquiv ((([(3 : ℕ+)] : List ℕ+).get 0 : ℕ)) (bead [(3 : ℕ+)] cycRun 0) = cyc3 := by
  change runPermEquiv 3 (bead [(3 : ℕ+)] cycRun 0) = cyc3
  rw [cycRun, bead_ofCell, Equiv.apply_symm_apply]

/-- **The twist is not the identity**: along the merge `⋁[2, 1] ⟶ ⋁[3]` the cyclic run
restricts one way twisted and the other way plain. -/
theorem twistRun_merge21_ne : twistRun cycRun merge21 ≠ merge21 ≫ cycRun := by
  obtain ⟨f, hfac, hemb⟩ := exists_face_merge21
  intro hc
  have hb := bead_of_factor merge21 0 0 f hfac
  have h1 := runPermEquiv_bead_twistRun cycRun merge21 0 0 f hb
  have h2 := runPermEquiv_bead_comp cycRun merge21 0 0 f hb
  rw [runPermEquiv_bead_cycRun] at h1 h2
  rw [hc] at h1
  have hkey := h1.symm.trans h2
  have htuple : ∀ σ : Equiv.Perm (Fin 3),
      SHom.sortPerm (J.map f) σ = (Tuple.sort fun i => σ (low2 i))⁻¹ := fun σ => by
    rw [SHom.sortPerm_J_map]
    exact congrArg (fun t => (Tuple.sort t)⁻¹) (funext fun i => congrArg σ (hemb i))
  have hA : SHom.sortPerm (J.map f) cyc3 = 1 := by
    rw [htuple, Tuple.sort_eq_refl_iff_monotone.mpr monotone_cyc3]
    exact inv_one
  have hB : SHom.sortPerm (J.map f) cyc3⁻¹ ≠ 1 := by
    rw [htuple]
    intro hcc
    exact not_monotone_cyc3_inv (Tuple.sort_eq_refl_iff_monotone.mp (inv_eq_one.mp hcc))
  exact hB (inv_eq_one.mp (hkey.trans hA))

/-- **A merge does not restrict runs the way the product would**: the source run is the target
run pulled back along the *twisted* map, and the twist is not the identity. -/
theorem exists_merge_twistRun_ne :
    ∃ (a b : Ch Zbp) (u : a ⟶ b) (ρ : ⋁b.dims ⟶ runBp),
      merge Zbp u ∧ twistRun ρ (Hom.φ u) ≠ Hom.φ u ≫ ρ :=
  ⟨_, _, mergeHom ([] : List ℕ+) [] 2 1, cycRun, merge_mergeHom _ _ _ _, twistRun_merge21_ne⟩

/-! ## The verdict: `desym` is not natural -/

/-- **The run leg of `desym` is not natural** — already over the terminal `Zbp`, where the chain
leg carries no information at all. -/
theorem not_runOf_natural :
    ¬ ∀ (K : BPSet) (a b : List ℕ+) (φ : ⋁a ⟶ ⋁b) (β : ⋁b ⟶ Hbp.obj K),
        runOf K (φ ≫ β) = φ ≫ runOf K β := by
  intro h
  obtain ⟨a, b, u, ρ, -, hne⟩ := exists_merge_twistRun_ne
  refine hne ?_
  have hβ := h Zbp a.dims b.dims (Hom.φ u)
    (symOf ρ ≫ Hbp.map (isTerminalZbp.from (⋁b.dims)))
  rwa [runOf_comp, runOf_symOf_comp, ← twistRun_eq] at hβ

/-- **`desym` is not natural in the chain**: `wedgeHoms (Hbp K)` is not the product presheaf, and
`desym_comp`'s twist is exactly the discrepancy. -/
theorem not_desym_natural :
    ¬ ∀ (K : BPSet) (a b : List ℕ+) (φ : ⋁a ⟶ ⋁b) (β : ⋁b ⟶ Hbp.obj K),
        desym K (φ ≫ β) = φ ≫ desym K β := fun h =>
  not_runOf_natural fun K a b φ β => by
    rw [runOf, runOf, h K a b φ β, Category.assoc]

/-! ## What any product splitting would cost

Not just `desym`: *no* natural splitting can coexist with `InvertsMerges (Hbp K)`, because the
run factor never inverts a merge. -/

/-- A **product splitting** of the fibre presheaf of `Hbp K`: bijections
`Hom(⋁d, Hbp K) ≃ Hom(⋁d, K) × Hom(⋁d, runBp)` commuting with restriction. -/
structure ProductSplitting (K : BPSet) where
  /-- The comparison, one shape at a time. -/
  equiv (d : List ℕ+) : (⋁d ⟶ Hbp.obj K) ≃ ((⋁d ⟶ K) × (⋁d ⟶ runBp))
  /-- …commuting with restriction along a wedge map. -/
  naturality {d e : List ℕ+} (φ : ⋁d ⟶ ⋁e) (β : ⋁e ⟶ Hbp.obj K) :
    equiv d (φ ≫ β) = (φ ≫ (equiv e β).1, φ ≫ (equiv e β).2)

/-- The bead merge `⋁[1, 1] ⟶ ⋁[2]`, as a bare wedge map. -/
private def merge11 : ⋁[(1 : ℕ+), 1] ⟶ ⋁[(1 : ℕ+) + 1] :=
  Hom.φ (mergeHom ([] : List ℕ+) [] 1 1)

/-- **A product splitting would kill `InvertsMerges (Hbp K)`.**  A merge is bijective on the
product only if it is bijective on each factor, and it never is on the run factor. -/
theorem not_invertsMerges_of_splitting {K : BPSet} (S : ProductSplitting K)
    (c : ⋁[(1 : ℕ+) + 1] ⟶ K) : ¬ InvertsMerges (Hbp.obj K) := fun h => by
  have hsub : Subsingleton (⋁([(1 : ℕ+), 1]) ⟶ runBp) := subsingleton_runs_of_ones (by decide)
  have hstep : merge11 ≫ (S.equiv _).symm (c, ofCell (1 + 1) ((runPermEquiv 2).symm 1))
      = merge11 ≫ (S.equiv _).symm (c, ofCell (1 + 1) ((runPermEquiv 2).symm (Equiv.swap 0 1))) :=
    (S.equiv [(1 : ℕ+), 1]).injective (by
      rw [S.naturality, S.naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        hsub.elim (merge11 ≫ ofCell (1 + 1) ((runPermEquiv 2).symm 1))
          (merge11 ≫ ofCell (1 + 1) ((runPermEquiv 2).symm (Equiv.swap 0 1)))])
  exact runCell_two_ne (ofCell_injective _ (congrArg Prod.snd
    ((S.equiv _).symm.injective ((bijective_merge11_of_invertsMerges h).1 hstep))))

/-- **`InvertsMerges (Hbp □²)` and a product splitting of `Hbp (□2)` are incompatible** — the cube
labelling has to compensate for the run data a merge destroys. -/
theorem isEmpty_splitting_of_invertsMerges_cube_two (h : InvertsMerges (Hbp.obj (□2))) :
    IsEmpty (ProductSplitting (□2)) :=
  ⟨fun S => not_invertsMerges_of_splitting S (serialWedge1 (1 + 1)).hom h⟩

/-! ## The tower

`Hbp` is a functor and `Zbp` is terminal, so a decorated chain has a canonical run and a
canonical shape:

    Ch (Hbp K)  ⟶  Ch (Hbp Zbp)  ⟶  Ch Zbp

The first stage forgets the `K`-labels and keeps the run; the second forgets the run.  Both are
discrete fibrations (`Concurrency/Presentation/ElementsFibration`) with fibres `wedgeHoms`; the
tower is *not* a product, by `not_desym_natural`. -/

/-- Forget a decorated chain's labels, keep its run. -/
def forgetLabels (K : BPSet) : Ch (Hbp.obj K) ⥤ Ch (Hbp.obj Zbp) :=
  pushforward (Hbp.map (isTerminalZbp.from K))

/-- Forget a decorated chain's run. -/
def forgetRun : Ch (Hbp.obj Zbp) ⥤ Ch Zbp := toChZ (Hbp.obj Zbp)

/-- The first stage is `HbpOverRun` read through `Hbp Zbp ≅ runBp`. -/
theorem HbpOverRun_app (K : BPSet) :
    HbpOverRun.app K = Hbp.map (isTerminalZbp.from K) ≫ HbpZIsoRun.hom :=
  hom_ext (congrArg (· ≫ HZIsoRun.hom) (congrArg H.map (isTerminalZ.hom_ext _ _)))

/-- **The tower composes to the fibration over the shapes.** -/
theorem forgetLabels_comp_forgetRun (K : BPSet) :
    forgetLabels K ⋙ forgetRun = toChZ (Hbp.obj K) := by
  rw [forgetLabels, forgetRun, toChZ, toChZ, ← pushforward_comp]
  exact congrArg pushforward (Subsingleton.elim _ _)

/-! ## The run object corepresents

A chain map out of the all-edges chain is a run of its target: `blockIdx` is monotone and the
coordinate map is bijective, so the assignment of events to beads is forced and the only freedom
left is the order inside each bead. -/

/-- An all-edges chain has one bead per event. -/
theorem run_dims_eq {X : BPSet} {n : ℕ} (r : Run X) (hn : dimSum r.dims = n) : r.dims = 𝟙^n :=
  (eq_replicate_of_ones r.ones).trans
    (congrArg (List.replicate · (1 : ℕ+)) ((dimSum_eq_length_of_ones r.ones).symm.trans hn))

/-- **A chain map out of the all-edges chain is a run of the target**, whenever the target has
`n` events along every chain. -/
def onesHomEquivRun {X : BPSet} {n : ℕ} (hn : ∀ {d : List ℕ+} (_ : ⋁d ⟶ X), dimSum d = n) :
    (⋁(𝟙^n) ⟶ X) ≃ Run X where
  toFun φ := ⟨⟨𝟙^n, φ⟩, fun _ hx => List.eq_of_mem_replicate hx⟩
  invFun r := ⋁≡ (run_dims_eq r (hn r.map)).symm ≫ r.map
  left_inv φ := Category.id_comp φ
  right_inv r := Run.ext (Obj.mk_eq_mk (run_dims_eq r (hn r.map)).symm rfl)

/-- **The maps out of the all-edges chain are the runs classified by `Hbp Zbp`.**  Gotcha: the
two sides are covariant and contravariant in `b`, so this is a bijection of fibres and not a
natural isomorphism — along the merge `[1,1] ⟶ [2]` the left grows and the right shrinks. -/
def onesHomEquivRunClassifier (b : Ch Zbp) {n : ℕ} (hn : dimSum b.dims = n) :
    (zObj (𝟙^n) ⟶ b) ≃ (⋁b.dims ⟶ Hbp.obj Zbp) :=
  serialWedgeFullyFaithful.homEquiv.trans <|
    (onesHomEquivRun fun φ => (serialWedge_dimSum_eq φ).trans hn).trans <|
    (runPshEquiv b.dims).symm.trans <| (homEquivPsh (⋁b.dims) runBp).symm.trans <|
      Iso.homCongr (Iso.refl _) HbpZIsoRun.symm

/-- **The simples are the cells of the run classifier** — an intrinsic description of
`Hom(onesObj m, topObj m)` with no `Perm` in it. -/
def simplesEquivCells (m : ℕ+) :
    (zObj (𝟙^(m : ℕ)) ⟶ zObj [m]) ≃ (Hbp.obj Zbp).cells (m : ℕ) :=
  (onesHomEquivRunClassifier (zObj [m]) rfl).trans (oneBeadEquivCell m)

/-! ## The point's decorated chains collapse

An edge of `Hbp Zbp` carries no order, so there is exactly one all-edges decorated chain in each
degree.  Its merge into every other chain therefore lifts freely — the compatibility condition
lives in a one-element hom-set — and the localized component is a single object. -/

instance (n : ℕ) : Inhabited ((Hbp.obj Zbp).cells n) := ⟨(1, PUnit.unit)⟩

/-- **A decorated all-edges chain of the point is unique** — an edge has one order. -/
theorem subsingleton_homHbpZbp_of_ones {d : List ℕ+} (h : ∀ x ∈ d, x = 1) :
    Subsingleton (⋁d ⟶ Hbp.obj Zbp) :=
  haveI := subsingleton_runs_of_ones h
  (Iso.homCongr (Iso.refl (⋁d)) HbpZIsoRun).subsingleton

/-- The all-edges decorated chain of the point on `n` events. -/
def onesH (n : ℕ) : Ch (Hbp.obj Zbp) := ⟨𝟙^n, ofCells (𝟙^n) fun _ => default⟩

/-- **The base's merge out of the all-edges chain lifts to the decoration**: its compatibility
condition is an equation in a one-element hom-set, so nothing has to be checked about runs. -/
theorem exists_W_from_onesH (A : Ch (Hbp.obj Zbp)) {N : ℕ} (h : dimSum A.dims = N) :
    ∃ u : onesH N ⟶ A, W (Hbp.obj Zbp) u := by
  have hsub : Subsingleton (⋁(𝟙^N) ⟶ Hbp.obj Zbp) :=
    subsingleton_homHbpZbp_of_ones fun _ hx => List.eq_of_mem_replicate hx
  obtain ⟨u, hu⟩ := exists_W_from_ones A.dims h
  obtain ⟨φ, hw⟩ := u
  refine ⟨⟨φ, hsub.elim _ _⟩, ?_⟩
  rw [W_iff_crossPerm_eq_one (dimSum_replicate N)] at hu ⊢
  exact hu

/-! ## The cube's do not

An edge of `Hbp K` is an edge of `K`, so the all-edges decorated chains of `□ⁿ` are the `n!` runs
of the cube.  They are rigid and pairwise distinct, so no object maps to them all and nothing is
wide-initial: `H` supplies the arrows, the cube supplies the objects. -/

instance (k : ℕ) : Inhabited (runBp.cells k) := ⟨(runPermEquiv k).symm 1⟩

/-- A run on a wedge — the identity order in each bead. -/
def onesRun (d : List ℕ+) : ⋁d ⟶ runBp := ofCells d fun _ => default

theorem desym_eq_prodLift {K : BPSet} {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) :
    desym K α = prodLift (chainOf K α) (runOf K α) :=
  prod_hom_ext (prodLift_fst _ _).symm (prodLift_snd _ _).symm

/-- **An all-edges decorated chain is an all-edges chain**: the order on an edge is no data. -/
def runHbpEquiv (K : BPSet) : Run (Hbp.obj K) ≃ Run K where
  toFun a := ⟨⟨a.dims, chainOf K a.map⟩, a.property⟩
  invFun b := ⟨⟨b.dims, resym K (prodLift b.map (onesRun b.dims))⟩, b.property⟩
  left_inv a := Run.ext (congrArg (fun m => (⟨a.dims, m⟩ : Ch (Hbp.obj K))) (by
    haveI := subsingleton_runs_of_ones a.ones
    rw [show prodLift (chainOf K a.map) (onesRun a.dims)
        = prodLift (chainOf K a.map) (runOf K a.map) from
      congrArg _ (Subsingleton.elim _ _), ← desym_eq_prodLift, resym_desym]))
  right_inv b := Run.ext (congrArg (fun m => (⟨b.dims, m⟩ : Ch K)) (by
    rw [chainOf, desym_resym, prodLift_fst]))

/-- **The decorated cube has `n!` all-edges chains** — the runs of `□ⁿ`. -/
def runHbpCubeEquivPerm (n : ℕ) : Run (Hbp.obj (□n)) ≃ Equiv.Perm (Fin n) :=
  (runHbpEquiv (□n)).trans (runPermEquiv n)

/-- **The point has one all-edges chain per degree** — the contrast the cube breaks. -/
theorem run_HbpZbp_eq {r s : Run (Hbp.obj Zbp)} (h : dimSum r.dims = dimSum s.dims) : r = s := by
  have hd : r.dims = s.dims := by
    rw [eq_replicate_of_ones r.ones, eq_replicate_of_ones s.ones,
      ← dimSum_eq_length_of_ones r.ones, ← dimSum_eq_length_of_ones s.ones, h]
  haveI := subsingleton_homHbpZbp_of_ones r.ones
  exact Run.ext (Obj.mk_eq_mk hd (Subsingleton.elim _ _))

/-- **A morphism into a run has a run source** — the runs are the bottom of the degree grading. -/
theorem isRun_of_hom_to_run {X : BPSet} {y : Ch X} {r : Run X} (f : y ⟶ r.chain) :
    IsRun X y :=
  (isRun_iff_degree_eq_zero y).mpr <| Nat.le_zero.mp <|
    (ChainCat.degree_le_of_hom f).trans_eq ((isRun_iff_degree_eq_zero r.chain).mp r.property)

/-- **Two runs cannot both be reached from one object** — `Run X` is discrete. -/
theorem eq_of_hom_to_runs {X : BPSet} {y : Ch X} {r s : Run X}
    (f : y ⟶ r.chain) (g : y ⟶ s.chain) : r = s :=
  haveI hy : IsRun X y := isRun_of_hom_to_run f
  (Run.eq_of_hom (r := ⟨y, hy⟩) (s := r) (ObjectProperty.homMk f)).symm.trans
    (Run.eq_of_hom (r := ⟨y, hy⟩) (s := s) (ObjectProperty.homMk g))

/-- **No decorated chain of `□ⁿ` maps to every one** for `n ≥ 2`, so nothing in `Ch (Hbp □ⁿ)` is
wide-initial and the merges cannot collapse it. -/
theorem not_exists_hom_to_all_cube {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ y : Ch (Hbp.obj (□n)), ∀ A : Ch (Hbp.obj (□n)), Nonempty (y ⟶ A) := by
  rintro ⟨y, hy⟩
  set i : Fin n := ⟨0, by omega⟩
  set j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := fun hc => absurd (congrArg Fin.val hc) (by simp [i, j])
  have hswap : (1 : Equiv.Perm (Fin n)) ≠ Equiv.swap i j := by
    intro hc
    have h1 := congrArg (fun σ : Equiv.Perm (Fin n) => σ i) hc
    simp only [Equiv.Perm.coe_one, id_eq, Equiv.swap_apply_left] at h1
    exact hij h1
  obtain ⟨f⟩ := hy ((runHbpCubeEquivPerm n).symm 1).chain
  obtain ⟨g⟩ := hy ((runHbpCubeEquivPerm n).symm (Equiv.swap i j)).chain
  exact hswap ((runHbpCubeEquivPerm n).symm.injective (eq_of_hom_to_runs f g))

end CubeChains
