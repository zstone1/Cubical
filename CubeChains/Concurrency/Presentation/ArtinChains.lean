import CubeChains.Concurrency.Presentation.ArtinCells
import CubeChains.Concurrency.Presentation.PairChain
import CubeChains.Machinery.Presentation.Bijective

/-!
# Concurrency/Presentation/ArtinChains — Artin's presentation, written in chains

The polygraph written out by hand, with no colimit and no localization in sight:

* a **0-cell** is a run of `H(□ⁿ)` — a chain all of whose beads are edges;
* a **1-cell** is a **codimension-one chain**, one 2-bead at a cut `k` and edges elsewhere, read
  from its crossing leg to its merge leg;
* a **2-cell** is a parallel pair of words closing a **codimension-two chain**: a square where the
  two cuts are far apart, a hexagon where they are adjacent.

`atomLoop_comm` and `atomLoop_braid` are those two shapes in the localized base; here they are the
relations themselves.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits

namespace ChainCat

variable {n : ℕ}

/-! ## The cells -/

/-- A **run** of the decorated cube: a chain every bead of which is an edge. -/
abbrev CubeRun (n : ℕ) : Type := ⋁(𝟙^n) ⟶ Hbp.obj (□n)

/-- A **codimension-one chain of `H(□ⁿ)` cut at `k`**, named by its two legs: the crossing leg
`atomOnes` restricts it to `x`, the merge leg `mergeOnes` to `y`.  Inverting the merge makes it an
arrow `x ⟶ y`. -/
structure AtomChain (n : ℕ) (k : Fin (n - 1)) (x y : CubeRun n) where
  /-- the chain itself -/
  chart : ⋁(atomComp n k) ⟶ Hbp.obj (□n)
  /-- its crossing leg -/
  cross : (atomOnes n k).φ ≫ chart = x
  /-- its merge leg -/
  merge : (mergeOnes n k).φ ≫ chart = y

/-- The 1-cells: a codimension-one chain, its cut forgotten. -/
def AtomGen (n : ℕ) (x y : CubeRun n) : Type := Σ k : Fin (n - 1), AtomChain n k x y

/-- A codimension-one chain, as a 1-cell. -/
def atomEdge {k : Fin (n - 1)} {x y : CubeRun n} (e : AtomChain n k x y) :
    (⟨x⟩ : GenObj (AtomGen n)) ⟶ ⟨y⟩ := ⟨k, e⟩

/-- A two-letter word. -/
def atomWord₂ {i j : Fin (n - 1)} {x y z : CubeRun n}
    (e₁ : AtomChain n i x y) (e₂ : AtomChain n j y z) :
    Quiver.Path (⟨x⟩ : GenObj (AtomGen n)) ⟨z⟩ :=
  (Quiver.Hom.toPath (atomEdge e₁)).comp (Quiver.Hom.toPath (atomEdge e₂))

/-- A three-letter word. -/
def atomWord₃ {i j k : Fin (n - 1)} {w x y z : CubeRun n}
    (e₁ : AtomChain n i w x) (e₂ : AtomChain n j x y) (e₃ : AtomChain n k y z) :
    Quiver.Path (⟨w⟩ : GenObj (AtomGen n)) ⟨z⟩ :=
  (atomWord₂ e₁ e₂).comp (Quiver.Hom.toPath (atomEdge e₃))

/-- **The two shapes a codimension-two chain has**: far-apart cuts close a square, adjacent ones a
hexagon.  This is `atomLoop_comm` / `atomLoop_braid`, read on the chains themselves. -/
inductive ArtinChainRel (n : ℕ) : ∀ {A B : GenObj (AtomGen n)},
    Quiver.Path A B → Quiver.Path A B → Prop
  | comm {x y y' z : CubeRun n} {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 < (j : ℕ))
      (e₁ : AtomChain n j x y) (e₂ : AtomChain n i y z)
      (f₁ : AtomChain n i x y') (f₂ : AtomChain n j y' z) :
      ArtinChainRel n (atomWord₂ e₁ e₂) (atomWord₂ f₁ f₂)
  | braid {x y₁ y₂ y₁' y₂' z : CubeRun n} {i j : Fin (n - 1)} (hij : (j : ℕ) = (i : ℕ) + 1)
      (e₁ : AtomChain n i x y₁) (e₂ : AtomChain n j y₁ y₂) (e₃ : AtomChain n i y₂ z)
      (f₁ : AtomChain n j x y₁') (f₂ : AtomChain n i y₁' y₂') (f₃ : AtomChain n j y₂' z) :
      ArtinChainRel n (atomWord₃ e₁ e₂ e₃) (atomWord₃ f₁ f₂ f₃)

/-- **Artin's presentation of `Ch(H(□ⁿ))[W⁻¹]`, hand-written**: 0-cells the runs, 1-cells the
codimension-one chains, 2-cells the codimension-two ones. -/
def artinChainPoly (n : ℕ) : Polygraph.{0, 0, 0} where
  V := CubeRun n
  Gen := AtomGen n
  Rel A B := {P : Quiver.Path A B × Quiver.Path A B // ArtinChainRel n P.1 P.2}
  src α := α.1.1
  tgt α := α.1.2

/-- **A 2-cell is its parallel pair of words** — it carries no filler. -/
theorem boundaryDetermined_artinChainPoly : (artinChainPoly n).BoundaryDetermined :=
  fun _ _ hs ht => Subtype.ext (Prod.ext hs ht)

/-! ## A codimension-one chain is its merge leg

The merges act bijectively on the charts (`IsSegal`), so a cut and a run below it determine the
chain: `AtomChain n k x y` is a subsingleton, inhabited exactly when the `k`-th atom carries `y`
to `x`. -/

/-- **The chart is forced by the merge leg.** -/
theorem AtomChain.eq_atomWitness {k : Fin (n - 1)} {x y : CubeRun n} (e : AtomChain n k x y) :
    e.chart = atomWitness k y :=
  ChainCat.eq_atomWitness k y e.merge

theorem AtomChain.ext {k : Fin (n - 1)} {x y : CubeRun n} (e f : AtomChain n k x y) : e = f := by
  obtain ⟨w, hc, hm⟩ := e
  obtain ⟨w', hc', hm'⟩ := f
  obtain rfl : w = w' :=
    (AtomChain.eq_atomWitness ⟨w, hc, hm⟩).trans (AtomChain.eq_atomWitness ⟨w', hc', hm'⟩).symm
  rfl

/-- The run the `k`-th atom carries a run to. -/
noncomputable def atomStep (k : Fin (n - 1)) (z : CubeRun n) : CubeRun n :=
  (hFibre n).map (ChainCat.atomLoop n k) z

/-- **…and the crossing leg is the atom acting on it.** -/
theorem AtomChain.atomLoop {k : Fin (n - 1)} {x y : CubeRun n} (e : AtomChain n k x y) :
    atomStep k y = x := by
  rw [atomStep, ← atomOnes_atomWitness k y, ← e.eq_atomWitness]
  exact e.cross

/-- **The `k`-th atom acting on a run is a codimension-one chain** — its chart is the run
un-merged across the cut. -/
noncomputable def AtomChain.of {k : Fin (n - 1)} {x y : CubeRun n}
    (h : atomStep k y = x) : AtomChain n k x y where
  chart := atomWitness k y
  cross := (atomOnes_atomWitness k y).trans h
  merge := mergeOnes_atomWitness k y

/-! ### The atoms act by their transpositions

A run *is* an ordering (`runFibreEquiv`) and an atom translates it, so the relations among the
`atomStep`s are the relations among the `adjT`s and nothing else. -/

theorem runFibreEquiv_atomStep (k : Fin (n - 1)) (z : CubeRun n) :
    runFibreEquiv n (atomStep k z) = (adjT k)⁻¹ * runFibreEquiv n z :=
  runFibreEquiv_atomLoop k z

/-- **Far-apart cuts commute on the runs.** -/
theorem atomStep_comm {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 < (j : ℕ)) (z : CubeRun n) :
    atomStep i (atomStep j z) = atomStep j (atomStep i z) := by
  have h := congrArg (fun σ : Equiv.Perm (Fin n) => σ⁻¹) (adjT_comm i j hij)
  simp only [mul_inv_rev, ← mul_assoc] at h
  exact (runFibreEquiv n).injective (by simp only [runFibreEquiv_atomStep, ← mul_assoc, h])

/-- **…and adjacent ones braid.** -/
theorem atomStep_braid {i j : Fin (n - 1)} (hij : (j : ℕ) = (i : ℕ) + 1) (z : CubeRun n) :
    atomStep i (atomStep j (atomStep i z)) = atomStep j (atomStep i (atomStep j z)) := by
  have h := congrArg (fun σ : Equiv.Perm (Fin n) => σ⁻¹) (adjT_braid i j hij)
  simp only [mul_inv_rev, ← mul_assoc] at h
  exact (runFibreEquiv n).injective (by simp only [runFibreEquiv_atomStep, ← mul_assoc, h])

/-! ## The comparison with `Br artinBP (H □ⁿ)`

A codimension-one chain indexes a copy of the base's cells, and that copy has exactly one crossing
(`action_atomRunAt`); `ιV_atomLeg` and `ιV_mergeLeg` say its two 0-cells are the chain's two
legs. -/

/-- **The 1-cell of `Br p K` a codimension-one chain is**: the one crossing of the copy it indexes,
read between its two legs. -/
noncomputable def atomChainCell (K : BPSet) {k : Fin (n - 1)} (w : ⋁(atomComp n k) ⟶ K) :
    artinBP.ιRun K ((atomOnes n k).φ ≫ w) ⟶ artinBP.ιRun K ((mergeOnes n k).φ ≫ w) :=
  Quiver.homOfEq (ιE K artinBP.fam (op ⟨op (zObj (atomComp n k)), w⟩)
      (artinBP.runGen k (action_atomRunAt k)))
    (ιV_atomLeg k K w) (ιV_mergeLeg k K w)

/-- **The runs and the codimension-one chains, mapped into `Br artinBP (H □ⁿ)`.** -/
noncomputable def artinChainPre (n : ℕ) :
    GenObj (artinChainPoly n).Gen ⥤q GenObj (artinBP.Br (Hbp.obj (□n))).Gen where
  obj A := artinBP.ιRun (Hbp.obj (□n)) A.as
  map {_ _} e := Quiver.homOfEq (atomChainCell (Hbp.obj (□n)) e.2.chart)
    (congrArg (artinBP.ιRun (Hbp.obj (□n))) e.2.cross)
    (congrArg (artinBP.ιRun (Hbp.obj (□n))) e.2.merge)

/-! ### A cell of a copy, read in another copy

`ιV_leg`/`ιE_leg` say what a leg of the elements does; `famV_runPt` and `artinRunGen_ext` say
what pushing does to a run's 0-cell and to a generator between two of them.  Everything below is
those four, so no cell of the colimit is ever unfolded. -/

/-- **A run's 0-cell, pushed along a leg.** -/
theorem ιV_pushLeg (p : BraidPresentation) (K : BPSet) {d : Ch Zbp} (W : (wedgeHoms K).obj (op d))
    {e : Ch Zbp} (f : e ⟶ d) {N : ℕ} (u : RunAt e N) :
    ιV K p.fam (op ⟨op d, W⟩) (p.runPt (RunAt.push f u))
      = ιV K p.fam (op ⟨op e, (wedgeHoms K).map f.op W⟩) (p.runPt u) :=
  (congrArg (ιV K p.fam (op ⟨op d, W⟩)) (p.famV_runPt f u).symm).trans
    (ιV_leg K p.fam (eltLeg K f W) (p.runPt u))

/-- **The 0-cell of a run of a copy is the run's own** — its chart restricted along it. -/
theorem ιV_runPush (p : BraidPresentation) (K : BPSet) {d : Ch Zbp}
    (W : (wedgeHoms K).obj (op d)) {N : ℕ} (t : zObj (𝟙^N) ⟶ d) :
    ιV K p.fam (op ⟨op d, W⟩) (p.runPt (RunAt.push t (runAtSelf N)))
      = p.ιRun K (t.φ ≫ W) :=
  ιV_pushLeg p K W t (runAtSelf N)

/-- **Every run over `d` is the identity run pushed along its own arrow.** -/
theorem exists_runPush {d : Ch Zbp} {N : ℕ} (hd : dimSum d.dims = N) (u : RunAt d N) :
    ∃ t : zObj (𝟙^N) ⟶ d, RunAt.push t (runAtSelf N) = u := by
  obtain ⟨⟨⟨l, ⟨⟩, g⟩, hr⟩, hN⟩ := u
  obtain rfl : l = zObj (𝟙^N) := RunOver.left_eq hd ⟨Over.mk g, hr⟩
  exact ⟨g, Subtype.ext (Subtype.ext (congrArg Over.mk (Category.id_comp g)))⟩

/-- **Pushing a copy along a leg pushes its generator**, run and all. -/
theorem fam_map_runGen {e d : Ch Zbp} (f : e ⟶ d) {N : ℕ} {u v : RunAt e N} (s : artinBP.S N)
    (hact : RunGermStep (artinBP.braid s) u v) :
    Quiver.homOfEq ((artinBP.fam.map f).pre.map (artinBP.runGen s hact))
        (congrArg GenObj.mk (artinBP.famV_runPt f v)) (congrArg GenObj.mk (artinBP.famV_runPt f u))
      = artinBP.runGen s (germStep_push f hact) :=
  artinRunGen_ext (artinBP.famV_runPt f v) (artinBP.famV_runPt f u) _ _ HEq.rfl

/-- **A generator acting in a copy is that generator acting in the copy it was pushed from.** -/
theorem ιE_pushLeg (K : BPSet) {d : Ch Zbp} (W : (wedgeHoms K).obj (op d))
    {e : Ch Zbp} (f : e ⟶ d) {N : ℕ} {u v : RunAt e N} (s : artinBP.S N)
    (hact : RunGermStep (artinBP.braid s) u v) :
    ιE K artinBP.fam (op ⟨op d, W⟩) (artinBP.runGen s (germStep_push f hact))
      = Quiver.homOfEq (ιE K artinBP.fam (op ⟨op e, (wedgeHoms K).map f.op W⟩)
          (artinBP.runGen s hact))
          (ιV_pushLeg artinBP K W f v).symm (ιV_pushLeg artinBP K W f u).symm := by
  refine eq_of_heq (HEq.trans ?_ (Quiver.homOfEq_heq _ _ _).symm)
  refine HEq.trans (heq_of_eq (congrArg (ιE K artinBP.fam (op ⟨op d, W⟩))
    (fam_map_runGen f s hact).symm)) ?_
  refine HEq.trans (Prefunctor.map_heq_congr _
    (congrArg GenObj.mk (artinBP.famV_runPt f v)).symm
    (congrArg GenObj.mk (artinBP.famV_runPt f u)).symm (Quiver.homOfEq_heq _ _ _)) ?_
  exact (heq_of_eq (ιE_leg K artinBP.fam (eltLeg K f W) (artinBP.runGen s hact))).trans
    (Quiver.homOfEq_heq _ _ _)

/-- **A generator acting in any copy is a codimension-one chain's own 1-cell** — the copy's chart,
restricted along the atom's leg.  Everything about the 2-cells is read off this. -/
theorem ιE_runGen_eq (K : BPSet) {d : Ch Zbp} (W : (wedgeHoms K).obj (op d))
    {k : Fin (n - 1)} (t : zObj (atomComp n k) ⟶ d) :
    Quiver.homOfEq
        (ιE K artinBP.fam (op ⟨op d, W⟩)
          (artinBP.runGen k (germStep_push t (action_atomRunAt k))))
        ((ιV_pushLeg artinBP K W t (atomRunAt k)).trans (ιV_atomLeg k K (t.φ ≫ W)))
        ((ιV_pushLeg artinBP K W t (mergeRunAt k)).trans (ιV_mergeLeg k K (t.φ ≫ W)))
      = atomChainCell K (t.φ ≫ W) := by
  refine eq_of_heq (((Quiver.homOfEq_heq _ _ _).trans ?_).trans (Quiver.homOfEq_heq _ _ _).symm)
  exact (heq_of_eq (ιE_pushLeg K W t k (action_atomRunAt k))).trans
    (Quiver.homOfEq_heq _ _ _)

/-! ### The run a 0-cell of a copy carries

A run over `d` is its own arrow out of `1ⁿ` (`exists_runPush`), and that arrow is pinned by the run
(`push_runAtSelf_injective`), so `runOf` is well defined: the copy's chart, restricted along it. -/

theorem RunAt.push_push {d' d e : Ch Zbp} (f : d' ⟶ d) (g : d ⟶ e) {N : ℕ} (u : RunAt d' N) :
    RunAt.push g (RunAt.push f u) = RunAt.push (f ≫ g) u :=
  Subtype.ext (Subtype.ext (congrArg Over.mk (Category.assoc _ _ _)))

theorem push_runAtSelf_injective {d : Ch Zbp} {N : ℕ} {t t' : zObj (𝟙^N) ⟶ d}
    (h : RunAt.push t (runAtSelf N) = RunAt.push t' (runAtSelf N)) : t = t' := by
  have hp := congrArg RunAt.perm h
  rw [RunAt.push_perm t (dimSum_replicate N), RunAt.push_perm t' (dimSum_replicate N),
    perm_runAtSelf, mul_one, mul_one] at hp
  exact hom_ext_of_crossPerm hp

variable (K : BPSet)

/-- **The run a 0-cell of a copy carries**: the copy's chart, restricted along the run's arrow. -/
noncomputable def runOf {d : Ch Zbp} (hd : dimSum d.dims = n) (W : (wedgeHoms K).obj (op d))
    (u : RunAt d n) : ⋁(𝟙^n) ⟶ K :=
  (exists_runPush hd u).choose.φ ≫ W

theorem runOf_eq {d : Ch Zbp} (hd : dimSum d.dims = n) (W : (wedgeHoms K).obj (op d))
    {u : RunAt d n} {t : zObj (𝟙^n) ⟶ d} (ht : RunAt.push t (runAtSelf n) = u) :
    runOf K hd W u = t.φ ≫ W :=
  congrArg (fun s : zObj (𝟙^n) ⟶ d => s.φ ≫ W)
    (push_runAtSelf_injective ((exists_runPush hd u).choose_spec.trans ht.symm))

/-- **…and it is the 0-cell of the colimit that 0-cell names.** -/
theorem ιV_runOf {d : Ch Zbp} (hd : dimSum d.dims = n) (W : (wedgeHoms K).obj (op d))
    (u : RunAt d n) :
    ιV K artinBP.fam (op ⟨op d, W⟩) (artinBP.runPt u)
      = artinBP.ιRun K (runOf K hd W u) := by
  obtain ⟨t, ht⟩ := exists_runPush hd u
  rw [runOf_eq K hd W ht, ← ht]
  exact ιV_runPush artinBP K W t

/-- **A generator acting in a copy is a codimension-one chain joining the two runs.**  The chain is
the copy's chart restricted along the atom's leg, and `exists_atomComp_leg` supplies the leg. -/
theorem ιE_runGen_atomChain {d : Ch Zbp} (hd : dimSum d.dims = n)
    (W : (wedgeHoms K).obj (op d)) {k : Fin (n - 1)} {u v : RunAt d n}
    (hact : RunGermStep (posPerm (adjT k)) u v) :
    ∃ (w : ⋁(atomComp n k) ⟶ K) (h₁ : (atomOnes n k).φ ≫ w = runOf K hd W v)
      (h₂ : (mergeOnes n k).φ ≫ w = runOf K hd W u),
      Quiver.homOfEq (ιE K artinBP.fam (op ⟨op d, W⟩) (artinBP.runGen k hact))
          (ιV_runOf K hd W v) (ιV_runOf K hd W u)
        = Quiver.homOfEq (atomChainCell K w) (congrArg (artinBP.ιRun K) h₁)
            (congrArg (artinBP.ιRun K) h₂) := by
  obtain ⟨t, hatom, hmerge⟩ := exists_atomComp_leg hd hact
  subst hatom
  subst hmerge
  have hpa : RunAt.push (atomOnes n k ≫ t) (runAtSelf n) = RunAt.push t (atomRunAt k) :=
    (RunAt.push_push (atomOnes n k) t (runAtSelf n)).symm
  have hpm : RunAt.push (mergeOnes n k ≫ t) (runAtSelf n) = RunAt.push t (mergeRunAt k) :=
    (RunAt.push_push (mergeOnes n k) t (runAtSelf n)).symm
  refine ⟨t.φ ≫ W, (Category.assoc _ _ _).symm.trans (runOf_eq K hd W hpa).symm,
    (Category.assoc _ _ _).symm.trans (runOf_eq K hd W hpm).symm, ?_⟩
  refine eq_of_heq (((Quiver.homOfEq_heq _ _ _).trans ?_).trans (Quiver.homOfEq_heq _ _ _).symm)
  exact (Quiver.homOfEq_heq _ _ _).symm.trans (heq_of_eq (ιE_runGen_eq K W t))

variable {K}

/-! ### A 2-cell of a copy is the relation of the base it carries

The copy's cells lie over the base's along a **covering** — a restriction of a category of
elements — so a word is pinned by its projection, and hence a 2-cell by the relation below it. -/

/-- The copy's cells, read in the base: a germ lies over its own strand count's polygraph. -/
noncomputable def sliceDown (d : Ch Zbp) : artinBP.slicePoly d ⟶ artinBP.poly :=
  Polygraph.coprodDesc _ fun N =>
    Polygraph.comapDown _ _ (artinBP.germProj (runGermChart d N)) ≫
      artinBP.incl N

/-- The projection of a copy's cells down to the base's. -/
noncomputable def sliceProj (d : Ch Zbp) :
    GenObj (artinBP.slicePoly d).Gen ⥤q GenObj artinBP.poly.Gen := (sliceDown d).pre

/-- The relation of the base a 2-cell of a copy carries. -/
noncomputable def sliceCell {d : Ch Zbp} {A B : GenObj (artinBP.slicePoly d).Gen}
    (β : (artinBP.slicePoly d).Rel A B) :
    artinBP.poly.Rel ((sliceProj d).obj A) ((sliceProj d).obj B) := (sliceDown d).two β

/-- **A copy's word is its germ word, at its own strand count.** -/
theorem sliceProj_coproductPre {d : Ch Zbp} (N : ℕ)
    {x y : GenObj (artinBP.GermGen (runGermChart d N))} (w : Quiver.Path x y) :
    (sliceProj d).mapPath
        ((Polygraph.coproductPre (fun M => artinBP.germPoly (runGermChart d M)) N).mapPath w)
      = (artinBP.pre N).mapPath
          (artinBP.germWord (runGermChart d N) w) :=
  (Polygraph.descPre_mapPath (fun M => artinBP.germPoly (runGermChart d M))
      (fun M => Polygraph.comapDown _ _ (artinBP.germProj (runGermChart d M)) ≫
        artinBP.incl M) N w).trans
    (Prefunctor.mapPath_comp_apply (artinBP.germProj (runGermChart d N))
      (artinBP.pre N) w)

instance sliceProj_faithful (d : Ch Zbp) : (sliceProj d).pathsFunctor.Faithful where
  map_injective {X Y} {R₁ R₂} h := by
    obtain ⟨⟨N, u⟩⟩ := X
    obtain ⟨⟨M, v⟩⟩ := Y
    obtain rfl : N = M :=
      Polygraph.coproduct_path_fst (fun M => artinBP.germPoly (runGermChart d M)) R₁
    obtain ⟨R₁', rfl⟩ :=
      Polygraph.coproduct_exists_mapPath (fun M => artinBP.germPoly (runGermChart d M)) N R₁
    obtain ⟨R₂', rfl⟩ :=
      Polygraph.coproduct_exists_mapPath (fun M => artinBP.germPoly (runGermChart d M)) N R₂
    have h' := (sliceProj_coproductPre (d := d) N R₁').symm.trans
      (h.trans (sliceProj_coproductPre (d := d) N R₂'))
    exact congrArg
      (Polygraph.coproductPre (fun M => artinBP.germPoly (runGermChart d M)) N).mapPath
      (artinBP.germWord_injective (runGermChart d N)
        ((Prefunctor.pathsFunctor_faithful _
          (Polygraph.strandPre_star_injective N)).map_injective h'))

/-- **A copy's 2-cell projects to the relation it carries.** -/
theorem sliceProj_src {d : Ch Zbp} {A B : GenObj (artinBP.slicePoly d).Gen}
    (β : (artinBP.slicePoly d).Rel A B) :
    (sliceProj d).mapPath ((artinBP.slicePoly d).src β)
      = artinBP.poly.src (sliceCell β) := ((sliceDown d).src_two β).symm

theorem sliceProj_tgt {d : Ch Zbp} {A B : GenObj (artinBP.slicePoly d).Gen}
    (β : (artinBP.slicePoly d).Rel A B) :
    (sliceProj d).mapPath ((artinBP.slicePoly d).tgt β)
      = artinBP.poly.tgt (sliceCell β) := ((sliceDown d).tgt_two β).symm

/-- **A 2-cell of a copy is pinned by the relation of the base it carries** — its two words are
the unique lifts of that relation's, so nothing else is left. -/
theorem sliceRel_ext {d : Ch Zbp} {A B : GenObj (artinBP.slicePoly d).Gen}
    (β β' : (artinBP.slicePoly d).Rel A B) (h : sliceCell β = sliceCell β') :
    β = β' :=
  Polygraph.boundaryDetermined_coproduct _
    (fun _ => Polygraph.boundaryDetermined_comap (boundaryDetermined_monoidPoly _) _ _)
    β β'
    ((sliceProj d).pathsFunctor.map_injective
      ((sliceProj_src β).trans ((congrArg artinBP.poly.src h).trans (sliceProj_src β').symm)))
    ((sliceProj d).pathsFunctor.map_injective
      ((sliceProj_tgt β).trans ((congrArg artinBP.poly.tgt h).trans (sliceProj_tgt β').symm)))

/-- A codimension-one chain, read as a 1-cell of the fibration route's polygraph. -/
def atomGenToHLoc {x y : CubeRun n} (e : AtomGen n x y) :
    (artinPt y : GenObj (hLocArtinPoly n).Gen) ⟶ artinPt x :=
  ⟨e.1, by
    have h : (hFibre n).map (ChainCat.atomLoop n e.1) y = x := e.2.atomLoop
    rw [← runLoop_adjT] at h
    exact h⟩

/-- …and back. -/
noncomputable def hLocToAtomGen {x y : CubeRun n}
    (e : (artinPt y : GenObj (hLocArtinPoly n).Gen) ⟶ artinPt x) : AtomGen n x y :=
  ⟨e.1, AtomChain.of (show (hFibre n).map (ChainCat.atomLoop n e.1) y = x by
    rw [← runLoop_adjT]; exact e.2)⟩

/-- **The codimension-one chains from `x` to `y` are the fibration route's 1-cells** — the chart is
forced, so only the cut is left. -/
noncomputable def atomGenEquiv (x y : CubeRun n) :
    AtomGen n x y ≃ ((artinPt y : GenObj (hLocArtinPoly n).Gen) ⟶ artinPt x) where
  toFun := atomGenToHLoc
  invFun := hLocToAtomGen
  left_inv _ := Sigma.ext rfl (heq_of_eq (AtomChain.ext _ _))
  right_inv _ := Subtype.ext rfl

/-! ## The codimension-two chain below a realization

Where both cuts act at a run, the pair chain sits below the chain — with a leg carrying its merge
run to that run.  This is what makes a cell of the pair chain's copy travel into every copy where
the relation is realised. -/

/-- **A run is its crossing permutation, read out of the run on `n` events.** -/
theorem exists_runHom {d : Ch Zbp} (hd : dimSum d.dims = n) (v : RunAt d n) :
    ∃ a : zObj (𝟙^n) ⟶ d, crossPerm (dimSum_replicate n) a = v.perm := by
  obtain ⟨⟨⟨l, ⟨⟩, g⟩, hr⟩, hN⟩ := v
  obtain rfl : l = zObj (𝟙^n) := RunOver.left_eq hd ⟨Over.mk g, hr⟩
  exact ⟨g, rfl⟩

variable {i j : Fin (n - 1)}

/-- **The merge run over the pair chain.** -/
noncomputable def pairMergeRun (hij : (i : ℕ) ≠ (j : ℕ)) : RunAt (pairChain n i j hij) n :=
  RunAt.push (runMerge (pairChain n i j hij) (dimSum_pairChain hij)) (runAtSelf n)

@[simp] theorem perm_pairMergeRun (hij : (i : ℕ) ≠ (j : ℕ)) :
    (pairMergeRun hij).perm = 1 := by
  rw [pairMergeRun, RunAt.push_perm _ (dimSum_replicate n), perm_runAtSelf, mul_one,
    crossPerm_eq_one_of_W _ (W_runMerge _ _)]

/-- **Both cuts acting at a run put the pair chain below it**, merge run to run. -/
theorem exists_pairRunLeg (hij : (i : ℕ) ≠ (j : ℕ)) {d : Ch Zbp} (hd : dimSum d.dims = n)
    {u vi vj : RunAt d n}
    (hi : RunGermStep (posPerm (adjT i)) u vi)
    (hj : RunGermStep (posPerm (adjT j)) u vj) :
    ∃ t : pairChain n i j hij ⟶ d, RunAt.push t (pairMergeRun hij) = u := by
  -- each cut ascends at `u`, and its atom's run descends there
  have step : ∀ (k : Fin (n - 1)) (v : RunAt d n),
      RunGermStep (posPerm (adjT k)) u v →
      u.perm (adjLo k) < u.perm (adjHi k) ∧
        ((dimComp d.dims hd).index (adjLo k) : ℕ)
          = ((dimComp d.dims hd).index (adjHi k) : ℕ) := by
    intro k v hv
    obtain ⟨hperm, hlen⟩ := (runGermStep_adjT_iff k u v).mp hv
    have hasc : u.perm (adjLo k) < u.perm (adjHi k) :=
      ascent_of_permLen_mul_adjT (by rw [← hperm]; omega)
    refine ⟨hasc, ?_⟩
    obtain ⟨a, ha⟩ := exists_runHom hd v
    refine index_adj_eq_of_descent hd a ?_
    rw [ha, hperm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, adjT_hi, adjT_lo]
    exact hasc
  obtain ⟨hasci, hbeadi⟩ := step i vi hi
  obtain ⟨hascj, hbeadj⟩ := step j vj hj
  obtain ⟨a, ha⟩ := exists_runHom hd u
  obtain ⟨t, ht⟩ := exists_pairLeg hij hd
    (fun k hk => by rcases hk with hk | hk
                    · exact (Fin.ext hk : k = i) ▸ hbeadi
                    · exact (Fin.ext hk : k = j) ▸ hbeadj)
    (fun k hk => by rcases hk with hk | hk
                    · exact (Fin.ext hk : k = i) ▸ hasci
                    · exact (Fin.ext hk : k = j) ▸ hascj) ha
  exact ⟨t, RunAt.perm_injective
    (by rw [RunAt.push_perm t (dimSum_pairChain hij), perm_pairMergeRun, mul_one, ht])⟩

/-! ### The square and the hexagon, realised over the pair chain

One step at a time: an ascent at either of the two cuts extends a run over the pair chain, because
the atom's shape sits below it (`exists_leg`) and the crossing is new. -/

/-- A map out of the run, as a run over its target. -/
def runAtOf {d : Ch Zbp} {N : ℕ} (g : zObj (𝟙^N) ⟶ d) : RunAt d N := RunAt.push g (runAtSelf N)

@[simp] theorem perm_runAtOf {d : Ch Zbp} {N : ℕ} (g : zObj (𝟙^N) ⟶ d) :
    (runAtOf g).perm = crossPerm (dimSum_replicate N) g := by
  rw [runAtOf, RunAt.push_perm g (dimSum_replicate N), perm_runAtSelf, mul_one]

/-- **An ascent at either cut extends a run over the pair chain**, and the extension is the
generator acting. -/
theorem exists_sliceStep (hij : (i : ℕ) ≠ (j : ℕ)) {k : Fin (n - 1)}
    (hk : k = i ∨ k = j) {σ : Equiv.Perm (Fin n)} (hasc : σ (adjLo k) < σ (adjHi k))
    (u : RunAt (pairChain n i j hij) n) (hu : u.perm = σ) :
    ∃ v : RunAt (pairChain n i j hij) n, v.perm = σ * adjT k ∧
      RunGermStep (posPerm (adjT k)) u v := by
  obtain ⟨a, ha⟩ := exists_runHom (dimSum_pairChain hij) u
  have hnk : Nonempty (zObj (atomComp n k) ⟶ pairChain n i j hij) := by
    rcases hk with rfl | rfl
    · exact nonempty_left_pairChain hij
    · exact nonempty_right_pairChain hij
  obtain ⟨w, hw⟩ := exists_leg k (dimSum_pairChain hij) hnk hasc (ha.trans hu)
  refine ⟨runAtOf (atomOnes n k ≫ w), ?_, ?_⟩
  · rw [perm_runAtOf, crossPerm_comp, hw, crossPerm_atomOnes]
  · refine (runGermStep_adjT_iff k u _).mpr ⟨?_, ?_⟩
    · rw [perm_runAtOf, crossPerm_comp, hw, crossPerm_atomOnes, hu]
    · rw [perm_runAtOf, crossPerm_comp, hw, crossPerm_atomOnes, hu, permLen_mul_adjT hasc]

/-- **The chart above a run** — the run, un-merged along the merge into `d`. -/
noncomputable def mergeWitness {d : Ch Zbp} (hd : dimSum d.dims = n) (z : CubeRun n) :
    (wedgeHoms (Hbp.obj (□n))).obj (op d) :=
  wWitness (W_runMerge d hd) z

theorem runMerge_mergeWitness {d : Ch Zbp} (hd : dimSum d.dims = n) (z : CubeRun n) :
    (runMerge d hd).φ ≫ mergeWitness hd z = z :=
  φ_wWitness (W_runMerge d hd) z

/-- **…and it is the only chart above it.** -/
theorem eq_mergeWitness {d : Ch Zbp} (hd : dimSum d.dims = n)
    {W : (wedgeHoms (Hbp.obj (□n))).obj (op d)} {z : CubeRun n}
    (hW : (runMerge d hd).φ ≫ W = z) : W = mergeWitness hd z :=
  eq_wWitness (W_runMerge d hd) hW

attribute [irreducible] mergeWitness

/-- **A relation of the base, lifted to a parallel pair of words over the runs** — the 2-cell of the
copy it names. -/
def sliceRelOf {d : Ch Zbp} {N : ℕ} {u v : RunAt d N}
    (S T : Quiver.Path (⟨u⟩ : GenObj (artinBP.GermGen (runGermChart d N))) ⟨v⟩)
    (ρ : (artinBP.P N).Rel ⟨artinBP.v N⟩ ⟨artinBP.v N⟩)
    (hS : artinBP.germWord (runGermChart d N) S = (artinBP.P N).src ρ)
    (hT : artinBP.germWord (runGermChart d N) T = (artinBP.P N).tgt ρ) :
    (artinBP.slicePoly d).Rel ⟨artinBP.runPt u⟩ ⟨artinBP.runPt v⟩ :=
  Polygraph.CoproductRel.mk (i := N)
    { src := S, tgt := T, cell := ρ, src_eq := hS, tgt_eq := hT }

@[simp] theorem sliceRelOf_cell {d : Ch Zbp} {N : ℕ} {u v : RunAt d N} (S T) (ρ) (hS) (hT) :
    sliceCell (sliceRelOf (d := d) (N := N) (u := u) (v := v) S T ρ hS hT)
      = Polygraph.StrandRel.mk (i := N) ρ := rfl

@[simp] theorem sliceRelOf_src {d : Ch Zbp} {N : ℕ} {u v : RunAt d N} (S T) (ρ) (hS) (hT) :
    (artinBP.slicePoly d).src (sliceRelOf (d := d) (N := N) (u := u) (v := v) S T ρ hS hT)
      = (Polygraph.coproductPre (fun M => artinBP.germPoly (runGermChart d M)) N).mapPath S := rfl

@[simp] theorem sliceRelOf_tgt {d : Ch Zbp} {N : ℕ} {u v : RunAt d N} (S T) (ρ) (hS) (hT) :
    (artinBP.slicePoly d).tgt (sliceRelOf (d := d) (N := N) (u := u) (v := v) S T ρ hS hT)
      = (Polygraph.coproductPre (fun M => artinBP.germPoly (runGermChart d M)) N).mapPath T := rfl

/-! ### The two relations, realised over the pair chain -/

theorem adjT_apply_of_ne {k : Fin (n - 1)} {x : Fin n} (h1 : (x : ℕ) ≠ (k : ℕ))
    (h2 : (x : ℕ) ≠ (k : ℕ) + 1) : adjT k x = x :=
  Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h, adjLo_val]))
    fun h => h2 (by rw [h, adjHi_val])

theorem adjT_lo_lt_hi (k : Fin (n - 1)) : adjLo k < adjHi k := by
  rw [Fin.lt_def, adjLo_val, adjHi_val]; omega

/-- A cut, as a one-letter word of the base. -/
noncomputable def artinBaseLetter (i : Fin (n - 1)) :
    Quiver.Path (⟨artinBP.v n⟩ : GenObj (artinBP.P n).Gen) ⟨artinBP.v n⟩ :=
  Quiver.Hom.toPath (i : (⟨artinBP.v n⟩ : GenObj (artinBP.P n).Gen) ⟶ ⟨artinBP.v n⟩)

/-- The two-letter word of the base at a pair of cuts. -/
noncomputable def artinBaseWord₂ (i j : Fin (n - 1)) :
    Quiver.Path (⟨artinBP.v n⟩ : GenObj (artinBP.P n).Gen) ⟨artinBP.v n⟩ :=
  (artinBaseLetter i).comp (artinBaseLetter j)

/-- …and the three-letter one. -/
noncomputable def artinBaseWord₃ (i j k : Fin (n - 1)) :
    Quiver.Path (⟨artinBP.v n⟩ : GenObj (artinBP.P n).Gen) ⟨artinBP.v n⟩ :=
  (artinBaseWord₂ i j).comp (artinBaseLetter k)

/-- **A generator acting in a copy is the codimension-one chain the two runs name.** -/
theorem ιE_runGen_atomEdge {d : Ch Zbp} (hd : dimSum d.dims = n)
    (W : (wedgeHoms (Hbp.obj (□n))).obj (op d)) {k : Fin (n - 1)} {u v : RunAt d n}
    (hact : RunGermStep (posPerm (adjT k)) u v)
    {a b : CubeRun n} (ha : runOf (Hbp.obj (□n)) hd W v = a)
    (hb : runOf (Hbp.obj (□n)) hd W u = b) (E : AtomChain n k a b) :
    Quiver.homOfEq (ιE (Hbp.obj (□n)) artinBP.fam (op ⟨op d, W⟩) (artinBP.runGen k hact))
        ((ιV_runOf (Hbp.obj (□n)) hd W v).trans (congrArg (artinBP.ιRun _) ha))
        ((ιV_runOf (Hbp.obj (□n)) hd W u).trans (congrArg (artinBP.ιRun _) hb))
      = (artinChainPre n).map (atomEdge E) := by
  subst ha
  subst hb
  obtain ⟨w, h₁, h₂, hE⟩ := ιE_runGen_atomChain (K := Hbp.obj (□n)) hd W hact
  obtain rfl : E = ⟨w, h₁, h₂⟩ := AtomChain.ext _ _
  simpa using hE

/-- A generator acting on a run, read as a 1-cell of the copy — the slice polygraph reversed, so
the 1-cell runs from the acted-to run back to the run. -/
noncomputable def famGen {d : Ch Zbp} {N : ℕ} {u v : RunAt d N} (s : artinBP.S N)
    (h : RunGermStep (artinBP.braid s) u v) :
    (⟨artinBP.runPt v⟩ : GenObj (artinBP.fam.obj d).Gen) ⟶ ⟨artinBP.runPt u⟩ :=
  artinBP.runGen s h

/-- **The `Br` boundary of a two-letter word of a copy**, letter by letter. -/
theorem cellCongr_ιWord₂ {d : Ch Zbp} (hd : dimSum d.dims = n)
    (W : (wedgeHoms (Hbp.obj (□n))).obj (op d)) {k l : Fin (n - 1)} {u₀ u₁ u₂ : RunAt d n}
    (h₀₁ : RunGermStep (posPerm (adjT k)) u₀ u₁)
    (h₁₂ : RunGermStep (posPerm (adjT l)) u₁ u₂)
    {a b c : CubeRun n} (ha : runOf (Hbp.obj (□n)) hd W u₂ = a)
    (hb : runOf (Hbp.obj (□n)) hd W u₁ = b) (hc : runOf (Hbp.obj (□n)) hd W u₀ = c)
    (E₁ : AtomChain n l a b) (E₂ : AtomChain n k b c) :
    cellCongr Quiver.Path
        ((ιV_runOf (Hbp.obj (□n)) hd W u₂).trans (congrArg (artinBP.ιRun _) ha))
        ((ιV_runOf (Hbp.obj (□n)) hd W u₀).trans (congrArg (artinBP.ιRun _) hc))
        ((Limits.colimit.ι (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)
            (op ⟨op d, W⟩)).pre.mapPath
          ((Quiver.Hom.toPath (famGen l h₁₂)).cons (famGen k h₀₁)))
      = (artinChainPre n).mapPath (atomWord₂ E₁ E₂) := by
  change cellCongr Quiver.Path _ _
      ((Quiver.Hom.toPath
          (ιE (Hbp.obj (□n)) artinBP.fam (op ⟨op d, W⟩) (famGen l h₁₂))).cons
        (ιE (Hbp.obj (□n)) artinBP.fam (op ⟨op d, W⟩) (famGen k h₀₁))) = _
  rw [cellCongr_cons _ ((ιV_runOf (Hbp.obj (□n)) hd W u₁).trans
      (congrArg (artinBP.ιRun _) hb)) _, cellCongr_toPath]
  exact congrArg₂ Quiver.Path.cons
    (congrArg Quiver.Hom.toPath (ιE_runGen_atomEdge hd W h₁₂ ha hb E₁))
    (ιE_runGen_atomEdge hd W h₀₁ hb hc E₂)

/-- …and of a three-letter one. -/
theorem cellCongr_ιWord₃ {d : Ch Zbp} (hd : dimSum d.dims = n)
    (W : (wedgeHoms (Hbp.obj (□n))).obj (op d)) {k l m : Fin (n - 1)}
    {u₀ u₁ u₂ u₃ : RunAt d n}
    (h₀₁ : RunGermStep (posPerm (adjT k)) u₀ u₁)
    (h₁₂ : RunGermStep (posPerm (adjT l)) u₁ u₂)
    (h₂₃ : RunGermStep (posPerm (adjT m)) u₂ u₃)
    {a b c e : CubeRun n} (ha : runOf (Hbp.obj (□n)) hd W u₃ = a)
    (hb : runOf (Hbp.obj (□n)) hd W u₂ = b) (hc : runOf (Hbp.obj (□n)) hd W u₁ = c)
    (he : runOf (Hbp.obj (□n)) hd W u₀ = e)
    (E₁ : AtomChain n m a b) (E₂ : AtomChain n l b c) (E₃ : AtomChain n k c e) :
    cellCongr Quiver.Path
        ((ιV_runOf (Hbp.obj (□n)) hd W u₃).trans (congrArg (artinBP.ιRun _) ha))
        ((ιV_runOf (Hbp.obj (□n)) hd W u₀).trans (congrArg (artinBP.ιRun _) he))
        ((Limits.colimit.ι (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)
            (op ⟨op d, W⟩)).pre.mapPath
          (((Quiver.Hom.toPath (famGen m h₂₃)).cons (famGen l h₁₂)).cons (famGen k h₀₁)))
      = (artinChainPre n).mapPath (atomWord₃ E₁ E₂ E₃) := by
  change cellCongr Quiver.Path _ _
      (((Quiver.Hom.toPath
            (ιE (Hbp.obj (□n)) artinBP.fam (op ⟨op d, W⟩) (famGen m h₂₃))).cons
          (ιE (Hbp.obj (□n)) artinBP.fam (op ⟨op d, W⟩) (famGen l h₁₂))).cons
        (ιE (Hbp.obj (□n)) artinBP.fam (op ⟨op d, W⟩) (famGen k h₀₁))) = _
  rw [cellCongr_cons _ ((ιV_runOf (Hbp.obj (□n)) hd W u₁).trans
      (congrArg (artinBP.ιRun _) hc)) _]
  exact congrArg₂ Quiver.Path.cons
    (cellCongr_ιWord₂ hd W h₁₂ h₂₃ ha hb hc E₁ E₂)
    (ιE_runGen_atomEdge hd W h₀₁ hc he E₃)

/-! ### A word of codimension-one chains is its cuts and the runs it passes through

Reading a word off as a list avoids every heterogeneous equality: two equal words have equal
lists, and a list is injective in its entries. -/

/-- The cuts a word crosses, each with the run it lands on.  `Quiver.Path.rec` and not the equation
compiler: only the eliminator gives definitional equations on a `comp`. -/
def wordData {A : GenObj (AtomGen n)} :
    ∀ {B : GenObj (AtomGen n)}, Quiver.Path A B → List (Fin (n - 1) × CubeRun n) :=
  fun {_} p =>
    Quiver.Path.rec (motive := fun {_} _ => List (Fin (n - 1) × CubeRun n)) []
      (fun {B C} _ (e : AtomGen n B.as C.as) ih => ih ++ [(e.1, C.as)]) p

@[simp] theorem wordData_atomWord₂ {i j : Fin (n - 1)} {x y z : CubeRun n}
    (e₁ : AtomChain n i x y) (e₂ : AtomChain n j y z) :
    wordData (atomWord₂ e₁ e₂) = [(i, y), (j, z)] := rfl

@[simp] theorem wordData_atomWord₃ {i j k : Fin (n - 1)} {w x y z : CubeRun n}
    (e₁ : AtomChain n i w x) (e₂ : AtomChain n j x y) (e₃ : AtomChain n k y z) :
    wordData (atomWord₃ e₁ e₂ e₃) = [(i, x), (j, y), (k, z)] := rfl

/-- **A run over a copy is pinned by the 0-cell it names** — `fibrePerm` reads the run's crossing
permutation off the chart it restricts. -/
theorem runOf_injective {d : Ch Zbp} (hd : dimSum d.dims = n)
    (W : (wedgeHoms (Hbp.obj (□n))).obj (op d)) :
    Function.Injective (runOf (Hbp.obj (□n)) hd W) := by
  intro v v' h
  obtain ⟨t, ht⟩ := exists_runPush hd v
  obtain ⟨t', ht'⟩ := exists_runPush hd v'
  rw [runOf_eq _ hd W ht, runOf_eq _ hd W ht'] at h
  have h2 := congrArg (fibrePerm (A := zObj (𝟙^n)) (dimSum_replicate n)) h
  rw [fibrePerm_comp (dimSum_replicate n) hd t W,
    fibrePerm_comp (dimSum_replicate n) hd t' W] at h2
  have hcross : crossPerm (dimSum_replicate n) t = crossPerm (dimSum_replicate n) t' :=
    inv_injective (mul_right_cancel h2)
  rw [← ht, ← ht', hom_ext_of_crossPerm hcross]

/-! ### The braid a copy's 2-cell performs

`germStep_germWord` is the whole content: a word of a copy is its own germ word, so the cell's own
relation makes the germ step joining the runs its boundary spans.  Then the germ's product is
defined stepwise, so a step of a product is a step of its first factor — which is the cut the
codimension-two chain is entered by. -/

/-- **A word of a copy performs the braid it spells** — the whole content, read on a word so that
the two words of a 2-cell are one statement. -/
theorem sliceWord_action {d : Ch Zbp} {N : ℕ} {u v : RunAt d N}
    (R : Quiver.Path (⟨artinBP.runPt u⟩ : GenObj (artinBP.slicePoly d).Gen)
      ⟨artinBP.runPt v⟩)
    {W : Quiver.Path (⟨artinBP.v N⟩ : GenObj (artinBP.P N).Gen) ⟨artinBP.v N⟩}
    (hW : (sliceProj d).mapPath R = (artinBP.pre N).mapPath W) :
    RunGermStep (((artinBP.comp N).eval.map W).unop) u v := by
  obtain ⟨R', rfl⟩ :=
    Polygraph.coproduct_exists_mapPath (fun M => artinBP.germPoly (runGermChart d M)) N R
  obtain rfl : artinBP.germWord (runGermChart d N) R' = W :=
    (Prefunctor.pathsFunctor_faithful _
      (Polygraph.strandPre_star_injective N)).map_injective
        ((sliceProj_coproductPre (d := d) N R').symm.trans hW)
  exact artinBP.germStep_germWord (runGermChart d N) R'

theorem sliceRel_action {d : Ch Zbp} {N : ℕ} {u v : RunAt d N}
    (β : (artinBP.slicePoly d).Rel ⟨artinBP.runPt u⟩ ⟨artinBP.runPt v⟩)
    {W : Quiver.Path (⟨artinBP.v N⟩ : GenObj (artinBP.P N).Gen) ⟨artinBP.v N⟩}
    (hW : artinBP.poly.src (sliceCell β) = (artinBP.pre N).mapPath W) :
    RunGermStep (((artinBP.comp N).eval.map W).unop) u v :=
  sliceWord_action ((artinBP.slicePoly d).src β) ((sliceProj_src β).trans hW)

theorem sliceRel_action_tgt {d : Ch Zbp} {N : ℕ} {u v : RunAt d N}
    (β : (artinBP.slicePoly d).Rel ⟨artinBP.runPt u⟩ ⟨artinBP.runPt v⟩)
    {W : Quiver.Path (⟨artinBP.v N⟩ : GenObj (artinBP.P N).Gen) ⟨artinBP.v N⟩}
    (hW : artinBP.poly.tgt (sliceCell β) = (artinBP.pre N).mapPath W) :
    RunGermStep (((artinBP.comp N).eval.map W).unop) u v :=
  sliceWord_action ((artinBP.slicePoly d).tgt β) ((sliceProj_tgt β).trans hW)

/-- **A germ step of a product is a germ step of its first factor.** -/
theorem runGermStep_first {d : Ch Zbp} {N : ℕ} (a b : PosBraid N) {u v : RunAt d N}
    (h : RunGermStep (a * b) u v) : ∃ w, RunGermStep a u w :=
  (runGermStep_prefix h).imp fun _ hw => hw.1

/-! ### The shapes, named

A codimension-two chain is its two cuts and which of the two shapes they make; everything about
the cell it carries — the chain, the relation of the base, the runs its words pass through — is a
function of that. -/

/-- **Which shape a codimension-two chain has**, and where its two cuts are. -/
inductive PairKind (n : ℕ) : Type
  | comm (i j : Fin (n - 1)) (hij : (i : ℕ) + 1 < (j : ℕ)) : PairKind n
  | braid (i j : Fin (n - 1)) (hij : (j : ℕ) = (i : ℕ) + 1) : PairKind n

namespace PairKind

/-- Its two cuts. -/
def cuts : PairKind n → Fin (n - 1) × Fin (n - 1)
  | .comm i j _ => (i, j)
  | .braid i j _ => (i, j)

theorem ne : ∀ K : PairKind n, ((K.cuts.1 : ℕ) ≠ (K.cuts.2 : ℕ))
  | .comm _ _ hij => by simp only [cuts]; omega
  | .braid _ _ hij => by simp only [cuts]; omega

/-- The codimension-two chain it is. -/
noncomputable def chain (K : PairKind n) : Ch Zbp := pairChain n K.cuts.1 K.cuts.2 K.ne

theorem hdim (K : PairKind n) : dimSum K.chain.dims = n := dimSum_pairChain K.ne

/-- …and the merge run over it. -/
noncomputable def mergeRun (K : PairKind n) : RunAt K.chain n := pairMergeRun K.ne

/-- The relation of the base it carries. -/
noncomputable def rel : ∀ K : PairKind n, (artinBP.P n).Rel ⟨artinBP.v n⟩ ⟨artinBP.v n⟩
  | .comm i j hij => ⟨(artinBaseWord₂ i j, artinBaseWord₂ j i), ArtinRel.comm i j hij⟩
  | .braid i j hij => ⟨(artinBaseWord₃ i j i, artinBaseWord₃ j i j), ArtinRel.braid i j hij⟩

/-- The run its source word ends at: its cuts, acting on `z` in order. -/
noncomputable def top : PairKind n → CubeRun n → CubeRun n
  | .comm i j _, z => atomStep j (atomStep i z)
  | .braid i j _, z => atomStep i (atomStep j (atomStep i z))

/-- **The codimension-two chain of a shape at a run, as a 2-cell** — the square, or the hexagon.
Only the far corner needs an argument: it is where the two cuts' actions meet. -/
noncomputable def cell : ∀ (K : PairKind n) (z : CubeRun n),
    (artinChainPoly n).Rel ⟨K.top z⟩ ⟨z⟩
  | .comm i j hij, z =>
      ⟨(atomWord₂ (AtomChain.of (k := j) (y := atomStep i z) rfl)
          (AtomChain.of (k := i) (y := z) rfl),
        atomWord₂ (AtomChain.of (k := i) (y := atomStep j z) (atomStep_comm hij z))
          (AtomChain.of (k := j) (y := z) rfl)),
        ArtinChainRel.comm hij _ _ _ _⟩
  | .braid i j hij, z =>
      ⟨(atomWord₃ (AtomChain.of (k := i) (y := atomStep j (atomStep i z)) rfl)
          (AtomChain.of (k := j) (y := atomStep i z) rfl)
          (AtomChain.of (k := i) (y := z) rfl),
        atomWord₃ (AtomChain.of (k := j) (y := atomStep i (atomStep j z))
            (atomStep_braid hij z).symm)
          (AtomChain.of (k := i) (y := atomStep j z) rfl)
          (AtomChain.of (k := j) (y := z) rfl)),
        ArtinChainRel.braid hij _ _ _ _ _ _⟩

/-- The cuts its source word crosses, each with the run it lands on. -/
noncomputable def srcData : PairKind n → CubeRun n → List (Fin (n - 1) × CubeRun n)
  | .comm i j _, z => [(j, atomStep i z), (i, z)]
  | .braid i j _, z => [(i, atomStep j (atomStep i z)), (j, atomStep i z), (i, z)]

/-- **…and that is what the cell's source word spells.** -/
theorem wordData_src_cell (K : PairKind n) (z : CubeRun n) :
    wordData ((artinChainPoly n).src (K.cell z)) = K.srcData z := by cases K <;> rfl

/-- **A shape and a run are read off the word they spell.** -/
theorem srcData_inj : ∀ {K K' : PairKind n} {z z' : CubeRun n},
    K.srcData z = K'.srcData z' → K = K' ∧ z = z'
  | .comm _ _ _, .comm _ _ _, _, _, h => by
      simp only [srcData, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, -⟩, ⟨rfl, rfl⟩, -⟩ := h
      exact ⟨rfl, rfl⟩
  | .braid _ _ _, .braid _ _ _, _, _, h => by
      simp only [srcData, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨-, ⟨rfl, -⟩, ⟨rfl, rfl⟩, -⟩ := h
      exact ⟨rfl, rfl⟩
  | .comm _ _ _, .braid _ _ _, _, _, h => by simp [srcData] at h
  | .braid _ _ _, .comm _ _ _, _, _, h => by simp [srcData] at h

end PairKind

/-- **`γ` is the codimension-two chain's own 2-cell**: it comes from a copy at the shape's chain
whose chart restricts to `z`, and carries the shape's relation from the merge run. -/
def IsPairCell (K : PairKind n) (z : CubeRun n)
    {A B : GenObj (artinBP.Br (Hbp.obj (□n))).Gen}
    (γ : (artinBP.Br (Hbp.obj (□n))).Rel A B) : Prop :=
  ∃ (V : (wedgeHoms (Hbp.obj (□n))).obj (op K.chain)) (v : RunAt K.chain n)
    (β : (artinBP.slicePoly K.chain).Rel
        ⟨artinBP.runPt K.mergeRun⟩ ⟨artinBP.runPt v⟩)
    (hA : ιV (Hbp.obj (□n)) artinBP.fam (op ⟨op K.chain, V⟩) (artinBP.runPt v) = A)
    (hB : ιV (Hbp.obj (□n)) artinBP.fam (op ⟨op K.chain, V⟩)
      (artinBP.runPt K.mergeRun) = B),
    (runMerge K.chain K.hdim).φ ≫ V = z ∧
      sliceCell β = Polygraph.StrandRel.mk (i := n) K.rel ∧
        cellCongr (artinBP.Br (Hbp.obj (□n))).Rel hA hB
          ((Limits.colimit.ι (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)
            (op ⟨op K.chain, V⟩)).two β)
          = γ

/-- **The shape and the run pin the cell, endpoints and all**: the chart above `z` is unique
(`eq_mergeWitness`), the run its boundary reaches is the relation acting (`sliceRel_action`), and a
2-cell of a copy is the relation it carries (`sliceRel_ext`). -/
theorem IsPairCell.eq {K : PairKind n} {z : CubeRun n}
    {A B A' B' : GenObj (artinBP.Br (Hbp.obj (□n))).Gen}
    {γ : (artinBP.Br (Hbp.obj (□n))).Rel A B} {γ' : (artinBP.Br (Hbp.obj (□n))).Rel A' B'}
    (h : IsPairCell K z γ) (h' : IsPairCell K z γ') :
    ∃ (hA : A = A') (hB : B = B'), cellCongr (artinBP.Br (Hbp.obj (□n))).Rel hA hB γ = γ' := by
  obtain ⟨V, v, β, hA, hB, hV, hcell, hγ⟩ := h
  obtain ⟨V', v', β', hA', hB', hV', hcell', hγ'⟩ := h'
  obtain rfl : V' = V := (eq_mergeWitness K.hdim hV').trans (eq_mergeWitness K.hdim hV).symm
  obtain rfl : v' = v :=
    RunAt.perm_injective
      ((CubeChains.GermStep.mul_eq
          (sliceRel_action β' (congrArg artinBP.poly.src hcell'))).trans
        (CubeChains.GermStep.mul_eq
          (sliceRel_action β (congrArg artinBP.poly.src hcell))).symm)
  obtain rfl : β' = β := sliceRel_ext β' β (hcell'.trans hcell.symm)
  subst hA; subst hB; subst hA'; subst hB'
  exact ⟨rfl, rfl, hγ.symm.trans hγ'⟩

/-! ### The codimension-two chain's own 2-cell

Over the pair chain both cuts ascend from the merge run, one step at a time (`exists_sliceStep`),
and each step is a codimension-one chain (`ιE_runGen_atomChain`); so the shape's relation is
realised there with the shape's own two words as its boundary. -/

/-- **A 2-cell of a copy at the pair chain, above `z`, is the shape's.** -/
theorem isPairCell_of_copy (K : PairKind n) {z : CubeRun n}
    {V : (wedgeHoms (Hbp.obj (□n))).obj (op K.chain)}
    (hV : (runMerge K.chain K.hdim).φ ≫ V = z) {v : RunAt K.chain n}
    (β : (artinBP.slicePoly K.chain).Rel ⟨artinBP.runPt K.mergeRun⟩ ⟨artinBP.runPt v⟩)
    (hcell : sliceCell β = Polygraph.StrandRel.mk (i := n) K.rel)
    {A B : GenObj (artinBP.Br (Hbp.obj (□n))).Gen}
    (hA : ιV (Hbp.obj (□n)) artinBP.fam (op ⟨op K.chain, V⟩) (artinBP.runPt v) = A)
    (hB : ιV (Hbp.obj (□n)) artinBP.fam (op ⟨op K.chain, V⟩)
      (artinBP.runPt K.mergeRun) = B) :
    IsPairCell K z (cellCongr (artinBP.Br (Hbp.obj (□n))).Rel hA hB
      ((Limits.colimit.ι (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)
        (op ⟨op K.chain, V⟩)).two β)) :=
  ⟨V, v, β, hA, hB, hV, hcell, rfl⟩

/-- **The 2-cell of `Br` a shape at a run is**, with the shape's own two words as its boundary. -/
theorem exists_pairBrCell (K : PairKind n) (z : CubeRun n) :
    ∃ γ : (artinBP.Br (Hbp.obj (□n))).Rel
        ((artinChainPre n).obj ⟨K.top z⟩) ((artinChainPre n).obj ⟨z⟩),
      (artinBP.Br (Hbp.obj (□n))).src γ
          = (artinChainPre n).mapPath ((artinChainPoly n).src (K.cell z)) ∧
        (artinBP.Br (Hbp.obj (□n))).tgt γ
          = (artinChainPre n).mapPath ((artinChainPoly n).tgt (K.cell z)) ∧
        IsPairCell K z γ := by
  have hlo : ∀ k : Fin (n - 1),
      (1 : Equiv.Perm (Fin n)) (adjLo k) < (1 : Equiv.Perm (Fin n)) (adjHi k) := fun k => by
    simpa using adjT_lo_lt_hi k
  cases K with
  | comm i j hij =>
      have hij' : (i : ℕ) ≠ (j : ℕ) := by omega
      have hd : dimSum (pairChain n i j hij').dims = n := dimSum_pairChain hij'
      have hfix : ∀ k l : Fin (n - 1), (k : ℕ) + 1 < (l : ℕ) ∨ (l : ℕ) + 1 < (k : ℕ) →
          adjT k (adjLo l) < adjT k (adjHi l) := fun k l hkl => by
        rw [adjT_apply_of_ne (by rw [adjLo_val]; omega) (by rw [adjLo_val]; omega),
          adjT_apply_of_ne (by rw [adjHi_val]; omega) (by rw [adjHi_val]; omega)]
        exact adjT_lo_lt_hi l
      obtain ⟨u₁, hp₁, h₀₁⟩ := exists_sliceStep hij' (Or.inl rfl) (hlo i) (pairMergeRun hij')
        (perm_pairMergeRun hij')
      obtain ⟨u₂, hp₂, h₁₂⟩ := exists_sliceStep hij' (Or.inr rfl) (hfix i j (Or.inl hij)) u₁
        (by rw [hp₁, one_mul])
      obtain ⟨v₁, hq₁, k₀₁⟩ := exists_sliceStep hij' (Or.inr rfl) (hlo j) (pairMergeRun hij')
        (perm_pairMergeRun hij')
      obtain ⟨v₂, hq₂, k₁₂⟩ := exists_sliceStep hij' (Or.inl rfl) (hfix j i (Or.inr hij)) v₁
        (by rw [hq₁, one_mul])
      obtain rfl : u₂ = v₂ :=
        RunAt.perm_injective (by rw [hp₂, hq₂, adjT_comm i j hij])
      have hr₀ : runOf (Hbp.obj (□n)) hd (mergeWitness hd z) (pairMergeRun hij') = z :=
        (runOf_eq (Hbp.obj (□n)) hd (mergeWitness hd z) rfl).trans (runMerge_mergeWitness hd z)
      obtain ⟨w₁, hc₁, hm₁, -⟩ :=
        ιE_runGen_atomChain (K := Hbp.obj (□n)) hd (mergeWitness hd z) h₀₁
      have hry : runOf (Hbp.obj (□n)) hd (mergeWitness hd z) u₁ = atomStep i z :=
        (AtomChain.atomLoop (⟨w₁, hc₁, hm₁.trans hr₀⟩ : AtomChain n i _ z)).symm
      obtain ⟨w₂, hc₂, hm₂, -⟩ :=
        ιE_runGen_atomChain (K := Hbp.obj (□n)) hd (mergeWitness hd z) h₁₂
      have hrx : runOf (Hbp.obj (□n)) hd (mergeWitness hd z) u₂ = atomStep j (atomStep i z) :=
        (AtomChain.atomLoop (⟨w₂, hc₂, hm₂.trans hry⟩ : AtomChain n j _ (atomStep i z))).symm
      obtain ⟨w₃, hc₃, hm₃, -⟩ :=
        ιE_runGen_atomChain (K := Hbp.obj (□n)) hd (mergeWitness hd z) k₀₁
      have hry' : runOf (Hbp.obj (□n)) hd (mergeWitness hd z) v₁ = atomStep j z :=
        (AtomChain.atomLoop (⟨w₃, hc₃, hm₃.trans hr₀⟩ : AtomChain n j _ z)).symm
      refine ⟨cellCongr (artinBP.Br (Hbp.obj (□n))).Rel
        ((ιV_runOf (Hbp.obj (□n)) hd (mergeWitness hd z) u₂).trans
          (congrArg (artinBP.ιRun (Hbp.obj (□n))) hrx))
        ((ιV_runOf (Hbp.obj (□n)) hd (mergeWitness hd z) (pairMergeRun hij')).trans
          (congrArg (artinBP.ιRun (Hbp.obj (□n))) hr₀))
        ((Limits.colimit.ι (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)
            (op ⟨op (pairChain n i j hij'), mergeWitness hd z⟩)).two
          (sliceRelOf
            ((Quiver.Path.nil.cons (artinBP.runGenFibre i h₀₁)).cons
              (artinBP.runGenFibre j h₁₂))
            ((Quiver.Path.nil.cons (artinBP.runGenFibre j k₀₁)).cons
              (artinBP.runGenFibre i k₁₂))
            (⟨(artinBaseWord₂ i j, artinBaseWord₂ j i), ArtinRel.comm i j hij⟩ :
              (artinBP.P n).Rel ⟨artinBP.v n⟩ ⟨artinBP.v n⟩) rfl rfl)), ?_, ?_, ?_⟩
      · exact (src_cellCongr _ _ _).trans
          ((congrArg (cellCongr Quiver.Path _ _)
            ((Limits.colimit.ι (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)
              (op ⟨op (pairChain n i j hij'), mergeWitness hd z⟩)).src_two _)).trans
            (cellCongr_ιWord₂ hd (mergeWitness hd z) h₀₁ h₁₂ hrx hry hr₀ _ _))
      · exact (tgt_cellCongr _ _ _).trans
          ((congrArg (cellCongr Quiver.Path _ _)
            ((Limits.colimit.ι (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)
              (op ⟨op (pairChain n i j hij'), mergeWitness hd z⟩)).tgt_two _)).trans
            (cellCongr_ιWord₂ hd (mergeWitness hd z) k₀₁ k₁₂ hrx hry' hr₀ _ _))
      · exact isPairCell_of_copy _ (runMerge_mergeWitness hd z) _ rfl _ _
  | braid i j hij =>
      have hij' : (i : ℕ) ≠ (j : ℕ) := by omega
      have hd : dimSum (pairChain n i j hij').dims = n := dimSum_pairChain hij'
      have hji : adjLo j = adjHi i := Fin.ext (by rw [adjLo_val, adjHi_val]; omega)
      have c1 : adjT j (adjLo i) = adjLo i :=
        adjT_apply_of_ne (by rw [adjLo_val]; omega) (by rw [adjLo_val]; omega)
      have c2 : adjT i (adjLo i) = adjHi i := adjT_lo i
      have c3 : adjT j (adjHi i) = adjHi j := by rw [← hji]; exact adjT_lo j
      have c4 : adjT i (adjHi j) = adjHi j :=
        adjT_apply_of_ne (by rw [adjHi_val]; omega) (by rw [adjHi_val]; omega)
      have c6 : adjT i (adjLo j) = adjLo i := by rw [hji]; exact adjT_hi i
      have c7 : adjT j (adjHi j) = adjLo j := adjT_hi j
      have ha2 : adjT i (adjLo j) < adjT i (adjHi j) := by
        rw [c6, c4, Fin.lt_def, adjLo_val, adjHi_val]; omega
      have ha3 : (adjT i * adjT j) (adjLo i) < (adjT i * adjT j) (adjHi i) := by
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, c1, c2, c3, c4, Fin.lt_def, adjHi_val,
          adjHi_val]
        omega
      have hb2 : adjT j (adjLo i) < adjT j (adjHi i) := by
        rw [c1, c3, Fin.lt_def, adjLo_val, adjHi_val]; omega
      have hb3 : (adjT j * adjT i) (adjLo j) < (adjT j * adjT i) (adjHi j) := by
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, c6, c1, c4, c7, Fin.lt_def, adjLo_val,
          adjLo_val]
        omega
      obtain ⟨u₁, hp₁, h₀₁⟩ := exists_sliceStep hij' (Or.inl rfl) (hlo i) (pairMergeRun hij')
        (perm_pairMergeRun hij')
      obtain ⟨u₂, hp₂, h₁₂⟩ := exists_sliceStep hij' (Or.inr rfl) ha2 u₁ (by rw [hp₁, one_mul])
      obtain ⟨u₃, hp₃, h₂₃⟩ := exists_sliceStep hij' (Or.inl rfl) ha3 u₂ (by rw [hp₂])
      obtain ⟨v₁, hq₁, k₀₁⟩ := exists_sliceStep hij' (Or.inr rfl) (hlo j) (pairMergeRun hij')
        (perm_pairMergeRun hij')
      obtain ⟨v₂, hq₂, k₁₂⟩ := exists_sliceStep hij' (Or.inl rfl) hb2 v₁ (by rw [hq₁, one_mul])
      obtain ⟨v₃, hq₃, k₂₃⟩ := exists_sliceStep hij' (Or.inr rfl) hb3 v₂ (by rw [hq₂])
      obtain rfl : u₃ = v₃ :=
        RunAt.perm_injective (by rw [hp₃, hq₃, adjT_braid i j hij])
      have hr₀ : runOf (Hbp.obj (□n)) hd (mergeWitness hd z) (pairMergeRun hij') = z :=
        (runOf_eq (Hbp.obj (□n)) hd (mergeWitness hd z) rfl).trans (runMerge_mergeWitness hd z)
      obtain ⟨w₁, hc₁, hm₁, -⟩ :=
        ιE_runGen_atomChain (K := Hbp.obj (□n)) hd (mergeWitness hd z) h₀₁
      have hr₁ : runOf (Hbp.obj (□n)) hd (mergeWitness hd z) u₁ = atomStep i z :=
        (AtomChain.atomLoop (⟨w₁, hc₁, hm₁.trans hr₀⟩ : AtomChain n i _ z)).symm
      obtain ⟨w₂, hc₂, hm₂, -⟩ :=
        ιE_runGen_atomChain (K := Hbp.obj (□n)) hd (mergeWitness hd z) h₁₂
      have hr₂ : runOf (Hbp.obj (□n)) hd (mergeWitness hd z) u₂ = atomStep j (atomStep i z) :=
        (AtomChain.atomLoop (⟨w₂, hc₂, hm₂.trans hr₁⟩ : AtomChain n j _ (atomStep i z))).symm
      obtain ⟨w₃, hc₃, hm₃, -⟩ :=
        ιE_runGen_atomChain (K := Hbp.obj (□n)) hd (mergeWitness hd z) h₂₃
      have hr₃ : runOf (Hbp.obj (□n)) hd (mergeWitness hd z) u₃
          = atomStep i (atomStep j (atomStep i z)) :=
        (AtomChain.atomLoop
          (⟨w₃, hc₃, hm₃.trans hr₂⟩ : AtomChain n i _ (atomStep j (atomStep i z)))).symm
      obtain ⟨w₄, hc₄, hm₄, -⟩ :=
        ιE_runGen_atomChain (K := Hbp.obj (□n)) hd (mergeWitness hd z) k₀₁
      have hs₁ : runOf (Hbp.obj (□n)) hd (mergeWitness hd z) v₁ = atomStep j z :=
        (AtomChain.atomLoop (⟨w₄, hc₄, hm₄.trans hr₀⟩ : AtomChain n j _ z)).symm
      obtain ⟨w₅, hc₅, hm₅, -⟩ :=
        ιE_runGen_atomChain (K := Hbp.obj (□n)) hd (mergeWitness hd z) k₁₂
      have hs₂ : runOf (Hbp.obj (□n)) hd (mergeWitness hd z) v₂ = atomStep i (atomStep j z) :=
        (AtomChain.atomLoop (⟨w₅, hc₅, hm₅.trans hs₁⟩ : AtomChain n i _ (atomStep j z))).symm
      refine ⟨cellCongr (artinBP.Br (Hbp.obj (□n))).Rel
        ((ιV_runOf (Hbp.obj (□n)) hd (mergeWitness hd z) u₃).trans
          (congrArg (artinBP.ιRun (Hbp.obj (□n))) hr₃))
        ((ιV_runOf (Hbp.obj (□n)) hd (mergeWitness hd z) (pairMergeRun hij')).trans
          (congrArg (artinBP.ιRun (Hbp.obj (□n))) hr₀))
        ((Limits.colimit.ι (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)
            (op ⟨op (pairChain n i j hij'), mergeWitness hd z⟩)).two
          (sliceRelOf
            (((Quiver.Path.nil.cons (artinBP.runGenFibre i h₀₁)).cons
              (artinBP.runGenFibre j h₁₂)).cons (artinBP.runGenFibre i h₂₃))
            (((Quiver.Path.nil.cons (artinBP.runGenFibre j k₀₁)).cons
              (artinBP.runGenFibre i k₁₂)).cons (artinBP.runGenFibre j k₂₃))
            (⟨(artinBaseWord₃ i j i, artinBaseWord₃ j i j), ArtinRel.braid i j hij⟩ :
              (artinBP.P n).Rel ⟨artinBP.v n⟩ ⟨artinBP.v n⟩) rfl rfl)), ?_, ?_, ?_⟩
      · exact (src_cellCongr _ _ _).trans
          ((congrArg (cellCongr Quiver.Path _ _)
            ((Limits.colimit.ι (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)
              (op ⟨op (pairChain n i j hij'), mergeWitness hd z⟩)).src_two _)).trans
            (cellCongr_ιWord₃ hd (mergeWitness hd z) h₀₁ h₁₂ h₂₃ hr₃ hr₂ hr₁ hr₀ _ _ _))
      · exact (tgt_cellCongr _ _ _).trans
          ((congrArg (cellCongr Quiver.Path _ _)
            ((Limits.colimit.ι (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)
              (op ⟨op (pairChain n i j hij'), mergeWitness hd z⟩)).tgt_two _)).trans
            (cellCongr_ιWord₃ hd (mergeWitness hd z) k₀₁ k₁₂ k₂₃ hr₃ hs₂ hs₁ hr₀ _ _ _))
      · exact isPairCell_of_copy _ (runMerge_mergeWitness hd z) _ rfl _ _

/-- **Every 2-cell of the hand-written polygraph is a shape at a run** — the chains are forced by
their merge legs (`AtomChain.ext`), so a square or a hexagon has nothing beyond its two cuts and
the run it stands over. -/
theorem cell_induction {motive : ∀ {A B : GenObj (artinChainPoly n).Gen},
      (artinChainPoly n).Rel A B → Prop}
    (h : ∀ (K : PairKind n) (z : CubeRun n), motive (K.cell z))
    {A B : GenObj (artinChainPoly n).Gen} (α : (artinChainPoly n).Rel A B) : motive α := by
  obtain ⟨⟨S, T⟩, hα⟩ := α
  cases hα with
  | @comm x y y' z i j hij e₁ e₂ f₁ f₂ =>
      obtain rfl : y = atomStep i z := e₂.atomLoop.symm
      obtain rfl : x = atomStep j (atomStep i z) := e₁.atomLoop.symm
      obtain rfl : y' = atomStep j z := f₂.atomLoop.symm
      obtain rfl : e₁ = AtomChain.of (k := j) (y := atomStep i z) rfl := AtomChain.ext _ _
      obtain rfl : e₂ = AtomChain.of (k := i) (y := z) rfl := AtomChain.ext _ _
      obtain rfl : f₁ = AtomChain.of (k := i) (y := atomStep j z) (atomStep_comm hij z) :=
        AtomChain.ext _ _
      obtain rfl : f₂ = AtomChain.of (k := j) (y := z) rfl := AtomChain.ext _ _
      exact h (.comm i j hij) z
  | @braid x y₁ y₂ y₁' y₂' z i j hij e₁ e₂ e₃ f₁ f₂ f₃ =>
      obtain rfl : y₂ = atomStep i z := e₃.atomLoop.symm
      obtain rfl : y₁ = atomStep j (atomStep i z) := e₂.atomLoop.symm
      obtain rfl : x = atomStep i (atomStep j (atomStep i z)) := e₁.atomLoop.symm
      obtain rfl : y₂' = atomStep j z := f₃.atomLoop.symm
      obtain rfl : y₁' = atomStep i (atomStep j z) := f₂.atomLoop.symm
      obtain rfl : e₁ = AtomChain.of (k := i) (y := atomStep j (atomStep i z)) rfl :=
        AtomChain.ext _ _
      obtain rfl : e₂ = AtomChain.of (k := j) (y := atomStep i z) rfl := AtomChain.ext _ _
      obtain rfl : e₃ = AtomChain.of (k := i) (y := z) rfl := AtomChain.ext _ _
      obtain rfl : f₁ = AtomChain.of (k := j) (y := atomStep i (atomStep j z))
          (atomStep_braid hij z).symm := AtomChain.ext _ _
      obtain rfl : f₂ = AtomChain.of (k := i) (y := atomStep j z) rfl := AtomChain.ext _ _
      obtain rfl : f₃ = AtomChain.of (k := j) (y := z) rfl := AtomChain.ext _ _
      exact h (.braid i j hij) z

/-- **Every square and hexagon is realised in `Br`**, with that pair of words as its boundary. -/
theorem exists_brRel {A B : GenObj (artinChainPoly n).Gen} (α : (artinChainPoly n).Rel A B) :
    ∃ γ : (artinBP.Br (Hbp.obj (□n))).Rel ((artinChainPre n).obj A) ((artinChainPre n).obj B),
      (artinBP.Br (Hbp.obj (□n))).src γ
          = (artinChainPre n).mapPath ((artinChainPoly n).src α) ∧
        (artinBP.Br (Hbp.obj (□n))).tgt γ
          = (artinChainPre n).mapPath ((artinChainPoly n).tgt α) :=
  cell_induction
    (motive := fun {A B} α => ∃ γ : (artinBP.Br (Hbp.obj (□n))).Rel
      ((artinChainPre n).obj A) ((artinChainPre n).obj B),
      (artinBP.Br (Hbp.obj (□n))).src γ
          = (artinChainPre n).mapPath ((artinChainPoly n).src α) ∧
        (artinBP.Br (Hbp.obj (□n))).tgt γ
          = (artinChainPre n).mapPath ((artinChainPoly n).tgt α))
    (fun K z => (exists_pairBrCell K z).imp fun _ hγ => ⟨hγ.1, hγ.2.1⟩) α

/-- **The two dictionaries name the same 1-cell.** -/
theorem artinChainPre_map {x y : CubeRun n} (e : AtomGen n x y) :
    (artinChainPre n).map (show (⟨x⟩ : GenObj (artinChainPoly n).Gen) ⟶ ⟨y⟩ from e)
      = genCell (atomGenToHLoc e) := by
  obtain ⟨k, w, hc, hm⟩ := e
  obtain rfl : w = atomWitness k y := ChainCat.eq_atomWitness k y hm
  exact eq_of_heq (((Quiver.homOfEq_heq _ _ _).trans (Quiver.homOfEq_heq _ _ _)).trans
    (Quiver.homOfEq_heq _ _ _).symm)

/-! ## The 0-cells and the 1-cells biject

`bijective_obCell` and `bijective_genCell` say the fibration route's cells match the colimit's; the
chains match the fibration route's on the nose (`atomGenEquiv`), so they match the colimit's. -/

theorem bijective_artinChainPre_obj (n : ℕ) : Function.Bijective (artinChainPre n).obj :=
  ⟨fun _ _ h => congrArg (fun v : CubeRun n => (⟨v⟩ : GenObj (artinChainPoly n).Gen))
      (injective_ιRun n h),
    fun A => by
      obtain ⟨x, hx⟩ := surjective_obCell n ⟨A.as⟩
      exact ⟨⟨artinRun x⟩, congrArg
        (fun v : GenObj ((artinBP.Br (Hbp.obj (□n))).op).Gen =>
          (⟨v.as⟩ : GenObj (artinBP.Br (Hbp.obj (□n))).Gen)) hx⟩⟩

theorem bijective_artinChainPre_map (n : ℕ) (A B : GenObj (artinChainPoly n).Gen) :
    Function.Bijective ((artinChainPre n).map : (A ⟶ B) → _) := by
  obtain ⟨x⟩ := A
  obtain ⟨y⟩ := B
  have h : ((artinChainPre n).map : (AtomGen n x y) → _)
      = genCell ∘ (atomGenEquiv x y) := funext fun e => artinChainPre_map e
  rw [h]
  exact bijective_genCell.comp (atomGenEquiv x y).bijective

theorem artinChainPre_star_injective (n : ℕ) (A : GenObj (artinChainPoly n).Gen) :
    Function.Injective ((artinChainPre n).star A) := by
  rintro ⟨B₁, e₁⟩ ⟨B₂, e₂⟩ h
  obtain ⟨hB, he⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : B₁ = B₂ := (bijective_artinChainPre_obj n).1 hB
  exact Sigma.ext rfl (heq_of_eq ((bijective_artinChainPre_map n A B₁).1 (eq_of_heq he)))

instance artinChainPre_faithful (n : ℕ) : (artinChainPre n).pathsFunctor.Faithful :=
  Prefunctor.pathsFunctor_faithful _ (artinChainPre_star_injective n)

/-! ## The comparison, in all three dimensions

`exists_brRel` supplies the 2-cells, so `artinChainPre` extends to a morphism of polygraphs; it is
bijective on 0-cells and on 1-cells, and injective on 2-cells because a 2-cell of the hand-written
polygraph *is* its boundary. -/

/-- **The hand-written Artin presentation, mapped into `Br artinBP (H □ⁿ)`** — a codimension-one
chain to the crossing of its own copy, a codimension-two chain to the relation of the copy at the
pair chain. -/
noncomputable def artinChainMap (n : ℕ) : artinChainPoly n ⟶ artinBP.Br (Hbp.obj (□n)) where
  pre := artinChainPre n
  two {_ _} α := (exists_brRel α).choose
  src_two α := (exists_brRel α).choose_spec.1
  tgt_two α := (exists_brRel α).choose_spec.2

@[simp] theorem artinChainMap_pre (n : ℕ) : (artinChainMap n).pre = artinChainPre n := rfl

/-- **Distinct squares and hexagons stay distinct** — a 2-cell of the hand-written polygraph is its
boundary, and the boundary is carried faithfully. -/
theorem injective_artinChainMap_two (n : ℕ) {A B : GenObj (artinChainPoly n).Gen} :
    Function.Injective
      ((artinChainMap n).two : (artinChainPoly n).Rel A B → _) := by
  intro α β h
  refine boundaryDetermined_artinChainPoly α β
    ((artinChainPre n).pathsFunctor.map_injective ?_)
    ((artinChainPre n).pathsFunctor.map_injective ?_)
  · exact ((artinChainMap n).src_two α).symm.trans
      ((congrArg (artinBP.Br (Hbp.obj (□n))).src h).trans ((artinChainMap n).src_two β))
  · exact ((artinChainMap n).tgt_two α).symm.trans
      ((congrArg (artinBP.Br (Hbp.obj (□n))).tgt h).trans ((artinChainMap n).tgt_two β))


/-! ## Every 2-cell of `Br` is a codimension-two chain

A 2-cell lives in one copy (`exists_colimit_ι_two`); the relation it carries there is one of the
base's two (`coproductRel_mk_of_eq`), and each of its two words begins with one of the two cuts, so
both ascend at the run below and the pair chain sits under the copy (`exists_pairRunLeg`).  A
2-cell of a copy is the relation it carries, so it is the shape's own cell, pushed up. -/

/-- **A relation of the base is a shape's.** -/
theorem exists_pairKind {x y : FreeMonoid (Fin (n - 1))} (h : ArtinRel n x y) :
    ∃ K : PairKind n,
      x = MonoidPoly.word (rels := ArtinRel n) ((artinBP.P n).src K.rel) ∧
        y = MonoidPoly.word (rels := ArtinRel n) ((artinBP.P n).tgt K.rel) := by
  cases h with
  | comm i j hij => exact ⟨PairKind.comm i j hij, rfl, rfl⟩
  | braid i j hij => exact ⟨PairKind.braid i j hij, rfl, rfl⟩

/-- …and the words spell it back (`path_word`), so the 2-cell itself is the shape's. -/
theorem eq_pairKind_rel (ρ : (artinBP.P n).Rel ⟨artinBP.v n⟩ ⟨artinBP.v n⟩) :
    ∃ K : PairKind n, ρ = K.rel := by
  obtain ⟨⟨S, T⟩, hρ⟩ := ρ
  obtain ⟨K, hS, hT⟩ := exists_pairKind hρ
  exact ⟨K, Subtype.ext (Prod.ext
    ((MonoidPoly.path_word S).symm.trans
      ((congrArg MonoidPoly.path hS).trans (MonoidPoly.path_word _)))
    ((MonoidPoly.path_word T).symm.trans
      ((congrArg MonoidPoly.path hT).trans (MonoidPoly.path_word _))))⟩

/-- A cut performs its atom. -/
theorem eval_artinBaseLetter (i : Fin (n - 1)) :
    ((artinBP.comp n).eval.map (artinBaseLetter i)).unop = posPerm (adjT i) := by
  have h : (artinBP.comp n).eval.map (artinBaseLetter i)
      = (artinBP.comp n).eval.map (Quiver.Path.nil (a := ⟨artinBP.v n⟩))
        ≫ (artinBP.comp n).arrow
          (i : (⟨artinBP.v n⟩ : GenObj (artinBP.P n).Gen) ⟶ ⟨artinBP.v n⟩) :=
    Presents.eval_cons (artinBP.comp n) Quiver.Path.nil _
  rw [h, Presents.eval_nil, Category.id_comp]
  exact artinBP_braid i

/-- …so a word that starts with one performs its atom first. -/
theorem eval_comp_letter (i : Fin (n - 1))
    (w : Quiver.Path (⟨artinBP.v n⟩ : GenObj (artinBP.P n).Gen) ⟨artinBP.v n⟩) :
    ((artinBP.comp n).eval.map ((artinBaseLetter i).comp w)).unop
      = posPerm (adjT i) * ((artinBP.comp n).eval.map w).unop := by
  have h : ((artinBP.comp n).eval.map ((artinBaseLetter i).comp w)).unop
      = ((artinBP.comp n).eval.map w).unop ≫ ((artinBP.comp n).eval.map (artinBaseLetter i)).unop :=
    congrArg Quiver.Hom.unop ((artinBP.comp n).eval.map_comp (artinBaseLetter i) w)
  rw [h, SingleObj.comp_as_mul, eval_artinBaseLetter]

/-- **A shape's source word is entered by its first cut**, and its target word by its second. -/
theorem exists_eval_src (K : PairKind n) :
    ∃ b, ((artinBP.comp n).eval.map ((artinBP.P n).src K.rel)).unop
      = posPerm (adjT K.cuts.1) * b := by
  cases K with
  | comm i j hij => exact ⟨_, eval_comp_letter i (artinBaseLetter j)⟩
  | braid i j hij =>
      exact ⟨_, (congrArg (fun p => ((artinBP.comp n).eval.map p).unop)
        (Quiver.Path.comp_assoc (artinBaseLetter i) (artinBaseLetter j)
          (artinBaseLetter i))).trans (eval_comp_letter i _)⟩

theorem exists_eval_tgt (K : PairKind n) :
    ∃ b, ((artinBP.comp n).eval.map ((artinBP.P n).tgt K.rel)).unop
      = posPerm (adjT K.cuts.2) * b := by
  cases K with
  | comm i j hij => exact ⟨_, eval_comp_letter j (artinBaseLetter i)⟩
  | braid i j hij =>
      exact ⟨_, (congrArg (fun p => ((artinBP.comp n).eval.map p).unop)
        (Quiver.Path.comp_assoc (artinBaseLetter j) (artinBaseLetter i)
          (artinBaseLetter j))).trans (eval_comp_letter j _)⟩

/-- **A 2-cell of a copy is pinned by the relation it carries**, across an identification of its
0-cells. -/
theorem sliceRel_ext' {d : Ch Zbp} {A B A' B' : GenObj (artinBP.slicePoly d).Gen}
    (hA : A = A') (hB : B = B') (β : (artinBP.slicePoly d).Rel A B)
    (β' : (artinBP.slicePoly d).Rel A' B') (h : sliceCell β ≍ sliceCell β') : β ≍ β' := by
  subst hA; subst hB; exact heq_of_eq (sliceRel_ext β β' (eq_of_heq h))

/-- **Pushing a copy's 2-cell along a leg keeps the relation of the base it carries.** -/
theorem cell_two_fam_map {d' d : Ch Zbp} (f : d' ⟶ d)
    {X Y : GenObj (artinBP.fam.obj d').Gen} (β : (artinBP.fam.obj d').Rel X Y) :
    sliceCell ((artinBP.fam.map f).two β) = sliceCell β := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  cases β with
  | mk _ => rfl

/-- **Every 2-cell of `Br artinBP (H □ⁿ)` is a codimension-two chain's.** -/
theorem exists_isPairCell {A B : GenObj (artinBP.Br (Hbp.obj (□n))).Gen}
    (γ : (artinBP.Br (Hbp.obj (□n))).Rel A B) :
    ∃ (K : PairKind n) (z : CubeRun n), IsPairCell K z γ := by
  obtain ⟨c, X, Y, β, hX, hY, hγ⟩ :=
    Polygraph.exists_colimit_ι_two (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam) γ
  obtain ⟨⟨⟨d⟩, W⟩⟩ := c
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  have hd : dimSum d.dims = n := dimSum_of_hbpCubeHom W
  obtain ⟨v, rfl⟩ := artinBP.exists_runPt_of_strands hd X
  obtain ⟨u, rfl⟩ := artinBP.exists_runPt_of_strands hd Y
  obtain ⟨ρ, hρ⟩ := Polygraph.strandRel_mk_of_eq (sliceCell β) (i := n) rfl rfl
  obtain ⟨K, rfl⟩ := eq_pairKind_rel ρ
  have hcell : sliceCell β = Polygraph.StrandRel.mk (i := n) K.rel := eq_of_heq hρ
  -- both cuts ascend at the run below, so the pair chain sits under the copy
  obtain ⟨bS, hbS⟩ := exists_eval_src K
  obtain ⟨bT, hbT⟩ := exists_eval_tgt K
  obtain ⟨vi, hvi⟩ := runGermStep_first (posPerm (adjT K.cuts.1)) bS
    (by rw [← hbS]; exact sliceRel_action β (congrArg artinBP.poly.src hcell))
  obtain ⟨vj, hvj⟩ := runGermStep_first (posPerm (adjT K.cuts.2)) bT
    (by rw [← hbT]; exact sliceRel_action_tgt β (congrArg artinBP.poly.tgt hcell))
  obtain ⟨t, ht⟩ := exists_pairRunLeg K.ne hd hvi hvj
  have hpu : RunAt.push (runMerge K.chain K.hdim ≫ t) (runAtSelf n) = u :=
    (RunAt.push_push _ t (runAtSelf n)).symm.trans ht
  have hz : (runMerge K.chain K.hdim).φ ≫ (wedgeHoms (Hbp.obj (□n))).map t.op W
      = runOf (Hbp.obj (□n)) hd W u :=
    (Category.assoc _ _ _).symm.trans (runOf_eq (Hbp.obj (□n)) hd W hpu).symm
  -- the shape's own cell over the pair chain, pushed along the leg
  obtain ⟨γ₀, -, -, V₀, v₀, β₀, -, -, -, hcell₀, -⟩ :=
    exists_pairBrCell K (runOf (Hbp.obj (□n)) hd W u)
  have hstep : RunGermStep (((artinBP.comp n).eval.map ((artinBP.P n).src K.rel)).unop) u
      (RunAt.push t v₀) := by
    rw [← ht]
    exact germStep_push t (sliceRel_action β₀ (congrArg artinBP.poly.src hcell₀))
  have hv : RunAt.push t v₀ = v :=
    RunAt.perm_injective ((CubeChains.GermStep.mul_eq hstep).trans
      (CubeChains.GermStep.mul_eq
        (sliceRel_action β (congrArg artinBP.poly.src hcell))).symm)
  refine ⟨K, runOf (Hbp.obj (□n)) hd W u, (wedgeHoms (Hbp.obj (□n))).map t.op W, v₀, β₀,
    ((ιV_pushLeg artinBP (Hbp.obj (□n)) W t v₀).symm.trans
      ((congrArg (fun r => ιV (Hbp.obj (□n)) artinBP.fam (op ⟨op d, W⟩)
        (artinBP.runPt r)) hv).trans hX)),
    ((ιV_pushLeg artinBP (Hbp.obj (□n)) W t K.mergeRun).symm.trans
      ((congrArg (fun r => ιV (Hbp.obj (□n)) artinBP.fam (op ⟨op d, W⟩)
        (artinBP.runPt r)) ht).trans hY)),
    hz, hcell₀, ?_⟩
  refine Eq.trans ?_ hγ
  refine eq_of_heq (((cellCongr_heq _ _ _ _).trans ?_).trans (cellCongr_heq _ _ _ _).symm)
  refine HEq.trans (Polygraph.Hom.two_heq_of_eq
    (Limits.colimit.w (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)
      (eltLeg (Hbp.obj (□n)) t W)).symm β₀) ?_
  exact Polygraph.Hom.two_heq_congr _
    (congrArg GenObj.mk ((artinBP.famV_runPt t v₀).trans (congrArg artinBP.runPt hv)))
    (congrArg GenObj.mk ((artinBP.famV_runPt t K.mergeRun).trans (congrArg artinBP.runPt ht)))
    (sliceRel_ext'
      (congrArg GenObj.mk ((artinBP.famV_runPt t K.mergeRun).trans (congrArg artinBP.runPt ht)))
      (congrArg GenObj.mk ((artinBP.famV_runPt t v₀).trans (congrArg artinBP.runPt hv)))
      ((artinBP.fam.map t).two β₀) β
      (heq_of_eq ((cell_two_fam_map t β₀).trans (hcell₀.trans hcell.symm))))

/-! ## The 2-cells biject

A cell's shape and run are read off its source word — that word is `wordData`, and `srcData_inj`
sees the shape and the run in it — so a 2-cell of `Br` is its boundary, and the hand-written
polygraph supplies exactly one 2-cell for each. -/

/-- **A cell's source word is its shape's**, across an identification of its 0-cells. -/
theorem IsPairCell.src_eq {K : PairKind n} {z : CubeRun n}
    {A B : GenObj (artinBP.Br (Hbp.obj (□n))).Gen}
    {γ : (artinBP.Br (Hbp.obj (□n))).Rel A B} (h : IsPairCell K z γ) :
    ∃ (hA : A = (artinChainPre n).obj ⟨K.top z⟩) (hB : B = (artinChainPre n).obj ⟨z⟩),
      cellCongr Quiver.Path hA hB ((artinBP.Br (Hbp.obj (□n))).src γ)
        = (artinChainPre n).mapPath ((artinChainPoly n).src (K.cell z)) := by
  obtain ⟨γ₀, hs₀, -, hp₀⟩ := exists_pairBrCell K z
  obtain ⟨hA, hB, hγ⟩ := h.eq hp₀
  exact ⟨hA, hB, (src_cellCongr hA hB γ).symm.trans
    ((congrArg (fun δ => (artinBP.Br (Hbp.obj (□n))).src δ) hγ).trans hs₀)⟩

theorem wordData_cellCongr {A B A' B' : GenObj (AtomGen n)} (hA : A = A') (hB : B = B')
    (p : Quiver.Path A B) : wordData (cellCongr Quiver.Path hA hB p) = wordData p := by
  subst hA; subst hB; rfl

/-- **Two cells with one source word have one shape and one run.** -/
theorem pairKind_eq_of_src {K K' : PairKind n} {z z' : CubeRun n}
    {A B : GenObj (artinBP.Br (Hbp.obj (□n))).Gen}
    {γ γ' : (artinBP.Br (Hbp.obj (□n))).Rel A B}
    (h : IsPairCell K z γ) (h' : IsPairCell K' z' γ')
    (hs : (artinBP.Br (Hbp.obj (□n))).src γ = (artinBP.Br (Hbp.obj (□n))).src γ') :
    K = K' ∧ z = z' := by
  obtain ⟨hA, hB, he⟩ := h.src_eq
  obtain ⟨hA', hB', he'⟩ := h'.src_eq
  obtain rfl : z' = z :=
    congrArg GenObj.as ((bijective_artinChainPre_obj n).1 (hB'.symm.trans hB))
  have eK : (⟨K.top z'⟩ : GenObj (artinChainPoly n).Gen) = ⟨K'.top z'⟩ :=
    (bijective_artinChainPre_obj n).1 (hA.symm.trans hA')
  have key : (artinChainPre n).mapPath
      (cellCongr Quiver.Path eK rfl ((artinChainPoly n).src (K.cell z')))
      = (artinChainPre n).mapPath ((artinChainPoly n).src (K'.cell z')) := by
    rw [Prefunctor.mapPath_cellCongr, ← he, ← he', ← hs, cellCongr_trans]
  refine ⟨?_, rfl⟩
  refine (PairKind.srcData_inj (z := z') (z' := z') ?_).1
  rw [← PairKind.wordData_src_cell, ← PairKind.wordData_src_cell,
    ← wordData_cellCongr eK rfl ((artinChainPoly n).src (K.cell z'))]
  exact congrArg wordData ((artinChainPre n).pathsFunctor.map_injective key)

/-- **A 2-cell of `Br artinBP (H □ⁿ)` is its boundary.** -/
theorem boundaryDetermined_Br (n : ℕ) : (artinBP.Br (Hbp.obj (□n))).BoundaryDetermined := by
  intro A B γ γ' hs _
  obtain ⟨K, z, h⟩ := exists_isPairCell γ
  obtain ⟨K', z', h'⟩ := exists_isPairCell γ'
  obtain ⟨rfl, rfl⟩ := pairKind_eq_of_src h h' hs
  obtain ⟨hA, hB, hγ⟩ := h.eq h'
  exact hγ

/-- **The 2-cells biject**: distinct squares and hexagons stay distinct, and `Br` has no others. -/
theorem bijective_artinChainMap_two (n : ℕ) {A B : GenObj (artinChainPoly n).Gen} :
    Function.Bijective ((artinChainMap n).two : (artinChainPoly n).Rel A B → _) := by
  refine ⟨injective_artinChainMap_two n, fun γ => ?_⟩
  obtain ⟨K, z, h⟩ := exists_isPairCell γ
  obtain ⟨γ₀, hs₀, ht₀, h₀⟩ := exists_pairBrCell K z
  obtain ⟨hA, hB, hγ⟩ := h.eq h₀
  obtain rfl : A = ⟨K.top z⟩ := (bijective_artinChainPre_obj n).1 hA
  obtain rfl : B = (⟨z⟩ : GenObj (artinChainPoly n).Gen) := (bijective_artinChainPre_obj n).1 hB
  have hγ₀ : γ = γ₀ := hγ
  exact ⟨K.cell z, boundaryDetermined_Br n _ _
    (((artinChainMap n).src_two _).trans
      (hs₀.symm.trans (congrArg (fun δ => (artinBP.Br (Hbp.obj (□n))).src δ) hγ₀).symm))
    (((artinChainMap n).tgt_two _).trans
      (ht₀.symm.trans (congrArg (fun δ => (artinBP.Br (Hbp.obj (□n))).tgt δ) hγ₀).symm))⟩

/-- **Artin's presentation of `Ch(H(□ⁿ))[W⁻¹]`, written in chains**: `Br artinBP (H □ⁿ)` matches
`artinChainPoly n` cell for cell in all three dimensions — its 0-cells are the runs, its 1-cells
the codimension-one chains, its 2-cells the codimension-two ones, and it has no others. -/
theorem bijective_artinChainMap (n : ℕ) :
    Function.Bijective (artinChainMap n).pre.obj ∧
      (∀ A B : GenObj (artinChainPoly n).Gen,
        Function.Bijective ((artinChainMap n).pre.map : (A ⟶ B) → _)) ∧
      ∀ A B : GenObj (artinChainPoly n).Gen,
        Function.Bijective ((artinChainMap n).two : (artinChainPoly n).Rel A B → _) :=
  ⟨bijective_artinChainPre_obj n, bijective_artinChainPre_map n,
    fun _ _ => bijective_artinChainMap_two n⟩

/-- **…so the hand-written polygraph presents `Ch(H(□ⁿ))[W⁻¹]`** — runs, codimension-one chains
and codimension-two chains, with no colimit and no localization in sight. -/
noncomputable def presentsArtinChains (n : ℕ) :
    Presents (artinChainPoly n) ((W (Hbp.obj (□n))).Localization) :=
  Polygraph.Presents.ofBijective (artinChainMap n) (bijective_artinChainPre_obj n)
    (bijective_artinChainPre_map n) (fun _ _ => bijective_artinChainMap_two n)
    (artinBP.presentsBr (Hbp.obj (□n)))

end ChainCat
