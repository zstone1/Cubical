import CubeChains.Concurrency.Presentation.TopRefinement
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Concurrency/Presentation/PaperPoly — the polygraph, defined directly

0-cells the runs; cells the **objects**, degree one a 1-cell and degree two a 2-cell:

    X.chain ──bottomHom──▸ obj ◂──topHom── Y.chain            a cell  X ⟶ Y

An ascent between two runs over an object is a degree-one object, so a climb spells a word; over a
degree-two object the runs are a polygon, and a 2-cell's two words are its two maximal climbs. -/

open CategoryTheory CategoryTheory.Polygraph BPSet CubeChains Equiv

namespace ChainCat.Paper

variable {K : BPSet}

/-! ## The cells -/

/-- A **cell** `X ⟶ Y` of dimension `n`: an **object of degree `n`**, read between the two runs it
spans — `X` the run below it (its merge), `Y` the run at its top (its longest run). -/
structure Cell (n : ℕ) (X Y : Run K) where
  /-- the object -/
  obj : Ch K
  /-- …of degree `n` -/
  degree_obj : degree obj = n
  /-- the run below it -/
  below : bottomRun obj = X
  /-- the run at its top -/
  top : topRun obj = Y

/-- **A cell is its object** — the three remaining fields are proofs. -/
theorem Cell.ext {n : ℕ} {X Y : Run K} : ∀ {α β : Cell n X Y}, α.obj = β.obj → α = β
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, h => by subst h; rfl

/-- A **1-cell**: a degree-one object. -/
abbrev Gen (X Y : Run K) : Type := Cell 1 X Y

/-- **The merge a cell carries**, out of the run below it. -/
noncomputable abbrev Cell.bot {n : ℕ} {X Y : Run K} (α : Cell n X Y) : X.chain ⟶ α.obj :=
  eqToHom (congrArg Run.chain α.below.symm) ≫ bottomHom α.obj

theorem Cell.W_bot {n : ℕ} {X Y : Run K} (α : Cell n X Y) : W K α.bot :=
  (W K).comp_mem _ _ (W_eqToHom _) (W_bottomHom _)

/-- **The refinement a cell carries**, out of the run at its far end. -/
noncomputable abbrev Cell.hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) : Y.chain ⟶ α.obj :=
  eqToHom (congrArg Run.chain α.top.symm) ≫ topHom α.obj

/-- **A cell's refinement has codimension `n`** — it comes out of a run. -/
theorem Cell.codim_hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) : codim α.hom = n := by
  change degree α.obj - degree Y.chain = n
  rw [(isRun_iff_degree_eq_zero _).mp Y.property, Nat.sub_zero]
  exact α.degree_obj

/-- **A 1-cell's refinement crosses one pair** — the longest run over an atom's shape is the
atom. -/
theorem Cell.permLen_crossPerm_hom {X Y : Run K} (α : Gen X Y) {N : ℕ}
    (hN : dimSum Y.chain.dims = N) : permLen (crossPerm hN α.hom) = 1 := by
  obtain ⟨e, he, -, rfl⟩ := α
  refine (permLen_crossPerm (dimSum_replicate (dimSum e.dims)) hN _).trans ?_
  simp only [Cell.hom, eqToHom_refl, Category.id_comp]
  exact (congrArg permLen ((crossPerm_eq_of_φ (dimSum_replicate (dimSum e.dims))
    (g' := (shapeTop (zObj e.dims) rfl).arr) rfl).trans (shapeTop _ rfl).crossPerm_arr)).trans
    (permLen_shapeTop_of_degree_one rfl he)

/-- **…so it crosses.** -/
theorem Cell.not_W_hom {X Y : Run K} (α : Gen X Y) : ¬ W K α.hom := fun h => by
  have hL := α.permLen_crossPerm_hom (N := dimSum Y.chain.dims) rfl
  rw [(W_iff_crossPerm_eq_one rfl α.hom).mp h, permLen_one] at hL
  exact zero_ne_one hL

/-- **A 1-cell's refinement is any crossing refinement out of its far end** — at degree one there is
only one (`hom_eq_of_not_W_deg_one`). -/
theorem Cell.hom_eq {X Y : Run K} (α : Gen X Y) {f : Y.chain ⟶ α.obj} (hf : ¬ W K f) :
    α.hom = f :=
  hom_eq_of_not_W_deg_one α.degree_obj α.not_W_hom hf

/-- A 0-cell, as a vertex of the generating quiver — `Polygraph.pt` before `poly` exists. -/
abbrev runPt (X : Run K) : GenObj (Gen (K := K)) := ⟨X⟩

/-- A word read at other names for its two ends — the only transport a word here carries. -/
def readAt {X X' Y Y' : Run K} (hx : X = X') (hy : Y = Y')
    (w : Quiver.Path (runPt X) (runPt Y)) : Quiver.Path (runPt X') (runPt Y') :=
  cellCongr Quiver.Path (congrArg runPt hx) (congrArg runPt hy) w

theorem readAt_trans {X Y X' Y' X'' Y'' : Run K} (hx : X = X') (hy : Y = Y') (hx' : X' = X'')
    (hy' : Y' = Y'') (p : Quiver.Path (runPt X) (runPt Y)) :
    readAt hx' hy' (readAt hx hy p) = readAt (hx.trans hx') (hy.trans hy') p := by
  subst hx; subst hy; subst hx'; subst hy'; rfl

theorem readAt_nil {X X' : Run K} (h h' : X = X') :
    readAt h h' (Quiver.Path.nil : Quiver.Path (runPt X) (runPt X)) = Quiver.Path.nil := by
  subst h; rfl

/-- A 1-cell, read as a one-letter word. -/
noncomputable abbrev genWord {X Y : Run K} (α : Gen X Y) : Quiver.Path (runPt X) (runPt Y) :=
  Quiver.Hom.toPath (V := GenObj (Gen (K := K))) α

/-- **A word's last letter is its object**, read at other names for the ends. -/
theorem readAt_cons {X Y Z X' Y' Z' : Run K} (hx : X = X') (hy : Y = Y') (hz : Z = Z')
    (p : Quiver.Path (runPt X) (runPt Y)) {L : Gen Y Z} {L' : Gen Y' Z'} (hL : L.obj = L'.obj) :
    readAt hx hz (p.cons L) = (readAt hx hy p).cons L' := by
  subst hx; subst hy; subst hz
  exact congrArg (fun M : Gen Y Z => p.cons M) (Cell.ext hL)

/-- **A letter is its object**, read at other names for its two ends. -/
theorem genWord_congr {X Y X' Y' : Run K} (hx : X = X') (hy : Y = Y')
    {α : Gen X Y} {β : Gen X' Y'} (h : α.obj = β.obj) :
    readAt hx hy (genWord α) = genWord β := by
  subst hx; subst hy
  exact congrArg (fun γ : Gen X Y => genWord γ) (Cell.ext h)

/-! ## The runs over a chain, and the atoms between them

A run-arrow into a chain's *shape* is a run over the chain: the chain on the arrow's own events,
carrying the composite.  The shape is all these see, so a climb is the same term over every `K`,
which is why the words are natural on the nose. -/

/-- The wedge map a refinement of shapes carries. -/
abbrev zPhi {p q : List ℕ+} (r : zObj p ⟶ zObj q) : ⋁p ⟶ ⋁q := Hom.φ r

/-- The runs over a chain, on `N` events. -/
abbrev ChPerm (e : Ch K) (N : ℕ) : Type := ShapePerm N (zObj e.dims)

/-- An ascent between two of them. -/
abbrev ChAsc (e : Ch K) {N : ℕ} (a b : ChPerm e N) : Type :=
  Ascent (shapeLower N (zObj e.dims)).perm a b

/-- The run over a chain a run-arrow of its shape names. -/
noncomputable def shapeRun (e : Ch K) {N : ℕ} (σ : ChPerm e N) : Run K :=
  ⟨⟨𝟙^N, zPhi σ.arr ≫ e.map⟩, fun _ hd => List.eq_of_mem_replicate hd⟩

/-- …with the refinement it makes. -/
noncomputable def shapeHom (e : Ch K) {N : ℕ} (σ : ChPerm e N) : (shapeRun e σ).chain ⟶ e :=
  ⟨zPhi σ.arr, rfl⟩

/-- **The run below a chain is the one its shape's merge names** — `W` sees only the wedge map. -/
theorem bottomRun_eq_shapeRun (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N) :
    bottomRun e = shapeRun e (shapeBot (zObj e.dims) hN) :=
  eq_bottomRun_of_W (shapeHom e _) ((W_iff_of_φ (f := shapeHom e (shapeBot (zObj e.dims) hN))
    (f' := (shapeBot (zObj e.dims) hN).arr) rfl).mpr (W_shapeBot_arr hN))

/-- **The run at the top of a chain is the one its shape's longest run names.** -/
theorem topRun_eq_shapeRun (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N) :
    topRun e = shapeRun e (shapeTop (zObj e.dims) hN) := by
  subst hN; rfl

/-- The degree-one object an ascent of a chain's runs names: the atom it crosses, over the
chain. -/
noncomputable def ascObj (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) : Ch K :=
  ⟨atomComp N ε.idx, zPhi (ascLeg ε) ≫ e.map⟩

theorem degree_ascObj (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) :
    degree (ascObj e ε) = 1 :=
  degree_atomComp N ε.idx

/-- A leg out of an ascent's atom commutes over `K`, the leg below it being the ascent's own. -/
private theorem asc_w (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b)
    {m : zObj (𝟙^N) ⟶ zObj (atomComp N ε.idx)} {σ : ChPerm e N} (h : m ≫ ascLeg ε = σ.arr) :
    zPhi m ≫ zPhi (ascLeg ε) ≫ e.map = zPhi σ.arr ≫ e.map := by
  rw [← Category.assoc, show zPhi m ≫ zPhi (ascLeg ε) = zPhi (m ≫ ascLeg ε) from rfl, h]

/-- The merge onto it out of the run below. -/
noncomputable def ascBot (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) :
    (shapeRun e a).chain ⟶ ascObj e ε :=
  ⟨zPhi (mergeOnes N ε.idx), asc_w e ε (mergeOnes_ascLeg ε)⟩

/-- …and the atom's own cut, out of the run above. -/
noncomputable def ascTop (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) :
    (shapeRun e b).chain ⟶ ascObj e ε :=
  ⟨zPhi (atomOnes N ε.idx), asc_w e ε (atomOnes_ascLeg ε)⟩

theorem W_ascBot (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) : W K (ascBot e ε) :=
  (W_iff_of_φ (f := ascBot e ε) (f' := mergeOnes N ε.idx) rfl).mpr (W_mergeOnes _ ε.idx)

theorem not_W_ascTop (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) :
    ¬ W K (ascTop e ε) :=
  fun h => not_W_atomOnes N ε.idx
    ((W_iff_of_φ (f := ascTop e ε) (f' := atomOnes N ε.idx) rfl).mp h)

/-- **The run at the top of an ascent's atom is the run above** — the longest run over an atom's
shape is the atom. -/
theorem topRun_ascObj (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) :
    topRun (ascObj e ε) = shapeRun e b :=
  (topRun_eq_shapeRun (ascObj e ε) (dimSum_atomComp N ε.idx)).trans
    (Run.ext (congrArg (fun m => (⟨𝟙^N, m⟩ : Ch K))
      ((congrArg (fun r => zPhi r ≫ zPhi (ascLeg ε) ≫ e.map)
        (arr_shapeTop_atomComp ε.idx (dimSum_atomComp N ε.idx))).trans
        (asc_w e ε (atomOnes_ascLeg ε)))))

/-- **An ascent of a chain's runs is a 1-cell** — its atom is a degree-one object, entered by the
merge below and cut by the atom above. -/
noncomputable def ascGen (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) :
    Gen (shapeRun e a) (shapeRun e b) where
  obj := ascObj e ε
  degree_obj := degree_ascObj e ε
  below := eq_bottomRun_of_W (ascBot e ε) (W_ascBot e ε)
  top := topRun_ascObj e ε

@[simp] theorem obj_ascGen (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) :
    (ascGen e ε).obj = ascObj e ε := rfl

/-- The leg an ascent's atom makes onto the chain. -/
noncomputable def ascLegHom (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) :
    ascObj e ε ⟶ e :=
  ⟨zPhi (ascLeg ε), rfl⟩

/-- **The merge below an ascent's atom is the run below it, read on the chain.** -/
theorem ascBot_comp (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) :
    ascBot e ε ≫ ascLegHom e ε = shapeHom e a :=
  hom_ext' (congrArg zPhi (mergeOnes_ascLeg ε))

/-- **…and its cut is the run above it.** -/
theorem ascTop_comp (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) :
    ascTop e ε ≫ ascLegHom e ε = shapeHom e b :=
  hom_ext' (congrArg zPhi (atomOnes_ascLeg ε))

/-- **The 1-cells out of the runs over a chain, as a prefunctor on the ascent quiver** — a climb's
word of 1-cells is its `mapPath`. -/
noncomputable def ascPre (e : Ch K) (N : ℕ) :
    Ascents (shapeLower N (zObj e.dims)).perm ⥤q GenObj (Gen (K := K)) where
  obj a := runPt (shapeRun e a)
  map ε := ascGen e ε

/-! ## The polygon over a degree-two object

The runs over a degree-two object climb from the bottom alternately through its two junctions, and
either climb ends at the object's longest run. -/

/-- **The top of a climb through the two junctions is the object's top run.** -/
theorem topRun_eq_riseElem (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N)
    (h2 : degree (zObj e.dims) = 2) {i k : Fin (N - 1)} (hik : (i : ℕ) ≠ (k : ℕ))
    (hi : Nonempty (zObj (atomComp N i) ⟶ zObj e.dims))
    (hk : Nonempty (zObj (atomComp N k) ⟶ zObj e.dims)) :
    topRun e = shapeRun e (riseElem hN hik hi hk (cox i k) le_rfl) :=
  (topRun_eq_shapeRun e hN).trans (congrArg (shapeRun e) (riseElem_cox hN h2 hik hi hk).symm)

/-- **The word the climb through `i, k` spells**, between the object's two runs. -/
noncomputable def riseWord (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N)
    (h2 : degree (zObj e.dims) = 2) {i k : Fin (N - 1)} (hik : (i : ℕ) ≠ (k : ℕ))
    (hi : Nonempty (zObj (atomComp N i) ⟶ zObj e.dims))
    (hk : Nonempty (zObj (atomComp N k) ⟶ zObj e.dims)) :
    Quiver.Path (runPt (bottomRun e)) (runPt (topRun e)) :=
  readAt (bottomRun_eq_shapeRun e hN).symm (topRun_eq_riseElem e hN h2 hik hi hk).symm
    ((ascPre e N).mapPath (riseClimb hN hik hi hk (cox i k) le_rfl))

/-- The word out of the bottom through the lower junction. -/
noncomputable abbrev loWord (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N)
    (h2 : degree (zObj e.dims) = 2) : Quiver.Path (runPt (bottomRun e)) (runPt (topRun e)) :=
  riseWord e hN h2 (shapePair (zObj e.dims) hN h2).ne (nonempty_atomComp_lo hN h2)
    (nonempty_atomComp_hi hN h2)

/-- …and through the upper. -/
noncomputable abbrev hiWord (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N)
    (h2 : degree (zObj e.dims) = 2) : Quiver.Path (runPt (bottomRun e)) (runPt (topRun e)) :=
  riseWord e hN h2 (shapePair (zObj e.dims) hN h2).ne.symm (nonempty_atomComp_hi hN h2)
    (nonempty_atomComp_lo hN h2)

/-- **The polygraph**: the runs, the degree-one objects, and one relation per degree-two object,
equating the two maximal climbs of its polygon of runs. -/
noncomputable def poly (K : BPSet) : Polygraph where
  V := Run K
  Gen := Gen
  Rel x y := Cell 2 x.as y.as
  src α := readAt α.below α.top (loWord α.obj rfl α.degree_obj)
  tgt α := readAt α.below α.top (hiWord α.obj rfl α.degree_obj)

/-- A word read at renamed ends names the arrow it names, renamed. -/
theorem quot_readAt {X X' Y Y' : Run K} (hx : X = X') (hy : Y = Y')
    (w : Quiver.Path (runPt X) (runPt Y)) :
    (poly K).quot.map (readAt hx hy w)
      = eqToHom (congrArg (fun Z : Run K => (poly K).quot.obj (runPt Z)) hx).symm
        ≫ (poly K).quot.map w
        ≫ eqToHom (congrArg (fun Z : Run K => (poly K).quot.obj (runPt Z)) hy) :=
  Paths.map_cellCongr₂ (poly K).quot _ _ w

/-- **A 2-cell's boundary, spelled at any count of its events.** -/
theorem poly_src {X Y : Run K} (α : Cell 2 X Y) {N : ℕ} (hN : dimSum α.obj.dims = N) :
    (poly K).src (x := runPt X) (y := runPt Y) α
      = readAt α.below α.top (loWord α.obj hN α.degree_obj) := by
  subst hN; rfl

theorem poly_tgt {X Y : Run K} (α : Cell 2 X Y) {N : ℕ} (hN : dimSum α.obj.dims = N) :
    (poly K).tgt (x := runPt X) (y := runPt Y) α
      = readAt α.below α.top (hiWord α.obj hN α.degree_obj) := by
  subst hN; rfl

/-- **The relation a degree-two object imposes**, at any count of its events. -/
theorem quot_loWord (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N) (h2 : degree e = 2) :
    (poly K).quot.map (loWord e hN h2) = (poly K).quot.map (hiWord e hN h2) := by
  have h := (poly K).quot_src_tgt (x := runPt (bottomRun e)) (y := runPt (topRun e))
    (⟨e, h2, rfl, rfl⟩ : Cell 2 (bottomRun e) (topRun e))
  rwa [poly_src _ hN, poly_tgt _ hN] at h

end ChainCat.Paper
