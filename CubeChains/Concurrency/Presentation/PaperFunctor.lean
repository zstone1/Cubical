import CubeChains.Concurrency.Presentation.DirectPresents
import CubeChains.Concurrency.Presentation.LocFunctor

/-!
# Concurrency/Presentation/PaperFunctor — the paper's polygraph, as a functor of `K`

A map of `K` moves the object a cell carries and no shape, so a cell transports with every field and
a 2-cell's climbs are the same climbs; the reading is natural **on the nose**:

    Paper.poly K ──────polyMap──────▸ Paper.poly K'
         │ paperE                          │ paperE
         ▾                                 ▾
    Ch(K)[W⁻¹] ───────chLocOpMap─────▸ Ch(K')[W⁻¹]
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat.Paper

variable {K K' : BPSet} (f : K ⟶ K')

/-! ## The cells, carried along -/

/-- **A map of `K` carries a cell along** — it moves the object and no shape, so the runs below and
at the top move with it. -/
noncomputable def cellMap {n : ℕ} {X Y : Run K} (α : Cell n X Y) :
    Cell n ((Run.pushforward f).obj X) ((Run.pushforward f).obj Y) where
  obj := (pushforward f).obj α.obj
  degree_obj := α.degree_obj
  below := congrArg (Run.pushforward f).obj α.below
  top := congrArg (Run.pushforward f).obj α.top

/-- **…and its refinement is the refinement pushed forward** — the top run is a function of the
shape, so the renaming of the far end is the only transport. -/
theorem hom_cellMap {n : ℕ} {X Y : Run K} (α : Cell n X Y) :
    (cellMap f α).hom = (pushforward f).map α.hom :=
  (((pushforward f).map_comp (eqToHom (congrArg Run.chain α.top.symm)) (topHom α.obj)).trans
    (congrArg (fun t => t ≫ (pushforward f).map (topHom α.obj))
      (eqToHom_map (pushforward f) (congrArg Run.chain α.top.symm)))).symm

/-- **The comparison of generating quivers**: 0-cells the runs pushed forward, 1-cells the
degree-one objects pushed forward. -/
noncomputable def polyPre : GenObj (Gen (K := K)) ⥤q GenObj (Gen (K := K')) where
  obj X := ⟨(Run.pushforward f).obj X.as⟩
  map α := cellMap f α

/-- **…carrying a word read at other names for its ends along** — the only transport a word here
carries. -/
theorem mapPath_readAt {X X' Y Y' : Run K} (hx : X = X') (hy : Y = Y')
    (w : Quiver.Path (runPt X) (runPt Y)) :
    (polyPre f).mapPath (readAt hx hy w)
      = readAt (congrArg (Run.pushforward f).obj hx) (congrArg (Run.pushforward f).obj hy)
          ((polyPre f).mapPath w) := by
  subst hx; subst hy; rfl

/-! ## The words of a 2-cell, carried along

A climb is spelled on the shape alone, and a map of `K` moves no shape: the climb is the *same* term
over `K'`, and only the classifying map of each letter moves. -/

/-- **A climb's word is carried to the same climb's word** — an ascent's atom keeps its leg and only
its classifying map moves, so the two prefunctors agree on the nose. -/
theorem mapPath_ascPre (e : Ch K) {N : ℕ} {a b : zObj (𝟙^N) ⟶ zObj e.dims}
    (R : Climb (shapeLower N (zObj e.dims)).perm a b) :
    (polyPre f).mapPath ((ascPre e N).mapPath R)
      = (ascPre ((pushforward f).obj e) N).mapPath R :=
  (Prefunctor.mapPath_comp_apply (ascPre e N) (polyPre f) R).symm

/-- **The word a climb through a pair spells is carried to the same climb's word.** -/
theorem riseWord_pushforward (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N)
    (h2 : degree (zObj e.dims) = 2) {i k : Fin (N - 1)} (hik : (i : ℕ) ≠ (k : ℕ))
    (hi : Nonempty (zObj (atomComp N i) ⟶ zObj e.dims))
    (hk : Nonempty (zObj (atomComp N k) ⟶ zObj e.dims)) :
    riseWord ((pushforward f).obj e) hN h2 hik hi hk
      = (polyPre f).mapPath (riseWord e hN h2 hik hi hk) := by
  rw [riseWord, riseWord, mapPath_readAt]
  exact congrArg (readAt _ _) (mapPath_ascPre f e _).symm

/-! ## The functor -/

/-- **A map of `K` carries the paper's polygraph along.** -/
noncomputable def polyMap : poly K ⟶ poly K' where
  pre := polyPre f
  two α := cellMap f α
  src_two α := (congrArg (readAt (cellMap f α).below (cellMap f α).top)
      (riseWord_pushforward f α.obj rfl _ _ _ _)).trans (mapPath_readAt f α.below α.top _).symm
  tgt_two α := (congrArg (readAt (cellMap f α).below (cellMap f α).top)
      (riseWord_pushforward f α.obj rfl _ _ _ _)).trans (mapPath_readAt f α.below α.top _).symm

/-- **The runs with the objects of degree one and two, as a functor of `K`** — for every `K` and
with no hypothesis on `K`. -/
noncomputable def polyFunctor : BPSet ⥤ Polygraph where
  obj K := poly K
  map f := polyMap f
  map_id _ := Hom.ext' (Prefunctor.ext_of_obj_eq rfl fun _ _ _ => HEq.rfl) fun _ => HEq.rfl
  map_comp _ _ := Hom.ext' (Prefunctor.ext_of_obj_eq rfl fun _ _ _ => HEq.rfl) fun _ => HEq.rfl

/-! ## The presentation, natural in `K` on the nose

A cell is read in `Ch(K)[W⁻¹]` as the cospan of its legs, and a map of `K` carries both legs and the
localization strictly, so the square commutes as an equality of functors. -/

/-- **…and so is its merge.** -/
theorem bot_cellMap {n : ℕ} {X Y : Run K} (α : Cell n X Y) :
    (cellMap f α).bot = (pushforward f).map α.bot :=
  (((pushforward f).map_comp (eqToHom (congrArg Run.chain α.below.symm)) (bottomHom α.obj)).trans
    (congrArg (fun t => t ≫ (pushforward f).map (bottomHom α.obj))
      (eqToHom_map (pushforward f) (congrArg Run.chain α.below.symm)))).symm

/-- **The arrow a cell names is carried along** — the only transports are its two runs' names. -/
theorem cellRconj_cellMap {n : ℕ} {X Y : Run K} (α : Cell n X Y) :
    (chLocOpMap f).map (cellRconj α)
      = eqToHom (chLocOpMap_obj f X.chain) ≫ cellRconj (cellMap f α)
        ≫ eqToHom (chLocOpMap_obj f Y.chain).symm :=
  (chLocOpMap_conj f α.W_bot α.hom).trans (congrArg (fun t => eqToHom _ ≫ t ≫ eqToHom _)
    (conj_congr _ _ (bot_cellMap f α).symm (hom_cellMap f α).symm))

/-- **The paper's reading of `Ch(K)[W⁻¹]` is natural in `K`** — an equality of functors. -/
theorem paperSquare :
    (polyFunctor.map f).functor ⋙ (paperPresents K').E
      = (paperPresents K).E ⋙ chLocOpMap f := by
  refine Polygraph.presented_ext_of_gen (fun x => (chLocOpMap_obj f x.as.chain).symm)
    fun {x y} e => ?_
  have hL : ((polyFunctor.map f).functor ⋙ (paperPresents K').E).map
        ((poly K).quot.map e.toPath) = cellRconj (cellMap f e) :=
    (congrArg (paperE K').map
        (congrArg (poly K').quot.map (Prefunctor.mapPath_toPath (polyPre f) e))).trans
      (paperE_map_gen ((polyPre f).map e))
  have hR : ((paperPresents K).E ⋙ chLocOpMap f).map ((poly K).quot.map e.toPath)
      = (chLocOpMap f).map (cellRconj e) :=
    congrArg (chLocOpMap f).map (paperE_map_gen e)
  exact (heq_of_eq hL).trans
    ((conj_eqToHom_iff_heq' _ _ _ _).mp (hR.trans (cellRconj_cellMap f e))).symm

/-- **…so the comparison is the transport it has to be.** -/
noncomputable def paperPresentationIso :
    (polyFunctor.map f).functor ⋙ (paperPresents K').E
      ≅ (paperPresents K).E ⋙ chLocOpMap f := eqToIso (paperSquare f)

theorem paperSquare_id (K : BPSet) :
    (polyFunctor.map (𝟙 K)).functor ⋙ (paperPresents K).E
      = (paperPresents K).E ⋙ chLocOpMap (𝟙 K) :=
  square_id (Polygraph.functor_map_id polyFunctor K) (chLocOpMap_id K) _

/-- **The unit coherence, at the paper's polygraph** — both sides are the same transport. -/
theorem paperPresentationIso_id (K : BPSet) :
    paperPresentationIso (𝟙 K) = eqToIso (paperSquare_id K) := rfl

end ChainCat.Paper
