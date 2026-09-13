import CubeChains.Concurrency.Presentation.DirectPresents
import CubeChains.Concurrency.Presentation.RunCellFunctor

/-!
# Concurrency/Presentation/PaperFunctor — the paper's polygraph, as a functor of `K`

A map of `K` moves the object a cell carries and no shape, so `degree`, `cutsOf`, the run below and
the greatest refinement are untouched: a cell transports with every field and the two words a 2-cell
reads transport letter by letter.  Reading the cells in `Ch(K)[W⁻¹]` is then natural **on the
nose** — `Q ⋙ chLocOpMap f = (pushforward f).op ⋙ Q` is an equality of functors:

    Paper.poly K ──────polyMap──────▸ Paper.poly K'
         │ paperE                          │ paperE
         ▾                                 ▾
    Ch(K)[W⁻¹] ───────chLocOpMap─────▸ Ch(K')[W⁻¹]
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat.Paper

variable {K K' : BPSet} (f : K ⟶ K')

/-! ## The cells, carried along -/

/-- **A map of `K` carries a cell along** — it moves the object and no shape, so the run below and
the run the greatest refinement comes out of move with it. -/
noncomputable def cellMap {n : ℕ} {X Y : Run K} (α : Cell n X Y) :
    Cell n ((Run.pushforward f).obj X) ((Run.pushforward f).obj Y) where
  obj := (pushforward f).obj α.obj
  degree_obj := α.degree_obj
  below := congrArg (Run.pushforward f).obj α.below
  top := congrArg (Run.pushforward f).obj α.top

/-- **…and its refinement is the refinement pushed forward** — the greatest refinement is a function
of the shape, so the renaming of the far end is the only transport. -/
theorem hom_cellMap {n : ℕ} {X Y : Run K} (α : Cell n X Y) :
    (cellMap f α).hom = (pushforward f).map α.hom :=
  (((pushforward f).map_comp (eqToHom (congrArg Run.chain α.top.symm)) (topOf α.obj).2).trans
    (congrArg (fun t => t ≫ (pushforward f).map (topOf α.obj).2)
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

/-! ## The word a cut reads, carried along

`cutWord` is the contraction's own word for the bead cut, read on the runs, so its naturality is
`Spans.Map.pre_mapPath_subPre` at the one letter that cut is — a merge reading as the empty word on
either side. -/

theorem cutWord_of_W {c d : Ch K} {u : c ⟶ d} (hu : codim u = 1) (hW : W K u) :
    cutWord u hu = readAt rfl (bottomRun_eq_of_W u hW) Quiver.Path.nil := dif_pos hW

theorem cutWord_of_not_W {c d : Ch K} {u : c ⟶ d} (hu : codim u = 1) (hW : ¬ W K u) :
    cutWord u hu
      = runPre.mapPath ((chRunCutSpans K).pre.map
          (Polygraph.cell (P := (chCollapse K).poly) (chGenOf u hu hW))) := dif_neg hW

/-- **A kept cut read on the runs is the object it lands on, pushed forward.** -/
theorem runPre_map_naturality {x y : GenObj (chRunCutSpans K).poly.Gen} (e : x ⟶ y) :
    runPre.map ((chCellSpansMap f).pre.map e) = cellMap f (runPre.map e) :=
  Cell.ext ((obj_genOfRunCut _ _).trans
    (congrArg (pushforward f).obj (obj_genOfRunCut _ _)).symm)

/-- **…so reading the kept cuts on the runs commutes with a map of `K`.** -/
theorem runPre_naturality : (chCellSpansMap f).pre ⋙q runPre = runPre ⋙q polyPre f :=
  Prefunctor.ext_of_obj_eq rfl fun _ _ e => heq_of_eq (runPre_map_naturality f e)

theorem runPre_mapPath_naturality {x y : GenObj (chRunCutSpans K).poly.Gen}
    (w : Quiver.Path x y) :
    runPre.mapPath ((chCellSpansMap f).pre.mapPath w) = (polyPre f).mapPath (runPre.mapPath w) :=
  (Prefunctor.mapPath_comp_apply (chCellSpansMap f).pre runPre w).symm.trans
    ((eq_of_heq (Prefunctor.mapPath_heq_of_eq (runPre_naturality f) w)).trans
      (Prefunctor.mapPath_comp_apply runPre (polyPre f) w))

/-- **The word a codimension-one refinement reads is carried to the word its image reads** — the
chosen word is the contraction's, and that is carried along by `chCellSpansMap`. -/
theorem cutWord_pushforward {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    cutWord ((pushforward f).map u) hu = (polyPre f).mapPath (cutWord u hu) := by
  by_cases hW : W K u
  · rw [cutWord_of_W (u := (pushforward f).map u) hu ((W_pushforward_iff f u).mpr hW),
      cutWord_of_W hu hW]
    exact (mapPath_readAt f rfl (bottomRun_eq_of_W u hW) Quiver.Path.nil).symm
  · have hW' : ¬ W K' ((pushforward f).map u) := fun h => hW ((W_pushforward_iff f u).mp h)
    rw [cutWord_of_not_W (u := (pushforward f).map u) hu hW', cutWord_of_not_W hu hW]
    exact (congrArg runPre.mapPath
        (Spans.Map.pre_mapPath_subPre (chCellSpansMap f)
          (Polygraph.cell (P := (chCollapse K).poly) (chGenOf u hu hW))).symm).trans
      (runPre_mapPath_naturality f _)

/-! ## The two words a codimension-two refinement out of a run reads

`cutsOf` reads the two ends' junctions and nothing else, so a map of `K` moves neither which cuts a
refinement has nor which of them a factorisation makes: `oneCutEquivBool` commutes on the nose. -/

/-- The word a named one-cut factorisation reads — `factorWords` is this, definitionally, at the
factorisation the boolean names. -/
noncomputable def oneCutWord {X : Run K} {b : Ch K} {u : X.chain ⟶ b} (hu : codim u = 2)
    (F : OneCut u) : Quiver.Path (runPt (bottomRun b)) (runPt X) :=
  readAt rfl (bottomRun_self X) ((cutWord F.1.snd (F.codim_snd hu)).comp (cutWord F.1.fst F.2))

/-- A one-cut factorisation, carried along a map of `K`. -/
def oneCutMap {a b : Ch K} {u : a ⟶ b} (F : OneCut u) : OneCut ((pushforward f).map u) :=
  ⟨⟨(pushforward f).obj F.1.mid, (pushforward f).map F.1.fst, (pushforward f).map F.1.snd,
      ((pushforward f).map_comp _ _).symm.trans (congrArg (pushforward f).map F.1.comp)⟩, F.2⟩

/-- **A map of `K` does not move which cut a factorisation makes.** -/
theorem oneCutEquivBool_oneCutMap {a b : Ch K} {u : a ⟶ b} (hu : codim u = 2) (F : OneCut u) :
    oneCutEquivBool ((pushforward f).map u) hu (oneCutMap f F) = oneCutEquivBool u hu F := rfl

/-- …so it carries the factorisation a boolean names to the factorisation that boolean names. -/
theorem oneCutEquivBool_symm_pushforward {a b : Ch K} {u : a ⟶ b} (hu : codim u = 2) (ε : Bool) :
    (oneCutEquivBool ((pushforward f).map u) hu).symm ε
      = oneCutMap f ((oneCutEquivBool u hu).symm ε) :=
  (oneCutEquivBool ((pushforward f).map u) hu).injective
    ((Equiv.apply_symm_apply _ ε).trans
      ((oneCutEquivBool_oneCutMap f hu _).trans (Equiv.apply_symm_apply _ ε)).symm)

/-- **A factorisation's word is carried letter by letter** — both legs are codimension-one cuts. -/
theorem oneCutWord_pushforward {X : Run K} {b : Ch K} {u : X.chain ⟶ b} (hu : codim u = 2)
    (F : OneCut u) :
    oneCutWord (X := (Run.pushforward f).obj X) (u := (pushforward f).map u) hu (oneCutMap f F)
      = (polyPre f).mapPath (oneCutWord hu F) := by
  refine Eq.trans (congrArg (readAt rfl (bottomRun_self ((Run.pushforward f).obj X)))
    ((congrArg₂ Quiver.Path.comp (cutWord_pushforward f F.1.snd (F.codim_snd hu))
        (cutWord_pushforward f F.1.fst F.2)).trans
      (Prefunctor.mapPath_comp (polyPre f) _ _).symm)) ?_
  exact (mapPath_readAt f rfl (bottomRun_self X) _).symm

/-- Which factorisation a word spells matters, which proof names its codimension does not. -/
private theorem factorWords_congr {X : Run K} {b : Ch K} {u v : X.chain ⟶ b} (h : u = v)
    (hu : codim u = 2) (ε : Bool) : factorWords u hu ε = factorWords v hu ε := by subst h; rfl

theorem factorWords_pushforward {X : Run K} {b : Ch K} (u : X.chain ⟶ b) (hu : codim u = 2)
    (ε : Bool) :
    factorWords (X := (Run.pushforward f).obj X) ((pushforward f).map u) hu ε
      = (polyPre f).mapPath (factorWords u hu ε) :=
  (congrArg (oneCutWord (X := (Run.pushforward f).obj X) (u := (pushforward f).map u) hu)
      (oneCutEquivBool_symm_pushforward f hu ε)).trans (oneCutWord_pushforward f hu _)

/-- **The two words a 2-cell reads are carried along** — its refinement is the refinement pushed
forward, and each leg's word is. -/
theorem cellWords_cellMap {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) :
    cellWords (cellMap f α) ε = (polyPre f).mapPath (cellWords α ε) := by
  refine Eq.trans (congrArg (readAt (cellMap f α).below rfl)
    ((factorWords_congr (hom_cellMap f α) (cellMap f α).codim_hom ε).trans
      (factorWords_pushforward f α.hom α.codim_hom ε))) ?_
  exact (mapPath_readAt f α.below rfl _).symm

/-! ## The functor -/

/-- **A map of `K` carries the paper's polygraph along.** -/
noncomputable def polyMap : poly K ⟶ poly K' where
  pre := polyPre f
  two α := cellMap f α
  src_two α := cellWords_cellMap f α false
  tgt_two α := cellWords_cellMap f α true

/-- **The runs with the objects of degree one and two, as a functor of `K`** — for every `K` and
with no hypothesis on `K`. -/
noncomputable def polyFunctor : BPSet ⥤ Polygraph where
  obj K := poly K
  map f := polyMap f
  map_id _ := Hom.ext' (Prefunctor.ext_of_obj_eq rfl fun _ _ _ => HEq.rfl) fun _ => HEq.rfl
  map_comp _ _ := Hom.ext' (Prefunctor.ext_of_obj_eq rfl fun _ _ _ => HEq.rfl) fun _ => HEq.rfl

/-! ## The presentation, natural in `K` on the nose

The paper's cells are read in `Ch(K)[W⁻¹]` by `Rconj`, built from `Q` and the merge below a chain;
both are carried along strictly, so the square commutes as an equality of functors. -/

/-- Two nested renamings of one arrow, however they are named. -/
private theorem uncancel {C : Type*} [Category C] {A A' B B' : C} (p : A = A') (q : B = B')
    (g : A ⟶ B) : g = eqToHom p ≫ (eqToHom p.symm ≫ g ≫ eqToHom q) ≫ eqToHom q.symm := by
  subst p; subst q; simp

private theorem collapse3 {C : Type*} [Category C] {A₀ A₁ A₂ A₃ B₃ B₂ B₁ B₀ : C}
    (a₀ : A₀ = A₁) (a₁ : A₁ = A₂) (a₂ : A₂ = A₃) {g : A₃ ⟶ B₃} (b₂ : B₃ = B₂) (b₁ : B₂ = B₁)
    (b₀ : B₁ = B₀) (p : A₀ = A₃) (q : B₃ = B₀) :
    eqToHom a₀ ≫ (eqToHom a₁ ≫ (eqToHom a₂ ≫ g ≫ eqToHom b₂) ≫ eqToHom b₁) ≫ eqToHom b₀
      = eqToHom p ≫ g ≫ eqToHom q := by
  subst a₀; subst a₁; subst a₂; subst b₂; subst b₁; subst b₀; simp

/-- **The arrow a cell names is carried along** — the merge below and the localized pushforward are
both strict, so the only transports are the two runs' names. -/
theorem cellRconj_cellMap {n : ℕ} {X Y : Run K} (α : Cell n X Y) :
    cellRconj (cellMap f α)
      = eqToHom (chLocOpMap_obj f X.chain).symm ≫ (chLocOpMap f).map (cellRconj α)
        ≫ eqToHom (chLocOpMap_obj f Y.chain) := by
  have hR : (chLocOpMap f).map (Rconj α.hom)
      = eqToHom (locObj_bottom f α.obj) ≫ Rconj ((pushforward f).map α.hom)
        ≫ eqToHom (locObj_bottom f Y.chain).symm := by
    rw [← chLocOpMap_Rconj f α.hom]
    exact uncancel _ _ _
  have hc : cellRconj α = eqToHom (congrArg (fun Z : Run K => rho Z.chain) α.below.symm)
      ≫ Rconj α.hom ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_self Y)) := rfl
  have hc' : cellRconj (cellMap f α)
      = eqToHom (congrArg (fun Z : Run K' => rho Z.chain) (cellMap f α).below.symm)
        ≫ Rconj (cellMap f α).hom
        ≫ eqToHom (congrArg (fun Z : Run K' => rho Z.chain)
            (bottomRun_self ((Run.pushforward f).obj Y))) := rfl
  rw [hc, hc', hom_cellMap f α, (chLocOpMap f).map_comp, (chLocOpMap f).map_comp,
    eqToHom_map, eqToHom_map, hR]
  exact (collapse3 _ _ _ _ _ _ _ _).symm

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
  refine (conj_eqToHom_iff_heq _ _ (chLocOpMap_obj f x.as.chain).symm
    (chLocOpMap_obj f y.as.chain).symm).mp ?_
  exact hL.trans ((cellRconj_cellMap f e).trans
    (congrArg (fun t => eqToHom (chLocOpMap_obj f x.as.chain).symm ≫ t
      ≫ eqToHom (chLocOpMap_obj f y.as.chain)) hR.symm))

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
