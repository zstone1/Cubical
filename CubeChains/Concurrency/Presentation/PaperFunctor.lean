import CubeChains.Concurrency.Presentation.PaperPresents
import CubeChains.Concurrency.Presentation.CellNatural

/-!
# Concurrency/Presentation/PaperFunctor — the paper's polygraph, as a functor of `K`

A map of `K` moves the object a cell carries and no shape, so `degree`, `cutsOf`, the run below and
the greatest refinement are untouched: a cell transports with every field and the two words a 2-cell
reads transport letter by letter.  The square below is strict, so `chCellPresentationIso` conjugated
by it is the naturality of the presentation.

    Paper.poly K ──────polyMap──────▸ Paper.poly K'
         │ paperHom                        │ paperHom
         ▾                                 ▾
    (chRunCutSpans K).poly ─────────▸ (chRunCutSpans K').poly
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

@[simp] theorem obj_cellMap {n : ℕ} {X Y : Run K} (α : Cell n X Y) :
    (cellMap f α).obj = (pushforward f).obj α.obj := rfl

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
          (Polygraph.cell (P := (chContraction K).poly) (chGenOf u hu hW))) := dif_neg hW

/-- **A map of `K` neither creates nor destroys a merge** — `W` is monotonicity of the coordinate
map, which reads the wedge map alone. -/
theorem W_pushforward_iff {a b : Ch K} (u : a ⟶ b) : W K' ((pushforward f).map u) ↔ W K u :=
  (W_iff_monotone_coordMap _).trans (W_iff_monotone_coordMap u).symm

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
          (Polygraph.cell (P := (chContraction K).poly) (chGenOf u hu hW))).symm).trans
      (runPre_mapPath_naturality f _)

/-! ## The two words a codimension-two refinement out of a run reads

`cutsOf` reads the two ends' junctions and nothing else, so a map of `K` moves neither which cuts a
refinement has nor which of them a factorisation makes: `oneCutEquivBool` commutes on the nose. -/

/-- The word a named one-cut factorisation reads — `factorWords` is this at the factorisation the
boolean names. -/
noncomputable def oneCutWord {X : Run K} {b : Ch K} {u : X.chain ⟶ b} (hu : codim u = 2)
    (F : OneCut u) : Quiver.Path (runPt (bottomRun b)) (runPt X) :=
  readAt rfl (bottomRun_self X) ((cutWord F.1.snd (F.codim_snd hu)).comp (cutWord F.1.fst F.2))

theorem factorWords_eq_oneCutWord {X : Run K} {b : Ch K} (u : X.chain ⟶ b) (hu : codim u = 2)
    (ε : Bool) : factorWords u hu ε = oneCutWord hu ((oneCutEquivBool u hu).symm ε) := rfl

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

@[simp] theorem polyFunctor_obj (K : BPSet) : polyFunctor.obj K = poly K := rfl

@[simp] theorem polyFunctor_map : polyFunctor.map f = polyMap f := rfl

/-! ## …lying over the degree-zero cells

`paperHom` is a bijection in every dimension below two, and the bijection is natural: the kept cut a
degree-one object is moves with the object. -/

/-- **A kept cut is pinned by its reading on the runs** — `genOfRunCut_injective`, as injectivity of
the comparison prefunctor. -/
theorem runPre_map_injective {x y : GenObj (chRunCutSpans K).poly.Gen} :
    Function.Injective (runPre.map : (x ⟶ y) → (runPre.obj x ⟶ runPre.obj y)) :=
  genOfRunCut_injective

/-- **The kept cut a degree-one object is moves with the object.** -/
theorem paperPre_map_naturality {X Y : GenObj (Gen (K := K))} (α : X ⟶ Y) :
    paperPre.map (cellMap f α) = (chCellSpansMap f).pre.map (paperPre.map α) :=
  runPre_map_injective
    ((runPre_map_paperPre_map (cellMap f α)).trans
      ((congrArg (cellMap f) (runPre_map_paperPre_map α)).symm.trans
        (runPre_map_naturality f (paperPre.map α)).symm))

/-- **…so `paperHom` is natural in `K` on the generating quivers** — on the nose. -/
theorem paperPre_naturality : polyPre f ⋙q paperPre = paperPre ⋙q (chCellSpansMap f).pre :=
  Prefunctor.ext_of_obj_eq rfl fun _ _ α => heq_of_eq (paperPre_map_naturality f α)

/-- **…and so in the presented categories**, a morphism's functor seeing only its prefunctor. -/
theorem paperHom_naturality :
    (polyFunctor.map f).functor ⋙ (paperHom (K := K')).functor
      = (paperHom (K := K)).functor ⋙ (chCellFunctor.map f).functor :=
  Polygraph.functor_naturality (polyMap f) (paperHom (K := K')) (paperHom (K := K))
    (chCellFunctor.map f) (paperPre_naturality f)

/-! ## The presentation, natural in `K` -/

theorem paperPresents_E (K : BPSet) :
    (paperPresents K).E = (paperHom (K := K)).functor ⋙ (chCellPresentation K).E :=
  Presents.ofCells_E (paperHom (K := K)) paperPre_obj_bijective
    (fun x y => paperPre_map_bijective x y) (chCellPresentation K) paperCellsDerivable

/-- **The paper's presentation of `Ch(K)[W⁻¹]` is natural in `K`, up to isomorphism** — the
degree-zero square conjugated by `paperHom`, which contributes an equality. -/
noncomputable def paperPresentationIso :
    (polyFunctor.map f).functor ⋙ (paperPresents K').E
      ≅ (paperPresents K).E ⋙ chLocOpMap f :=
  eqToIso (((congrArg (fun H => (polyMap f).functor ⋙ H) (paperPresents_E K')).trans
        (congrArg (fun G => G ⋙ (chCellPresentation K').E) (paperHom_naturality f))).trans
      (Functor.assoc _ _ _))
    ≪≫ Functor.isoWhiskerLeft (paperHom (K := K)).functor (chCellPresentationIso f)
    ≪≫ eqToIso ((Functor.assoc _ _ _).symm.trans
      (congrArg (fun G => G ⋙ chLocOpMap f) (paperPresents_E K).symm))

theorem paperSquare_id (K : BPSet) :
    (polyFunctor.map (𝟙 K)).functor ⋙ (paperPresents K).E
      = (paperPresents K).E ⋙ chLocOpMap (𝟙 K) :=
  square_id (Polygraph.functor_map_id polyFunctor K) (chLocOpMap_id K) _

/-- **Conjugating a transport by two transports is a transport** — stated with every functor a
variable, so `subst` does the work a transport calculation would. -/
private theorem conj_eqToIso {A B C : Type*} [Category A] [Category B] [Category C] (F : A ⥤ B)
    {G H : B ⥤ C} (e : G = H) {P Q : A ⥤ C} {h₁ : P = F ⋙ G} {h₂ : F ⋙ H = Q} (h : P = Q) :
    eqToIso h₁ ≪≫ Functor.isoWhiskerLeft F (eqToIso e) ≪≫ eqToIso h₂ = eqToIso h := by
  subst e; subst h₁; subst h₂
  ext X
  simp

/-- **The unit coherence, at the paper's polygraph.** -/
theorem paperPresentationIso_id (K : BPSet) :
    paperPresentationIso (𝟙 K) = eqToIso (paperSquare_id K) := by
  rw [paperPresentationIso, chCellPresentationIso_id]
  exact conj_eqToIso (paperHom (K := K)).functor (chCellSquare_id K) (paperSquare_id K)

end ChainCat.Paper
