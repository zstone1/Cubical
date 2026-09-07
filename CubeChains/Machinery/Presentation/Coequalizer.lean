import CubeChains.Machinery.Presentation.Coproduct
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Machinery/Presentation/Coequalizer — coequalizers, and all colimits

The coequalizer is levelwise: in each dimension, a cell of `Q` **with its coequalized boundary
pinned as fields**, modulo the two readings of each cell of `P`.  Pinning is the whole trick — the
two readings sit over 0-cells that are equal but not definitionally so, and `Quot.sound` applies
only once those are substituted away.  The boundary maps carry the one transport in sight,
`cellCongr`; definitional proof irrelevance is why it descends to the quotient.

With `Coproduct`'s cofans this gives every colimit, at the one universe where neither construction
bumps.
-/

universe w u' w₂ u

/-- A cell of a family fibred over a boundary, read at indices its boundary is equal to.
`Quiver.homOfEq` is this gadget for 1-cells; words and 2-cells have no mathlib version. -/
def cellCongr {ι : Sort*} (F : ι → ι → Sort*) :
    ∀ {a b A B : ι}, a = A → b = B → F a b → F A B
  | _, _, _, _, rfl, rfl, c => c

/-- Which proofs name the indices is irrelevant, so `cellCongr` descends to a quotient. -/
theorem cellCongr_heq {ι : Sort*} (F : ι → ι → Sort*) {a b A B : ι} (ha : a = A) (hb : b = B)
    (c : F a b) : cellCongr F ha hb c ≍ c := by subst ha; subst hb; rfl

theorem cellCongr_trans {ι : Sort*} (F : ι → ι → Sort*) {a b A B A' B' : ι} (ha : a = A)
    (hb : b = B) (ha' : A = A') (hb' : B = B') (c : F a b) :
    cellCongr F ha' hb' (cellCongr F ha hb c) = cellCongr F (ha.trans ha') (hb.trans hb') c := by
  subst ha; subst hb; subst ha'; subst hb'; rfl

/-- **A prefunctor carries a transported word to the transported word.** -/
theorem Prefunctor.mapPath_cellCongr {V : Type*} [Quiver V] {W : Type*} [Quiver W] (π : V ⥤q W)
    {x y x' y' : V} (hx : x = x') (hy : y = y') (p : Quiver.Path x y) :
    π.mapPath (cellCongr Quiver.Path hx hy p)
      = cellCongr Quiver.Path (congrArg π.obj hx) (congrArg π.obj hy) (π.mapPath p) := by
  subst hx; subst hy; rfl

/-- **Equal prefunctors agree on 1-cells** — `Prefunctor.map_of_eq`, said with `HEq`. -/
theorem Prefunctor.map_heq_of_eq {V : Type*} [Quiver V] {W : Type*} [Quiver W] {π σ : V ⥤q W}
    (h : π = σ) {x y : V} (e : x ⟶ y) : π.map e ≍ σ.map e := by subst h; rfl

/-- **A prefunctor respects a heterogeneous equality of 1-cells.** -/
theorem Prefunctor.map_heq_congr {V : Type*} [Quiver V] {W : Type*} [Quiver W] (π : V ⥤q W)
    {x y x' y' : V} (hx : x = x') (hy : y = y') {e : x ⟶ y} {e' : x' ⟶ y'} (h : e ≍ e') :
    π.map e ≍ π.map e' := by subst hx; subst hy; cases h; rfl

/-- **Equal prefunctors agree on words**, read at 0-cells named the same way. -/
theorem Prefunctor.congr_mapPath {V : Type*} [Quiver V] {W : Type*} [Quiver W] {π σ : V ⥤q W}
    (h : π = σ) {x y : V} (p : Quiver.Path x y) {A B : W}
    (hx : π.obj x = A) (hy : π.obj y = B) (hx' : σ.obj x = A) (hy' : σ.obj y = B) :
    cellCongr Quiver.Path hx hy (π.mapPath p) = cellCongr Quiver.Path hx' hy' (σ.mapPath p) := by
  subst h; rfl

namespace CategoryTheory

namespace Polygraph

variable {P Q : Polygraph.{max u' w, u', max u' w₂}} (f g : P ⟶ Q)

/-! ## 0-cells -/

/-- The two readings of a 0-cell of `P`. -/
def CoeqPtRel : Q.V → Q.V → Prop :=
  fun a b => ∃ c : P.V, (f.pre.obj ⟨c⟩).as = a ∧ (g.pre.obj ⟨c⟩).as = b

/-- 0-cells: `Q`'s, with the two readings of each of `P`'s identified. -/
def CoeqV : Type u' := Quot (CoeqPtRel f g)

/-- The 0-cell a 0-cell of `Q` names. -/
def coeqPt (a : Q.V) : CoeqV f g := Quot.mk _ a

/-- **The two readings of a 0-cell of `P` name one 0-cell.** -/
theorem coeqPt_pre (x : GenObj P.Gen) :
    coeqPt f g (f.pre.obj x).as = coeqPt f g (g.pre.obj x).as :=
  Quot.sound ⟨x.as, rfl, rfl⟩

/-! ## 1-cells -/

/-- A 1-cell of `Q` with the 0-cells it joins pinned. -/
structure CoeqRaw (A B : CoeqV f g) : Type (max u' w) where
  /-- its source in `Q` -/
  a : Q.V
  /-- its target in `Q` -/
  b : Q.V
  /-- the 1-cell -/
  cell : Q.Gen a b
  /-- the 0-cell its source names -/
  ha : coeqPt f g a = A
  /-- the 0-cell its target names -/
  hb : coeqPt f g b = B

/-- **The two readings of a 1-cell of `P`.** -/
inductive CoeqEq : ∀ {A B : CoeqV f g}, CoeqRaw f g A B → CoeqRaw f g A B → Prop
  | mk {x y : GenObj P.Gen} (e : x ⟶ y) {A B : CoeqV f g}
      (hA : coeqPt f g (f.pre.obj x).as = A) (hB : coeqPt f g (f.pre.obj y).as = B) :
      CoeqEq ⟨_, _, f.pre.map e, hA, hB⟩
        ⟨_, _, g.pre.map e, (coeqPt_pre f g x).symm.trans hA,
          (coeqPt_pre f g y).symm.trans hB⟩

/-- 1-cells: `Q`'s, modulo the two readings of each of `P`'s. -/
def CoeqGen (A B : CoeqV f g) : Type (max u' w) := Quot (@CoeqEq _ _ f g A B)

/-- The projection, on cells of dimension ≤ 1. -/
def coeqPre : GenObj Q.Gen ⥤q GenObj (CoeqGen f g) where
  obj x := ⟨coeqPt f g x.as⟩
  map e := Quot.mk _ ⟨_, _, e, rfl, rfl⟩

/-- **A 1-cell of `Q` read at any 0-cells its endpoints name** — the pinning substituted away. -/
theorem coeqGen_heq {a b : Q.V} (e : Q.Gen a b) {A B : CoeqV f g}
    (ha : coeqPt f g a = A) (hb : coeqPt f g b = B) :
    (Quot.mk _ ⟨a, b, e, ha, hb⟩ : CoeqGen f g A B) ≍ (coeqPre f g).map e := by
  subst ha; subst hb; rfl

/-- **The two readings of a 1-cell of `P` are one 1-cell.** -/
theorem coeqPre_map_heq {x y : GenObj P.Gen} (e : x ⟶ y) :
    (coeqPre f g).map (f.pre.map e) ≍ (coeqPre f g).map (g.pre.map e) :=
  (heq_of_eq (Quot.sound (CoeqEq.mk e rfl rfl))).trans (coeqGen_heq f g (g.pre.map e) _ _)

/-- **The projection coequalizes on cells of dimension ≤ 1.** -/
theorem coeqPreEq : f.pre ⋙q coeqPre f g = g.pre ⋙q coeqPre f g :=
  Prefunctor.ext' (fun x => congrArg (fun v => (⟨v⟩ : GenObj (CoeqGen f g))) (coeqPt_pre f g x))
    fun _ _ e => eq_of_heq ((Quiver.homOfEq_heq_right_iff _ _ _ _).2 (coeqPre_map_heq f g e))

/-- …at the level of 0-cells of the generating quiver. -/
theorem coeqPre_obj_eq (x : GenObj P.Gen) :
    (coeqPre f g).obj (f.pre.obj x) = (coeqPre f g).obj (g.pre.obj x) :=
  congrArg (fun π : GenObj P.Gen ⥤q GenObj (CoeqGen f g) => π.obj x) (coeqPreEq f g)

/-- **A prefunctor out of the coequalizer, read on a raw 1-cell.** -/
theorem map_coeqGen_heq {W : Type*} [Quiver W] (π : GenObj (CoeqGen f g) ⥤q W)
    {A B : CoeqV f g} (r : CoeqRaw f g A B) :
    π.map (Quot.mk _ r) ≍ (coeqPre f g ⋙q π).map (X := ⟨r.a⟩) (Y := ⟨r.b⟩) r.cell :=
  Prefunctor.map_heq_congr π (congrArg (fun v => (⟨v⟩ : GenObj (CoeqGen f g))) r.ha).symm
    (congrArg (fun v => (⟨v⟩ : GenObj (CoeqGen f g))) r.hb).symm
    (coeqGen_heq f g r.cell r.ha r.hb)

/-- **The projection is epi on prefunctors**: it is surjective on 0-cells and on 1-cells, so a
prefunctor out of the coequalizer is pinned by its restriction. -/
theorem coeqPre_comp_injective {W : Type u'} [Quiver W] {π σ : GenObj (CoeqGen f g) ⥤q W}
    (h : coeqPre f g ⋙q π = coeqPre f g ⋙q σ) : π = σ := by
  refine Prefunctor.ext' ?_ ?_
  · rintro ⟨A⟩
    induction A using Quot.ind with
    | _ a => exact congrArg (fun φ : GenObj Q.Gen ⥤q W => φ.obj ⟨a⟩) h
  · rintro _ _ e
    induction e using Quot.ind with
    | _ r =>
      exact eq_of_heq ((((map_coeqGen_heq f g π r).trans
        (Prefunctor.map_heq_of_eq h (x := ⟨r.a⟩) (y := ⟨r.b⟩) r.cell)).trans
        (map_coeqGen_heq f g σ r).symm).trans (Quiver.homOfEq_heq _ _ _).symm)

/-! ## 2-cells -/

/-- A 2-cell of `Q` with the 0-cells its boundary spans pinned. -/
structure CoeqRawRel (A B : GenObj (CoeqGen f g)) : Type (max u' w₂) where
  /-- the source of its boundary, in `Q` -/
  x : GenObj Q.Gen
  /-- the target of its boundary, in `Q` -/
  y : GenObj Q.Gen
  /-- the 2-cell -/
  cell : Q.Rel x y
  /-- the 0-cell its boundary starts at -/
  hx : (coeqPre f g).obj x = A
  /-- the 0-cell its boundary ends at -/
  hy : (coeqPre f g).obj y = B

/-- **The two readings of a 2-cell of `P`.** -/
inductive CoeqRelEq :
    ∀ {A B : GenObj (CoeqGen f g)}, CoeqRawRel f g A B → CoeqRawRel f g A B → Prop
  | mk {x y : GenObj P.Gen} (α : P.Rel x y) {A B : GenObj (CoeqGen f g)}
      (hA : (coeqPre f g).obj (f.pre.obj x) = A) (hB : (coeqPre f g).obj (f.pre.obj y) = B) :
      CoeqRelEq ⟨_, _, f.two α, hA, hB⟩
        ⟨_, _, g.two α, (coeqPre_obj_eq f g x).symm.trans hA,
          (coeqPre_obj_eq f g y).symm.trans hB⟩

/-- 2-cells: `Q`'s, modulo the two readings of each of `P`'s. -/
def CoeqRel (A B : GenObj (CoeqGen f g)) : Type (max u' w₂) := Quot (@CoeqRelEq _ _ f g A B)

/-- **A boundary of the coequalizer**: `Q`'s, read at the 0-cells the raw datum pins.  Stated for
either boundary at once, since `src` and `tgt` differ only in the two naturality inputs. -/
def coeqBoundary (bP : ∀ {x y : GenObj P.Gen}, P.Rel x y → Quiver.Path x y)
    (bQ : ∀ {x y : GenObj Q.Gen}, Q.Rel x y → Quiver.Path x y)
    (hf : ∀ {x y : GenObj P.Gen} (α : P.Rel x y), bQ (f.two α) = f.pre.mapPath (bP α))
    (hg : ∀ {x y : GenObj P.Gen} (α : P.Rel x y), bQ (g.two α) = g.pre.mapPath (bP α))
    {A B : GenObj (CoeqGen f g)} : CoeqRel f g A B → Quiver.Path A B :=
  Quot.lift (fun r => cellCongr Quiver.Path r.hx r.hy ((coeqPre f g).mapPath (bQ r.cell)))
    (by
      rintro _ _ ⟨α, _, _⟩
      dsimp only
      rw [hf α, hg α, ← Prefunctor.mapPath_comp_apply, ← Prefunctor.mapPath_comp_apply]
      exact Prefunctor.congr_mapPath (coeqPreEq f g) _ _ _ _ _)

/-- **The coequalizer of two morphisms of polygraphs**, taken in every dimension. -/
def coeq : Polygraph.{max u' w, u', max u' w₂} where
  V := CoeqV f g
  Gen := CoeqGen f g
  Rel := CoeqRel f g
  src := coeqBoundary f g (fun {_ _} => P.src) (fun {_ _} => Q.src) f.src_two g.src_two
  tgt := coeqBoundary f g (fun {_ _} => P.tgt) (fun {_ _} => Q.tgt) f.tgt_two g.tgt_two

/-- The projection. -/
def coeqπ : Q ⟶ coeq f g where
  pre := coeqPre f g
  two β := Quot.mk _ ⟨_, _, β, rfl, rfl⟩
  src_two _ := rfl
  tgt_two _ := rfl

/-- **A 2-cell of `Q` read at any 0-cells its boundary names.** -/
theorem coeqRel_heq {x y : GenObj Q.Gen} (β : Q.Rel x y) {A B : GenObj (CoeqGen f g)}
    (hx : (coeqPre f g).obj x = A) (hy : (coeqPre f g).obj y = B) :
    (Quot.mk _ ⟨x, y, β, hx, hy⟩ : CoeqRel f g A B) ≍ (coeqπ f g).two β := by
  subst hx; subst hy; rfl

/-- **The projection coequalizes.** -/
theorem coeqπ_condition : f ≫ coeqπ f g = g ≫ coeqπ f g :=
  Hom.ext' (coeqPreEq f g) fun α =>
    (heq_of_eq (Quot.sound (CoeqRelEq.mk α rfl rfl))).trans (coeqRel_heq f g (g.two α) _ _)

/-! ## The universal property -/

section Desc

variable {T : Polygraph.{max u' w, u', max u' w₂}} (t : Q ⟶ T) (ht : f ≫ t = g ≫ t)

/-- The 0-cell of `T` a 0-cell names. -/
def coeqDescPt : CoeqV f g → T.V :=
  Quot.lift (fun a => (t.pre.obj ⟨a⟩).as)
    (by
      rintro _ _ ⟨c, rfl, rfl⟩
      exact congrArg GenObj.as (congrArg (fun m : P ⟶ T => m.pre.obj ⟨c⟩) ht))

/-- The cells of dimension ≤ 1, descended. -/
def coeqDescPre : GenObj (CoeqGen f g) ⥤q GenObj T.Gen where
  obj A := ⟨coeqDescPt f g t ht A.as⟩
  map := Quot.lift
    (fun r => Quiver.homOfEq (t.pre.map r.cell)
      (congrArg (fun v => (⟨coeqDescPt f g t ht v⟩ : GenObj T.Gen)) r.ha)
      (congrArg (fun v => (⟨coeqDescPt f g t ht v⟩ : GenObj T.Gen)) r.hb))
    (by
      rintro _ _ ⟨e, _, _⟩
      exact eq_of_heq (((Quiver.homOfEq_heq _ _ _).trans
        (Prefunctor.map_heq_of_eq (congrArg Polygraph.Hom.pre ht) e)).trans
        (Quiver.homOfEq_heq _ _ _).symm))

/-- The defeq that makes `coeqπ_desc` hold on the nose. -/
theorem coeqPre_comp_descPre : coeqPre f g ⋙q coeqDescPre f g t ht = t.pre := rfl

/-- **The descent.** -/
def coeqDesc : coeq f g ⟶ T where
  pre := coeqDescPre f g t ht
  two := Quot.lift
    (fun r => cellCongr T.Rel (congrArg (coeqDescPre f g t ht).obj r.hx)
      (congrArg (coeqDescPre f g t ht).obj r.hy) (t.two r.cell))
    (by
      rintro _ _ ⟨α, _, _⟩
      exact eq_of_heq (((cellCongr_heq _ _ _ _).trans (Hom.two_heq_of_eq ht α)).trans
        (cellCongr_heq _ _ _ _).symm))
  src_two := by
    refine fun {_ _} => Quot.ind fun r => ?_
    obtain ⟨_, _, α, rfl, rfl⟩ := r
    change T.src (t.two α) = (coeqDescPre f g t ht).mapPath ((coeqPre f g).mapPath (Q.src α))
    exact (t.src_two α).trans
      (Prefunctor.mapPath_comp_apply (coeqPre f g) (coeqDescPre f g t ht) (Q.src α))
  tgt_two := by
    refine fun {_ _} => Quot.ind fun r => ?_
    obtain ⟨_, _, α, rfl, rfl⟩ := r
    change T.tgt (t.two α) = (coeqDescPre f g t ht).mapPath ((coeqPre f g).mapPath (Q.tgt α))
    exact (t.tgt_two α).trans
      (Prefunctor.mapPath_comp_apply (coeqPre f g) (coeqDescPre f g t ht) (Q.tgt α))

/-- **The descent restricts to what it descends** — on the nose. -/
theorem coeqπ_desc : coeqπ f g ≫ coeqDesc f g t ht = t := rfl

/-- **…and is the only such map.** -/
theorem coeqDesc_uniq (n : coeq f g ⟶ T) (hn : coeqπ f g ≫ n = t) : n = coeqDesc f g t ht := by
  refine Hom.ext' (coeqPre_comp_injective f g
    ((congrArg Polygraph.Hom.pre hn).trans (coeqPre_comp_descPre f g t ht).symm)) ?_
  refine fun {_ _} => Quot.ind fun r => ?_
  obtain ⟨_, _, α, rfl, rfl⟩ := r
  exact Hom.two_heq_of_eq hn α

end Desc

open Limits

/-- **The levelwise quotient is the coequalizer.** -/
def coeqIsColimit : IsColimit (Cofork.ofπ (coeqπ f g) (coeqπ_condition f g)) :=
  Cofork.IsColimit.mk _ (fun s => coeqDesc f g s.π s.condition)
    (fun s => coeqπ_desc f g s.π s.condition)
    (fun s m hm => coeqDesc_uniq f g s.π s.condition m hm)

instance hasCoequalizer : HasColimit (parallelPair f g) :=
  HasColimit.mk ⟨_, coeqIsColimit f g⟩

instance : HasCoequalizers Polygraph.{max u' w, u', max u' w₂} :=
  hasCoequalizers_of_hasColimit_parallelPair _

instance : HasCoproducts.{u} Polygraph.{u, u, u} :=
  hasCoproducts_of_colimit_cofans (fun P => Cofan.mk (coproduct P) (coproductIncl P))
    fun P => coprodIsColimit P

/-- **Polygraphs have all colimits** — at the one universe where neither the coproduct nor the
coequalizer bumps. -/
instance hasColimitsOfSize : HasColimitsOfSize.{u, u} Polygraph.{u, u, u} :=
  has_colimits_of_hasCoequalizers_and_coproducts

end Polygraph

end CategoryTheory
