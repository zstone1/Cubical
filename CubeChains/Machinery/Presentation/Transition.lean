import CubeChains.Machinery.Presentation.Adjunction
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Machinery/Presentation/Transition — the bicolimit of a diagram of categories, presented

`bicolimit F` is `Grothendieck F` with the fibrewise isomorphisms inverted: an arrow of the index
acts by an invertible **transition** instead of the identification `Limits.colimit` imposes, which
is what lets a pseudo-cocone descend.

`transitionPoly P` reads that on cells — a copy of `P c` for each `c`, a transition and its formal
inverse for each arrow of the index, and the unit, cocycle, naturality and cancellation 2-cells —
and presents it (`presentsBicolimit`), nothing asked of the 0-cells.  A consumer holding their own
`X ≌ bicolimit (P ⋙ presentedFunctor)` reaches `Presents _ X` through `Presents.transport`.
-/

universe v₁ u₁ v₂ u₂ u

namespace CategoryTheory

/-! ## The bicolimit -/

/-- **What the bicolimit inverts**: the arrows whose fibre component is invertible. -/
def Grothendieck.fibrewiseIsos {I : Type u₁} [Category.{v₁} I] (F : I ⥤ Cat.{v₂, u₂}) :
    MorphismProperty (Grothendieck F) := fun _ _ f => IsIso f.fiber

/-- **The bicolimit of a diagram of categories**: `Grothendieck F` with the fibrewise isomorphisms
inverted.  `Limits.colimit` glues the legs by an equality, so only a cocone commuting on the nose
descends; here each arrow of the index keeps an invertible transition of its own, and a cocone
commuting up to coherent isomorphism descends instead. -/
abbrev bicolimit {I : Type u₁} [Category.{v₁} I] (F : I ⥤ Cat.{v₂, u₂}) :=
  (Grothendieck.fibrewiseIsos F).Localization

namespace Polygraph

section Transition

variable {I : Type u} [Category.{u} I] (P : I ⥤ Polygraph.{u, u, u})

/-- The diagram of categories the copies present. -/
private abbrev fib : I ⥤ Cat.{u, u} := P ⋙ presentedFunctor.{u, u}

/-- …and the class the bicolimit of that diagram inverts. -/
private abbrev wFib : MorphismProperty (Grothendieck (fib P)) := Grothendieck.fibrewiseIsos (fib P)

/-- A 0-cell: an index and a 0-cell of its copy. -/
private abbrev Obj : Type u := Σ c : I, (P.obj c).V

/-- **The 0-cell an arrow of the index carries a 0-cell to** — the target of its transition. -/
def transitionPoly.push {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) : (P.obj c').V :=
  ((P.map u).pre.obj ⟨a⟩).as

private theorem push_id (c : I) (a : (P.obj c).V) : transitionPoly.push P (𝟙 c) a = a :=
  congrArg (fun m : P.obj c ⟶ P.obj c => (m.pre.obj ⟨a⟩).as) (P.map_id c)

private theorem push_comp {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
    transitionPoly.push P (u ≫ v) a
      = transitionPoly.push P v (transitionPoly.push P u a) :=
  congrArg (fun m : P.obj c₁ ⟶ P.obj c₃ => (m.pre.obj ⟨a⟩).as) (P.map_comp u v)

/-- **1-cells**: a copy's generator, a transition, or a transition's formal inverse. -/
private inductive Arrow : Obj P → Obj P → Type u
  | copy {c : I} {a b : (P.obj c).V} (e : (P.obj c).Gen a b) : Arrow ⟨c, a⟩ ⟨c, b⟩
  | fwd {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) : Arrow ⟨c, a⟩ ⟨c', transitionPoly.push P u a⟩
  | bwd {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) : Arrow ⟨c', transitionPoly.push P u a⟩ ⟨c, a⟩

/-- A 0-cell of the copy at `c`. -/
private def copyPt (c : I) (x : GenObj (P.obj c).Gen) : GenObj (Arrow P) := ⟨⟨c, x.as⟩⟩

/-- A copy's generator, as a 1-cell. -/
private def copyGen {c : I} {a b : (P.obj c).V} (e : (P.obj c).Gen a b) :
    (⟨⟨c, a⟩⟩ : GenObj (Arrow P)) ⟶ ⟨⟨c, b⟩⟩ := Arrow.copy e

/-- A transition, as a 1-cell. -/
private def fwdGen {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    (⟨⟨c, a⟩⟩ : GenObj (Arrow P)) ⟶ ⟨⟨c', transitionPoly.push P u a⟩⟩ := Arrow.fwd u a

/-- Its formal inverse, as a 1-cell. -/
private def bwdGen {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    (⟨⟨c', transitionPoly.push P u a⟩⟩ : GenObj (Arrow P)) ⟶ ⟨⟨c, a⟩⟩ := Arrow.bwd u a

/-- The copy at `c`, on generating quivers. -/
private def copyPre (c : I) : GenObj (P.obj c).Gen ⥤q GenObj (Arrow P) where
  obj x := copyPt P c x
  map e := copyGen P e

/-- The 0-cell equality a transition along an identity spans. -/
private theorem copyPt_id (c : I) (a : (P.obj c).V) :
    (⟨⟨c, a⟩⟩ : GenObj (Arrow P)) = ⟨⟨c, transitionPoly.push P (𝟙 c) a⟩⟩ :=
  congrArg (fun z => (⟨⟨c, z⟩⟩ : GenObj (Arrow P))) (push_id P c a).symm

/-- …and the one a pair of transitions spans. -/
private theorem copyPt_comp {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
    (⟨⟨c₃, transitionPoly.push P (u ≫ v) a⟩⟩ : GenObj (Arrow P))
      = ⟨⟨c₃, transitionPoly.push P v (transitionPoly.push P u a)⟩⟩ :=
  congrArg (fun z => (⟨⟨c₃, z⟩⟩ : GenObj (Arrow P))) (push_comp P u v a)

/-- **2-cells**: the copies', the unit and cocycle of the transitions, their naturality against a
copy's generators, and the two cancellations. -/
private inductive Law : GenObj (Arrow P) → GenObj (Arrow P) → Type u
  | copy {c : I} {x y : GenObj (P.obj c).Gen} (α : (P.obj c).Rel x y) :
      Law (copyPt P c x) (copyPt P c y)
  | unit {c : I} (a : (P.obj c).V) : Law ⟨⟨c, a⟩⟩ ⟨⟨c, transitionPoly.push P (𝟙 c) a⟩⟩
  | cocyc {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
      Law ⟨⟨c₁, a⟩⟩ ⟨⟨c₃, transitionPoly.push P v (transitionPoly.push P u a)⟩⟩
  | nat {c c' : I} (u : c ⟶ c') {a b : (P.obj c).V} (e : (P.obj c).Gen a b) :
      Law ⟨⟨c, a⟩⟩ ⟨⟨c', transitionPoly.push P u b⟩⟩
  | cancel {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) : Law ⟨⟨c, a⟩⟩ ⟨⟨c, a⟩⟩
  | cancel' {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
      Law ⟨⟨c', transitionPoly.push P u a⟩⟩ ⟨⟨c', transitionPoly.push P u a⟩⟩

/-- The source word of a 2-cell. -/
private def srcWord : ∀ {x y : GenObj (Arrow P)}, Law P x y → Quiver.Path x y
  | _, _, .copy (c := c) α => (copyPre P c).mapPath ((P.obj c).src α)
  | _, _, .unit a => (fwdGen P (𝟙 _) a).toPath
  | _, _, .cocyc u v a =>
      cellCongr Quiver.Path rfl (copyPt_comp P u v a) (fwdGen P (u ≫ v) a).toPath
  | _, _, .nat (b := b) u e => (copyGen P e).toPath.comp (fwdGen P u b).toPath
  | _, _, .cancel u a => (fwdGen P u a).toPath.comp (bwdGen P u a).toPath
  | _, _, .cancel' u a => (bwdGen P u a).toPath.comp (fwdGen P u a).toPath

/-- The target word of a 2-cell. -/
private def tgtWord : ∀ {x y : GenObj (Arrow P)}, Law P x y → Quiver.Path x y
  | _, _, .copy (c := c) α => (copyPre P c).mapPath ((P.obj c).tgt α)
  | _, _, .unit a => cellCongr Quiver.Path rfl (copyPt_id P _ a) Quiver.Path.nil
  | _, _, .cocyc u v a =>
      (fwdGen P u a).toPath.comp (fwdGen P v (transitionPoly.push P u a)).toPath
  | _, _, .nat (a := a) u e =>
      (fwdGen P u a).toPath.comp (copyGen P ((P.map u).pre.map (cell e))).toPath
  | _, _, .cancel _ _ => Quiver.Path.nil
  | _, _, .cancel' _ _ => Quiver.Path.nil

/-- **The Grothendieck construction of `P`, read on cells.** -/
def transitionPoly : Polygraph.{u, u, u} where
  V := Obj P
  Gen := Arrow P
  Rel := Law P
  src := srcWord P
  tgt := tgtWord P

/-- **The copy at `c`**, as a morphism of polygraphs. -/
def transitionPoly.incl (c : I) : P.obj c ⟶ transitionPoly P where
  pre := copyPre P c
  two α := Law.copy α
  src_two _ := rfl
  tgt_two _ := rfl

/-! ## The transitions, as arrows of the presented category -/

/-- **A transition**, at a 0-cell of its source copy. -/
def transitionPoly.fwd {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    (⟨⟨⟨c, a⟩⟩⟩ : (transitionPoly P).presented) ⟶ ⟨⟨⟨c', transitionPoly.push P u a⟩⟩⟩ :=
  (transitionPoly P).quot.map (fwdGen P u a).toPath

/-- …and its formal inverse. -/
def transitionPoly.bwd {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    (⟨⟨⟨c', transitionPoly.push P u a⟩⟩⟩ : (transitionPoly P).presented) ⟶ ⟨⟨⟨c, a⟩⟩⟩ :=
  (transitionPoly P).quot.map (bwdGen P u a).toPath

theorem transitionPoly.fwd_bwd {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    transitionPoly.fwd P u a ≫ transitionPoly.bwd P u a = 𝟙 _ :=
  ((transitionPoly P).quot.map_comp _ _).symm.trans
    ((transitionPoly P).quot_src_tgt (Law.cancel u a))

theorem transitionPoly.bwd_fwd {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    transitionPoly.bwd P u a ≫ transitionPoly.fwd P u a = 𝟙 _ :=
  ((transitionPoly P).quot.map_comp _ _).symm.trans
    ((transitionPoly P).quot_src_tgt (Law.cancel' u a))

private instance isIso_fwd {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    IsIso (transitionPoly.fwd P u a) :=
  ⟨transitionPoly.bwd P u a, transitionPoly.fwd_bwd P u a, transitionPoly.bwd_fwd P u a⟩

/-! ## The cocartesian arrows the transitions name

`wFib` is inverted: the cocartesian arrows are fibrewise identities, and the arrows already
invertible in `Grothendieck` are fibrewise invertible too, so nothing is lost by taking the whole
fibrewise-invertible class. -/

/-- The object of the Grothendieck construction a 0-cell names. -/
private def grObj (xa : Obj P) : Grothendieck (fib P) where
  base := xa.1
  fiber := (⟨⟨xa.2⟩⟩ : (P.obj xa.1).presented)

private theorem grObj_id (c : I) (a : (P.obj c).V) :
    grObj P ⟨c, a⟩ = grObj P ⟨c, transitionPoly.push P (𝟙 c) a⟩ :=
  congrArg (fun z => grObj P ⟨c, z⟩) (push_id P c a).symm

private theorem grObj_comp {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
    grObj P ⟨c₃, transitionPoly.push P (u ≫ v) a⟩
      = grObj P ⟨c₃, transitionPoly.push P v (transitionPoly.push P u a)⟩ :=
  congrArg (fun z => grObj P ⟨c₃, z⟩) (push_comp P u v a)

/-- **The cocartesian arrow a transition names** — `Grothendieck.ιNatTrans`, at a 0-cell. -/
private def cocart {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    grObj P ⟨c, a⟩ ⟶ grObj P ⟨c', transitionPoly.push P u a⟩ :=
  ⟨u, 𝟙 _⟩

/-- …on the nose, which is what the naturality 2-cell is read against. -/
private theorem cocart_eq_ιNatTrans {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    cocart P u a
      = (Grothendieck.ιNatTrans (F := fib P) u).app (⟨⟨a⟩⟩ : (P.obj c).presented) := rfl

private theorem wFib_cocart {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    wFib P (cocart P u a) := show IsIso (𝟙 _) from inferInstance

private instance isIso_Q_cocart {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    IsIso ((wFib P).Q.map (cocart P u a)) :=
  Localization.inverts (wFib P).Q (wFib P) _ (wFib_cocart P u a)

/-- **A transition along an identity is an identity**, read at the 0-cell it names. -/
private theorem cocart_id (c : I) (a : (P.obj c).V) :
    cocart P (𝟙 c) a = eqToHom (grObj_id P c a) := by
  refine Grothendieck.ext _ _ ?_ ?_
  · rw [Grothendieck.base_eqToHom]
    exact (eqToHom_refl _ _).symm
  · rw [Grothendieck.fiber_eqToHom]
    exact (Category.comp_id _).trans rfl

/-- **…and a transition along a composite is the composite of transitions.** -/
private theorem cocart_comp {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
    cocart P (u ≫ v) a ≫ eqToHom (grObj_comp P u v a)
      = cocart P u a ≫ cocart P v (transitionPoly.push P u a) := by
  have hb : (eqToHom (grObj_comp P u v a)).base = 𝟙 c₃ := by
    rw [Grothendieck.base_eqToHom]; exact eqToHom_refl _ _
  refine Grothendieck.ext _ _ ?_ ?_
  · rw [Grothendieck.comp_base, Grothendieck.comp_base, hb]
    exact (Category.comp_id _).trans rfl
  · rw [Grothendieck.comp_fiber, Grothendieck.comp_fiber, Grothendieck.fiber_eqToHom,
      show (cocart P (u ≫ v) a).fiber = 𝟙 _ from rfl,
      show (cocart P u a).fiber = 𝟙 _ from rfl,
      show (cocart P v (transitionPoly.push P u a)).fiber = 𝟙 _ from rfl]
    -- `erw`: the fibre lives at `↥(Cat.of …)`, so `Functor.map_id`'s and `Category.id_comp`'s
    -- objects are `rfl`-equal to the goal's but not syntactically equal, and `rw` will not unfold
    -- the bundled coercion to see it.
    erw [Functor.map_id, Functor.map_id]
    erw [Category.id_comp]
    erw [Category.id_comp]
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact eqToHom_comp₃ _ _ _ _

/-- The copy at `c`, read in the bicolimit. -/
private noncomputable def leg (c : I) : (P.obj c).presented ⥤ bicolimit (fib P) :=
  Grothendieck.ι (fib P) c ⋙ (wFib P).Q

private theorem leg_map (c : I) {Y Z : (P.obj c).presented} (f : Y ⟶ Z) :
    (leg P c).map f = (wFib P).Q.map ((Grothendieck.ι (fib P) c).map f) := rfl

/-- What a 1-cell names. -/
private noncomputable def evalMap {xa ya : Obj P} :
    Arrow P xa ya → ((wFib P).Q.obj (grObj P xa) ⟶ (wFib P).Q.obj (grObj P ya))
  | .copy (c := c) e => (leg P c).map ((P.obj c).quot.map (cell e).toPath)
  | .fwd u a => (wFib P).Q.map (cocart P u a)
  | .bwd u a => inv ((wFib P).Q.map (cocart P u a))

/-- **The cells, read in the bicolimit.** -/
private noncomputable def evalPre : GenObj (Arrow P) ⥤q bicolimit (fib P) where
  obj x := (wFib P).Q.obj (grObj P x.as)
  map e := evalMap P e

/-- A copy's word is read through the copy's leg. -/
private theorem eval_copy (c : I) {x y : GenObj (P.obj c).Gen} (w : Quiver.Path x y) :
    (Paths.lift (evalPre P)).map ((copyPre P c).mapPath w)
      = (leg P c).map ((P.obj c).quot.map w) := by
  induction w with
  | nil =>
      rw [Prefunctor.mapPath_nil, Paths.lift_nil]
      exact ((congrArg (leg P c).map ((P.obj c).quot.map_id _)).trans
        ((leg P c).map_id _)).symm
  | cons w e ih =>
      have hc : (P.obj c).quot.map (w.cons e)
          = (P.obj c).quot.map w ≫ (P.obj c).quot.map (Quiver.Hom.toPath e) :=
        (P.obj c).quot.map_comp w (Quiver.Hom.toPath e)
      rw [Prefunctor.mapPath_cons, Paths.lift_cons, ih, hc, Functor.map_comp]
      rfl

/-- **The 2-cells hold in the bicolimit.** -/
private theorem evalSound {x y : GenObj (Arrow P)} (α : Law P x y) :
    (Paths.lift (evalPre P)).map (srcWord P α)
      = (Paths.lift (evalPre P)).map (tgtWord P α) := by
  cases α with
  | copy α =>
      rw [srcWord, tgtWord]
      exact (eval_copy P _ _).trans
        ((congrArg (leg P _).map ((P.obj _).quot_src_tgt α)).trans
          (eval_copy P _ _).symm)
  | unit a =>
      rw [srcWord, tgtWord, Paths.lift_cellCongr, Paths.lift_toPath]
      change evalMap P (Arrow.fwd (𝟙 _) a) = _
      rw [evalMap, cocart_id, eqToHom_map, Paths.lift_nil]
      exact (Category.id_comp _).symm
  | cocyc u v a =>
      rw [srcWord, tgtWord, Paths.lift_cellCongr, Paths.lift_toPath, Paths.lift_map_comp,
        Paths.lift_toPath, Paths.lift_toPath]
      change evalMap P (Arrow.fwd (u ≫ v) a) ≫ _
        = evalMap P (Arrow.fwd u a) ≫ evalMap P (Arrow.fwd v (transitionPoly.push P u a))
      rw [evalMap, evalMap, evalMap, ← (wFib P).Q.map_comp, ← cocart_comp,
        (wFib P).Q.map_comp, eqToHom_map]
      rfl
  | nat u e =>
      rw [srcWord, tgtWord, Paths.lift_map_comp, Paths.lift_map_comp]
      simp only [Paths.lift_toPath]
      change evalMap P (Arrow.copy e) ≫ evalMap P (Arrow.fwd u _)
        = evalMap P (Arrow.fwd u _) ≫ evalMap P (Arrow.copy ((P.map u).pre.map (cell e)))
      rw [evalMap, evalMap, evalMap, evalMap, leg_map, leg_map]
      exact ((wFib P).Q.map_comp _ _).symm.trans
        ((congrArg (wFib P).Q.map ((Grothendieck.ιNatTrans (F := fib P) u).naturality
          ((P.obj _).quot.map (cell e).toPath))).trans ((wFib P).Q.map_comp _ _))
  | cancel u a =>
      rw [srcWord, tgtWord, Paths.lift_map_comp, Paths.lift_toPath, Paths.lift_toPath,
        Paths.lift_nil]
      change evalMap P (Arrow.fwd u a) ≫ evalMap P (Arrow.bwd u a) = _
      rw [evalMap, evalMap, IsIso.hom_inv_id]
      rfl
  | cancel' u a =>
      rw [srcWord, tgtWord, Paths.lift_map_comp, Paths.lift_toPath, Paths.lift_toPath,
        Paths.lift_nil]
      change evalMap P (Arrow.bwd u a) ≫ evalMap P (Arrow.fwd u a) = _
      rw [evalMap, evalMap, IsIso.inv_hom_id]
      rfl

/-! ## The transitions as the Grothendieck construction's comparison data -/

/-- The transport a transition along an identity carries. -/
private theorem quotPt_id (c : I) (a : (P.obj c).V) :
    (⟨⟨⟨c, a⟩⟩⟩ : (transitionPoly P).presented) = ⟨⟨⟨c, transitionPoly.push P (𝟙 c) a⟩⟩⟩ :=
  congrArg (fun z => (⟨z⟩ : (transitionPoly P).presented)) (copyPt_id P c a)

/-- …and the one a pair of transitions carries. -/
private theorem quotPt_comp {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
    (⟨⟨⟨c₃, transitionPoly.push P (u ≫ v) a⟩⟩⟩ : (transitionPoly P).presented)
      = ⟨⟨⟨c₃, transitionPoly.push P v (transitionPoly.push P u a)⟩⟩⟩ :=
  congrArg (fun z => (⟨z⟩ : (transitionPoly P).presented)) (copyPt_comp P u v a)

/-- The unit 2-cell, read in the presented category. -/
private theorem fwd_unit (c : I) (a : (P.obj c).V) :
    transitionPoly.fwd P (𝟙 c) a = eqToHom (quotPt_id P c a) :=
  ((transitionPoly P).quot_src_tgt (Law.unit a)).trans
    (((transitionPoly P).quot_map_cellCongr (copyPt_id P c a) Quiver.Path.nil).trans
      ((congrArg (· ≫ eqToHom (quotPt_id P c a)) ((transitionPoly P).quot.map_id _)).trans
        (Category.id_comp _)))

/-- …and the cocycle. -/
private theorem fwd_cocyc {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
    transitionPoly.fwd P (u ≫ v) a ≫ eqToHom (quotPt_comp P u v a)
      = transitionPoly.fwd P u a
        ≫ transitionPoly.fwd P v (transitionPoly.push P u a) :=
  ((transitionPoly P).quot_map_cellCongr (copyPt_comp P u v a)
      (fwdGen P (u ≫ v) a).toPath).symm.trans
    (((transitionPoly P).quot_src_tgt (Law.cocyc u v a)).trans
      ((transitionPoly P).quot.map_comp _ _))

/-- **The transitions, as a 2-cell between the copies** — the `hom` datum of the Grothendieck
construction, read on cells; naturality is the `nat` 2-cell. -/
private def transNat {c c' : I} (u : c ⟶ c') :
    (transitionPoly.incl P c).functor ⟶ (P.map u).functor ⋙ (transitionPoly.incl P c').functor :=
  natTransOfGen _ _ (fun x => transitionPoly.fwd P u x.as) fun {_ _} e =>
    ((transitionPoly P).quot.map_comp _ _).symm.trans
      (((transitionPoly P).quot_src_tgt (Law.nat u e)).trans
        ((transitionPoly P).quot.map_comp _ _))

private theorem incl_id_eq (c : I) :
    (transitionPoly.incl P c).functor
      = ((fib P).map (𝟙 c)).toFunctor ⋙ (transitionPoly.incl P c).functor := by
  simp only [Functor.map_id]
  rfl

private theorem incl_comp_eq {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) :
    ((fib P).map u).toFunctor ⋙ ((fib P).map v).toFunctor ⋙ (transitionPoly.incl P c₃).functor
      = ((fib P).map (u ≫ v)).toFunctor ⋙ (transitionPoly.incl P c₃).functor := by
  simp only [Functor.map_comp]
  rfl

private theorem transNat_id (c : I) : transNat P (𝟙 c) = eqToHom (incl_id_eq P c) :=
  NatTrans.ext (funext fun X =>
    (fwd_unit P c X.as.as).trans (eqToHom_app (incl_id_eq P c) X).symm)

private theorem transNat_comp {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) :
    transNat P (u ≫ v)
      = transNat P u ≫ Functor.whiskerLeft ((fib P).map u).toFunctor (transNat P v)
        ≫ eqToHom (incl_comp_eq P u v) := by
  refine NatTrans.ext (funext fun X => ?_)
  refine Eq.trans ?_ (congrArg (fun z => transitionPoly.fwd P u X.as.as
    ≫ transitionPoly.fwd P v (transitionPoly.push P u X.as.as) ≫ z)
    (eqToHom_app (incl_comp_eq P u v) X).symm)
  refine (Category.comp_id _).symm.trans ?_
  refine (congrArg (transitionPoly.fwd P (u ≫ v) X.as.as ≫ ·)
    ((eqToHom_refl _ ((quotPt_comp P u v X.as.as).trans
        (Functor.congr_obj (incl_comp_eq P u v) X))).symm.trans
      (eqToHom_trans (quotPt_comp P u v X.as.as)
        (Functor.congr_obj (incl_comp_eq P u v) X)).symm)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (congrArg (· ≫ _) (fwd_cocyc P u v X.as.as)).trans (Category.assoc _ _ _)

/-- **The Grothendieck construction, read on the copies** — `functorFrom` at the transitions. -/
private def fromGrothendieck : Grothendieck (fib P) ⥤ (transitionPoly P).presented :=
  Grothendieck.functorFrom (fun c => (transitionPoly.incl P c).functor) (fun u => transNat P u)
    (transNat_id P) (fun _ _ _ u v => transNat_comp P u v)

private theorem fromGrothendieck_map {X Y : Grothendieck (fib P)} (f : X ⟶ Y) :
    (fromGrothendieck P).map f
      = transitionPoly.fwd P f.base X.fiber.as.as
        ≫ (transitionPoly.incl P Y.base).functor.map f.fiber := rfl

private theorem fromGrothendieck_inverts : (wFib P).IsInvertedBy (fromGrothendieck P) := by
  rintro X Y f hf
  rw [fromGrothendieck_map]
  -- the fibre's `Category` instance arrives through `Cat`'s bundling, so the local `IsIso` is
  -- passed by hand rather than found by instance search
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (isIso_fwd P _ _)
    (Iso.isIso_hom ((transitionPoly.incl P Y.base).functor.mapIso (@asIso _ _ _ _ f.fiber hf)))

/-- **The retraction**: the Grothendieck construction is read on cells, and the transitions are
already invertible there. -/
private noncomputable def retract : bicolimit (fib P) ⥤ (transitionPoly P).presented :=
  Localization.Construction.lift (fromGrothendieck P) (fromGrothendieck_inverts P)

/-! ## The comparison, and that it is an equivalence -/

/-- **The comparison**: a word of `transitionPoly P`, read in the bicolimit. -/
private noncomputable def toBicolimit : (transitionPoly P).presented ⥤ bicolimit (fib P) :=
  Polygraph.desc (P := transitionPoly P) (evalPre P) (evalSound P)

/-- A copy, read by the comparison, is that copy's leg. -/
private theorem incl_comp_toBicolimit (c : I) :
    (transitionPoly.incl P c).functor ⋙ toBicolimit P = leg P c :=
  Quotient.lift_unique' (P.obj c).homRel _ _
    (Functor.ext (fun _ => rfl) fun _ _ w =>
      (eval_copy P c w).trans ((Category.comp_id _).symm.trans (Category.id_comp _).symm))

private theorem incl_toBicolimit_map (c : I) {Y Z : (P.obj c).presented} (g : Y ⟶ Z) :
    (toBicolimit P).map ((transitionPoly.incl P c).functor.map g) = (leg P c).map g :=
  (Functor.congr_hom (incl_comp_toBicolimit P c) g).trans
    ((Category.id_comp _).trans (Category.comp_id _))

/-- **Every arrow of the Grothendieck construction is a transition then a fibre arrow.** -/
private theorem cocart_comp_ι {X Y : Grothendieck (fib P)} (f : X ⟶ Y) :
    cocart P f.base X.fiber.as.as ≫ (Grothendieck.ι (fib P) Y.base).map f.fiber = f :=
  Grothendieck.ext _ _ ((Category.comp_id _).trans rfl)
    ((eqToHom_map_id_chain _ _ _ _ _ rfl).trans (Category.id_comp _))

/-- A word of `transitionPoly P`, read by the comparison. -/
private theorem toBicolimit_quot {x y : GenObj (Arrow P)} (w : Quiver.Path x y) :
    (toBicolimit P).map ((transitionPoly P).quot.map w) = (Paths.lift (evalPre P)).map w := rfl

private theorem toBicolimit_fwd {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    (toBicolimit P).map (transitionPoly.fwd P u a) = (wFib P).Q.map (cocart P u a) :=
  (toBicolimit_quot P _).trans (Paths.lift_toPath (evalPre P) (fwdGen P u a))

/-- **The comparison undoes the retraction** — the Grothendieck construction is read cell by cell
back onto itself. -/
private theorem fromGrothendieck_comp_toBicolimit :
    fromGrothendieck P ⋙ toBicolimit P = (wFib P).Q :=
  Functor.ext (fun _ => rfl) fun X Y f => by
    refine Eq.trans ?_ ((Category.comp_id _).symm.trans (Category.id_comp _).symm)
    refine (congrArg (toBicolimit P).map (fromGrothendieck_map P f)).trans ?_
    refine ((toBicolimit P).map_comp _ _).trans ?_
    refine (congrArg (· ≫ (toBicolimit P).map
      ((transitionPoly.incl P Y.base).functor.map f.fiber))
      (toBicolimit_fwd P f.base X.fiber.as.as)).trans ?_
    refine (congrArg ((wFib P).Q.map (cocart P f.base X.fiber.as.as) ≫ ·)
      ((incl_toBicolimit_map P Y.base f.fiber).trans (leg_map P Y.base f.fiber))).trans ?_
    exact (((wFib P).Q.map_comp _ _).symm.trans
      (congrArg (wFib P).Q.map (cocart_comp_ι P f)))

private theorem retract_comp_toBicolimit : retract P ⋙ toBicolimit P = 𝟭 _ :=
  Localization.Construction.uniq _ _ (by
    rw [← Functor.assoc, show (wFib P).Q ⋙ retract P = fromGrothendieck P from
        Localization.Construction.fac _ _,
      fromGrothendieck_comp_toBicolimit, Functor.comp_id])

/-- An arrow of the Grothendieck construction, read by the retraction. -/
private theorem retract_Q {X Y : Grothendieck (fib P)} (g : X ⟶ Y) :
    (retract P).map ((wFib P).Q.map g) = (fromGrothendieck P).map g :=
  (Functor.congr_hom
      (Localization.Construction.fac (fromGrothendieck P) (fromGrothendieck_inverts P)) g).trans
    ((Category.id_comp _).trans (Category.comp_id _))

/-- A copy's arrow, read by the Grothendieck comparison. -/
private theorem fromGrothendieck_ι (c : I) {Y Z : (P.obj c).presented} (g : Y ⟶ Z) :
    (fromGrothendieck P).map ((Grothendieck.ι (fib P) c).map g)
      = (transitionPoly.incl P c).functor.map g := by
  refine (fromGrothendieck_map P _).trans ?_
  refine (congrArg (· ≫ (transitionPoly.incl P c).functor.map
    (((Grothendieck.ι (fib P) c).map g).fiber)) (fwd_unit P c Y.as.as)).trans ?_
  refine (congrArg (eqToHom (quotPt_id P c Y.as.as) ≫ ·)
    ((transitionPoly.incl P c).functor.map_comp _ g)).trans ?_
  refine (congrArg (fun z => eqToHom (quotPt_id P c Y.as.as) ≫ z
    ≫ (transitionPoly.incl P c).functor.map g)
    (eqToHom_map (transitionPoly.incl P c).functor _)).trans ?_
  exact eqToHom_comp_cancel _ _ _

private theorem retract_fwd {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    (retract P).map ((wFib P).Q.map (cocart P u a)) = transitionPoly.fwd P u a := by
  refine (retract_Q P _).trans ((fromGrothendieck_map P _).trans ?_)
  refine (congrArg (transitionPoly.fwd P u a ≫ ·)
    ((transitionPoly.incl P c').functor.map_id _)).trans ?_
  exact Category.comp_id _

/-- **The cells are read back to themselves** — the three generator cases. -/
private theorem retract_evalPre :
    evalPre P ⋙q (retract P).toPrefunctor
      = Paths.of (GenObj (Arrow P)) ⋙q (transitionPoly P).quot.toPrefunctor := by
  refine Prefunctor.ext (fun _ => rfl) ?_
  rintro ⟨⟨cx, ax⟩⟩ ⟨⟨cy, ay⟩⟩ e
  cases e
  · exact (retract_Q P _).trans (fromGrothendieck_ι P _ _)
  · exact retract_fwd P _ _
  · rename_i u
    have h1 : (wFib P).Q.map (cocart P u ay) ≫ evalMap P (Arrow.bwd u ay) = 𝟙 _ :=
      @IsIso.hom_inv_id _ _ _ _ _ (isIso_Q_cocart P u ay)
    have key : transitionPoly.fwd P u ay ≫ (retract P).map (evalMap P (Arrow.bwd u ay)) = 𝟙 _ :=
      (congrArg (· ≫ (retract P).map (evalMap P (Arrow.bwd u ay)))
          (retract_fwd P u ay)).symm.trans
        ((((retract P).map_comp _ _).symm.trans
          (congrArg (retract P).map h1)).trans ((retract P).map_id _))
    exact (Category.id_comp _).symm.trans
      ((congrArg (· ≫ (retract P).map (evalMap P (Arrow.bwd u ay)))
        (transitionPoly.bwd_fwd P u ay).symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (transitionPoly.bwd P u ay ≫ ·) key).trans (Category.comp_id _))))

private theorem toBicolimit_comp_retract : toBicolimit P ⋙ retract P = 𝟭 _ :=
  Quotient.lift_unique' (transitionPoly P).homRel _ _ (by
    rw [← Functor.assoc, show (transitionPoly P).quot ⋙ toBicolimit P = Paths.lift (evalPre P) from
        Polygraph.quot_comp_desc _ _,
      Functor.comp_id]
    refine (Paths.lift_unique _ _ ?_).trans (Paths.lift_unique _ _ rfl).symm
    exact (congrArg (fun ψ => ψ ⋙q (retract P).toPrefunctor)
      (Paths.lift_spec (evalPre P))).trans (retract_evalPre P))

/-- **The transition polygraph presents the bicolimit.** -/
noncomputable def presentsBicolimit :
    Presents (transitionPoly P) (bicolimit (P ⋙ presentedFunctor.{u, u})) :=
  ⟨toBicolimit P,
    (CategoryTheory.Equivalence.mk (toBicolimit P) (retract P)
      (eqToIso (toBicolimit_comp_retract P).symm)
      (eqToIso (retract_comp_toBicolimit P))).isEquivalence_functor⟩

end Transition

end Polygraph

end CategoryTheory
