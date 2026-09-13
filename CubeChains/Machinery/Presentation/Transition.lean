import CubeChains.Machinery.Bicolimit
import CubeChains.Machinery.Presentation.Adjunction
import CubeChains.Machinery.Presentation.Localize

/-!
# Machinery/Presentation/Transition — the bicolimit of a diagram of categories, presented

`grothPoly P` reads the Grothendieck construction on cells — a copy of `P c` for each `c`, a
transition for each arrow of the index, and the unit, cocycle and naturality 2-cells
(`presentsGroth`).  Every arrow of the construction is a transition then a fibre arrow, so formally
inverting the transitions inverts the whole fibrewise-invertible class, and `Localize` turns
`presentsGroth` into a presentation of every bicolimit of the diagram the copies present
(`presentsBicolimit`), nothing asked of the 0-cells.
-/

universe v₁ u₁ v₂ u₂ u

namespace CategoryTheory

/-! ## What the bicolimit inverts is multiplicative

The fibre of an identity is a transport and the fibre of a composite a composite. -/

namespace Grothendieck

instance isMultiplicative_fibrewiseIsos {I : Type u₁} [Category.{v₁} I] {F : I ⥤ Cat.{v₂, u₂}} :
    (fibrewiseIsos F).IsMultiplicative where
  id_mem X := by change IsIso (Hom.fiber (𝟙 X)); rw [id_fiber]; infer_instance
  comp_mem f g hf hg := by
    haveI : IsIso f.fiber := hf
    haveI : IsIso g.fiber := hg
    change IsIso (Hom.fiber (f ≫ g))
    rw [comp_fiber]
    infer_instance

end Grothendieck

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
def grothPoly.push {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) : (P.obj c').V :=
  ((P.map u).pre.obj ⟨a⟩).as

private theorem push_id (c : I) (a : (P.obj c).V) : grothPoly.push P (𝟙 c) a = a :=
  congrArg (fun m : P.obj c ⟶ P.obj c => (m.pre.obj ⟨a⟩).as) (P.map_id c)

private theorem push_comp {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
    grothPoly.push P (u ≫ v) a = grothPoly.push P v (grothPoly.push P u a) :=
  congrArg (fun m : P.obj c₁ ⟶ P.obj c₃ => (m.pre.obj ⟨a⟩).as) (P.map_comp u v)

/-- **1-cells**: a copy's generator, or a transition. -/
private inductive Arrow : Obj P → Obj P → Type u
  | copy {c : I} {a b : (P.obj c).V} (e : (P.obj c).Gen a b) : Arrow ⟨c, a⟩ ⟨c, b⟩
  | fwd {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) : Arrow ⟨c, a⟩ ⟨c', grothPoly.push P u a⟩

/-- A 0-cell of the copy at `c`. -/
private def copyPt (c : I) (x : GenObj (P.obj c).Gen) : GenObj (Arrow P) := ⟨⟨c, x.as⟩⟩

/-- A copy's generator, as a 1-cell. -/
private def copyGen {c : I} {a b : (P.obj c).V} (e : (P.obj c).Gen a b) :
    (⟨⟨c, a⟩⟩ : GenObj (Arrow P)) ⟶ ⟨⟨c, b⟩⟩ := Arrow.copy e

/-- A transition, as a 1-cell. -/
private def fwdGen {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    (⟨⟨c, a⟩⟩ : GenObj (Arrow P)) ⟶ ⟨⟨c', grothPoly.push P u a⟩⟩ := Arrow.fwd u a

/-- A copy's generator pushed along an arrow of the index.  The 0-cells are pinned to `push`: the
inferred spelling is the one `push` unfolds to, and a word must carry the same one as its type. -/
private def pushGen {c c' : I} (u : c ⟶ c') {a b : (P.obj c).V} (e : (P.obj c).Gen a b) :
    (P.obj c').Gen (grothPoly.push P u a) (grothPoly.push P u b) :=
  (P.map u).pre.map (cell e)

/-- The copy at `c`, on generating quivers. -/
private def copyPre (c : I) : GenObj (P.obj c).Gen ⥤q GenObj (Arrow P) where
  obj x := copyPt P c x
  map e := copyGen P e

/-- The 0-cell equality a transition along an identity spans. -/
private theorem copyPt_id (c : I) (a : (P.obj c).V) :
    (⟨⟨c, a⟩⟩ : GenObj (Arrow P)) = ⟨⟨c, grothPoly.push P (𝟙 c) a⟩⟩ :=
  congrArg (fun z => (⟨⟨c, z⟩⟩ : GenObj (Arrow P))) (push_id P c a).symm

/-- …and the one a pair of transitions spans. -/
private theorem copyPt_comp {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
    (⟨⟨c₃, grothPoly.push P (u ≫ v) a⟩⟩ : GenObj (Arrow P))
      = ⟨⟨c₃, grothPoly.push P v (grothPoly.push P u a)⟩⟩ :=
  congrArg (fun z => (⟨⟨c₃, z⟩⟩ : GenObj (Arrow P))) (push_comp P u v a)

/-- **2-cells**: the copies', the unit and cocycle of the transitions, and their naturality against
a copy's generators. -/
private inductive Law : GenObj (Arrow P) → GenObj (Arrow P) → Type u
  | copy {c : I} {x y : GenObj (P.obj c).Gen} (α : (P.obj c).Rel x y) :
      Law (copyPt P c x) (copyPt P c y)
  | unit {c : I} (a : (P.obj c).V) : Law ⟨⟨c, a⟩⟩ ⟨⟨c, grothPoly.push P (𝟙 c) a⟩⟩
  | cocyc {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
      Law ⟨⟨c₁, a⟩⟩ ⟨⟨c₃, grothPoly.push P v (grothPoly.push P u a)⟩⟩
  | nat {c c' : I} (u : c ⟶ c') {a b : (P.obj c).V} (e : (P.obj c).Gen a b) :
      Law ⟨⟨c, a⟩⟩ ⟨⟨c', grothPoly.push P u b⟩⟩

/-- The source word of a 2-cell. -/
private def srcWord : ∀ {x y : GenObj (Arrow P)}, Law P x y → Quiver.Path x y
  | _, _, .copy (c := c) α => (copyPre P c).mapPath ((P.obj c).src α)
  | _, _, .unit a => (fwdGen P (𝟙 _) a).toPath
  | _, _, .cocyc u v a =>
      cellCongr Quiver.Path rfl (copyPt_comp P u v a) (fwdGen P (u ≫ v) a).toPath
  | _, _, .nat (b := b) u e => (copyGen P e).toPath.comp (fwdGen P u b).toPath

/-- The target word of a 2-cell. -/
private def tgtWord : ∀ {x y : GenObj (Arrow P)}, Law P x y → Quiver.Path x y
  | _, _, .copy (c := c) α => (copyPre P c).mapPath ((P.obj c).tgt α)
  | _, _, .unit a => cellCongr Quiver.Path rfl (copyPt_id P _ a) Quiver.Path.nil
  | _, _, .cocyc u v a =>
      (fwdGen P u a).toPath.comp (fwdGen P v (grothPoly.push P u a)).toPath
  | _, _, .nat (a := a) u e =>
      (fwdGen P u a).toPath.comp (copyGen P (pushGen P u e)).toPath

/-- **The Grothendieck construction of `P`, read on cells.** -/
def grothPoly : Polygraph.{u, u, u} where
  V := Obj P
  Gen := Arrow P
  Rel := Law P
  src := srcWord P
  tgt := tgtWord P

/-- **The copy at `c`**, as a morphism of polygraphs. -/
def grothPoly.incl (c : I) : P.obj c ⟶ grothPoly P where
  pre := copyPre P c
  two α := Law.copy α
  src_two _ := rfl
  tgt_two _ := rfl

/-- **A transition**, at a 0-cell of its source copy. -/
def grothPoly.fwd {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    (⟨⟨⟨c, a⟩⟩⟩ : (grothPoly P).presented) ⟶ ⟨⟨⟨c', grothPoly.push P u a⟩⟩⟩ :=
  (grothPoly P).quot.map (fwdGen P u a).toPath

/-! ## The cocartesian arrows the transitions name -/

/-- The object of the Grothendieck construction a 0-cell names. -/
private def grObj (xa : Obj P) : Grothendieck (fib P) where
  base := xa.1
  fiber := (⟨⟨xa.2⟩⟩ : (P.obj xa.1).presented)

private theorem grObj_id (c : I) (a : (P.obj c).V) :
    grObj P ⟨c, a⟩ = grObj P ⟨c, grothPoly.push P (𝟙 c) a⟩ :=
  congrArg (fun z => grObj P ⟨c, z⟩) (push_id P c a).symm

private theorem grObj_comp {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
    grObj P ⟨c₃, grothPoly.push P (u ≫ v) a⟩
      = grObj P ⟨c₃, grothPoly.push P v (grothPoly.push P u a)⟩ :=
  congrArg (fun z => grObj P ⟨c₃, z⟩) (push_comp P u v a)

/-- **The cocartesian arrow a transition names** — `Grothendieck.ιNatTrans`, at a 0-cell. -/
private def cocart {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    grObj P ⟨c, a⟩ ⟶ grObj P ⟨c', grothPoly.push P u a⟩ :=
  ⟨u, 𝟙 _⟩

private theorem wFib_cocart {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    wFib P (cocart P u a) := show IsIso (𝟙 _) from inferInstance

/-- **A transition along an identity is an identity**, read at the 0-cell it names. -/
private theorem cocart_id (c : I) (a : (P.obj c).V) :
    cocart P (𝟙 c) a = eqToHom (grObj_id P c a) :=
  (congr_app (Grothendieck.ιNatTrans_id (F := fib P) c) _).trans (eqToHom_app _ _)

/-- **…and a transition along a composite is the composite of transitions.** -/
private theorem cocart_comp {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
    cocart P (u ≫ v) a ≫ eqToHom (grObj_comp P u v a)
      = cocart P u a ≫ cocart P v (grothPoly.push P u a) := by
  have h := congr_app (Grothendieck.ιNatTrans_comp (F := fib P) u v)
    (⟨⟨a⟩⟩ : (P.obj c₁).presented)
  rw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app] at h
  refine (congrArg (· ≫ eqToHom (grObj_comp P u v a)) h).trans ?_
  refine (Category.assoc _ _ _).trans ((congrArg (cocart P u a ≫ ·)
    (Category.assoc _ _ _)).trans ?_)
  exact congrArg (cocart P u a ≫ ·)
    ((congrArg (cocart P v (grothPoly.push P u a) ≫ ·)
      ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans (Category.comp_id _))

/-- **Every arrow of the Grothendieck construction is a transition then a fibre arrow.** -/
private theorem cocart_comp_ι {X Y : Grothendieck (fib P)} (f : X ⟶ Y) :
    cocart P f.base X.fiber.as.as ≫ (Grothendieck.ι (fib P) Y.base).map f.fiber = f :=
  Grothendieck.ιNatTrans_app_comp_ι_map f

/-! ## The comparison with the Grothendieck construction -/

/-- What a 1-cell names. -/
private def evalMap {xa ya : Obj P} : Arrow P xa ya → (grObj P xa ⟶ grObj P ya)
  | .copy (c := c) e => (Grothendieck.ι (fib P) c).map ((P.obj c).quot.map (cell e).toPath)
  | .fwd u a => cocart P u a

/-- **The cells, read in the Grothendieck construction.** -/
private def evalPre : GenObj (Arrow P) ⥤q Grothendieck (fib P) where
  obj x := grObj P x.as
  map e := evalMap P e

/-- A copy's cells, read in the Grothendieck construction, are that copy's words through its fibre
inclusion — `Paths.lift_unique`, the two prefunctors agreeing on the nose. -/
private theorem lift_copyPre (c : I) :
    Paths.lift (copyPre P c ⋙q evalPre P) = (P.obj c).quot ⋙ Grothendieck.ι (fib P) c :=
  (Paths.lift_unique (copyPre P c ⋙q evalPre P)
    ((P.obj c).quot ⋙ Grothendieck.ι (fib P) c) rfl).symm

/-- A copy's word is read through the copy's fibre inclusion. -/
private theorem eval_copy (c : I) {x y : GenObj (P.obj c).Gen} (w : Quiver.Path x y) :
    (Paths.lift (evalPre P)).map ((copyPre P c).mapPath w)
      = (Grothendieck.ι (fib P) c).map ((P.obj c).quot.map w) :=
  (Paths.lift_mapPath (copyPre P c) (evalPre P) w).trans
    ((Functor.congr_hom (lift_copyPre P c) w).trans
      ((Category.id_comp _).trans (Category.comp_id _)))

/-- **The 2-cells hold in the Grothendieck construction.** -/
private theorem evalSound {x y : GenObj (Arrow P)} (α : Law P x y) :
    (Paths.lift (evalPre P)).map (srcWord P α)
      = (Paths.lift (evalPre P)).map (tgtWord P α) := by
  cases α with
  | copy α =>
      rw [srcWord, tgtWord]
      exact (eval_copy P _ _).trans
        ((congrArg (Grothendieck.ι (fib P) _).map ((P.obj _).quot_src_tgt α)).trans
          (eval_copy P _ _).symm)
  | unit a =>
      rw [srcWord, tgtWord, Paths.map_cellCongr, Paths.lift_toPath, Paths.lift_nil]
      exact (cocart_id P _ a).trans (Category.id_comp _).symm
  | cocyc u v a =>
      rw [srcWord, tgtWord, Paths.map_cellCongr, Paths.lift_toPath, Paths.lift_map_comp,
        Paths.lift_toPath, Paths.lift_toPath]
      exact cocart_comp P u v a
  | nat u e =>
      rw [srcWord, tgtWord, Paths.lift_map_comp, Paths.lift_map_comp, Paths.lift_toPath,
        Paths.lift_toPath, Paths.lift_toPath, Paths.lift_toPath]
      exact (Grothendieck.ιNatTrans (F := fib P) u).naturality
        ((P.obj _).quot.map (cell e).toPath)

/-- **The comparison**: a word of `grothPoly P`, read in the Grothendieck construction. -/
private def toGroth : (grothPoly P).presented ⥤ Grothendieck (fib P) :=
  Polygraph.desc (P := grothPoly P) (evalPre P) (evalSound P)

/-- A copy, read by the comparison, is that copy's fibre inclusion. -/
private theorem incl_comp_toGroth (c : I) :
    (grothPoly.incl P c).functor ⋙ toGroth P = Grothendieck.ι (fib P) c :=
  Quotient.lift_unique' (P.obj c).homRel _ _
    (Functor.ext (fun _ => rfl) fun _ _ w =>
      (eval_copy P c w).trans ((Category.comp_id _).symm.trans (Category.id_comp _).symm))

private theorem incl_toGroth_map (c : I) {Y Z : (P.obj c).presented} (g : Y ⟶ Z) :
    (toGroth P).map ((grothPoly.incl P c).functor.map g) = (Grothendieck.ι (fib P) c).map g :=
  (Functor.congr_hom (incl_comp_toGroth P c) g).trans
    ((Category.id_comp _).trans (Category.comp_id _))

/-- A transition, read by the comparison — a word of `grothPoly P` is read by `Paths.lift` on the
nose, so there is nothing to unfold. -/
private theorem toGroth_fwd {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    (toGroth P).map (grothPoly.fwd P u a) = cocart P u a :=
  Paths.lift_toPath (evalPre P) (fwdGen P u a)

/-! ## The transitions as the Grothendieck construction's comparison data -/

/-- The transport a transition along an identity carries. -/
private theorem quotPt_id (c : I) (a : (P.obj c).V) :
    (⟨⟨⟨c, a⟩⟩⟩ : (grothPoly P).presented) = ⟨⟨⟨c, grothPoly.push P (𝟙 c) a⟩⟩⟩ :=
  congrArg (fun z => (⟨z⟩ : (grothPoly P).presented)) (copyPt_id P c a)

/-- …and the one a pair of transitions carries. -/
private theorem quotPt_comp {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
    (⟨⟨⟨c₃, grothPoly.push P (u ≫ v) a⟩⟩⟩ : (grothPoly P).presented)
      = ⟨⟨⟨c₃, grothPoly.push P v (grothPoly.push P u a)⟩⟩⟩ :=
  congrArg (fun z => (⟨z⟩ : (grothPoly P).presented)) (copyPt_comp P u v a)

/-- The unit 2-cell, read in the presented category. -/
private theorem fwd_unit (c : I) (a : (P.obj c).V) :
    grothPoly.fwd P (𝟙 c) a = eqToHom (quotPt_id P c a) :=
  ((grothPoly P).quot_src_tgt (Law.unit a)).trans
    (((grothPoly P).quot_map_cellCongr (copyPt_id P c a) Quiver.Path.nil).trans
      ((congrArg (· ≫ eqToHom (quotPt_id P c a)) ((grothPoly P).quot.map_id _)).trans
        (Category.id_comp _)))

/-- …and the cocycle. -/
private theorem fwd_cocyc {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (a : (P.obj c₁).V) :
    grothPoly.fwd P (u ≫ v) a ≫ eqToHom (quotPt_comp P u v a)
      = grothPoly.fwd P u a ≫ grothPoly.fwd P v (grothPoly.push P u a) :=
  ((grothPoly P).quot_map_cellCongr (copyPt_comp P u v a)
      (fwdGen P (u ≫ v) a).toPath).symm.trans
    (((grothPoly P).quot_src_tgt (Law.cocyc u v a)).trans
      ((grothPoly P).quot.map_comp _ _))

/-- **The transitions, as a 2-cell between the copies** — the `hom` datum of the Grothendieck
construction, read on cells; naturality is the `nat` 2-cell. -/
private def transNat {c c' : I} (u : c ⟶ c') :
    (grothPoly.incl P c).functor ⟶ (P.map u).functor ⋙ (grothPoly.incl P c').functor :=
  natTransOfGen _ _ (fun x => grothPoly.fwd P u x.as) fun {_ _} e =>
    ((grothPoly P).quot.map_comp _ _).symm.trans
      (((grothPoly P).quot_src_tgt (Law.nat u e)).trans
        ((grothPoly P).quot.map_comp _ _))

private theorem incl_id_eq (c : I) :
    (grothPoly.incl P c).functor
      = ((fib P).map (𝟙 c)).toFunctor ⋙ (grothPoly.incl P c).functor := by
  simp only [Functor.map_id]
  rfl

private theorem incl_comp_eq {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) :
    ((fib P).map u).toFunctor ⋙ ((fib P).map v).toFunctor ⋙ (grothPoly.incl P c₃).functor
      = ((fib P).map (u ≫ v)).toFunctor ⋙ (grothPoly.incl P c₃).functor := by
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
  refine Eq.trans ?_ (congrArg (fun z => grothPoly.fwd P u X.as.as
    ≫ grothPoly.fwd P v (grothPoly.push P u X.as.as) ≫ z)
    (eqToHom_app (incl_comp_eq P u v) X).symm)
  refine (Category.comp_id _).symm.trans ?_
  refine (congrArg (grothPoly.fwd P (u ≫ v) X.as.as ≫ ·)
    ((eqToHom_refl _ ((quotPt_comp P u v X.as.as).trans
        (Functor.congr_obj (incl_comp_eq P u v) X))).symm.trans
      (eqToHom_trans (quotPt_comp P u v X.as.as)
        (Functor.congr_obj (incl_comp_eq P u v) X)).symm)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (congrArg (· ≫ _) (fwd_cocyc P u v X.as.as)).trans (Category.assoc _ _ _)

/-- **The retraction**: the Grothendieck construction's universal property, at the copies and their
transitions. -/
private def fromGroth : Grothendieck (fib P) ⥤ (grothPoly P).presented :=
  Grothendieck.functorFrom (fun c => (grothPoly.incl P c).functor) (fun u => transNat P u)
    (transNat_id P) fun _ _ _ u v => transNat_comp P u v

private theorem fromGroth_map {X Y : Grothendieck (fib P)} (f : X ⟶ Y) :
    (fromGroth P).map f
      = grothPoly.fwd P f.base X.fiber.as.as
        ≫ (grothPoly.incl P Y.base).functor.map f.fiber := rfl

/-- A copy's arrow, read by the retraction. -/
private theorem fromGroth_ι (c : I) {Y Z : (P.obj c).presented} (g : Y ⟶ Z) :
    (fromGroth P).map ((Grothendieck.ι (fib P) c).map g)
      = (grothPoly.incl P c).functor.map g := by
  refine (fromGroth_map P _).trans ?_
  refine (congrArg (· ≫ (grothPoly.incl P c).functor.map
    (((Grothendieck.ι (fib P) c).map g).fiber)) (fwd_unit P c Y.as.as)).trans ?_
  refine (congrArg (eqToHom (quotPt_id P c Y.as.as) ≫ ·)
    ((grothPoly.incl P c).functor.map_comp _ g)).trans ?_
  refine (congrArg (fun z => eqToHom (quotPt_id P c Y.as.as) ≫ z
    ≫ (grothPoly.incl P c).functor.map g)
    (eqToHom_map (grothPoly.incl P c).functor _)).trans ?_
  exact eqToHom_comp_cancel _ _ _

/-- …and a transition. -/
private theorem fromGroth_cocart {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    (fromGroth P).map (cocart P u a) = grothPoly.fwd P u a := by
  refine (fromGroth_map P _).trans ?_
  refine (congrArg (grothPoly.fwd P u a ≫ ·)
    ((grothPoly.incl P c').functor.map_id _)).trans ?_
  exact Category.comp_id _

/-- **The comparison undoes the retraction** — the Grothendieck construction is read cell by cell
back onto itself. -/
private theorem fromGroth_comp_toGroth : fromGroth P ⋙ toGroth P = 𝟭 _ :=
  Functor.ext (fun _ => rfl) fun X Y f => by
    refine Eq.trans ?_ ((Category.comp_id _).symm.trans (Category.id_comp _).symm)
    refine (congrArg (toGroth P).map (fromGroth_map P f)).trans ?_
    refine ((toGroth P).map_comp _ _).trans ?_
    refine (congrArg (· ≫ (toGroth P).map
      ((grothPoly.incl P Y.base).functor.map f.fiber))
      (toGroth_fwd P f.base X.fiber.as.as)).trans ?_
    refine (congrArg (cocart P f.base X.fiber.as.as ≫ ·)
      (incl_toGroth_map P Y.base f.fiber)).trans ?_
    exact cocart_comp_ι P f

/-- **The cells are read back to themselves** — the two generator cases. -/
private theorem fromGroth_evalPre :
    evalPre P ⋙q (fromGroth P).toPrefunctor
      = Paths.of (GenObj (Arrow P)) ⋙q (grothPoly P).quot.toPrefunctor := by
  refine Prefunctor.ext (fun _ => rfl) ?_
  rintro ⟨⟨cx, ax⟩⟩ ⟨⟨cy, ay⟩⟩ e
  cases e
  · exact fromGroth_ι P _ _
  · exact fromGroth_cocart P _ _

private theorem toGroth_comp_fromGroth : toGroth P ⋙ fromGroth P = 𝟭 _ :=
  Quotient.lift_unique' (grothPoly P).homRel _ _ (by
    rw [← Functor.assoc, show (grothPoly P).quot ⋙ toGroth P = Paths.lift (evalPre P) from
        Polygraph.quot_comp_desc _ _,
      Functor.comp_id]
    refine (Paths.lift_unique _ _ ?_).trans (Paths.lift_unique _ _ rfl).symm
    exact (congrArg (fun ψ => ψ ⋙q (fromGroth P).toPrefunctor)
      (Paths.lift_spec (evalPre P))).trans (fromGroth_evalPre P))

/-- **The copies and their transitions present the Grothendieck construction of the diagram the
copies present.** -/
noncomputable def presentsGroth :
    Presents (grothPoly P) (Grothendieck (P ⋙ presentedFunctor.{u, u})) :=
  ⟨toGroth P,
    (CategoryTheory.Equivalence.mk (toGroth P) (fromGroth P)
      (eqToIso (toGroth_comp_fromGroth P).symm)
      (eqToIso (fromGroth_comp_toGroth P))).isEquivalence_functor⟩

/-! ## Inverting the transitions inverts every fibrewise isomorphism -/

/-- Which 1-cells are transitions. -/
def grothPoly.isFwd : ∀ {xa ya : (grothPoly P).V}, (grothPoly P).Gen xa ya → Prop
  | _, _, .copy _ => False
  | _, _, .fwd _ _ => True

/-- **The Grothendieck construction with the transitions formally inverted.** -/
def transitionPoly : Polygraph.{u, u, u} := invPoly (grothPoly P) (grothPoly.isFwd P)

/-- The class the transitions generate. -/
private abbrev fwdClosure : MorphismProperty (Grothendieck (fib P)) :=
  ((presentsGroth P).pickedArrows (grothPoly.isFwd P)).multiplicativeClosure

private theorem arrow_fwd {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    (presentsGroth P).arrow (cell (Arrow.fwd u a)) = cocart P u a :=
  Paths.lift_toPath (evalPre P) (fwdGen P u a)

private theorem fwdClosure_cocart {c c' : I} (u : c ⟶ c') (a : (P.obj c).V) :
    fwdClosure P (cocart P u a) :=
  MorphismProperty.le_multiplicativeClosure _ _ (by
    rw [← arrow_fwd P u a]
    exact Presents.Picked.mk (p := presentsGroth P) (S := grothPoly.isFwd P)
      (Arrow.fwd u a) trivial)

/-- **A transition is a fibrewise identity**, so the transitions generate no more than the class the
bicolimit inverts. -/
private theorem fwdClosure_le : fwdClosure P ≤ wFib P := by
  refine (MorphismProperty.multiplicativeClosure_le_iff _ _).mpr ?_
  rintro X Y f ⟨e, he⟩
  cases e with
  | copy e => exact False.elim he
  | fwd u a => rw [arrow_fwd P u a]; exact wFib_cocart P u a

/-- **…and no less**: every arrow is a transition then a fibre arrow (`cocart_comp_ι`), and a
fibrewise isomorphism's fibre arrow is already invertible. -/
private theorem wFib_inverted : (wFib P).IsInvertedBy (fwdClosure P).Q := by
  intro X Y f hf
  haveI : IsIso f.fiber := hf
  haveI hc : IsIso ((fwdClosure P).Q.map (cocart P f.base X.fiber.as.as)) :=
    Localization.inverts _ _ _ (fwdClosure_cocart P f.base X.fiber.as.as)
  haveI : IsIso ((Grothendieck.ι (fib P) Y.base).map f.fiber) := Functor.map_isIso _ _
  haveI hi : IsIso ((fwdClosure P).Q.map ((Grothendieck.ι (fib P) Y.base).map f.fiber)) :=
    Functor.map_isIso _ _
  have h : (fwdClosure P).Q.map f
      = (fwdClosure P).Q.map (cocart P f.base X.fiber.as.as)
        ≫ (fwdClosure P).Q.map ((Grothendieck.ι (fib P) Y.base).map f.fiber) :=
    (congrArg (fwdClosure P).Q.map (cocart_comp_ι P f)).symm.trans
      ((fwdClosure P).Q.map_comp _ _)
  rw [h]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hc hi

/-- **The transition polygraph presents the chosen model of the bicolimit.** -/
noncomputable def presentsBicolimitModel :
    Presents (transitionPoly P) (bicolimit (P ⋙ presentedFunctor.{u, u})) :=
  (presentsGroth P).presentsLocalizationOfLe (grothPoly.isFwd P) (fwdClosure_le P)
    (wFib_inverted P)

/-- **The transition polygraph presents every bicolimit** of the diagram the copies present — the
model is one (`isBicolimit_bicolimitCocone`), and the vertices of two are equivalent. -/
noncomputable def presentsBicolimit {X : Type u} [Category.{u} X]
    {t : PseudoCocone (P ⋙ presentedFunctor.{u, u}) X} (ht : IsBicolimit t) :
    Presents (transitionPoly P) X :=
  (presentsBicolimitModel P).transport
    ((isBicolimit_bicolimitCocone (P ⋙ presentedFunctor.{u, u})).equiv ht)

end Transition

end Polygraph

end CategoryTheory
