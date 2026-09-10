import CubeChains.Machinery.StrictInverse
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Machinery/Bicolimit — the bicolimit of a diagram of categories

A `PseudoCocone F E` has a leg out of each fibre of `F : I ⥤ Cat` and an *invertible* transition
for each arrow of the index, strictly coherent; the transitions run in
`Grothendieck.functorFrom`'s direction, so a pseudo-cocone is exactly that construction's data with
`hom` inverted.  Pseudo-cocones with a fixed vertex form a category, whose arrows are the
modifications, and `IsBicolimit t` says precomposition with `t`'s legs
`(D ⥤ E) ⥤ PseudoCocone F E` is an equivalence for every `E` — the universal property.  `bicolimit
F`, the Grothendieck construction with the fibrewise isomorphisms inverted, is a model.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅

namespace CategoryTheory

/-! ## Transporting a functor along whiskering

`eqToHom` between functors survives whiskering; `subst` reduces both sides to an identity, which is
the only route when the objects are `Cat`-coerced. -/

theorem Functor.whiskerRight_eqToHom {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E] {A B : C ⥤ D} (h : A = B) (G : D ⥤ E) :
    Functor.whiskerRight (eqToHom h) G = eqToHom (congrArg (· ⋙ G) h) := by
  subst h; simp

/-- Whiskering on the two sides of a composite commutes, strictly. -/
theorem Functor.whiskerRight_whiskerLeft {B : Type*} [Category B] {C : Type*} [Category C]
    {D : Type*} [Category D] {E : Type*} [Category E] (A : B ⥤ C) {G H : C ⥤ D} (β : G ⟶ H)
    (K : D ⥤ E) : Functor.whiskerRight (Functor.whiskerLeft A β) K
      = Functor.whiskerLeft A (Functor.whiskerRight β K) := rfl

/-! ## Pseudo-cocones -/

variable {I : Type u₁} [Category.{v₁} I] {F : I ⥤ Cat.{v₂, u₂}}

/-- A cocone on a diagram of categories whose legs commute with the index only up to a coherent
isomorphism: `Grothendieck.functorFrom`'s data, with the transition inverted. -/
structure PseudoCocone (F : I ⥤ Cat.{v₂, u₂}) (E : Type u₃) [Category.{v₃} E] where
  /-- The leg out of the fibre at `c`. -/
  ι : ∀ c : I, F.obj c ⥤ E
  /-- The transition an arrow of the index carries the legs along. -/
  κ : ∀ {c c' : I} (u : c ⟶ c'), ι c ≅ (F.map u).toFunctor ⋙ ι c'
  κ_id : ∀ c : I, (κ (𝟙 c)).hom = eqToHom (by simp only [Functor.map_id]; rfl)
  κ_comp : ∀ {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃), (κ (u ≫ v)).hom
    = (κ u).hom ≫ Functor.whiskerLeft (F.map u).toFunctor (κ v).hom
      ≫ eqToHom (by simp only [Functor.map_comp]; rfl)

namespace PseudoCocone

variable {E : Type u₃} [Category.{v₃} E]

/-- A modification: a transformation of legs commuting with the transitions. -/
@[ext]
structure Hom (s t : PseudoCocone F E) where
  /-- The transformation of legs. -/
  app : ∀ c : I, s.ι c ⟶ t.ι c
  naturality : ∀ {c c' : I} (u : c ⟶ c'),
    (s.κ u).hom ≫ Functor.whiskerLeft (F.map u).toFunctor (app c') = app c ≫ (t.κ u).hom

instance : Category (PseudoCocone F E) where
  Hom := Hom
  id s := ⟨fun _ => 𝟙 _, by simp⟩
  comp m n := ⟨fun c => m.app c ≫ n.app c, by
    intro c c' u
    rw [Functor.whiskerLeft_comp, ← Category.assoc, m.naturality u, Category.assoc,
      n.naturality u, Category.assoc]⟩

@[simp] theorem id_app (s : PseudoCocone F E) (c : I) : Hom.app (𝟙 s) c = 𝟙 (s.ι c) := rfl

@[simp] theorem comp_app {s t w : PseudoCocone F E} (m : s ⟶ t) (n : t ⟶ w) (c : I) :
    Hom.app (m ≫ n) c = m.app c ≫ n.app c := rfl

@[ext] theorem hom_ext {s t : PseudoCocone F E} {m n : s ⟶ t} (h : ∀ c : I, m.app c = n.app c) :
    m = n := Hom.ext (funext h)

/-- A family of leg isomorphisms commuting with the transitions is an isomorphism of
pseudo-cocones. -/
@[simps]
def isoMk {s t : PseudoCocone F E} (e : ∀ c : I, s.ι c ≅ t.ι c)
    (h : ∀ {c c' : I} (u : c ⟶ c'),
      (s.κ u).hom ≫ Functor.whiskerLeft (F.map u).toFunctor (e c').hom
        = (e c).hom ≫ (t.κ u).hom) : s ≅ t where
  hom := ⟨fun c => (e c).hom, h⟩
  inv := ⟨fun c => (e c).inv, by
    intro c c' u
    rw [show Functor.whiskerLeft (F.map u).toFunctor (e c').inv
        = (Functor.isoWhiskerLeft (F.map u).toFunctor (e c')).inv from rfl,
      Iso.comp_inv_eq, Category.assoc, Functor.isoWhiskerLeft_hom, h u, Iso.inv_hom_id_assoc]⟩
  hom_inv_id := by ext c; simp
  inv_hom_id := by ext c; simp

/-- **Precomposition with the legs**: the pseudo-cocone a functor out of the vertex induces. -/
@[simps]
def precompose {D : Type u₄} [Category.{v₄} D] (t : PseudoCocone F D) (E : Type u₃)
    [Category.{v₃} E] : (D ⥤ E) ⥤ PseudoCocone F E where
  obj G :=
    { ι := fun c => t.ι c ⋙ G
      κ := fun u => Functor.isoWhiskerRight (t.κ u) G
      κ_id := fun c => by
        rw [Functor.isoWhiskerRight_hom, t.κ_id c, Functor.whiskerRight_eqToHom]; rfl
      κ_comp := fun u v => by
        rw [Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_hom,
          t.κ_comp u v, Functor.whiskerRight_comp, Functor.whiskerRight_comp,
          Functor.whiskerRight_eqToHom, Functor.whiskerRight_whiskerLeft]
        rfl }
  map α := ⟨fun c => Functor.whiskerLeft (t.ι c) α, by
    intro c c' u
    exact NatTrans.ext (funext fun x => α.naturality ((t.κ u).hom.app x))⟩

section Precompose

variable {D : Type u₄} [Category.{v₄} D] {D' : Type u₅} [Category.{v₅} D']

theorem precompose_obj_id (t : PseudoCocone F D) : (t.precompose D).obj (𝟭 D) = t := rfl

theorem precompose_obj_comp (t : PseudoCocone F D) (G : D ⥤ D') (H : D' ⥤ E) :
    (t.precompose E).obj (G ⋙ H) = (((t.precompose D').obj G).precompose E).obj H := rfl

/-- …and in the pseudo-cocone: a modification whiskers. -/
def mapPrecompose {s t : PseudoCocone F D} (m : s ⟶ t) (H : D ⥤ E) :
    (s.precompose E).obj H ⟶ (t.precompose E).obj H where
  app c := Functor.whiskerRight (m.app c) H
  naturality u :=
    (Functor.whiskerRight_comp _ _ H).symm.trans
      ((congrArg (Functor.whiskerRight · H) (m.naturality u)).trans
        (Functor.whiskerRight_comp _ _ H))

/-- The leg isomorphism an isomorphism of pseudo-cocones carries. -/
@[simps]
def isoApp {s t : PseudoCocone F E} (e : s ≅ t) (c : I) : s.ι c ≅ t.ι c where
  hom := e.hom.app c
  inv := e.inv.app c
  hom_inv_id := (comp_app e.hom e.inv c).symm.trans (congrArg (Hom.app · c) e.hom_inv_id)
  inv_hom_id := (comp_app e.inv e.hom c).symm.trans (congrArg (Hom.app · c) e.inv_hom_id)

/-- An isomorphism of pseudo-cocones survives precomposition. -/
@[simps]
def precomposeIso {s t : PseudoCocone F D} (e : s ≅ t) (H : D ⥤ E) :
    (s.precompose E).obj H ≅ (t.precompose E).obj H where
  hom := mapPrecompose e.hom H
  inv := mapPrecompose e.inv H
  hom_inv_id := by
    refine hom_ext fun c => ?_
    exact (Functor.whiskerRight_comp _ _ H).symm.trans
      ((congrArg (Functor.whiskerRight · H) (isoApp e c).hom_inv_id).trans
        (Functor.whiskerRight_id' H))
  inv_hom_id := by
    refine hom_ext fun c => ?_
    exact (Functor.whiskerRight_comp _ _ H).symm.trans
      ((congrArg (Functor.whiskerRight · H) (isoApp e c).inv_hom_id).trans
        (Functor.whiskerRight_id' H))

end Precompose

end PseudoCocone

/-! ## The transitions of the Grothendieck construction -/

namespace Grothendieck

/-- **A transition along an identity is a transport.** -/
theorem ιNatTrans_id (c : I) :
    ιNatTrans (F := F) (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl) := by
  refine NatTrans.ext (funext fun d => ?_)
  rw [eqToHom_app]
  refine Grothendieck.ext _ _ ?_ ?_
  · rw [Grothendieck.base_eqToHom]
    exact (eqToHom_refl _ _).symm
  · rw [Grothendieck.fiber_eqToHom]
    exact (Category.comp_id _).trans rfl

/-- The 0-cell a pair of transitions spans. -/
private theorem ιObj_comp {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (d : F.obj c₁) :
    (⟨c₃, (F.map v).toFunctor.obj ((F.map u).toFunctor.obj d)⟩ : Grothendieck F)
      = ⟨c₃, (F.map (u ≫ v)).toFunctor.obj d⟩ :=
  congrArg (fun z => (⟨c₃, z⟩ : Grothendieck F))
    (by simp only [Functor.map_comp]; rfl)

private theorem ιNatTrans_comp_app {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) (d : F.obj c₁) :
    (ιNatTrans (F := F) (u ≫ v)).app d
      = (ιNatTrans u).app d ≫ (ιNatTrans v).app ((F.map u).toFunctor.obj d)
        ≫ eqToHom (ιObj_comp u v d) := by
  have hb : (eqToHom (ιObj_comp (F := F) u v d)).base = 𝟙 c₃ :=
    (Grothendieck.base_eqToHom _).trans (eqToHom_refl _ _)
  refine Grothendieck.ext _ _ ?_ ?_
  · exact ((congrArg (fun z : c₃ ⟶ c₃ => u ≫ v ≫ z) hb).trans
      (congrArg (u ≫ ·) (Category.comp_id v))).symm
  · rw [Grothendieck.comp_fiber, Grothendieck.comp_fiber, Grothendieck.fiber_eqToHom,
      show ((ιNatTrans (F := F) u).app d).fiber = 𝟙 _ from rfl,
      show ((ιNatTrans (F := F) v).app ((F.map u).toFunctor.obj d)).fiber = 𝟙 _ from rfl,
      show ((ιNatTrans (F := F) (u ≫ v)).app d).fiber = 𝟙 _ from rfl]
    -- `erw`: the fibre lives at `↥(Cat.of …)`, so these lemmas' objects are `rfl`-equal to the
    -- goal's but not syntactically equal, and `rw` will not unfold the bundled coercion
    erw [Functor.map_id, Functor.map_id]
    erw [Category.id_comp]
    erw [Category.id_comp]
    refine (Category.comp_id _).trans ?_
    exact ((congrArg (eqToHom _ ≫ ·) (eqToHom_trans _ _)).trans (eqToHom_trans _ _)).symm

/-- **…and a transition along a composite is the composite of transitions.** -/
theorem ιNatTrans_comp {c₁ c₂ c₃ : I} (u : c₁ ⟶ c₂) (v : c₂ ⟶ c₃) :
    ιNatTrans (F := F) (u ≫ v) = ιNatTrans u
      ≫ Functor.whiskerLeft (F.map u).toFunctor (ιNatTrans v)
      ≫ eqToHom (by simp only [Functor.map_comp]; rfl) := by
  refine NatTrans.ext (funext fun d => ?_)
  rw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app]
  exact ιNatTrans_comp_app u v d

/-- **Every arrow is a transition followed by a fibre arrow.** -/
theorem ιNatTrans_app_comp_ι_map {X Y : Grothendieck F} (f : X ⟶ Y) :
    (ιNatTrans f.base).app X.fiber ≫ (ι F Y.base).map f.fiber = f :=
  Grothendieck.ext _ _ ((Category.comp_id _).trans rfl)
    ((eqToHom_map_id_chain _ _ _ _ _ rfl).trans (Category.id_comp _))

/-- **A transformation out of `Grothendieck F` is its legs and their compatibility with the
transitions** — every arrow factors as a transition then a fibre arrow. -/
@[simps]
def natTransFrom {E : Type u₃} [Category.{v₃} E] {G H : Grothendieck F ⥤ E}
    (φ : ∀ c : I, ι F c ⋙ G ⟶ ι F c ⋙ H)
    (hφ : ∀ {c c' : I} (u : c ⟶ c'),
      Functor.whiskerRight (ιNatTrans u) G ≫ Functor.whiskerLeft (F.map u).toFunctor (φ c')
        = φ c ≫ Functor.whiskerRight (ιNatTrans u) H) :
    G ⟶ H where
  app X := (φ X.base).app X.fiber
  naturality {X Y} f := by
    have hfac : (ιNatTrans (F := F) f.base).app X.fiber ≫ (ι F Y.base).map f.fiber = f :=
      ιNatTrans_app_comp_ι_map f
    have hu : G.map ((ιNatTrans (F := F) f.base).app X.fiber)
          ≫ (φ Y.base).app ((F.map f.base).toFunctor.obj X.fiber)
        = (φ X.base).app X.fiber ≫ H.map ((ιNatTrans (F := F) f.base).app X.fiber) :=
      congr_app (hφ f.base) X.fiber
    have hn : G.map ((ι F Y.base).map f.fiber) ≫ (φ Y.base).app Y.fiber
        = (φ Y.base).app ((F.map f.base).toFunctor.obj X.fiber)
          ≫ H.map ((ι F Y.base).map f.fiber) := (φ Y.base).naturality f.fiber
    have hG : G.map f = G.map ((ιNatTrans (F := F) f.base).app X.fiber)
        ≫ G.map ((ι F Y.base).map f.fiber) := (congrArg G.map hfac.symm).trans (G.map_comp _ _)
    have hH : H.map f = H.map ((ιNatTrans (F := F) f.base).app X.fiber)
        ≫ H.map ((ι F Y.base).map f.fiber) := (congrArg H.map hfac.symm).trans (H.map_comp _ _)
    refine (congrArg (· ≫ (φ Y.base).app Y.fiber) hG).trans
      (Eq.trans ?_ (congrArg ((φ X.base).app X.fiber ≫ ·) hH.symm))
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (G.map ((ιNatTrans (F := F) f.base).app X.fiber) ≫ ·) hn).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ H.map ((ι F Y.base).map f.fiber)) hu).trans ?_
    exact Category.assoc _ _ _

/-- **What the bicolimit inverts**: the arrows whose fibre component is invertible. -/
def fibrewiseIsos (F : I ⥤ Cat.{v₂, u₂}) : MorphismProperty (Grothendieck F) :=
  fun _ _ f => IsIso f.fiber

end Grothendieck

/-- **The bicolimit of a diagram of categories**: `Grothendieck F` with the fibrewise isomorphisms
inverted.  `Limits.colimit` glues the legs by an equality, so only a cocone commuting on the nose
descends; here each arrow of the index keeps an invertible transition of its own, and a cocone
commuting up to coherent isomorphism descends instead. -/
abbrev bicolimit (F : I ⥤ Cat.{v₂, u₂}) := (Grothendieck.fibrewiseIsos F).Localization

instance isIso_Q_ιNatTrans {c c' : I} (u : c ⟶ c') :
    IsIso (Functor.whiskerRight (Grothendieck.ιNatTrans u)
      (Grothendieck.fibrewiseIsos F).Q) := by
  haveI : ∀ d : F.obj c, IsIso ((Functor.whiskerRight (Grothendieck.ιNatTrans u)
      (Grothendieck.fibrewiseIsos F).Q).app d) := fun d =>
    Localization.inverts (Grothendieck.fibrewiseIsos F).Q (Grothendieck.fibrewiseIsos F)
      ((Grothendieck.ιNatTrans u).app d) (show IsIso (𝟙 _) from inferInstance)
  exact NatIso.isIso_of_isIso_app _

/-- **The bicolimit's own pseudo-cocone**: the fibre inclusions, with the transitions, invertible
because a transition is a fibrewise identity. -/
noncomputable def bicolimitCocone (F : I ⥤ Cat.{v₂, u₂}) : PseudoCocone F (bicolimit F) where
  ι c := Grothendieck.ι F c ⋙ (Grothendieck.fibrewiseIsos F).Q
  κ u := @asIso _ _ _ _ _ (isIso_Q_ιNatTrans u)
  κ_id c := by
    rw [asIso_hom, Grothendieck.ιNatTrans_id, Functor.whiskerRight_eqToHom]; rfl
  κ_comp u v := by
    rw [asIso_hom, asIso_hom, asIso_hom, Grothendieck.ιNatTrans_comp,
      Functor.whiskerRight_comp, Functor.whiskerRight_comp, Functor.whiskerRight_eqToHom,
      Functor.whiskerRight_whiskerLeft]
    rfl

/-! ## The universal property -/

/-- **The universal property of the bicolimit**: precomposition with the legs is an equivalence onto
the pseudo-cocones.  Equality of the legs is too strong — `isoComparison_not_enough` has a diagram
whose strict colimit admits the comparison isomorphism and not the equality.  As with
`Limits.IsColimit`, the target ranges over one ambient pair of universes, the vertex's own. -/
def IsBicolimit {D : Type u₃} [Category.{v₃} D] (t : PseudoCocone F D) : Prop :=
  ∀ (E : Type u₃) [Category.{v₃} E], (t.precompose E).IsEquivalence

namespace PseudoCocone

variable {E : Type u₃} [Category.{v₃} E]

/-- A pseudo-cocone read on the Grothendieck construction: its transitions are already coherent. -/
def functorFrom (s : PseudoCocone F E) : Grothendieck F ⥤ E :=
  Grothendieck.functorFrom s.ι (fun u => (s.κ u).hom) s.κ_id fun _ _ _ u v => s.κ_comp u v

/-- **The Grothendieck comparison reads a leg back to that leg** — `Grothendieck.ιCompFunctorFrom`
at a pseudo-cocone's own data. -/
def ιCompFunctorFrom (s : PseudoCocone F E) (c : I) :
    Grothendieck.ι F c ⋙ s.functorFrom ≅ s.ι c :=
  Grothendieck.ιCompFunctorFrom s.ι (fun u => (s.κ u).hom) s.κ_id
    (fun _ _ _ u v => s.κ_comp u v) c

theorem functorFrom_inverts (s : PseudoCocone F E) :
    (Grothendieck.fibrewiseIsos F).IsInvertedBy s.functorFrom := by
  rintro X Y f hf
  -- the fibre's `Category` instance arrives through `Cat`'s bundling, so the local `IsIso` is
  -- passed by hand rather than found by instance search
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom ((s.κ f.base).app X.fiber))
    (Iso.isIso_hom ((s.ι Y.base).mapIso (@asIso _ _ _ _ f.fiber hf)))

/-- **The functor out of the bicolimit a pseudo-cocone descends to.** -/
noncomputable def desc (s : PseudoCocone F E) : bicolimit F ⥤ E :=
  Localization.Construction.lift s.functorFrom s.functorFrom_inverts

theorem Q_comp_desc (s : PseudoCocone F E) :
    (Grothendieck.fibrewiseIsos F).Q ⋙ s.desc = s.functorFrom :=
  Localization.Construction.fac _ _

theorem descLeg_eq (s : PseudoCocone F E) (c : I) :
    (bicolimitCocone F).ι c ⋙ s.desc = Grothendieck.ι F c ⋙ s.functorFrom :=
  congrArg (fun Φ => Grothendieck.ι F c ⋙ Φ) s.Q_comp_desc

/-- **The descent reads a leg back to that leg** — `Grothendieck.ιCompFunctorFrom`, after the
localization's on-the-nose factorisation. -/
noncomputable def descLeg (s : PseudoCocone F E) (c : I) :
    (bicolimitCocone F).ι c ⋙ s.desc ≅ s.ι c :=
  eqToIso (s.descLeg_eq c) ≪≫ s.ιCompFunctorFrom c

theorem descLeg_hom_app (s : PseudoCocone F E) (c : I) (x : F.obj c) :
    (s.descLeg c).hom.app x = 𝟙 _ :=
  (congrArg (· ≫ 𝟙 _) (eqToHom_app (s.descLeg_eq c) x)).trans
    ((congrArg (· ≫ 𝟙 _) (eqToHom_refl _ _)).trans (Category.id_comp _))

theorem desc_map_Q (s : PseudoCocone F E) {X Y : Grothendieck F} (g : X ⟶ Y) :
    s.desc.map ((Grothendieck.fibrewiseIsos F).Q.map g) = s.functorFrom.map g :=
  (Functor.congr_hom s.Q_comp_desc g).trans ((Category.id_comp _).trans (Category.comp_id _))

/-- **A pseudo-cocone is its own descent, read back through the legs.** -/
noncomputable def precomposeDescIso (s : PseudoCocone F E) :
    ((bicolimitCocone F).precompose E).obj s.desc ≅ s :=
  isoMk s.descLeg fun {c c'} u => NatTrans.ext (funext fun x => by
    have h : s.desc.map ((Grothendieck.fibrewiseIsos F).Q.map
        ((Grothendieck.ιNatTrans u).app x)) = (s.κ u).hom.app x :=
      (s.desc_map_Q _).trans ((congrArg ((s.κ u).hom.app x ≫ ·)
        ((s.ι c').map_id _)).trans (Category.comp_id _))
    refine Eq.trans ?_ (congrArg (· ≫ (s.κ u).hom.app x) (s.descLeg_hom_app c x)).symm
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact (congrArg (· ≫ (s.descLeg c').hom.app _) h).trans
      ((congrArg ((s.κ u).hom.app x ≫ ·) (s.descLeg_hom_app c' _)).trans (Category.comp_id _)))

end PseudoCocone

/-! ## The model satisfies it -/

section Model

variable (F) {E : Type u₃} [Category.{v₃} E]

instance faithful_precompose_bicolimitCocone :
    ((bicolimitCocone F).precompose E).Faithful where
  map_injective {_ _ _ _} h :=
    Localization.natTrans_ext (Grothendieck.fibrewiseIsos F).Q (Grothendieck.fibrewiseIsos F)
      fun X => congr_app (congrArg (PseudoCocone.Hom.app · X.base) h) X.fiber

instance full_precompose_bicolimitCocone : ((bicolimitCocone F).precompose E).Full where
  map_surjective {G H} θ :=
    ⟨(Localization.whiskeringLeftFunctor' (Grothendieck.fibrewiseIsos F).Q
        (Grothendieck.fibrewiseIsos F) E).preimage
      (Grothendieck.natTransFrom (G := (Grothendieck.fibrewiseIsos F).Q ⋙ G)
        (H := (Grothendieck.fibrewiseIsos F).Q ⋙ H) (fun c => θ.app c) fun u => θ.naturality u),
    PseudoCocone.hom_ext fun c => NatTrans.ext (funext fun x =>
      congr_app (Functor.map_preimage (Localization.whiskeringLeftFunctor'
        (Grothendieck.fibrewiseIsos F).Q (Grothendieck.fibrewiseIsos F) E) _)
        ((Grothendieck.ι F c).obj x))⟩

instance essSurj_precompose_bicolimitCocone :
    ((bicolimitCocone F).precompose E).EssSurj where
  mem_essImage s := ⟨s.desc, ⟨s.precomposeDescIso⟩⟩

/-- **The bicolimit's pseudo-cocone is a bicolimit.** -/
theorem isBicolimit_bicolimitCocone : IsBicolimit (bicolimitCocone F) := fun _ _ =>
  { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

end Model

/-! ## What the property gives -/

namespace IsBicolimit

variable {D : Type u₃} [Category.{v₃} D] {D' : Type u₃} [Category.{v₃} D']
  {t : PseudoCocone F D} {t' : PseudoCocone F D'}

/-- The comparison into another pseudo-cocone. -/
noncomputable def comparison (h : IsBicolimit t) (t' : PseudoCocone F D') : D ⥤ D' :=
  haveI := h D'; (t.precompose D').objPreimage t'

/-- …and that it carries the legs to the legs. -/
noncomputable def comparisonLegs (h : IsBicolimit t) (t' : PseudoCocone F D') :
    (t.precompose D').obj (h.comparison t') ≅ t' :=
  haveI := h D'; (t.precompose D').objObjPreimageIso t'

/-- **Two bicolimits of one diagram have equivalent vertices** — each comparison is a pseudo-cocone
arrow, so full faithfulness sends the round trips to the identities (`comparisonLegs` is the
compatibility with the legs). -/
noncomputable def equiv (h : IsBicolimit t) (h' : IsBicolimit t') : D ≌ D' :=
  haveI := h D
  haveI := h' D'
  Equivalence.mk (h.comparison t') (h'.comparison t)
    ((t.precompose D).preimageIso (((PseudoCocone.precomposeIso (h.comparisonLegs t')
      (h'.comparison t)).trans (h'.comparisonLegs t)).trans
      (eqToIso (t.precompose_obj_id).symm)).symm)
    ((t'.precompose D').preimageIso ((PseudoCocone.precomposeIso (h'.comparisonLegs t)
      (h.comparison t')).trans ((h.comparisonLegs t').trans
      (eqToIso (t'.precompose_obj_id).symm))))

/-- **A bicolimit stays one along an equivalence of vertices.** -/
theorem precompose_equivalence (h : IsBicolimit t) (e : D ≌ D') :
    IsBicolimit ((t.precompose D').obj e.functor) := by
  intro E _
  haveI := h E
  exact show (((Functor.whiskeringLeft D D' E).obj e.functor) ⋙ t.precompose E).IsEquivalence from
    inferInstance

end IsBicolimit

end CategoryTheory
