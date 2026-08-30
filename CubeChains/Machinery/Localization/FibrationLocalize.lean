import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Localization.Equivalence
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Localizing a discrete fibration fibrewise

A discrete fibration over `B` is `P.Elements` for `P : B ⥤ Type w`, and base transport along
`G : D ⥤ C` is `CategoryOfElements.pre`.  If `P` inverts `W` then the localization of `P.Elements`
at the lifted morphisms is the category of elements of the descended `P̄ : B[W⁻¹] ⥤ Type w`: all of
the base's formal inverses lift, and nothing else is created.

The proof turns the universal property of `∫P̄` — which has no generators-and-relations
presentation — into that of `B[W⁻¹]`: a functor `∫G ⥤ E` is the *same thing* as a functor
`D ⥤ Fam E` lifting `G` (`Fam.pack`/`Fam.unpack`), `Fam E` being the free coproduct completion.
-/

universe w v u v₁ u₁ v₂ u₂

namespace CategoryTheory

/-! ## The free coproduct completion -/

/-- A family of objects of `E` indexed by a type: the free coproduct completion of `E`. -/
structure Fam.{w', v', u'} (E : Type u') [Category.{v'} E] : Type (max (w' + 1) u') where
  /-- the indexing type -/
  ι : Type w'
  /-- the family itself -/
  obj : ι → E

namespace Fam

variable {E : Type u} [Category.{v} E]

/-- A map of families: a reindexing, plus a morphism over each index. -/
structure Hom (X Y : Fam.{w} E) where
  /-- the reindexing -/
  map : X.ι → Y.ι
  /-- the component over each index -/
  app (i : X.ι) : X.obj i ⟶ Y.obj (map i)

/-- Two maps of families agree as soon as their reindexings and components do. -/
theorem Hom.ext {X Y : Fam.{w} E} :
    ∀ {f g : Hom X Y}, f.map = g.map → HEq f.app g.app → f = g
  | ⟨_, _⟩, ⟨_, _⟩, rfl, HEq.rfl => rfl

instance : Category.{max w v} (Fam.{w} E) where
  Hom X Y := Hom X Y
  id _ := ⟨_root_.id, fun _ => 𝟙 _⟩
  comp f g := ⟨fun i => g.map (f.map i), fun i => f.app i ≫ g.app (f.map i)⟩
  id_comp _ := Hom.ext rfl (heq_of_eq (funext fun _ => Category.id_comp _))
  comp_id _ := Hom.ext rfl (heq_of_eq (funext fun _ => Category.comp_id _))
  assoc _ _ _ := Hom.ext rfl (heq_of_eq (funext fun _ => Category.assoc _ _ _))

@[simp] theorem id_map (X : Fam.{w} E) : Hom.map (𝟙 X) = _root_.id := rfl
@[simp] theorem id_app (X : Fam.{w} E) (i : X.ι) : Hom.app (𝟙 X) i = 𝟙 _ := rfl
@[simp] theorem comp_map {X Y Z : Fam.{w} E} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).map = fun i => g.map (f.map i) := rfl
@[simp] theorem comp_app {X Y Z : Fam.{w} E} (f : X ⟶ Y) (g : Y ⟶ Z) (i : X.ι) :
    (f ≫ g).app i = f.app i ≫ g.app (f.map i) := rfl

/-- The transport-corrected extensionality, which is what a `Fam`-valued functor's axioms need. -/
theorem Hom.ext' {X Y : Fam.{w} E} {f g : X ⟶ Y} (hm : f.map = g.map)
    (ha : ∀ i, f.app i ≫ eqToHom (congrArg Y.obj (congrFun hm i)) = g.app i) : f = g := by
  obtain ⟨fm, fa⟩ := f
  obtain ⟨gm, ga⟩ := g
  cases hm
  exact Hom.ext rfl (heq_of_eq (funext fun i => by simpa using ha i))

/-- The component of `f` at `i`, retargeted along an identification of `f.map i`. -/
def Hom.at {X Y : Fam.{w} E} (f : X ⟶ Y) (i : X.ι) {j : Y.ι} (h : f.map i = j) :
    X.obj i ⟶ Y.obj j :=
  f.app i ≫ eqToHom (congrArg Y.obj h)

/-- `at` does not depend on the identification, only on its target. -/
theorem Hom.at_congr {X Y : Fam.{w} E} {f g : X ⟶ Y} (e : f = g) (i : X.ι) {j : Y.ι}
    (h₁ : f.map i = j) (h₂ : g.map i = j) : f.at i h₁ = g.at i h₂ := by
  subst e; rfl

@[simp] theorem Hom.at_rfl {X Y : Fam.{w} E} (f : X ⟶ Y) (i : X.ι) (h : f.map i = f.map i) :
    f.at i h = f.app i := by
  simp [Hom.at]

theorem Hom.at_id {X : Fam.{w} E} (i : X.ι) (h : (𝟙 X : X ⟶ X).map i = i) :
    (𝟙 X : X ⟶ X).at i h = 𝟙 (X.obj i) := by
  simp [Hom.at]

theorem Hom.at_comp {X Y Z : Fam.{w} E} (f : X ⟶ Y) (g : Y ⟶ Z) (i : X.ι) {j : Y.ι} {k : Z.ι}
    (h₁ : f.map i = j) (h₂ : g.map j = k) (h : (f ≫ g).map i = k) :
    (f ≫ g).at i h = f.at i h₁ ≫ g.at j h₂ := by
  subst h₁; subst h₂; simp [Hom.at]

/-- Reading off the index of a family. -/
@[simps] def index : Fam.{w} E ⥤ Type w where
  obj X := X.ι
  map f := ↾f.map

private theorem isoMk_aux {X Y : Fam.{w} E} (e : X.ι ≃ Y.ι) (a : ∀ i, X.obj i ≅ Y.obj (e i))
    {i k : X.ι} (h : i = k) :
    (a i).hom ≫ eqToHom (congrArg (fun j => Y.obj (e j)) h) ≫ (a k).inv =
      eqToHom (congrArg X.obj h) := by
  subst h; simp

/-- A reindexing bijection together with componentwise isomorphisms. -/
def isoMk {X Y : Fam.{w} E} (e : X.ι ≃ Y.ι) (a : ∀ i, X.obj i ≅ Y.obj (e i)) : X ≅ Y where
  hom := ⟨e, fun i => (a i).hom⟩
  inv := ⟨e.symm, fun j =>
    eqToHom (congrArg Y.obj (e.apply_symm_apply j).symm) ≫ (a (e.symm j)).inv⟩
  hom_inv_id := Hom.ext' (funext fun i => e.symm_apply_apply i) fun i => by
    rw [comp_app, isoMk_aux e a (e.symm_apply_apply i).symm]
    simp
  inv_hom_id := Hom.ext' (funext fun j => e.apply_symm_apply j) fun j => by
    simp

@[simp] theorem isoMk_hom {X Y : Fam.{w} E} (e : X.ι ≃ Y.ι) (a : ∀ i, X.obj i ≅ Y.obj (e i)) :
    (isoMk e a).hom = ⟨e, fun i => (a i).hom⟩ := rfl

/-- A map of families is invertible as soon as its reindexing and all its components are. -/
theorem isIso_of_bijective {X Y : Fam.{w} E} (f : X ⟶ Y) (hm : Function.Bijective f.map)
    (ha : ∀ i, IsIso (f.app i)) : IsIso f := by
  have h : (isoMk (Equiv.ofBijective f.map hm) fun i => @asIso _ _ _ _ (f.app i) (ha i)).hom = f :=
    rfl
  rw [← h]
  exact Iso.isIso_hom _

end Fam

/-! ## The cartesian lift -/

namespace CategoryOfElements

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The cartesian lift of `f` at `x`: the unique arrow of `∫G` over `f` out of `⟨d, x⟩`. -/
def lift (G : D ⥤ Type w) {d d' : D} (f : d ⟶ d') (x : G.obj d) :
    G.elementsMk d x ⟶ G.elementsMk d' (G.map f x) := ⟨f, rfl⟩

@[simp] theorem lift_val (G : D ⥤ Type w) {d d' : D} (f : d ⟶ d') (x : G.obj d) :
    (lift G f x).val = f := rfl

/-- **Base transport** (the `Elements`-level `Grothendieck.pre`): a functor `G : D ⥤ C` carries
`∫(G ⋙ P)` to `∫P`, `⟨d, x⟩ ↦ ⟨G.obj d, x⟩`. -/
def pre (P : C ⥤ Type w) (G : D ⥤ C) : (G ⋙ P).Elements ⥤ P.Elements where
  obj X := ⟨G.obj X.1, X.2⟩
  map f := ⟨G.map f.1, f.2⟩
  map_id X := ext P _ _ (G.map_id X.1)
  map_comp f g := ext P _ _ (G.map_comp f.1 g.1)

/-- The explicit inverse of `pre P e.functor`: an element `x` of `P` at `X` is carried to the
element of `e.functor ⋙ P` at `e.inverse.obj X` obtained by transporting `x` along the counit
`X ≅ e.functor.obj (e.inverse.obj X)`. -/
def preInv (P : C ⥤ Type w) (e : D ≌ C) : P.Elements ⥤ (e.functor ⋙ P).Elements where
  obj X := ⟨e.inverse.obj X.1, P.map (e.counitIso.inv.app X.1) X.2⟩
  map {X Y} k := ⟨e.inverse.map k.1, by
    have hn : e.counitIso.inv.app X.1 ≫ e.functor.map (e.inverse.map k.1)
        = k.1 ≫ e.counitIso.inv.app Y.1 := (e.counitIso.inv.naturality k.1).symm
    change P.map (e.functor.map (e.inverse.map k.1)) (P.map (e.counitIso.inv.app X.1) X.2)
        = P.map (e.counitIso.inv.app Y.1) Y.2
    calc P.map (e.functor.map (e.inverse.map k.1)) (P.map (e.counitIso.inv.app X.1) X.2)
        = P.map (e.counitIso.inv.app X.1 ≫ e.functor.map (e.inverse.map k.1)) X.2 :=
          (P.map_comp_apply _ _ _).symm
      _ = P.map (k.1 ≫ e.counitIso.inv.app Y.1) X.2 := by rw [hn]; rfl
      _ = P.map (e.counitIso.inv.app Y.1) (P.map k.1 X.2) := P.map_comp_apply _ _ _
      _ = P.map (e.counitIso.inv.app Y.1) Y.2 := by rw [k.2]⟩
  map_id X := ext _ _ _ (e.inverse.map_id X.1)
  map_comp f g := ext _ _ _ (e.inverse.map_comp f.1 g.1)

/-- **Base transport is an equivalence** when the base functor is (analogue of
`Grothendieck.preEquivalence`); the inverse is spelled out as `preInv`, rather than obtained from
`EssSurj`, so that the equivalence computes. -/
def preEquivalenceComp (P : C ⥤ Type w) (e : D ≌ C) :
    (e.functor ⋙ P).Elements ≌ P.Elements where
  functor := pre P e.functor
  inverse := preInv P e
  unitIso := NatIso.ofComponents
    (fun Z => isoMk _ _ (e.unitIso.app Z.1) (by
      change P.map (e.functor.map (e.unitIso.hom.app Z.1)) Z.2
          = P.map (e.counitIso.inv.app (e.functor.obj Z.1)) Z.2
      rw [← e.counitInv_app_functor]
      rfl))
    (fun k => ext _ _ _ (e.unit_naturality k.1).symm)
  counitIso := NatIso.ofComponents
    (fun Z => isoMk _ _ (e.counitIso.app Z.1) (by
      change P.map (e.counitIso.hom.app Z.1) (P.map (e.counitIso.inv.app Z.1) Z.2) = Z.2
      rw [← P.map_comp_apply, e.counitIso.inv_hom_id_app, P.map_id_apply]))
    (fun k => ext _ _ _ (e.counit_naturality k.1))
  functor_unitIso_comp Z := ext _ _ _ (e.functor_unit_comp Z.1)

/-- A natural isomorphism of presheaves induces an equivalence of their categories of elements. -/
def mapEquivalence {F G : C ⥤ Type w} (e : F ≅ G) : F.Elements ≌ G.Elements :=
  Cat.equivOfIso (Functor.elementsFunctor.mapIso e)

/-- The base endomorphisms fixing an element. -/
def stabilizer (P : C ⥤ Type w) (p : P.Elements) : Submonoid (End p.1) where
  carrier := {g | P.map g p.2 = p.2}
  one_mem' := show P.map (𝟙 p.1) p.2 = p.2 from P.map_id_apply p.1 p.2
  mul_mem' {x y} hx hy := by
    change P.map (y ≫ x) p.2 = p.2
    rw [P.map_comp_apply, hy, hx]

/-- **The loops at an element are the stabilizer of that element.** -/
def endEquivStabilizer (P : C ⥤ Type w) (p : P.Elements) : End p ≃* stabilizer P p where
  toFun f := ⟨f.val, f.property⟩
  invFun g := ⟨g.val, g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- …and the loops at the *opposite* element are the opposite of that stabilizer. -/
def endOpEquivStabilizer (P : C ⥤ Type w) (p : P.Elements) :
    End (Opposite.op p) ≃* (stabilizer P p)ᵐᵒᵖ where
  toFun f := MulOpposite.op (endEquivStabilizer P p f.unop)
  invFun g := ((endEquivStabilizer P p).symm g.unop).op
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- A morphism of elements is invertible as soon as its base morphism is. -/
theorem isIso_of_isIso_val {P : C ⥤ Type w} {p q : P.Elements} (f : p ⟶ q) [IsIso f.val] :
    IsIso f := by
  have h : P.map (inv f.val) (P.map f.val p.2) = p.2 := by
    rw [← Functor.map_comp_apply, IsIso.hom_inv_id, P.map_id_apply]
  rw [f.property] at h
  exact ⟨⟨inv f.val, h⟩, ext P _ _ (by simp), ext P _ _ (by simp)⟩

end CategoryOfElements

/-! ## Functors out of a category of elements are `Fam`-valued functors -/

namespace Fam

variable {D : Type u₂} [Category.{v₂} D] {E : Type u} [Category.{v} E]

section

variable {G : D ⥤ Type w}

/-- The move that makes `pack` functorial: `F` may be applied to a cartesian lift before the
target element is identified. -/
private theorem map_eqToHom (F : G.Elements ⥤ E) {d d' : D} (f : d ⟶ d') {x : G.obj d}
    {y : G.obj d'} (h : G.map f x = y) :
    F.map (CategoryOfElements.lift G f x) ≫
        eqToHom (congrArg (fun z => F.obj (G.elementsMk d' z)) h) =
      F.map (⟨f, h⟩ : G.elementsMk d x ⟶ G.elementsMk d' y) := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- A functor out of `∫G`, packaged as a `Fam`-valued functor lifting `G`. -/
@[simps] def pack (F : G.Elements ⥤ E) : D ⥤ Fam.{w} E where
  obj d := ⟨G.obj d, fun x => F.obj (G.elementsMk d x)⟩
  map f := ⟨fun x => G.map f x, fun x => F.map (CategoryOfElements.lift G f x)⟩
  map_id d := Hom.ext' (funext fun x => by simp) fun x =>
    (map_eqToHom F (𝟙 d) (by simp : G.map (𝟙 d) x = x)).trans
      ((F.congr_map (CategoryOfElements.ext G _ (𝟙 _) rfl)).trans (F.map_id _))
  map_comp f g := Hom.ext' (funext fun x => by simp) fun x =>
    (map_eqToHom F (f ≫ g) (by simp : G.map (f ≫ g) x = G.map g (G.map f x))).trans
      ((F.congr_map (CategoryOfElements.ext G _
          (CategoryOfElements.lift G f x ≫ CategoryOfElements.lift G g _) rfl)).trans
        (F.map_comp _ _))

@[simp] theorem pack_comp_index (F : G.Elements ⥤ E) : pack F ⋙ index = G := rfl

end

/-- A `Fam`-valued functor, read as a functor out of the category of elements of its index. -/
def unpack (𝔉 : D ⥤ Fam.{w} E) : (𝔉 ⋙ index).Elements ⥤ E where
  obj p := (𝔉.obj p.1).obj p.2
  map {p q} f := (𝔉.map f.val).at p.2 f.property
  map_id p :=
    (Hom.at_congr (𝔉.map_id p.1) p.2 (𝟙 p : p ⟶ p).property rfl).trans (Hom.at_id _ rfl)
  map_comp {p q r} f g := by
    have h₂ : (𝔉.map f.val ≫ 𝔉.map g.val).map p.2 = r.2 := by
      change (𝔉.map g.val).map ((𝔉.map f.val).map p.2) = r.2
      rw [show (𝔉.map f.val).map p.2 = q.2 from f.property]
      exact g.property
    exact (Hom.at_congr (𝔉.map_comp f.val g.val) p.2 (f ≫ g).property h₂).trans
      (Hom.at_comp _ _ _ f.property g.property h₂)

/-- The `Functor.ext` obligation when the object parts agree definitionally. -/
private theorem eqToHom_conj {C : Type u₁} [Category.{v₁} C] {X Y : C} (f : X ⟶ Y) (hX : X = X)
    (hY : Y = Y) : f = eqToHom hX ≫ f ≫ eqToHom hY := by simp

theorem pack_unpack (𝔉 : D ⥤ Fam.{w} E) : pack (unpack 𝔉) = 𝔉 := by
  refine Functor.ext (fun _ => rfl) fun _ _ f => ?_
  have h : (pack (unpack 𝔉)).map f = 𝔉.map f :=
    Hom.ext' rfl fun x => by simp [unpack, Hom.at]
  exact h.trans (eqToHom_conj (𝔉.map f) rfl rfl)

theorem unpack_pack {G : D ⥤ Type w} (F : G.Elements ⥤ E) : unpack (pack F) = F := by
  refine Functor.ext (fun _ => rfl) fun p q f => ?_
  exact ((map_eqToHom F f.val f.property).trans (F.congr_map (Subtype.ext rfl))).trans
    (eqToHom_conj (F.map f) rfl rfl)

/-- `unpack` along an identification of the index functor. -/
def unpackEq (𝔉 : D ⥤ Fam.{w} E) {G : D ⥤ Type w} (h : 𝔉 ⋙ index = G) : G.Elements ⥤ E :=
  h ▸ unpack 𝔉

theorem unpackEq_pack {G : D ⥤ Type w} (F : G.Elements ⥤ E) : unpackEq (pack F) rfl = F :=
  unpack_pack F

theorem pack_unpackEq (𝔉 : D ⥤ Fam.{w} E) {G : D ⥤ Type w} (h : 𝔉 ⋙ index = G) :
    pack (unpackEq 𝔉 h) = 𝔉 := by
  subst h; exact pack_unpack 𝔉

theorem unpackEq_congr {𝔉₁ 𝔉₂ : D ⥤ Fam.{w} E} (e : 𝔉₁ = 𝔉₂) {G : D ⥤ Type w}
    (h₁ : 𝔉₁ ⋙ index = G) (h₂ : 𝔉₂ ⋙ index = G) : unpackEq 𝔉₁ h₁ = unpackEq 𝔉₂ h₂ := by
  subst e; rfl

theorem pack_injective {G : D ⥤ Type w} {F₁ F₂ : G.Elements ⥤ E} (h : pack F₁ = pack F₂) :
    F₁ = F₂ :=
  (unpackEq_pack F₁).symm.trans ((unpackEq_congr h rfl rfl).trans (unpackEq_pack F₂))

theorem pack_pre {C : Type u₁} [Category.{v₁} C] (P : C ⥤ Type w) (G : D ⥤ C)
    (F : P.Elements ⥤ E) :
    pack (CategoryOfElements.pre P G ⋙ F) = G ⋙ pack F := rfl

end Fam

/-! ## The descent theorem -/

namespace Localization

open CategoryOfElements MorphismProperty

variable {B : Type u₁} [Category.{v₁} B] (W : MorphismProperty B) (Pd : W.Localization ⥤ Type w)

/-- The morphisms of `∫(W.Q ⋙ Pd)` lying over `W`: the cartesian lifts of the base's `W`. -/
abbrev elementsW : MorphismProperty (W.Q ⋙ Pd).Elements := W.inverseImage (π (W.Q ⋙ Pd))

variable {E : Type u} [Category.{v} E]

private theorem pre_inverts : (elementsW W Pd).IsInvertedBy (pre Pd W.Q) := by
  intro p q f hf
  have : IsIso ((pre Pd W.Q).map f).val := W.Q_inverts f.val hf
  exact isIso_of_isIso_val _

private theorem pack_inverts (F : (W.Q ⋙ Pd).Elements ⥤ E)
    (hF : (elementsW W Pd).IsInvertedBy F) : W.IsInvertedBy (Fam.pack F) := by
  intro b b' u hu
  haveI : IsIso (W.Q.map u) := W.Q_inverts u hu
  haveI : IsIso ((W.Q ⋙ Pd).map u) := inferInstanceAs (IsIso (Pd.map (W.Q.map u)))
  refine Fam.isIso_of_bijective _ ?_ fun x => ?_
  · exact (isIso_iff_bijective ((W.Q ⋙ Pd).map u)).mp inferInstance
  · exact hF (CategoryOfElements.lift (W.Q ⋙ Pd) u x) hu

/-- The descent of `Fam.pack F` through the localization; its index functor is `Pd`. -/
private noncomputable def packLift (F : (W.Q ⋙ Pd).Elements ⥤ E)
    (hF : (elementsW W Pd).IsInvertedBy F) : W.Localization ⥤ Fam.{w} E :=
  Construction.lift (Fam.pack F) (pack_inverts W Pd F hF)

private theorem packLift_index (F : (W.Q ⋙ Pd).Elements ⥤ E)
    (hF : (elementsW W Pd).IsInvertedBy F) : packLift W Pd F hF ⋙ Fam.index = Pd :=
  Construction.uniq _ _ (by
    rw [← Functor.assoc, packLift, Construction.fac, Fam.pack_comp_index])

/-- **A discrete fibration localizes fibrewise.** `∫(W.Q ⋙ Pd)` localized at the cartesian lifts
of `W` is `∫Pd`: a `W`-inverting presheaf's category of elements sees the base's localization and
nothing more. -/
noncomputable def strictUniversalPropertyElements :
    StrictUniversalPropertyFixedTarget (pre Pd W.Q) (elementsW W Pd) E where
  inverts := pre_inverts W Pd
  lift F hF := Fam.unpackEq _ (packLift_index W Pd F hF)
  fac F hF := Fam.pack_injective (by
    rw [Fam.pack_pre, Fam.pack_unpackEq, packLift, Construction.fac])
  uniq F₁ F₂ h := Fam.pack_injective (Construction.uniq _ _ (by
    rw [← Fam.pack_pre, ← Fam.pack_pre, h]))

instance isLocalization_pre : (pre Pd W.Q).IsLocalization (elementsW W Pd) :=
  Functor.IsLocalization.mk' _ _ (strictUniversalPropertyElements W Pd)
    (strictUniversalPropertyElements W Pd)

/-! ### Starting from a `W`-inverting `P` -/

/-- `pre` read on `P` through an identification of `W.Q ⋙ Pd` with it. -/
noncomputable def preOf {P : B ⥤ Type w} {Pd : W.Localization ⥤ Type w}
    (h : W.Q ⋙ Pd = P) : P.Elements ⥤ Pd.Elements :=
  h ▸ pre Pd W.Q

theorem isLocalization_preOf {P : B ⥤ Type w} {Pd : W.Localization ⥤ Type w}
    (h : W.Q ⋙ Pd = P) : (preOf W h).IsLocalization (W.inverseImage (π P)) := by
  subst h; exact isLocalization_pre W Pd

/-- The presheaf descended through the localization; `P` must invert `W`. -/
noncomputable abbrev descend (P : B ⥤ Type w) (hP : W.IsInvertedBy P) :
    W.Localization ⥤ Type w :=
  Construction.lift P hP

/-- `∫P ⥤ ∫P̄` over `B ⥤ B[W⁻¹]`. -/
noncomputable def elementsDescent (P : B ⥤ Type w) (hP : W.IsInvertedBy P) :
    P.Elements ⥤ (descend W P hP).Elements :=
  preOf W (Construction.fac P hP)

/-- **The descent theorem in the form the input is usually met in.**  A `W`-inverting
`P : B ⥤ Type w` has `∫P` localized at the cartesian lifts of `W` equal to `∫P̄` over `B[W⁻¹]`. -/
theorem isLocalization_elementsDescent (P : B ⥤ Type w) (hP : W.IsInvertedBy P) :
    (elementsDescent W P hP).IsLocalization (W.inverseImage (π P)) :=
  isLocalization_preOf W (Construction.fac P hP)

end Localization

end CategoryTheory
