import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
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
`D ⥤ FormalCoproduct E` lifting `G` (`pack`/`unpack`), into the free coproduct completion.
-/

universe w v u v₁ u₁ v₂ u₂

namespace CategoryTheory

/-! ## Pulling a localization back along an equivalence -/

/-- **A localization pulls back along an equivalence of sources** — `W.RespectsIso` is genuine:
transporting a `V`-arrow backwards conjugates it by the counit. -/
theorem Functor.IsLocalization.of_inverseImage {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {E : Type u} [Category.{v} E] (G : C ⥤ D) [G.IsEquivalence] (L : D ⥤ E)
    (V : MorphismProperty D) [V.RespectsIso] [L.IsLocalization V]
    (U : MorphismProperty C) (hU : U = V.inverseImage G) :
    (G ⋙ L).IsLocalization U := by
  subst hU
  refine Functor.IsLocalization.of_equivalence_source L V (G ⋙ L) (V.inverseImage G)
    G.asEquivalence.symm (fun X Y f hf => ?_)
    (fun _ _ f hf => Localization.inverts L V _ hf)
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight G.asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _)
  refine MorphismProperty.le_isoClosure _ _ ?_
  change V (G.asEquivalence.functor.map (G.asEquivalence.inverse.map f))
  rw [Equivalence.fun_inv_map]
  exact MorphismProperty.RespectsIso.precomp _ (G.asEquivalence.counitIso.app X).hom _
    (MorphismProperty.RespectsIso.postcomp _ (G.asEquivalence.counitIso.app Y).inv _ hf)

/-! ## The free coproduct completion

The completion itself is `Limits.FormalCoproduct`; all that is wanted beyond it is the index
functor and the retargeting `at`, which is what carries a `FormalCoproduct`-valued functor's
transports. -/

namespace Limits.FormalCoproduct

variable {E : Type u} [Category.{v} E]

/-- The component of `f` at `i`, retargeted along an identification of `f.f i`. -/
def Hom.at {X Y : FormalCoproduct.{w} E} (f : X ⟶ Y) (i : X.I) {j : Y.I} (h : f.f i = j) :
    X.obj i ⟶ Y.obj j :=
  f.φ i ≫ eqToHom (congrArg Y.obj h)

/-- `at` does not depend on the identification, only on its target. -/
theorem Hom.at_congr {X Y : FormalCoproduct.{w} E} {f g : X ⟶ Y} (e : f = g) (i : X.I) {j : Y.I}
    (h₁ : f.f i = j) (h₂ : g.f i = j) : f.at i h₁ = g.at i h₂ := by
  subst e; rfl

theorem Hom.at_id {X : FormalCoproduct.{w} E} (i : X.I) (h : (𝟙 X : X ⟶ X).f i = i) :
    (𝟙 X : X ⟶ X).at i h = 𝟙 (X.obj i) := by
  simp [Hom.at]

theorem Hom.at_comp {X Y Z : FormalCoproduct.{w} E} (f : X ⟶ Y) (g : Y ⟶ Z) (i : X.I) {j : Y.I}
    {k : Z.I} (h₁ : f.f i = j) (h₂ : g.f j = k) (h : (f ≫ g).f i = k) :
    (f ≫ g).at i h = f.at i h₁ ≫ g.at j h₂ := by
  subst h₁; subst h₂; simp [Hom.at]

/-- Reading off the index of a family. -/
@[simps] def index : FormalCoproduct.{w} E ⥤ Type w where
  obj X := X.I
  map f := ↾f.f

/-- A map of families is invertible as soon as its reindexing and all its components are. -/
theorem isIso_of_bijective {X Y : FormalCoproduct.{w} E} (f : X ⟶ Y)
    (hm : Function.Bijective f.f) (ha : ∀ i, IsIso (f.φ i)) : IsIso f := by
  have h : (isoOfComponents (Equiv.ofBijective f.f hm)
      fun i => @asIso _ _ _ _ (f.φ i) (ha i)).hom = f := rfl
  rw [← h]
  exact Iso.isIso_hom _

end Limits.FormalCoproduct

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

/-- **Base transport is an equivalence** as soon as the base functor is fully faithful and every
object carrying an element is in its essential image. -/
theorem isEquivalence_pre (P : C ⥤ Type w) (G : D ⥤ C) [G.Full] [G.Faithful]
    (hcov : ∀ c : C, P.obj c → ∃ d : D, Nonempty (G.obj d ≅ c)) :
    (pre P G).IsEquivalence := by
  haveI : (pre P G).Faithful :=
    ⟨fun h => Subtype.ext (G.map_injective (congrArg Subtype.val h))⟩
  haveI : (pre P G).Full :=
    ⟨fun {x y} k => ⟨⟨G.preimage k.val, by
      change P.map (G.map (G.preimage k.val)) x.2 = y.2
      rw [G.map_preimage]
      exact k.property⟩, ext _ _ _ (G.map_preimage k.val)⟩⟩
  haveI : (pre P G).EssSurj := ⟨fun z => by
    obtain ⟨d, ⟨e⟩⟩ := hcov z.1 z.2
    refine ⟨⟨d, P.map e.inv z.2⟩, ⟨isoMk _ _ e ?_⟩⟩
    change P.map e.hom (P.map e.inv z.2) = z.2
    rw [← P.map_comp_apply, e.inv_hom_id, P.map_id_apply]⟩
  exact { }

/-- **…and in particular when the base functor is an equivalence**:
`Grothendieck.preEquivalence` read through `grothendieckTypeToCat`. -/
def preEquivalenceComp (P : C ⥤ Type w) (e : D ≌ C) :
    (e.functor ⋙ P).Elements ≌ P.Elements :=
  (Grothendieck.grothendieckTypeToCat (e.functor ⋙ P)).symm.trans
    ((Grothendieck.preEquivalence (P ⋙ typeToCat) e).trans
      (Grothendieck.grothendieckTypeToCat P))

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

/-! ## Functors out of a category of elements are family-valued functors -/

namespace Limits.FormalCoproduct

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

/-- A functor out of `∫G`, packaged as a family-valued functor lifting `G`. -/
@[simps] def pack (F : G.Elements ⥤ E) : D ⥤ FormalCoproduct.{w} E where
  obj d := ⟨G.obj d, fun x => F.obj (G.elementsMk d x)⟩
  map f := ⟨fun x => G.map f x, fun x => F.map (CategoryOfElements.lift G f x)⟩
  map_id d := hom_ext (funext fun x => by simp) fun x =>
    (map_eqToHom F (𝟙 d) (by simp : G.map (𝟙 d) x = x)).trans
      ((F.congr_map (CategoryOfElements.ext G _ (𝟙 _) rfl)).trans (F.map_id _))
  map_comp f g := hom_ext (funext fun x => by simp) fun x =>
    (map_eqToHom F (f ≫ g) (by simp : G.map (f ≫ g) x = G.map g (G.map f x))).trans
      ((F.congr_map (CategoryOfElements.ext G _
          (CategoryOfElements.lift G f x ≫ CategoryOfElements.lift G g _) rfl)).trans
        (F.map_comp _ _))

@[simp] theorem pack_comp_index (F : G.Elements ⥤ E) : pack F ⋙ index = G := rfl

end

/-- A family-valued functor, read as a functor out of the category of elements of its index. -/
def unpack (𝔉 : D ⥤ FormalCoproduct.{w} E) : (𝔉 ⋙ index).Elements ⥤ E where
  obj p := (𝔉.obj p.1).obj p.2
  map {p q} f := (𝔉.map f.val).at p.2 f.property
  map_id p :=
    (Hom.at_congr (𝔉.map_id p.1) p.2 (𝟙 p : p ⟶ p).property rfl).trans (Hom.at_id _ rfl)
  map_comp {p q r} f g := by
    have h₂ : (𝔉.map f.val ≫ 𝔉.map g.val).f p.2 = r.2 := by
      change (𝔉.map g.val).f ((𝔉.map f.val).f p.2) = r.2
      rw [show (𝔉.map f.val).f p.2 = q.2 from f.property]
      exact g.property
    exact (Hom.at_congr (𝔉.map_comp f.val g.val) p.2 (f ≫ g).property h₂).trans
      (Hom.at_comp _ _ _ f.property g.property h₂)

/-- The `Functor.ext` obligation when the object parts agree definitionally. -/
private theorem eqToHom_conj {C : Type u₁} [Category.{v₁} C] {X Y : C} (f : X ⟶ Y) (hX : X = X)
    (hY : Y = Y) : f = eqToHom hX ≫ f ≫ eqToHom hY := by simp

theorem pack_unpack (𝔉 : D ⥤ FormalCoproduct.{w} E) : pack (unpack 𝔉) = 𝔉 := by
  refine Functor.ext (fun _ => rfl) fun _ _ f => ?_
  have h : (pack (unpack 𝔉)).map f = 𝔉.map f :=
    hom_ext rfl fun x => by simp [unpack, Hom.at]
  exact h.trans (eqToHom_conj (𝔉.map f) rfl rfl)

theorem unpack_pack {G : D ⥤ Type w} (F : G.Elements ⥤ E) : unpack (pack F) = F := by
  refine Functor.ext (fun _ => rfl) fun p q f => ?_
  exact ((map_eqToHom F f.val f.property).trans (F.congr_map (Subtype.ext rfl))).trans
    (eqToHom_conj (F.map f) rfl rfl)

/-- `unpack` along an identification of the index functor. -/
def unpackEq (𝔉 : D ⥤ FormalCoproduct.{w} E) {G : D ⥤ Type w} (h : 𝔉 ⋙ index = G) :
    G.Elements ⥤ E :=
  h ▸ unpack 𝔉

theorem unpackEq_pack {G : D ⥤ Type w} (F : G.Elements ⥤ E) : unpackEq (pack F) rfl = F :=
  unpack_pack F

theorem pack_unpackEq (𝔉 : D ⥤ FormalCoproduct.{w} E) {G : D ⥤ Type w} (h : 𝔉 ⋙ index = G) :
    pack (unpackEq 𝔉 h) = 𝔉 := by
  subst h; exact pack_unpack 𝔉

theorem unpackEq_congr {𝔉₁ 𝔉₂ : D ⥤ FormalCoproduct.{w} E} (e : 𝔉₁ = 𝔉₂) {G : D ⥤ Type w}
    (h₁ : 𝔉₁ ⋙ index = G) (h₂ : 𝔉₂ ⋙ index = G) : unpackEq 𝔉₁ h₁ = unpackEq 𝔉₂ h₂ := by
  subst e; rfl

theorem pack_injective {G : D ⥤ Type w} {F₁ F₂ : G.Elements ⥤ E} (h : pack F₁ = pack F₂) :
    F₁ = F₂ :=
  (unpackEq_pack F₁).symm.trans ((unpackEq_congr h rfl rfl).trans (unpackEq_pack F₂))

theorem pack_pre {C : Type u₁} [Category.{v₁} C] (P : C ⥤ Type w) (G : D ⥤ C)
    (F : P.Elements ⥤ E) :
    pack (CategoryOfElements.pre P G ⋙ F) = G ⋙ pack F := rfl

end Limits.FormalCoproduct

/-! ## The descent theorem -/

namespace Localization

open CategoryOfElements Limits MorphismProperty

variable {B : Type u₁} [Category.{v₁} B] (W : MorphismProperty B) (Pd : W.Localization ⥤ Type w)

/-- The morphisms of `∫(W.Q ⋙ Pd)` lying over `W`: the cartesian lifts of the base's `W`. -/
abbrev elementsW : MorphismProperty (W.Q ⋙ Pd).Elements := W.inverseImage (π (W.Q ⋙ Pd))

variable {E : Type u} [Category.{v} E]

private theorem pre_inverts : (elementsW W Pd).IsInvertedBy (pre Pd W.Q) := by
  intro p q f hf
  have : IsIso ((pre Pd W.Q).map f).val := W.Q_inverts f.val hf
  exact isIso_of_isIso_val _

private theorem pack_inverts (F : (W.Q ⋙ Pd).Elements ⥤ E)
    (hF : (elementsW W Pd).IsInvertedBy F) : W.IsInvertedBy (FormalCoproduct.pack F) := by
  intro b b' u hu
  haveI : IsIso (W.Q.map u) := W.Q_inverts u hu
  haveI : IsIso ((W.Q ⋙ Pd).map u) := inferInstanceAs (IsIso (Pd.map (W.Q.map u)))
  refine FormalCoproduct.isIso_of_bijective _ ?_ fun x => ?_
  · exact (isIso_iff_bijective ((W.Q ⋙ Pd).map u)).mp inferInstance
  · exact hF (CategoryOfElements.lift (W.Q ⋙ Pd) u x) hu

/-- The descent of `pack F` through the localization; its index functor is `Pd`. -/
private noncomputable def packLift (F : (W.Q ⋙ Pd).Elements ⥤ E)
    (hF : (elementsW W Pd).IsInvertedBy F) : W.Localization ⥤ FormalCoproduct.{w} E :=
  Construction.lift (FormalCoproduct.pack F) (pack_inverts W Pd F hF)

private theorem packLift_index (F : (W.Q ⋙ Pd).Elements ⥤ E)
    (hF : (elementsW W Pd).IsInvertedBy F) : packLift W Pd F hF ⋙ FormalCoproduct.index = Pd :=
  Construction.uniq _ _ (by
    rw [← Functor.assoc, packLift, Construction.fac, FormalCoproduct.pack_comp_index])

/-- **A discrete fibration localizes fibrewise.** `∫(W.Q ⋙ Pd)` localized at the cartesian lifts
of `W` is `∫Pd`: a `W`-inverting presheaf's category of elements sees the base's localization and
nothing more. -/
noncomputable def strictUniversalPropertyElements :
    StrictUniversalPropertyFixedTarget (pre Pd W.Q) (elementsW W Pd) E where
  inverts := pre_inverts W Pd
  lift F hF := FormalCoproduct.unpackEq _ (packLift_index W Pd F hF)
  fac F hF := FormalCoproduct.pack_injective (by
    rw [FormalCoproduct.pack_pre, FormalCoproduct.pack_unpackEq, packLift, Construction.fac])
  uniq F₁ F₂ h := FormalCoproduct.pack_injective (Construction.uniq _ _ (by
    rw [← FormalCoproduct.pack_pre, ← FormalCoproduct.pack_pre, h]))

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
