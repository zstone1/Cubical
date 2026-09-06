import CubeChains.Machinery.Presentation.Elements
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Submonoid.Defs

/-!
# Machinery/Presentation/Partial — presenting a *partial* category of elements

A functor with **at most one** lift of each arrow is classified by a presheaf of partial functions
— equivalently, since `Par ≃ Set⋆`, by a presheaf `G` with a global section `bot`.  The category is
`∫G` minus that section, so nothing new is presented: `Presents.elements` presents `∫G`, and
`restrict` cuts it down freely because `bot` is **absorbing** (`Convex`, `restrict`'s only
hypothesis).  `partialElements` takes an arbitrary `Presents P C`, so the presheaf must be produced
*without* naming a presentation; `partialActionFunctor` is how — a monoid acting by partial maps,
landing in `strictEnd`, where absorbing is by construction.  `bot` unreachable is the total case,
where the defined part is `∫` of an honest presheaf (`definedEquiv`).
-/

universe t w₂ w v u' u v₂ u₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-! ## Convex object properties -/

/-- `Q` is **convex**: an object through which an arrow between `Q`-objects factors is itself a
`Q`-object.  The complement of a co-sieve is convex, and that is the only case used. -/
def ObjectProperty.Convex (Q : ObjectProperty C) : Prop :=
  ∀ {a b z : C}, Q a → Q b → (a ⟶ z) → (z ⟶ b) → Q z

/-- **An absorbing complement is convex**: if `¬Q` is closed under arrows out of it, a word between
`Q`-objects cannot leave `Q`. -/
theorem ObjectProperty.convex_of_absorbing {Q : ObjectProperty C}
    (h : ∀ {x y : C}, ¬ Q x → (x ⟶ y) → ¬ Q y) : Q.Convex :=
  fun _ hb _ g => not_not.mp fun hz => h hz g hb

/-- **A convex property is closed under isomorphism** — an iso `x ≅ y` *is* a factorization
`x ⟶ y ⟶ x` with a `Q`-object at each end.

So **`restrict` can never cut a category down to a skeleton**: it cuts out full subcategories
closed under isomorphism, and naming one object per iso-class is exactly what `Convex` forbids.
Where a presentation has one 0-cell per iso-class and the target has one object per object — a
localization, whose objects are the source's on the nose — this is the wrong tool. -/
theorem ObjectProperty.Convex.respectsIso {Q : ObjectProperty C} (hQ : Q.Convex)
    {x y : C} (e : x ≅ y) (hx : Q x) : Q y :=
  hQ hx hx e.hom e.inv

namespace Presents

/-! ## Restricting a presentation to a convex full subcategory -/

section Restrict

variable {P : Polygraph.{w, u', w₂}} (p : Presents P C) (Q : ObjectProperty C)

/-- The 0-cells of `p` that live at `Q`-objects. -/
abbrev restrictV : Type u' := {a : P.V // Q (p.at' (P.pt a))}

/-- The 1-cells between them — `P`'s, unchanged. -/
abbrev restrictGen (x y : p.restrictV Q) : Type w := P.pt x.1 ⟶ P.pt y.1

/-- The restricted generating quiver lies over the full one. -/
def restrictProj : GenObj (p.restrictGen Q) ⥤q GenObj P.Gen where
  obj x := P.pt x.as.1
  map g := g

/-- **The cells of the restriction** — `P`'s, taken at `Q`-objects only. -/
def restrictPoly : Polygraph := P.comap (p.restrictGen Q) (p.restrictProj Q)

/-- …interpreted in the full subcategory. -/
def restrictInterp : GenObj (p.restrictGen Q) ⥤q Q.FullSubcategory where
  obj a := ⟨p.at' (P.pt a.as.1), a.as.2⟩
  map g := ObjectProperty.homMk (p.arrow g)

/-- Words of the restricted quiver, as words of the full one. -/
abbrev restrictIncl : Paths (GenObj (p.restrictGen Q)) ⥤ P.Word :=
  (p.restrictProj Q).pathsFunctor

/-- **A restricted word is the word it includes to**, read in `C`. -/
theorem hom_eval_restrict {x y : GenObj (p.restrictGen Q)} (R : Quiver.Path x y) :
    ((Paths.lift (p.restrictInterp Q)).map R).hom
      = p.eval.map ((p.restrictProj Q).mapPath R) :=
  (Paths.lift_comp_map (p.restrictInterp Q) Q.ι R).trans
    (p.eval_mapPath (p.restrictProj Q) R).symm

theorem restrictProj_star_injective (x : GenObj (p.restrictGen Q)) :
    Function.Injective ((p.restrictProj Q).star x) := by
  rintro ⟨⟨⟨a₁, h₁⟩⟩, e₁⟩ ⟨⟨⟨a₂, h₂⟩⟩, e₂⟩ h
  obtain ⟨ha, he⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : a₁ = a₂ := congrArg GenObj.as ha
  obtain rfl : e₁ = e₂ := eq_of_heq he
  rfl

instance : (p.restrictIncl Q).Faithful :=
  Prefunctor.pathsFunctor_faithful _ (restrictProj_star_injective p Q)

variable (hconv : Q.Convex)

include hconv in
/-- **A word between `Q`-objects is a restricted word.**  Convexity supplies the `Q`-ness of each
object it passes through, one cons at a time. -/
theorem exists_restrictPath {x : GenObj (p.restrictGen Q)} :
    ∀ {z : GenObj P.Gen} (R : Quiver.Path ((p.restrictProj Q).obj x) z) (hz : Q (p.at' z)),
      ∃ R' : Quiver.Path x ⟨⟨z.as, hz⟩⟩, (p.restrictProj Q).mapPath R' = R := by
  intro z R
  induction R with
  | nil => exact fun _ => ⟨Quiver.Path.nil, rfl⟩
  | @cons y z R e ih =>
      intro hz
      have hy : Q (p.at' y) :=
        hconv x.as.2 hz (p.eval.map R) (p.eval.map e.toPath)
      obtain ⟨R', hR'⟩ := ih hy
      exact ⟨R'.cons e, by rw [Prefunctor.mapPath_cons, hR']; rfl⟩

include hconv in
theorem restrictIncl_full : (p.restrictIncl Q).Full where
  map_surjective {x y} f := by
    obtain ⟨⟨b, hb⟩⟩ := y
    obtain ⟨R, hR⟩ := exists_restrictPath p Q hconv f hb
    exact ⟨R, hR⟩

include hconv in
theorem exists_restrict_mid {x y : GenObj (p.restrictGen Q)} {z : P.Word}
    (u : (p.restrictIncl Q).obj x ⟶ z) (v : z ⟶ (p.restrictIncl Q).obj y) :
    ∃ z' : GenObj (p.restrictGen Q), (p.restrictIncl Q).obj z' = z :=
  ⟨⟨⟨(z : GenObj P.Gen).as, hconv x.as.2 y.as.2 (p.eval.map u) (p.eval.map v)⟩⟩, rfl⟩

include hconv in
/-- **A presentation restricts to a convex full subcategory**, cells and 2-cells unchanged apart
from being taken at `Q`-objects only. -/
def restrict : Presents (p.restrictPoly Q) Q.FullSubcategory :=
  haveI := restrictIncl_full p Q hconv
  Presents.ofDesc (p.restrictInterp Q)
    (fun α => ObjectProperty.hom_ext _ ((hom_eval_restrict p Q _).trans
      ((p.comap_sound (p.restrictProj Q) α).trans (hom_eval_restrict p Q _).symm)))
    (fun {x y} {R₁ R₂} h => by
      refine Polygraph.comap_quot_map_eq_of_gen (p.restrictProj Q)
        (gen_pullbackRel (p.restrictIncl Q) P.homRel
          (fun u v => exists_restrict_mid p Q hconv u v) ?_)
      exact p.gen_of_eval_eq ((hom_eval_restrict p Q R₁).symm.trans
        ((congrArg InducedCategory.Hom.hom h).trans (hom_eval_restrict p Q R₂))))
    { map_surjective := fun {x y} f => by
        obtain ⟨R, hR⟩ := p.eval.map_surjective
          (show p.eval.obj (P.pt x.as.1) ⟶ p.eval.obj (P.pt y.as.1) from f.hom)
        obtain ⟨R', hR'⟩ := exists_restrictPath p Q hconv R y.as.2
        exact ⟨R', ObjectProperty.hom_ext _ ((hom_eval_restrict p Q R').trans (hR' ▸ hR))⟩ }
    { mem_essImage := fun c => by
        obtain ⟨x, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := p.eval) c.obj
        have hx : Q (p.at' x) := hconv c.property c.property i.inv i.hom
        exact ⟨⟨⟨x.as, hx⟩⟩, ⟨{ hom := ObjectProperty.homMk i.hom
                                inv := ObjectProperty.homMk i.inv
                                hom_inv_id := ObjectProperty.hom_ext _ (by simp)
                                inv_hom_id := ObjectProperty.hom_ext _ (by simp) }⟩⟩ }

end Restrict

end Presents

/-! ## Partial maps as a monoid, and the presheaf one gives

A monoid acting by *partial* maps is a monoid hom into the `none`-preserving endomorphisms of
`Option X`.  That is the presentation-free way to build the `(G, bot)` above: `strictEnd` makes the
undefined point absorbing **by construction**, so `hbot` is a projection rather than a generation
argument on the image. -/

/-- The `none`-preserving endomorphisms of `Option X` — the partial maps of `X`, as a submonoid. -/
def strictEnd (X : Type*) : Submonoid (Function.End (Option X)) where
  carrier := {f | f none = none}
  mul_mem' {f g} hf hg := show f (g none) = none by rw [hg]; exact hf
  one_mem' := rfl

@[simp] theorem mem_strictEnd {X : Type*} {f : Function.End (Option X)} :
    f ∈ strictEnd X ↔ f none = none := Iff.rfl

/-- **A partial map is where it is defined and what it lands on.** -/
theorem strictEnd_ext {X : Type*} {f g : strictEnd X}
    (h : ∀ u v : X, f.val (some u) = some v ↔ g.val (some u) = some v) : f = g :=
  Subtype.ext (funext fun o => by
    cases o with
    | none => rw [f.2, g.2]
    | some u => exact Option.ext fun v => h u v)

/-- With nothing to act on, a partial action is unique. -/
theorem subsingleton_strictEnd {X : Type*} [IsEmpty X] : Subsingleton (strictEnd X) :=
  ⟨fun f g => Subtype.ext (funext fun o => by
    cases o with
    | none => rw [f.2, g.2]
    | some x => exact isEmptyElim x)⟩

/-- **A partial action of `M` is a presheaf on its one-object category.**  Contravariance is the
`ᵒᵖ`; landing in `strictEnd` is what makes the undefined point absorbing. -/
def partialActionFunctor {M : Type*} [Monoid M] {X : Type} (φ : M →* (strictEnd X)ᵐᵒᵖ) :
    (SingleObj M)ᵒᵖ ⥤ Type where
  obj _ := Option X
  map f := ↾((φ f.unop).unop.val)
  map_id _ := by
    change ↾((φ (1 : M)).unop.val) = _
    rw [φ.map_one]
    rfl
  map_comp f g := by
    change ↾((φ (f.unop * g.unop)).unop.val) = _
    rw [φ.map_mul]
    rfl

@[simp] theorem partialActionFunctor_map_none {M : Type*} [Monoid M] {X : Type}
    (φ : M →* (strictEnd X)ᵐᵒᵖ) {a b : (SingleObj M)ᵒᵖ} (f : a ⟶ b) :
    (partialActionFunctor φ).map f none = none := (φ f.unop).unop.2

namespace Presents

/-! ## The defined part of a partial presheaf -/

section Partial

variable (G : C ⥤ Type t) (bot : ∀ c, G.obj c)
  (hbot : ∀ {c c' : C} (g : c ⟶ c'), G.map g (bot c) = bot c')

/-- The elements of `G` away from the chosen global section — the *defined* part of the partial
presheaf that `(G, bot)` is. -/
def defined : ObjectProperty G.Elements := fun z => z.2 ≠ bot z.1

include hbot in
/-- **`bot` is absorbing**, so the defined part is convex. -/
theorem convex_defined : (defined G bot).Convex := by
  refine ObjectProperty.convex_of_absorbing (Q := defined G bot) ?_
  intro z z' hz f h
  exact h ((f.property.symm.trans (congrArg (fun t => (G.map f.val) t) (not_not.mp hz))).trans
    (hbot f.val))

variable {P : Polygraph.{w, u', w₂}} (p : Presents P C)

include hbot in
/-- **A presentation of `C` presents the defined part of `∫G`** — 0-cells the defined elements,
1-cells the base's generators *where they are defined*, 2-cells its relations there. -/
def partialElements :
    Presents ((p.elements G).restrictPoly (defined G bot)) (defined G bot).FullSubcategory :=
  (p.elements G).restrict (defined G bot) (convex_defined G bot hbot)

/-! ### Lifting a word to the defined part

The projection down to `P` is a covering — an element over the source picks the lift — and `bot` is
absorbing, so a word between *defined* elements passes through defined ones only.  The target
element is carried as **data**: that is what makes every statement about the lift homogeneous, and
it is why nothing below is an induction over words. -/

/-- The 0-cell a defined element over a 0-cell of `P` names. -/
def definedPt {x : GenObj P.Gen} (s : G.obj (p.at' x)) (hs : s ≠ bot _) :
    GenObj ((p.elements G).restrictGen (defined G bot)) := ⟨⟨⟨x.as, s⟩, hs⟩⟩

include hbot in
/-- **A word between defined elements lifts.**  Convexity supplies definedness in the middle. -/
theorem exists_definedPath {x y : GenObj P.Gen} (w : Quiver.Path x y)
    {s : G.obj (p.at' x)} {s' : G.obj (p.at' y)} (hw : G.map (p.eval.map w) s = s')
    (hs : s ≠ bot _) (hs' : s' ≠ bot _) :
    ∃ R : Quiver.Path (definedPt G bot p s hs) (definedPt G bot p s' hs'),
      (p.elementsProj G).mapPath
          (((p.elements G).restrictProj (defined G bot)).mapPath R) = w := by
  obtain ⟨R, hR⟩ := p.exists_lift G s w s' hw
  obtain ⟨R', hR'⟩ := exists_restrictPath (p.elements G) (defined G bot)
    (convex_defined G bot hbot) (x := definedPt G bot p s hs) R hs'
  exact ⟨R', (congrArg (fun t => (p.elementsProj G).mapPath t) hR').trans hR⟩

omit hbot in
/-- **…and the lift is unique**, the projection being a covering in both steps. -/
theorem definedPath_ext {A B : GenObj ((p.elements G).restrictGen (defined G bot))}
    {R R' : Quiver.Path A B}
    (h : (p.elementsProj G).mapPath (((p.elements G).restrictProj (defined G bot)).mapPath R)
      = (p.elementsProj G).mapPath
          (((p.elements G).restrictProj (defined G bot)).mapPath R')) : R = R' :=
  haveI := Prefunctor.pathsFunctor_faithful ((p.elements G).restrictProj (defined G bot))
    (restrictProj_star_injective (p.elements G) (defined G bot))
  haveI := Prefunctor.pathsFunctor_faithful (p.elementsProj G) (elementsProj_star_injective p G)
  ((p.elements G).restrictProj (defined G bot)).pathsFunctor.map_injective
    ((p.elementsProj G).pathsFunctor.map_injective h)

/-- **The lift of a word between defined elements.** -/
noncomputable def definedPath {x y : GenObj P.Gen} (w : Quiver.Path x y)
    {s : G.obj (p.at' x)} {s' : G.obj (p.at' y)} (hw : G.map (p.eval.map w) s = s')
    (hs : s ≠ bot _) (hs' : s' ≠ bot _) :
    Quiver.Path (definedPt G bot p s hs) (definedPt G bot p s' hs') :=
  (exists_definedPath G bot hbot p w hw hs hs').choose

@[simp] theorem definedPath_proj {x y : GenObj P.Gen} (w : Quiver.Path x y)
    {s : G.obj (p.at' x)} {s' : G.obj (p.at' y)} (hw : G.map (p.eval.map w) s = s')
    (hs : s ≠ bot _) (hs' : s' ≠ bot _) :
    (p.elementsProj G).mapPath (((p.elements G).restrictProj (defined G bot)).mapPath
        (definedPath G bot hbot p w hw hs hs')) = w :=
  (exists_definedPath G bot hbot p w hw hs hs').choose_spec

end Partial

/-! ## Transporting the defined part along the base

`bot` sits over *every* object, so `CategoryOfElements.pre` is never an equivalence of the whole
categories of elements.  On the defined part it is, as soon as every object carrying a **defined**
element is covered — the hypothesis `isEquivalence_pre` cannot ask for.  The comparison also
absorbs a change of presheaf, so a base functor whose restriction is only *isomorphic* to the
model still works. -/

section Pre

variable {D : Type u₂} [Category.{v₂} D]
  (P : C ⥤ Type t) (bot : ∀ c, P.obj c) (G : D ⥤ C) {Q : D ⥤ Type t} (botQ : ∀ d, Q.obj d)
  (α : G ⋙ P ≅ Q) (hα : ∀ d, α.inv.app d (botQ d) = bot (G.obj d))

include hα in
theorem defined_app_inv {z : D} {y : Q.obj z} (hy : y ≠ botQ z) :
    α.inv.app z y ≠ bot (G.obj z) := fun h =>
  hy ((α.app z).toEquiv.symm.injective (h.trans (hα z).symm))

/-- The comparison on the defined parts: read a defined element of `Q` in `P`, over `G`. -/
def preDefined :
    (defined Q botQ).FullSubcategory ⥤ (defined P bot).FullSubcategory where
  obj z := ⟨⟨G.obj z.obj.1, α.inv.app z.obj.1 z.obj.2⟩,
    defined_app_inv P bot G botQ α hα z.property⟩
  map {z w} f := ObjectProperty.homMk ⟨G.map f.hom.1,
    (NatTrans.naturality_apply α.inv f.hom.1 z.obj.2).symm.trans
      (congrArg (α.inv.app w.obj.1) f.hom.2)⟩
  map_id _ := ObjectProperty.hom_ext _ (Subtype.ext (G.map_id _))
  map_comp _ _ := ObjectProperty.hom_ext _ (Subtype.ext (G.map_comp _ _))

instance preDefined_faithful [G.Faithful] : (preDefined P bot G botQ α hα).Faithful where
  map_injective h := ObjectProperty.hom_ext _
    (Subtype.ext (G.map_injective (congrArg (fun t => t.hom.val) h)))

instance preDefined_full [G.Full] [G.Faithful] : (preDefined P bot G botQ α hα).Full where
  map_surjective {z w} h := by
    refine ⟨ObjectProperty.homMk ⟨G.preimage h.hom.1, ?_⟩,
      ObjectProperty.hom_ext _ (Subtype.ext (G.map_preimage _))⟩
    refine (α.app w.obj.1).toEquiv.symm.injective ?_
    refine ((NatTrans.naturality_apply α.inv (G.preimage h.hom.1) z.obj.2)).trans ?_
    change (G ⋙ P).map (G.preimage h.hom.1) (α.inv.app z.obj.1 z.obj.2) = _
    rw [show (G ⋙ P).map (G.preimage h.hom.1) = P.map h.hom.1 from
      congrArg P.map (G.map_preimage h.hom.1)]
    exact h.hom.2

include hα in
theorem preDefined_essSurj (hbot : ∀ {c c' : C} (g : c ⟶ c'), P.map g (bot c) = bot c')
    (hcov : ∀ (c : C) (x : P.obj c), x ≠ bot c → ∃ d, Nonempty (G.obj d ≅ c)) :
    (preDefined P bot G botQ α hα).EssSurj where
  mem_essImage v := by
    obtain ⟨d, ⟨e⟩⟩ := hcov v.obj.1 v.obj.2 v.property
    have hx : P.map e.inv v.obj.2 ≠ bot (G.obj d) := fun h => v.property (by
      have := congrArg (fun t => P.map e.hom t) h
      simpa only [← Functor.map_comp_apply, e.inv_hom_id, Functor.map_id_apply, hbot] using this)
    have hround : α.inv.app d (α.hom.app d (P.map e.inv v.obj.2)) = P.map e.inv v.obj.2 :=
      (α.app d).toEquiv.symm_apply_apply _
    refine ⟨⟨⟨d, α.hom.app d (P.map e.inv v.obj.2)⟩, fun h => hx ?_⟩,
      ⟨(ObjectProperty.fullyFaithfulι _).preimageIso (CategoryOfElements.isoMk _ _ e ?_)⟩⟩
    · have h : α.hom.app d (P.map e.inv v.obj.2) = botQ d := h
      rw [← hround, h, hα d]
    · change P.map e.hom (α.inv.app d (α.hom.app d (P.map e.inv v.obj.2))) = v.obj.2
      rw [hround, ← Functor.map_comp_apply, e.inv_hom_id, Functor.map_id_apply]

/-- **The defined parts agree**: covering is asked only of the objects that carry a defined
element, and the model presheaf need only be isomorphic to the restriction. -/
noncomputable def preDefinedEquiv [G.Full] [G.Faithful]
    (hbot : ∀ {c c' : C} (g : c ⟶ c'), P.map g (bot c) = bot c')
    (hcov : ∀ (c : C) (x : P.obj c), x ≠ bot c → ∃ d, Nonempty (G.obj d ≅ c)) :
    (defined Q botQ).FullSubcategory ≌ (defined P bot).FullSubcategory :=
  haveI := preDefined_essSurj P bot G botQ α hα hbot hcov
  haveI : (preDefined P bot G botQ α hα).IsEquivalence := { }
  (preDefined P bot G botQ α hα).asEquivalence

end Pre

/-! ## The total case: an honest pullback

`bot` unreachable from the defined part makes it a subfunctor, and then nothing was discarded: the
partial presentation is `Presents.elements` of that subfunctor. -/

section Total

variable (G : C ⥤ Type t) (bot : ∀ c, G.obj c)
  (htot : ∀ {c c' : C} (g : c ⟶ c') (x : G.obj c), x ≠ bot c → G.map g x ≠ bot c')

include htot in
/-- The defined part, as an honest presheaf. -/
def definedFunctor : C ⥤ Type t where
  obj c := {x : G.obj c // x ≠ bot c}
  map g := ↾fun x => ⟨G.map g x.1, htot g x.1 x.2⟩
  map_id c := by ext x; exact G.map_id_apply c x.1
  map_comp f g := by ext x; exact G.map_comp_apply f g x.1

include htot in
/-- **With `bot` unreachable the defined part is a genuine category of elements**, so the partial
presentation is the honest pullback. -/
def definedEquiv :
    (defined G bot).FullSubcategory ≌ (definedFunctor G bot htot).Elements where
  functor :=
    { obj := fun z => ⟨z.obj.1, z.obj.2, z.property⟩
      map := fun f => ⟨f.hom.val, Subtype.ext f.hom.property⟩
      map_id := fun _ => Subtype.ext rfl
      map_comp := fun _ _ => Subtype.ext rfl }
  inverse :=
    { obj := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      map := fun f => ObjectProperty.homMk ⟨f.val, congrArg Subtype.val f.property⟩
      map_id := fun _ => ObjectProperty.hom_ext _ rfl
      map_comp := fun _ _ => ObjectProperty.hom_ext _ rfl }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp _ := Subtype.ext (Category.comp_id _)

end Total

/-! ## A map of partial presheaves

`partialElements` is functorial in the presheaf, and only **laxly** so: a family `η` need not
commute with the action everywhere, only where both sides are defined.  That is exactly what a
morphism of polygraphs asks — a 1-cell is a *defined* step — and it is the general reason a family
of partial actions gives a functor even when it gives no natural transformation. -/

section PartialMap

variable {P : Polygraph.{w, u', w₂}} {p : Presents P C} {G G' : C ⥤ Type t}
  {bot : ∀ c, G.obj c} {bot' : ∀ c, G'.obj c} {η : ∀ c, G.obj c → G'.obj c}

/-- **A lax map of partial presheaves**: `η` carries defined elements to defined elements, and
commutes with the action wherever both sides are defined.  That is what a morphism of polygraphs
asks — a 1-cell is a *defined* step — and it is the general reason a family of partial actions
gives a functor even when it gives no natural transformation. -/
structure PartialFam (G G' : C ⥤ Type t) (bot : ∀ c, G.obj c) (bot' : ∀ c, G'.obj c)
    (η : ∀ c, G.obj c → G'.obj c) : Prop where
  /-- a defined element stays defined -/
  ne_bot : ∀ (c : C) (x : G.obj c), x ≠ bot c → η c x ≠ bot' c
  /-- …and a defined step commutes -/
  lax : ∀ {c c' : C} (g : c ⟶ c') (x : G.obj c), x ≠ bot c → G.map g x ≠ bot c' →
    G'.map g (η c x) = η c' (G.map g x)

/-- The 0-cells, carried across. -/
def famV (p : Presents P C) {G G' : C ⥤ Type t} {bot : ∀ c, G.obj c} {bot' : ∀ c, G'.obj c}
    (η : ∀ c, G.obj c → G'.obj c) (h : PartialFam G G' bot bot' η)
    (a : (p.elements G).restrictV (defined G bot)) :
    (p.elements G').restrictV (defined G' bot') :=
  ⟨⟨a.1.1, η _ a.1.2⟩, h.ne_bot _ a.1.2 a.2⟩

/-- **A defined step is carried across** — the whole content of `lax`. -/
theorem fam_step (p : Presents P C) {G G' : C ⥤ Type t} {bot : ∀ c, G.obj c}
    {bot' : ∀ c, G'.obj c} (η : ∀ c, G.obj c → G'.obj c) (h : PartialFam G G' bot bot' η)
    {x y : GenObj ((p.elements G).restrictGen (defined G bot))} (e : x ⟶ y) :
    G'.map (p.arrow e.1) (η _ x.as.1.2) = η _ y.as.1.2 :=
  (h.lax (p.arrow e.1) x.as.1.2 x.as.2 (by rw [e.2]; exact y.as.2)).trans (congrArg _ e.2)

/-- The generating quiver, carried across. -/
def famPre (p : Presents P C) {G G' : C ⥤ Type t} {bot : ∀ c, G.obj c} {bot' : ∀ c, G'.obj c}
    (η : ∀ c, G.obj c → G'.obj c) (h : PartialFam G G' bot bot' η) :
    GenObj ((p.elements G).restrictGen (defined G bot)) ⥤q
      GenObj ((p.elements G').restrictGen (defined G' bot')) where
  obj a := ⟨famV p η h a.as⟩
  map {_ _} e := ⟨e.1, fam_step p η h e⟩

/-- **The carried word projects to the projection of the word** — the two composites of quiver maps
down to `P` are the same map. -/
theorem famPre_proj (p : Presents P C) {G G' : C ⥤ Type t} {bot : ∀ c, G.obj c}
    {bot' : ∀ c, G'.obj c} (η : ∀ c, G.obj c → G'.obj c) (h : PartialFam G G' bot bot' η)
    {x y : GenObj ((p.elements G).restrictGen (defined G bot))}
    (u : Quiver.Path x y) :
    (p.elementsProj G').mapPath (((p.elements G').restrictProj (defined G' bot')).mapPath
        ((famPre p η h).mapPath u))
      = (p.elementsProj G).mapPath (((p.elements G).restrictProj (defined G bot)).mapPath u) := by
  induction u with
  | nil => rfl
  | cons u e ih =>
      change Quiver.Path.cons ((p.elementsProj G').mapPath
          (((p.elements G').restrictProj (defined G' bot')).mapPath ((famPre p η h).mapPath u))) _
        = Quiver.Path.cons ((p.elementsProj G).mapPath
          (((p.elements G).restrictProj (defined G bot)).mapPath u)) _
      rw [ih]
      rfl

/-- **Carrying a word across commutes with lifting it** — both sides lift `w` from the same 0-cell,
and a lift is unique.  This is the whole of the laxness at the level of *words*: no induction, and
no transport, because `famV` moves only the element a 0-cell carries. -/
theorem famPre_mapPath_definedPath (p : Presents P C) {G G' : C ⥤ Type t}
    {bot : ∀ c, G.obj c} {bot' : ∀ c, G'.obj c}
    (hbot : ∀ {c c' : C} (g : c ⟶ c'), G.map g (bot c) = bot c')
    (hbot' : ∀ {c c' : C} (g : c ⟶ c'), G'.map g (bot' c) = bot' c')
    (η : ∀ c, G.obj c → G'.obj c) (h : PartialFam G G' bot bot' η)
    {x y : GenObj P.Gen} (w : Quiver.Path x y)
    {s : G.obj (p.at' x)} {s' : G.obj (p.at' y)} (hw : G.map (p.eval.map w) s = s')
    (hs : s ≠ bot _) (hs' : s' ≠ bot _) :
    (famPre p η h).mapPath (definedPath G bot hbot p w hw hs hs')
      = definedPath G' bot' hbot' p w
          ((h.lax (p.eval.map w) s hs (by rw [hw]; exact hs')).trans (congrArg (η _) hw))
          (h.ne_bot _ s hs) (h.ne_bot _ s' hs') :=
  definedPath_ext G' bot' p
    ((famPre_proj p η h _).trans
      ((definedPath_proj G bot hbot p w hw hs hs').trans
        (definedPath_proj G' bot' hbot' p w _ _ _).symm))

/-- **The lift of a lax map of partial presheaves.**  Every cell is the one below it, with its
boundary words carried across; only the 0-cells move. -/
def partialElementsMap (p : Presents P C) {G G' : C ⥤ Type t} {bot : ∀ c, G.obj c}
    {bot' : ∀ c, G'.obj c} (η : ∀ c, G.obj c → G'.obj c) (h : PartialFam G G' bot bot' η) :
    Polygraph.Hom ((p.elements G).restrictPoly (defined G bot))
      ((p.elements G').restrictPoly (defined G' bot')) where
  pre := famPre p η h
  two α :=
    { src := (famPre p η h).mapPath α.src
      tgt := (famPre p η h).mapPath α.tgt
      cell :=
        { src := ((p.elements G').restrictProj (defined G' bot')).mapPath
            ((famPre p η h).mapPath α.src)
          tgt := ((p.elements G').restrictProj (defined G' bot')).mapPath
            ((famPre p η h).mapPath α.tgt)
          cell := α.cell.cell
          src_eq := (famPre_proj p η h α.src).trans
            ((congrArg (p.elementsProj G).mapPath α.src_eq).trans α.cell.src_eq)
          tgt_eq := (famPre_proj p η h α.tgt).trans
            ((congrArg (p.elementsProj G).mapPath α.tgt_eq).trans α.cell.tgt_eq) }
      src_eq := rfl
      tgt_eq := rfl }
  src_two _ := rfl
  tgt_two _ := rfl

/-- **The lift depends only on the family** — the laxness is a `Prop`. -/
theorem partialElementsMap_congr (p : Presents P C) {G G' : C ⥤ Type t} {bot : ∀ c, G.obj c}
    {bot' : ∀ c, G'.obj c} {η η' : ∀ c, G.obj c → G'.obj c} (h : PartialFam G G' bot bot' η)
    (h' : PartialFam G G' bot bot' η') (hη : η = η') :
    partialElementsMap p η h = partialElementsMap p η' h' := by subst hη; rfl

/-- The identity family. -/
theorem PartialFam.id (G : C ⥤ Type t) (bot : ∀ c, G.obj c) :
    PartialFam G G bot bot (fun _ => _root_.id) :=
  ⟨fun _ _ hx => hx, fun _ _ _ _ => rfl⟩

/-- …and the composite of two. -/
theorem PartialFam.comp {G G' G'' : C ⥤ Type t} {bot : ∀ c, G.obj c} {bot' : ∀ c, G'.obj c}
    {bot'' : ∀ c, G''.obj c} {η : ∀ c, G.obj c → G'.obj c} {η' : ∀ c, G'.obj c → G''.obj c}
    (h : PartialFam G G' bot bot' η) (h' : PartialFam G' G'' bot' bot'' η') :
    PartialFam G G'' bot bot'' (fun c x => η' c (η c x)) :=
  ⟨fun c x hx => h'.ne_bot c _ (h.ne_bot c x hx),
    fun {c c'} g x hx hgx => ((h'.lax g (η c x) (h.ne_bot c x hx)
      (by rw [h.lax g x hx hgx]; exact h.ne_bot c' _ hgx)).trans
        (congrArg (η' c') (h.lax g x hx hgx)))⟩

/-- **The identity family lifts to the identity.** -/
theorem partialElementsMap_id (p : Presents P C) (G : C ⥤ Type t) (bot : ∀ c, G.obj c) :
    partialElementsMap p (fun _ => _root_.id) (PartialFam.id G bot)
      = Polygraph.Hom.id ((p.elements G).restrictPoly (defined G bot)) :=
  Polygraph.Hom.ext' rfl fun α => heq_of_eq (Polygraph.ComapRel.ext
    (Prefunctor.mapPath_id _) (Prefunctor.mapPath_id _)
    (Polygraph.ComapRel.ext
      ((congrArg _ (Prefunctor.mapPath_id α.src)).trans α.src_eq)
      ((congrArg _ (Prefunctor.mapPath_id α.tgt)).trans α.tgt_eq) rfl))

/-- **…and a composite to the composite.** -/
theorem partialElementsMap_comp (p : Presents P C) {G G' G'' : C ⥤ Type t} {bot : ∀ c, G.obj c}
    {bot' : ∀ c, G'.obj c} {bot'' : ∀ c, G''.obj c} {η : ∀ c, G.obj c → G'.obj c}
    {η' : ∀ c, G'.obj c → G''.obj c} (h : PartialFam G G' bot bot' η)
    (h' : PartialFam G' G'' bot' bot'' η') :
    partialElementsMap p (fun c x => η' c (η c x)) (h.comp h')
      = Polygraph.Hom.comp (partialElementsMap p η h) (partialElementsMap p η' h') := by
  refine Polygraph.Hom.ext' rfl fun α => heq_of_eq (Polygraph.ComapRel.ext ?_ ?_ ?_)
  · exact Prefunctor.mapPath_comp_apply (F := famPre p η h) (G := famPre p η' h') α.src
  · exact Prefunctor.mapPath_comp_apply (F := famPre p η h) (G := famPre p η' h') α.tgt
  · refine Polygraph.ComapRel.ext ?_ ?_ rfl
    · exact congrArg (((p.elements G'').restrictProj (defined G'' bot'')).mapPath)
        (Prefunctor.mapPath_comp_apply (F := famPre p η h) (G := famPre p η' h') α.src)
    · exact congrArg (((p.elements G'').restrictProj (defined G'' bot'')).mapPath)
        (Prefunctor.mapPath_comp_apply (F := famPre p η h) (G := famPre p η' h') α.tgt)

end PartialMap

end Presents

end CategoryTheory
