import CubeChains.Machinery.Presentation.Elements
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Machinery/Presentation/Partial — presenting a *partial* category of elements

A functor with **at most one** lift of each arrow at each source is classified not by a presheaf of
sets but by one of *partial* functions — equivalently, since `Par ≃ Set⋆` and
`[Cᵒᵖ, Set⋆] = 1/PSh C`,
by an ordinary presheaf `G` together with a global section `bot`.  The category is then `∫G` minus
that section.

So nothing new has to be presented: `Presentation.elements` presents `∫G`, and `restrict` cuts it
down.  The cut is free because `bot` is **absorbing** — a word reaching `bot` stays there, so a word
between defined objects never passes through it.  That is `Convex`, and it is the only hypothesis
`restrict` takes.

`bot` unreachable from the defined part is the total case: then the defined part is `∫` of an
honest presheaf (`definedEquiv`), and the partial presentation is the honest pullback.
-/

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-! ## Convex object properties -/

/-- `P` is **convex**: an object through which an arrow between `P`-objects factors is itself a
`P`-object.  The complement of a co-sieve is convex, and that is the only case used. -/
def ObjectProperty.Convex (P : ObjectProperty C) : Prop :=
  ∀ {a b z : C}, P a → P b → (a ⟶ z) → (z ⟶ b) → P z

/-- **An absorbing complement is convex**: if `¬P` is closed under arrows out of it, a word between
`P`-objects cannot leave `P`. -/
theorem ObjectProperty.convex_of_absorbing {P : ObjectProperty C}
    (h : ∀ {x y : C}, ¬ P x → (x ⟶ y) → ¬ P y) : P.Convex :=
  fun _ hb _ g => not_not.mp fun hz => h hz g hb

namespace Presentation

/-! ## Restricting a presentation to a convex full subcategory -/

section Restrict

variable (p : Presentation C) (P : ObjectProperty C)

/-- The cells of `p` that live at `P`-objects. -/
def restrictGens : Gens P.FullSubcategory where
  V := {a : p.V // P (p.ob a)}
  ob a := ⟨p.ob a.1, a.2⟩
  Gen x y := p.Gen x.1 y.1
  arrow g := ObjectProperty.homMk (p.arrow g)

/-- The restricted generating quiver includes into the full one. -/
def restrictProj : GenObj (p.restrictGens P).Gen ⥤q GenObj p.Gen where
  obj x := ⟨x.as.1⟩
  map g := g

/-- **A restricted word is the word it includes to**, read in `C`. -/
theorem hom_eval_restrict {x y : GenObj (p.restrictGens P).Gen} (R : Quiver.Path x y) :
    ((p.restrictGens P).eval.map R).hom = p.toGens.eval.map ((p.restrictProj P).mapPath R) := by
  induction R with
  | nil => rfl
  | cons R e ih =>
      rw [Gens.eval_cons, Prefunctor.mapPath_cons, Gens.eval_cons, ← ih]
      rfl

/-- Words of the restricted quiver, as words of the full one. -/
def restrictIncl : Paths (GenObj (p.restrictGens P).Gen) ⥤ Paths (GenObj p.Gen) where
  obj x := (p.restrictProj P).obj x
  map R := (p.restrictProj P).mapPath R
  map_id _ := rfl
  map_comp _ _ := Prefunctor.mapPath_comp _ _ _

theorem restrictProj_star_injective (x : GenObj (p.restrictGens P).Gen) :
    Function.Injective ((p.restrictProj P).star x) := by
  rintro ⟨⟨⟨a₁, h₁⟩⟩, e₁⟩ ⟨⟨⟨a₂, h₂⟩⟩, e₂⟩ h
  obtain ⟨ha, he⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : a₁ = a₂ := congrArg GenObj.as ha
  obtain rfl : e₁ = e₂ := eq_of_heq he
  rfl

instance : (p.restrictIncl P).Faithful where
  map_injective {x y} {R₁ R₂} h := by
    have hs : (p.restrictProj P).pathStar x ⟨y, R₁⟩ = (p.restrictProj P).pathStar x ⟨y, R₂⟩ :=
      Sigma.ext rfl (heq_of_eq h)
    exact eq_of_heq (Sigma.mk.inj_iff.mp
      ((p.restrictProj P).pathStar_injective (restrictProj_star_injective p P) x hs)).2

variable (hconv : P.Convex)

include hconv in
/-- **A word between `P`-objects is a restricted word.**  Convexity supplies the `P`-ness of each
object it passes through, one cons at a time. -/
theorem exists_restrictPath {x : GenObj (p.restrictGens P).Gen} :
    ∀ {z : GenObj p.Gen} (R : Quiver.Path ((p.restrictProj P).obj x) z) (hz : P (p.ob z.as)),
      ∃ R' : Quiver.Path x ⟨⟨z.as, hz⟩⟩, (p.restrictProj P).mapPath R' = R := by
  intro z R
  induction R with
  | nil => exact fun _ => ⟨Quiver.Path.nil, rfl⟩
  | @cons y z R e ih =>
      intro hz
      have hy : P (p.ob y.as) :=
        hconv x.as.2 hz (p.toGens.eval.map R) (p.toGens.eval.map e.toPath)
      obtain ⟨R', hR'⟩ := ih hy
      exact ⟨R'.cons e, by rw [Prefunctor.mapPath_cons, hR']; rfl⟩

include hconv in
theorem restrictIncl_full : (p.restrictIncl P).Full where
  map_surjective {x y} f := by
    obtain ⟨⟨b, hb⟩⟩ := y
    obtain ⟨R, hR⟩ := exists_restrictPath p P hconv f hb
    exact ⟨R, hR⟩

include hconv in
theorem exists_restrict_mid {x y : GenObj (p.restrictGens P).Gen} {z : Paths (GenObj p.Gen)}
    (u : (p.restrictIncl P).obj x ⟶ z) (v : z ⟶ (p.restrictIncl P).obj y) :
    ∃ z' : GenObj (p.restrictGens P).Gen, (p.restrictIncl P).obj z' = z :=
  ⟨⟨⟨(z : GenObj p.Gen).as, hconv x.as.2 y.as.2 (p.toGens.eval.map u) (p.toGens.eval.map v)⟩⟩, rfl⟩

/-- **A presentation restricts to a convex full subcategory**, cells and relations unchanged apart
from being taken at `P`-objects only. -/
def restrict : Presentation P.FullSubcategory where
  toGens := p.restrictGens P
  rel := (p.restrictIncl P).pullbackRel p.rel
  sound h := ObjectProperty.hom_ext _
    ((hom_eval_restrict p P _).trans ((p.sound h).trans (hom_eval_restrict p P _).symm))
  spans {x y} f := by
    obtain ⟨R, hR⟩ := p.spans (x := (p.restrictProj P).obj x) (y := (p.restrictProj P).obj y) f.hom
    obtain ⟨R', hR'⟩ := exists_restrictPath p P hconv R y.as.2
    exact ⟨R', ObjectProperty.hom_ext _
      ((hom_eval_restrict p P R').trans (hR' ▸ hR))⟩
  complete {x y} {R₁ R₂} h := by
    haveI := restrictIncl_full p P hconv
    refine (HomRel.gen_iff_functor_map_eq _ _ _).mp
      (gen_pullbackRel (p.restrictIncl P) p.rel
        (fun u v => exists_restrict_mid p P hconv u v) ?_)
    exact (HomRel.gen_iff_functor_map_eq p.rel _ _).mpr
      (p.complete ((hom_eval_restrict p P R₁).symm.trans
        ((congrArg InducedCategory.Hom.hom h).trans (hom_eval_restrict p P R₂))))
  covers c := by
    obtain ⟨x, ⟨i⟩⟩ := p.covers c.obj
    have hx : P (p.toGens.at' x) := hconv c.property c.property i.inv i.hom
    exact ⟨⟨⟨x.as, hx⟩⟩, ⟨{ hom := ObjectProperty.homMk i.hom
                            inv := ObjectProperty.homMk i.inv
                            hom_inv_id := ObjectProperty.hom_ext _ (by simp)
                            inv_hom_id := ObjectProperty.hom_ext _ (by simp) }⟩⟩

end Restrict

/-! ## A presheaf given by generators and relations

The dual of `Presentation` itself, and what keeps a client from ever naming an object of `C`
outside the 0-cells: a set at each 0-cell, a map for each 1-cell, checked against the 2-cells.
`Presentation.elements` then consumes the presheaf it induces. -/

section OfAction

/-- The action of a generating word, on raw data — `Action.sound` needs it before the structure
exists. -/
def actPathOf {p : Presentation C} (fib : p.V → Type w)
    (act : ∀ {x y : p.V}, p.Gen x y → fib x → fib y) :
    ∀ {x y : GenObj p.Gen}, Quiver.Path x y → fib x.as → fib y.as :=
  fun {x _} R => Quiver.Path.rec (motive := fun z _ => fib x.as → fib z.as) id
    (fun _ e ih => act e ∘ ih) R

/-- **An action of a presentation**: a set at each 0-cell and a map for each 1-cell, agreeing on
related words.  Equivalently a presheaf on `C` (`toFunctor`), presented. -/
structure Action (p : Presentation C) where
  /-- the set at a 0-cell -/
  fib : p.V → Type w
  /-- the map a 1-cell acts by -/
  act {x y : p.V} : p.Gen x y → fib x → fib y
  /-- related words act equally -/
  sound {x y : GenObj p.Gen} {R S : Quiver.Path x y} :
    p.rel R S → actPathOf fib @act R = actPathOf fib @act S

namespace Action

variable {p : Presentation C} (a : p.Action)

/-- The action of a generating word. -/
abbrev path {x y : GenObj p.Gen} (R : Quiver.Path x y) : a.fib x.as → a.fib y.as :=
  actPathOf a.fib @a.act R

@[simp] theorem path_nil {x : GenObj p.Gen} :
    a.path (Quiver.Path.nil (a := x)) = id := rfl

@[simp] theorem path_cons {x y z : GenObj p.Gen} (R : Quiver.Path x y) (e : y ⟶ z) :
    a.path (R.cons e) = a.act e ∘ a.path R := rfl

theorem path_comp {x y z : GenObj p.Gen} (R : Quiver.Path x y) (S : Quiver.Path y z) :
    a.path (R.comp S) = a.path S ∘ a.path R := by
  induction S with
  | nil => rfl
  | cons S e ih => rw [Quiver.Path.comp_cons, path_cons, path_cons, ih]; rfl

/-- The presheaf on generating words. -/
def paths : Paths (GenObj p.Gen) ⥤ Type w where
  obj x := a.fib x.as
  map R := ↾(a.path R)
  map_id _ := rfl
  map_comp R S := by ext t; exact congrFun (a.path_comp R S) t

/-- …on the quotient. -/
def quot : p.Quot ⥤ Type w :=
  Quotient.lift p.rel a.paths fun _ _ _ _ h => by ext t; exact congrFun (a.sound h) t

/-- **The presheaf on `C` an action presents.** -/
noncomputable def toFunctor : C ⥤ Type w := p.equiv.inverse ⋙ a.quot

/-- …with the promised value at a 0-cell. -/
noncomputable def objIso (x : GenObj p.Gen) : a.toFunctor.obj (p.toGens.at' x) ≅ a.fib x.as :=
  a.quot.mapIso (p.equiv.unitIso.app (p.obj x)).symm

end Action

end OfAction


/-! ## The defined part of a partial presheaf -/

section Partial

variable (G : C ⥤ Type w) (bot : ∀ c, G.obj c)
  (hbot : ∀ {c c' : C} (g : c ⟶ c'), G.map g (bot c) = bot c')

/-- The elements of `G` away from the chosen global section — the *defined* part of the partial
presheaf that `(G, bot)` is. -/
def defined : ObjectProperty G.Elements := fun z => z.2 ≠ bot z.1

include hbot in
/-- **`bot` is absorbing**, so the defined part is convex. -/
theorem convex_defined : (defined G bot).Convex := by
  refine ObjectProperty.convex_of_absorbing (P := defined G bot) ?_
  intro z z' hz f h
  exact h ((f.property.symm.trans (congrArg (fun t => (G.map f.val) t) (not_not.mp hz))).trans
    (hbot f.val))

include hbot in
/-- **A presentation of `C` presents the defined part of `∫G`** — 0-cells the defined elements,
1-cells the base's generators *where they are defined*, 2-cells its relations there. -/
def partialElements (p : Presentation C) : Presentation (defined G bot).FullSubcategory :=
  (p.elements G).restrict (defined G bot) (convex_defined G bot hbot)

end Partial

/-! ## The client interface: a partial action

`Option`-valued generator data, and nothing else.  `none` is the absorbing section, so the whole
chain — presheaf, elements, restriction — runs with no object of `C` outside the 0-cells named. -/

section OptionAction

variable {p : Presentation C} (φ : p.V → Type w)
  (pact : ∀ {x y : p.V}, p.Gen x y → φ x → Option (φ y))
  (hsound : ∀ {x y : GenObj p.Gen} {R S : Quiver.Path x y}, p.rel R S →
    actPathOf (fun x => Option (φ x)) (fun e o => o.bind (pact e)) R
      = actPathOf (fun x => Option (φ x)) (fun e o => o.bind (pact e)) S)

/-- A **partial action**: each 1-cell acts where it is defined. -/
def optionAction : p.Action where
  fib x := Option (φ x)
  act e o := o.bind (pact e)
  sound := hsound

theorem optionAction_path_none {x y : GenObj p.Gen} (R : Quiver.Path x y) :
    (optionAction φ @pact hsound).path R none = none := by
  induction R with
  | nil => rfl
  | cons R e ih => rw [Action.path_cons, Function.comp_apply, ih]; rfl

/-- The undefined point, at every object of `C`. -/
noncomputable def optionBot (c : C) : (optionAction φ @pact hsound).toFunctor.obj c := none

theorem optionBot_absorbing {c c' : C} (g : c ⟶ c') :
    (optionAction φ @pact hsound).toFunctor.map g (optionBot φ @pact hsound c)
      = optionBot φ @pact hsound c' := by
  obtain ⟨R, hR⟩ := (Quotient.functor p.rel).map_surjective
    ((p.equiv.inverse).map g)
  change (optionAction φ @pact hsound).quot.map ((p.equiv.inverse).map g) none = none
  rw [← hR]
  exact optionAction_path_none φ @pact hsound R

/-- **A partial action of a presentation presents its defined part** — 0-cells the defined points,
1-cells the base's generators where they act, 2-cells the base's relations there. -/
noncomputable def partialAction :
    Presentation (defined (optionAction φ @pact hsound).toFunctor
      (optionBot φ @pact hsound)).FullSubcategory :=
  partialElements _ _ (fun {_ _} g => optionBot_absorbing φ @pact hsound g) p

end OptionAction


/-! ## The total case: an honest pullback

`bot` unreachable from the defined part makes it a subfunctor, and then nothing was discarded: the
partial presentation is `Presentation.elements` of that subfunctor. -/

section Total

variable (G : C ⥤ Type w) (bot : ∀ c, G.obj c)
  (htot : ∀ {c c' : C} (g : c ⟶ c') (x : G.obj c), x ≠ bot c → G.map g x ≠ bot c')

include htot in
/-- The defined part, as an honest presheaf. -/
def definedFunctor : C ⥤ Type w where
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
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

end Total

end Presentation

end CategoryTheory
