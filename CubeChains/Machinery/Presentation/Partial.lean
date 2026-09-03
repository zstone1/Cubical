import CubeChains.Machinery.Presentation.Elements
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Machinery/Presentation/Partial — presenting a *partial* category of elements

A functor with **at most one** lift of each arrow at each source is classified not by a presheaf of
sets but by one of *partial* functions — equivalently, since `Par ≃ Set⋆` and
`[Cᵒᵖ, Set⋆] = 1/PSh C`,
by an ordinary presheaf `G` together with a global section `bot`.  The category is then `∫G` minus
that section.

So nothing new has to be presented: `Presents.elements` presents `∫G`, and `restrict` cuts it
down.  The cut is free because `bot` is **absorbing** — a word reaching `bot` stays there, so a word
between defined objects never passes through it.  That is `Convex`, and it is the only hypothesis
`restrict` takes.

`bot` unreachable from the defined part is the total case: then the defined part is `∫` of an
honest presheaf (`definedEquiv`), and the partial presentation is the honest pullback.
-/

universe t w v u' u

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

namespace Presents

/-! ## Restricting a presentation to a convex full subcategory -/

section Restrict

variable {P : Polygraph.{w, u'}} (p : Presents P C) (Q : ObjectProperty C)

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
  P.comapIncl (p.restrictGen Q) (p.restrictProj Q)

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
  P.comapIncl_faithful _ (p.restrictProj Q) (restrictProj_star_injective p Q)

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
    (fun h => ObjectProperty.hom_ext _
      ((hom_eval_restrict p Q _).trans ((p.sound h).trans (hom_eval_restrict p Q _).symm)))
    (fun {x y} {R₁ R₂} h => by
      refine (HomRel.gen_iff_functor_map_eq _ _ _).mp
        (gen_pullbackRel (p.restrictIncl Q) P.rel
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

/-! ## A presheaf given by generators and relations

The dual of a polygraph itself, and what keeps a client from ever naming an object of `C` outside
the 0-cells: a set at each 0-cell, a map for each 1-cell, checked against the 2-cells.
`Presents.elements` then consumes the presheaf it induces. -/

namespace Polygraph

/-- The action of a generating word, on raw data — `Action.sound` needs it before the structure
exists. -/
def actPathOf {P : Polygraph.{w, u'}} (fib : P.V → Type t)
    (act : ∀ {x y : P.V}, P.Gen x y → fib x → fib y) :
    ∀ {x y : GenObj P.Gen}, Quiver.Path x y → fib x.as → fib y.as :=
  fun {x _} R => Quiver.Path.rec (motive := fun z _ => fib x.as → fib z.as) id
    (fun _ e ih => act e ∘ ih) R

/-- **An action of a polygraph**: a set at each 0-cell and a map for each 1-cell, agreeing on
related words.  Equivalently a presheaf on any category it presents (`toFunctor`). -/
structure Action (P : Polygraph.{w, u'}) where
  /-- the set at a 0-cell -/
  fib : P.V → Type t
  /-- the map a 1-cell acts by -/
  act {x y : P.V} : P.Gen x y → fib x → fib y
  /-- related words act equally -/
  sound {x y : GenObj P.Gen} {R S : Quiver.Path x y} :
    P.rel R S → actPathOf fib @act R = actPathOf fib @act S

namespace Action

variable {P : Polygraph.{w, u'}} (a : P.Action)

/-- The action of a generating word. -/
abbrev path {x y : GenObj P.Gen} (R : Quiver.Path x y) : a.fib x.as → a.fib y.as :=
  actPathOf a.fib @a.act R

@[simp] theorem path_nil {x : GenObj P.Gen} :
    a.path (Quiver.Path.nil (a := x)) = id := rfl

@[simp] theorem path_cons {x y z : GenObj P.Gen} (R : Quiver.Path x y) (e : y ⟶ z) :
    a.path (R.cons e) = a.act e ∘ a.path R := rfl

theorem path_comp {x y z : GenObj P.Gen} (R : Quiver.Path x y) (S : Quiver.Path y z) :
    a.path (R.comp S) = a.path S ∘ a.path R := by
  induction S with
  | nil => rfl
  | cons S e ih => rw [Quiver.Path.comp_cons, path_cons, path_cons, ih]; rfl

/-- The presheaf on generating words. -/
def paths : P.Word ⥤ Type t where
  obj x := a.fib x.as
  map R := ↾(a.path R)
  map_id _ := rfl
  map_comp R S := by ext u; exact congrFun (a.path_comp R S) u

/-- …on the presented category. -/
def quot : P.presented ⥤ Type t :=
  Quotient.lift P.rel a.paths fun _ _ _ _ h => by ext u; exact congrFun (a.sound h) u

/-- **The presheaf on `C` an action presents.** -/
noncomputable def toFunctor (p : Presents P C) : C ⥤ Type t := p.equiv.inverse ⋙ a.quot

/-- …with the promised value at a 0-cell. -/
noncomputable def objIso (p : Presents P C) (x : GenObj P.Gen) :
    (a.toFunctor p).obj (p.at' x) ≅ a.fib x.as :=
  a.quot.mapIso (p.equiv.unitIso.app ⟨x⟩).symm

end Action

end Polygraph

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

variable {P : Polygraph.{w, u'}} (p : Presents P C)

include hbot in
/-- **A presentation of `C` presents the defined part of `∫G`** — 0-cells the defined elements,
1-cells the base's generators *where they are defined*, 2-cells its relations there. -/
def partialElements :
    Presents ((p.elements G).restrictPoly (defined G bot)) (defined G bot).FullSubcategory :=
  (p.elements G).restrict (defined G bot) (convex_defined G bot hbot)

end Partial

/-! ## The client interface: a partial action

`Option`-valued generator data, and nothing else.  `none` is the absorbing section, so the whole
chain — presheaf, elements, restriction — runs with no object of `C` outside the 0-cells named. -/

section OptionAction

variable {P : Polygraph.{w, u'}} (φ : P.V → Type t)
  (pact : ∀ {x y : P.V}, P.Gen x y → φ x → Option (φ y))
  (hsound : ∀ {x y : GenObj P.Gen} {R S : Quiver.Path x y}, P.rel R S →
    Polygraph.actPathOf (fun x => Option (φ x)) (fun e o => o.bind (pact e)) R
      = Polygraph.actPathOf (fun x => Option (φ x)) (fun e o => o.bind (pact e)) S)

/-- A **partial action**: each 1-cell acts where it is defined. -/
def optionAction : P.Action where
  fib x := Option (φ x)
  act e o := o.bind (pact e)
  sound := hsound

theorem optionAction_path_none {x y : GenObj P.Gen} (R : Quiver.Path x y) :
    (optionAction φ @pact hsound).path R none = none := by
  induction R with
  | nil => rfl
  | cons R e ih => rw [Polygraph.Action.path_cons, Function.comp_apply, ih]; rfl

variable (p : Presents P C)

/-- The undefined point, at every object of `C`. -/
noncomputable def optionBot (c : C) : ((optionAction φ @pact hsound).toFunctor p).obj c := none

theorem optionBot_absorbing {c c' : C} (g : c ⟶ c') :
    ((optionAction φ @pact hsound).toFunctor p).map g (optionBot φ @pact hsound p c)
      = optionBot φ @pact hsound p c' := by
  obtain ⟨R, hR⟩ := (P.quot).map_surjective ((p.equiv.inverse).map g)
  change (optionAction φ @pact hsound).quot.map ((p.equiv.inverse).map g) none = none
  rw [← hR]
  exact optionAction_path_none φ @pact hsound R

/-- **A partial action of a presentation presents its defined part** — 0-cells the defined points,
1-cells the base's generators where they act, 2-cells the base's relations there. -/
noncomputable def partialAction :
    Presents ((p.elements ((optionAction φ @pact hsound).toFunctor p)).restrictPoly
        (defined ((optionAction φ @pact hsound).toFunctor p) (optionBot φ @pact hsound p)))
      (defined ((optionAction φ @pact hsound).toFunctor p)
        (optionBot φ @pact hsound p)).FullSubcategory :=
  partialElements _ _ (fun {_ _} g => optionBot_absorbing φ @pact hsound p g) p

end OptionAction


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
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

end Total

end Presents

end CategoryTheory
