import CubeChains.Machinery.Presentation.Restrict

/-!
# Machinery/Presentation/Partial — presenting a *partial* category of elements

A functor with **at most one** lift of each arrow is classified by a presheaf of partial functions
— equivalently, since `Par ≃ Set⋆`, by a presheaf `G` with a global section `bot`.  The category is
`∫G` minus that section, so nothing new is presented: `Presents.elements` presents `∫G`, and
`Presents.restrict` cuts it down freely because `bot` is **absorbing**, and absorbing is convex.
`bot` unreachable is the total case, where the defined part is `∫` of an honest presheaf
(`definedEquiv`).
-/

universe t w₂ w v u' u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- **An absorbing complement is convex**: if `¬Q` is closed under arrows out of it, a word between
`Q`-objects cannot leave `Q`. -/
theorem ObjectProperty.convex_of_absorbing {Q : ObjectProperty C}
    (h : ∀ {x y : C}, ¬ Q x → (x ⟶ y) → ¬ Q y) : Q.Convex :=
  fun _ hb _ g => not_not.mp fun hz => h hz g hb

namespace Presents

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

/-! ## The total case: an honest pullback

`bot` unreachable from the defined part makes it a subfunctor, and then nothing was discarded: the
partial presentation is `Presents.elements` of that subfunctor. -/

section Total

variable (htot : ∀ {c c' : C} (g : c ⟶ c') (x : G.obj c), x ≠ bot c → G.map g x ≠ bot c')

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

end Presents

end CategoryTheory
