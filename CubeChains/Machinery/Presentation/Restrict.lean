import CubeChains.Machinery.Presentation.Elements
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Machinery/Presentation/Restrict — a presentation cut down to a convex full subcategory

`Q` is **convex** when an object through which an arrow between `Q`-objects factors is again a
`Q`-object.  That is exactly what lets a presentation restrict with its cells untouched: a word
between `Q`-objects passes through `Q`-objects only, so `Q.FullSubcategory` is presented by `P`'s
own generators and relations taken at `Q`-objects (`restrict`).

Convexity forces closure under isomorphism (`Convex.respectsIso`), so `restrict` never cuts down
to a skeleton.
-/

universe w₂ w v u' u u''

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- `Q` is **convex**: an object through which an arrow between `Q`-objects factors is itself a
`Q`-object.  The complement of a co-sieve is convex, and that is the only case used. -/
def ObjectProperty.Convex (Q : ObjectProperty C) : Prop :=
  ∀ {a b z : C}, Q a → Q b → (a ⟶ z) → (z ⟶ b) → Q z

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

end Presents

end CategoryTheory
