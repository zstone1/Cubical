import CubeChains.Machinery.Presentation.Basic
import Mathlib.CategoryTheory.HomCongr

/-!
# Machinery/Presentation/Comparison — two presentations of one category

Two presentations of one category are abstractly equivalent for free (`p.equiv.trans q.equiv.symm`),
which says nothing.  The content is that the comparison is *spelled by the generators*: a
`Presents.Map` is a `Polygraph.Spelling` whose induced functor commutes with the two comparisons,
and it is then automatically an equivalence (`isEquivalence`).

A spelling sends a 1-cell to a *word*, so one exists whenever each generator of `P` can be spelled
in `Q` at all — a mere *choice* of word makes the statement vacuous.  The comparisons worth building
are those whose generators go to generators.
-/

universe v w w' u u' u'' w₂ w₂'

namespace CategoryTheory.Polygraph

variable {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}} {C : Type u} [Category.{v} C]

/-- **A comparison of presentations**: a spelling naming the same arrows. -/
structure Presents.Map (p : Presents P C) (q : Presents Q C) where
  /-- the word each generator spells -/
  hom : Spelling P Q
  /-- …naming the same arrow of `C` -/
  iso : hom.functor ⋙ q.E ≅ p.E

namespace Presents.Map

variable {p : Presents P C} {q : Presents Q C} (m : Presents.Map p q)

/-- **A comparison of presentations of one category is an equivalence.**  Neither polygraph is
assumed finite, small or related to the other: only that one spells the other's arrows. -/
instance isEquivalence : m.hom.functor.IsEquivalence :=
  haveI : (m.hom.functor ⋙ q.E).IsEquivalence := Functor.isEquivalence_of_iso m.iso.symm
  Functor.isEquivalence_of_comp_right _ q.E

/-- The two polygraphs present the same category, compatibly. -/
noncomputable def equiv : P.presented ≌ Q.presented := m.hom.functor.asEquivalence

end Presents.Map

/-! ## Building one

The 2-cells never have to be checked: a spelling that names the same arrow kills them, `q.E` being
faithful.  So a comparison *is* its generator data. -/

section OfSpelling

private theorem conj_comp_hom {A B A' B' : C} (α : A' ≅ A) (β : B' ≅ B) (f : A ⟶ B) :
    (α.hom ≫ f ≫ β.inv) ≫ β.hom = α.hom ≫ f := by simp

/-- **A prefunctor conjugate to `p`'s own interpretation lifts to one** — the induction every
comparison runs, stated where composition is the target category's, not `Paths`'. -/
theorem lift_conj {p : Presents P C} {ψ : GenObj P.Gen ⥤q C}
    (θ : ∀ x : GenObj P.Gen, ψ.obj x ≅ p.at' x)
    (hψ : ∀ {x y : GenObj P.Gen} (e : x ⟶ y), ψ.map e = (θ x).hom ≫ p.arrow e ≫ (θ y).inv)
    {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (Paths.lift ψ).map u = (θ x).hom ≫ p.eval.map u ≫ (θ y).inv := by
  induction u with
  | nil => rw [Paths.lift_nil, p.eval_nil, Category.id_comp, (θ x).hom_inv_id]
  | @cons b c u e ih =>
      rw [Paths.lift_cons, ih, hψ e, p.eval_cons]
      -- `Category.assoc` cannot fire: the outer `≫` spells its objects `(Paths.lift ψ).obj`
      -- where the inner spells them `ψ.obj`, so the step runs through `exact`.
      exact (Iso.homCongr_comp (θ x).symm (θ b).symm (θ c).symm (p.eval.map u) (p.arrow e)).symm

variable {p : Presents P C} {q : Presents Q C} (φ : GenObj P.Gen ⥤q Q.Word)
  (θ : ∀ x : GenObj P.Gen, q.eval.obj (φ.obj x) ≅ p.at' x)
  (hφ : ∀ {x y : GenObj P.Gen} (e : x ⟶ y),
    q.eval.map (φ.map e) = (θ x).hom ≫ p.arrow e ≫ (θ y).inv)

include hφ in
/-- **A spelling names the same arrow on whole words**, not only on generators. -/
theorem eval_lift_map {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    q.eval.map ((Paths.lift φ).map u) = (θ x).hom ≫ p.eval.map u ≫ (θ y).inv :=
  (Paths.lift_comp_map φ q.eval u).trans
    (lift_conj (ψ := φ ⋙q q.eval.toPrefunctor) θ (fun e => hφ e) u)

include hφ in
/-- **`Spelling`'s obligation, for free**: `q.E` is faithful, so a 2-cell of `P` whose two sides
name one arrow of `C` is spelled by two equal arrows of `Q.presented`. -/
theorem spelling_sound {x y : GenObj P.Gen} (α : P.Rel x y) :
    Q.quot.map ((Paths.lift φ).map (P.src α)) = Q.quot.map ((Paths.lift φ).map (P.tgt α)) :=
  q.E.map_injective
    (((eval_lift_map φ θ hφ _).trans (by rw [p.sound α])).trans (eval_lift_map φ θ hφ _).symm)

/-- **A comparison of presentations, from a spelling of the generators.**  `θ` names the 0-cells,
`hφ` says a 1-cell spells the same arrow; that is the whole of the data. -/
def Presents.Map.ofSpelling : Presents.Map p q where
  hom := ⟨φ, fun α => spelling_sound φ θ hφ α⟩
  iso := NatIso.ofComponents (fun X => θ X.as) (by
    rintro ⟨x⟩ ⟨y⟩ f
    obtain ⟨u, rfl⟩ := P.quot.map_surjective f
    change q.eval.map ((Paths.lift φ).map u) ≫ (θ y).hom = (θ x).hom ≫ p.eval.map u
    rw [eval_lift_map φ θ hφ]
    exact conj_comp_hom (θ x) (θ y) (p.eval.map u))

end OfSpelling

/-! A comparison whose generators go to *generators* — the form worth having, and the only one that
says anything: the words are single letters, so the two generating families biject onto each other's
arrows. -/

section OfGenerators

variable {p : Presents P C} {q : Presents Q C} (ob : GenObj P.Gen → GenObj Q.Gen)
  (gen : ∀ {x y : GenObj P.Gen}, (x ⟶ y) → (ob x ⟶ ob y))
  (θ : ∀ x : GenObj P.Gen, q.at' (ob x) ≅ p.at' x)
  (hgen : ∀ {x y : GenObj P.Gen} (e : x ⟶ y),
    q.arrow (gen e) = (θ x).hom ≫ p.arrow e ≫ (θ y).inv)

include hgen in
/-- **…generator by generator.** -/
def Presents.Map.ofGenerators : Presents.Map p q :=
  Presents.Map.ofSpelling ⟨ob, fun e => (gen e).toPath⟩ θ hgen

end OfGenerators

end CategoryTheory.Polygraph
