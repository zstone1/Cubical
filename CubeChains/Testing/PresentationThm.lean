import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.SingleObj
import Mathlib.GroupTheory.PresentedGroup

/-!
# Testing/PresentationThm — the vertex group of `FreeGroupoid C`, presented

`FreeGroupoid C` is the localization of `C`, so `End (mk x)` is `π₁` of the nerve.  Generators are
the arrows of `C`, relations their composable pairs, and a chosen path `τ a` to every object with
its arrows declared trivial.  Both directions are universal properties — `FreeGroupoid.lift` one
way, `PresentedGroup.toGroup` the other — and the round trips are `lift_unique` together with the
natural iso `𝟭 ≅ retract` that `liftNatIso` builds from its generator components.

`End` multiplies `u * v = v ≫ u`, so functoriality reads `⟨f ≫ g⟩ = ⟨g⟩ * ⟨f⟩`: the
`Conc (f ≫ g) = Conc g * Conc f` convention the word emitter already uses.
-/

namespace CategoryTheory

noncomputable section

universe v u

open FreeGroupoid

/-- An arrow with its endpoints — one presentation generator per arrow. -/
structure Arr (C : Type u) [Category.{v} C] where
  src : C
  tgt : C
  hom : src ⟶ tgt

namespace FreeGroupoid

variable {C : Type u} [Category.{v} C]

/-! ## The relations -/

/-- Functoriality, in `End`'s multiplication order. -/
def compRel (C : Type u) [Category.{v} C] : Set (FreeGroup (Arr C)) :=
  {r | ∃ (a b c : C) (f : a ⟶ b) (g : b ⟶ c),
    r = FreeGroup.of ⟨b, c, g⟩ * FreeGroup.of ⟨a, b, f⟩ * (FreeGroup.of ⟨a, c, f ≫ g⟩)⁻¹}

/-- The arrows a chosen-path system declares trivial. -/
def treeRel (W : Set (Arr C)) : Set (FreeGroup (Arr C)) := (fun e => FreeGroup.of e) '' W

/-- Generators the arrows, relations composability together with the tree. -/
def rels (C : Type u) [Category.{v} C] (W : Set (Arr C)) : Set (FreeGroup (Arr C)) :=
  compRel C ∪ treeRel W

/-! ## Chosen paths -/

/-- Morphisms of `FreeGroupoid C` spelled by `W`-arrows and their inverses. -/
inductive InTree (W : Set (Arr C)) : ∀ {a b : C}, (mk a ⟶ mk b) → Prop
  | one (a : C) : InTree W (𝟙 (mk a))
  | fwd {a : C} {e : Arr C} {p : mk a ⟶ mk e.src} :
      InTree W p → e ∈ W → InTree W (p ≫ homMk e.hom)
  | bwd {a : C} {e : Arr C} {p : mk a ⟶ mk e.tgt} :
      InTree W p → e ∈ W → InTree W (p ≫ Groupoid.inv (homMk e.hom))

/-- A basepoint with a chosen path to every object, spelled by the arrows it declares trivial. -/
structure Spanning (C : Type u) [Category.{v} C] (x : C) where
  τ : ∀ a : C, mk x ⟶ mk a
  root : τ x = 𝟙 (mk x)
  W : Set (Arr C)
  spans : ∀ a, InTree W (τ a)
  step : ∀ e ∈ W, τ e.src ≫ homMk e.hom = τ e.tgt

variable {x : C}

/-- The presented group of a chosen-path system. -/
abbrev Pres (S : Spanning C x) := PresentedGroup (rels C S.W)

/-! ## The presented group knows composition -/

/-- The composition relator, read in `Pres S`. -/
theorem of_comp (S : Spanning C x) {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    (PresentedGroup.of ⟨b, c, g⟩ : Pres S) * PresentedGroup.of ⟨a, b, f⟩
      = PresentedGroup.of ⟨a, c, f ≫ g⟩ := by
  have h : FreeGroup.of (Arr.mk b c g) * FreeGroup.of (Arr.mk a b f)
      * (FreeGroup.of (Arr.mk a c (f ≫ g)))⁻¹ ∈ rels C S.W := Or.inl ⟨a, b, c, f, g, rfl⟩
  have := PresentedGroup.mk_eq_mk_of_mul_inv_mem h
  rwa [map_mul] at this

/-- Identities are trivial: the composition relator at `𝟙 ≫ 𝟙`. -/
theorem of_id (S : Spanning C x) (a : C) : (PresentedGroup.of ⟨a, a, 𝟙 a⟩ : Pres S) = 1 := by
  have h := of_comp S (𝟙 a) (𝟙 a)
  rw [Category.comp_id] at h
  exact mul_right_cancel (h.trans (one_mul _).symm)

/-- Declared arrows are trivial. -/
theorem of_tree (S : Spanning C x) {e : Arr C} (he : e ∈ S.W) :
    (PresentedGroup.of e : Pres S) = 1 :=
  PresentedGroup.one_of_mem (Or.inr ⟨e, he, rfl⟩)

/-! ## `C ⥤ SingleObj (Pres S)` -/

/-- Each arrow to its generator — a functor exactly because the composition relators are imposed. -/
def toPres (S : Spanning C x) : C ⥤ SingleObj (Pres S) where
  obj _ := SingleObj.star _
  map {a b} f := PresentedGroup.of ⟨a, b, f⟩
  map_id a := of_id S a
  map_comp f g := (of_comp S f g).symm

/-- The lift of `toPres` to the free groupoid. -/
def presFunctor (S : Spanning C x) : FreeGroupoid C ⥤ SingleObj (Pres S) := lift (toPres S)

/-- The word a `FreeGroupoid`-morphism spells in the presented group. -/
def presWord (S : Spanning C x) {a b : C} (p : mk a ⟶ mk b) : Pres S := (presFunctor S).map p

@[simp] theorem presWord_id (S : Spanning C x) (a : C) : presWord S (𝟙 (mk a)) = 1 :=
  (presFunctor S).map_id _

@[simp] theorem presWord_comp (S : Spanning C x) {a b c : C} (p : mk a ⟶ mk b) (q : mk b ⟶ mk c) :
    presWord S (p ≫ q) = presWord S q * presWord S p := (presFunctor S).map_comp p q

@[simp] theorem presWord_inv (S : Spanning C x) {a b : C} (p : mk a ⟶ mk b) :
    presWord S (inv p) = (presWord S p)⁻¹ := by
  rw [presWord, presWord, Functor.map_inv, SingleObj.inv_as_inv]

@[simp] theorem presWord_ginv (S : Spanning C x) {a b : C} (p : mk a ⟶ mk b) :
    presWord S (Groupoid.inv p) = (presWord S p)⁻¹ := by
  rw [Groupoid.inv_eq_inv, presWord_inv]

@[simp] theorem presWord_homMk (S : Spanning C x) {a b : C} (f : a ⟶ b) :
    presWord S (homMk f) = PresentedGroup.of ⟨a, b, f⟩ := lift_map_homMk (toPres S) f

/-- A chosen path dies in the presented group — the point of declaring its arrows trivial. -/
theorem presWord_eq_one (S : Spanning C x) {a b : C} {p : mk a ⟶ mk b} (hp : InTree S.W p) :
    presWord S p = 1 := by
  induction hp with
  | one => simp
  | fwd _ he ih => simp [ih, of_tree S he]
  | bwd _ he ih => simp [ih, of_tree S he]

/-! ## Tree-relative loops -/

/-- The loop an arrow makes once the chosen paths close it up. -/
def loop (S : Spanning C x) (e : Arr C) : End (mk x : FreeGroupoid C) :=
  S.τ e.src ≫ homMk e.hom ≫ Groupoid.inv (S.τ e.tgt)

/-- Loops compose along composition of arrows. -/
theorem loop_comp (S : Spanning C x) {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    loop S ⟨a, b, f⟩ ≫ loop S ⟨b, c, g⟩ = loop S ⟨a, c, f ≫ g⟩ := by
  simp [loop, Groupoid.inv_eq_inv, Functor.map_comp]

/-- A declared arrow makes the trivial loop. -/
theorem loop_tree (S : Spanning C x) {e : Arr C} (he : e ∈ S.W) : loop S e = 1 := by
  rw [loop, ← Category.assoc, S.step e he]
  exact Groupoid.comp_inv _

/-- The identity arrow makes the trivial loop. -/
theorem loop_id (S : Spanning C x) (a : C) : loop S ⟨a, a, 𝟙 a⟩ = 1 := by
  rw [loop]
  simp only [Functor.map_id, Category.id_comp]
  exact Groupoid.comp_inv _

/-- Reading the presented group back as loops at the basepoint. -/
def toLoops (S : Spanning C x) : Pres S →* End (mk x : FreeGroupoid C) :=
  PresentedGroup.toGroup (f := loop S) (by
    rintro r (⟨a, b, c, f, g, rfl⟩ | ⟨e, he, rfl⟩)
    · have h : loop S ⟨b, c, g⟩ * loop S ⟨a, b, f⟩ = loop S ⟨a, c, f ≫ g⟩ := by
        rw [End.mul_def]; exact loop_comp S f g
      rw [map_mul, map_mul, map_inv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of, h, mul_inv_cancel]
    · rw [FreeGroup.lift_apply_of, loop_tree S he])

@[simp] theorem toLoops_of (S : Spanning C x) (e : Arr C) :
    toLoops S (PresentedGroup.of e) = loop S e := PresentedGroup.toGroup.of _

/-! ## The two homomorphisms -/

/-- A loop at the basepoint, read in the presented group. -/
def toPresHom (S : Spanning C x) : End (mk x : FreeGroupoid C) →* Pres S where
  toFun γ := presWord S γ
  map_one' := presWord_id S x
  map_mul' u v := presWord_comp S v u

@[simp] theorem toPresHom_apply (S : Spanning C x) (γ : End (mk x : FreeGroupoid C)) :
    toPresHom S γ = presWord S γ := rfl

/-! ## The retraction onto the basepoint -/

/-- Every object to the basepoint, every arrow to its loop. -/
def retract₀ (S : Spanning C x) : C ⥤ FreeGroupoid C where
  obj _ := mk x
  map {a b} f := loop S ⟨a, b, f⟩
  map_id a := loop_id S a
  map_comp f g := (loop_comp S f g).symm

/-- The retraction, as an endofunctor of the free groupoid. -/
def retract (S : Spanning C x) : FreeGroupoid C ⥤ FreeGroupoid C := lift (retract₀ S)

@[simp] theorem retract_homMk (S : Spanning C x) {a b : C} (f : a ⟶ b) :
    (retract S).map (homMk f) = loop S ⟨a, b, f⟩ := lift_map_homMk (retract₀ S) f

/-- Naturality of the reversed chosen paths: the loop reinstates the path it cancelled. -/
theorem inv_tau_loop (S : Spanning C x) {a b : C} (f : a ⟶ b) :
    homMk f ≫ Groupoid.inv (S.τ b) = Groupoid.inv (S.τ a) ≫ loop S ⟨a, b, f⟩ := by
  change homMk f ≫ Groupoid.inv (S.τ b)
    = Groupoid.inv (S.τ a) ≫ S.τ a ≫ homMk f ≫ Groupoid.inv (S.τ b)
  rw [← Category.assoc, Groupoid.inv_comp, Category.id_comp]

/-- Generator components of `𝟭 ≅ retract`: the chosen path, reversed. -/
def retractIso₀ (S : Spanning C x) : of C ⋙ 𝟭 (FreeGroupoid C) ≅ of C ⋙ retract S :=
  NatIso.ofComponents (fun a => asIso (Groupoid.inv (S.τ a))) (fun {a b} f => by
    simp only [Functor.comp_map, Functor.id_map, asIso_hom, retract_homMk]
    exact inv_tau_loop S f)

/-- **The retraction is homotopic to the identity** — `liftNatIso` from generator components. -/
def retractIso (S : Spanning C x) : 𝟭 (FreeGroupoid C) ≅ retract S :=
  liftNatIso _ _ (retractIso₀ S)

/-- The retraction fixes every loop at the basepoint, since the chosen path there is trivial. -/
theorem retract_map_end (S : Spanning C x) (γ : End (mk x : FreeGroupoid C)) :
    (retract S).map γ = γ := by
  have happ : (retractIso S).hom.app (mk x) = 𝟙 (mk x) := by
    rw [retractIso, liftNatIso_hom_app]
    simp only [retractIso₀, NatIso.ofComponents_hom_app, asIso_hom, S.root, Groupoid.inv_eq_inv]
    exact IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  have hn := (retractIso S).hom.naturality γ
  rw [happ] at hn
  exact ((Category.id_comp _).symm.trans hn.symm).trans (Category.comp_id _)

/-! ## The round trips -/

/-- The presented group, read back into the free groupoid. -/
def fromPres (S : Spanning C x) : SingleObj (Pres S) ⥤ FreeGroupoid C where
  obj _ := mk x
  map p := toLoops S p
  map_id _ := (toLoops S).map_one
  map_comp p q := by rw [SingleObj.comp_as_mul, map_mul]; rfl

/-- Reading a loop in `Pres S` and back is the retraction. -/
theorem presFunctor_comp_fromPres (S : Spanning C x) :
    presFunctor S ⋙ fromPres S = retract S :=
  lift_unique (retract₀ S) _ (Functor.ext (fun _ => rfl) fun a b f => by
    simp [presFunctor, fromPres, retract₀, toPres])

theorem toPres_left_inv (S : Spanning C x) (γ : End (mk x : FreeGroupoid C)) :
    toLoops S (toPresHom S γ) = γ := by
  have h := Functor.congr_hom (presFunctor_comp_fromPres S) γ
  rw [retract_map_end] at h
  refine h.trans ?_
  -- the `eqToHom`s prove a `rfl`-equality, hence are `𝟙` by proof irrelevance
  change (𝟙 (mk x) : mk x ⟶ mk x) ≫ γ ≫ 𝟙 (mk x) = γ
  rw [Category.id_comp, Category.comp_id]

theorem toPres_right_inv (S : Spanning C x) (p : Pres S) :
    toPresHom S (toLoops S p) = p := by
  have : (toPresHom S).comp (toLoops S) = MonoidHom.id (Pres S) := by
    ext e
    simp [loop, presWord_eq_one S (S.spans e.src), presWord_eq_one S (S.spans e.tgt)]
  exact congrArg (fun φ => φ p) this

/-! ## The theorem -/

/-- **The vertex group of the free groupoid is the presented group**: generators the arrows of `C`,
relations their composable pairs together with the chosen paths' arrows. -/
def presentationEquiv (S : Spanning C x) : End (mk x : FreeGroupoid C) ≃* Pres S where
  toFun := toPresHom S
  invFun := toLoops S
  left_inv := toPres_left_inv S
  right_inv := toPres_right_inv S
  map_mul' := (toPresHom S).map_mul

@[simp] theorem presentationEquiv_apply (S : Spanning C x) (γ : End (mk x : FreeGroupoid C)) :
    presentationEquiv S γ = (presFunctor S).map γ := rfl

@[simp] theorem presentationEquiv_symm_of (S : Spanning C x) (e : Arr C) :
    (presentationEquiv S).symm (PresentedGroup.of e) = loop S e := toLoops_of S e

/-- An initial object spans by its own star of arrows — the hypotheses are satisfiable. -/
def Spanning.ofInitial {z : C} (hz : Limits.IsInitial z) : Spanning C z where
  τ a := homMk (hz.to a)
  root := by rw [show hz.to z = 𝟙 z from hz.hom_ext _ _]; exact (of C).map_id z
  W := Set.range fun b : C => (⟨z, b, hz.to b⟩ : Arr C)
  spans a := by
    have h := InTree.fwd (W := Set.range fun b : C => (⟨z, b, hz.to b⟩ : Arr C))
      (e := ⟨z, a, hz.to a⟩) (InTree.one z) ⟨a, rfl⟩
    rwa [Category.id_comp] at h
  step e he := by
    obtain ⟨a, rfl⟩ := he
    change homMk (hz.to z) ≫ homMk (hz.to a) = homMk (hz.to a)
    rw [show hz.to z = 𝟙 z from hz.hom_ext _ _]
    simp

/-- A groupoid's isos at `X` are its endomorphisms there; both multiply by `u * v = v ≫ u`. -/
def autMulEquivEnd {D : Type*} [Groupoid D] (X : D) : Aut X ≃* End X :=
  { Groupoid.isoEquivHom X X with map_mul' := fun _ _ => rfl }

/-- **The same, stated for `Aut`.** -/
def autPresentationEquiv (S : Spanning C x) : Aut (mk x : FreeGroupoid C) ≃* Pres S :=
  (autMulEquivEnd _).trans (presentationEquiv S)

end FreeGroupoid

end

end CategoryTheory
