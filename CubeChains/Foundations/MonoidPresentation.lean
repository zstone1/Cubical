import Mathlib.Algebra.PresentedMonoid.Basic
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.SingleObj

/-!
# Foundations/MonoidPresentation — a presented monoid is a presented one-object category

Paths in the one-vertex quiver on `α` are words in `α`; imposing `rel` on those words presents
`PresentedMonoid rel`.  The **opposite** category is what comes out: path composition reads left
to right while `SingleObj` multiplies `f ≫ g = g * f`, and the flip is exactly `ᵒᵖ`.
-/

universe u

open CategoryTheory Quiver Opposite

namespace CategoryTheory.SingleObj

variable {α : Type u}

/-! ## Words

`Quiver.SingleObj.pathToList` reads a path backwards; `pathWord` reads it in path order.  It is
spelled by `Path.rec` at a constant motive, so that its two equations are definitional. -/

/-- The word a path spells, in path order. -/
def pathWord {x y : SingleObj α} (P : Path x y) : FreeMonoid α :=
  P.rec (motive := fun _ _ => FreeMonoid α) 1 fun {_ _} _ e ih => ih * FreeMonoid.of (e : α)

@[simp] theorem pathWord_nil {x : SingleObj α} : pathWord (Path.nil : Path x x) = 1 := rfl

@[simp] theorem pathWord_cons {x y z : SingleObj α} (P : Path x y) (e : y ⟶ z) :
    pathWord (P.cons e) = pathWord P * FreeMonoid.of (e : α) := rfl

@[simp] theorem pathWord_toPath {x y : SingleObj α} (e : x ⟶ y) :
    pathWord e.toPath = FreeMonoid.of (e : α) := one_mul _

theorem pathWord_comp {x y z : SingleObj α} (P : Path x y) (Q : Path y z) :
    pathWord (P.comp Q) = pathWord P * pathWord Q := by
  induction Q with
  | nil => simp
  | cons Q e ih => rw [Path.comp_cons, pathWord_cons, pathWord_cons, ih, mul_assoc]

theorem pathWord_eq_reverse {x : SingleObj α} (P : Path (star α) x) :
    pathWord P = List.reverse (Quiver.SingleObj.pathToList P) := by
  induction P with
  | nil => rfl
  | cons P e ih =>
      rw [pathWord_cons, ih]
      dsimp [Quiver.SingleObj.pathToList]
      rw [List.reverse_cons]
      rfl

/-- The path spelling a word. -/
def pathOfWord (w : FreeMonoid α) : Path (star α) (star α) :=
  Quiver.SingleObj.pathEquivList.symm (List.reverse w)

@[simp] theorem pathOfWord_one : pathOfWord (1 : FreeMonoid α) = Path.nil := rfl

@[simp] theorem pathWord_pathOfWord (w : FreeMonoid α) : pathWord (pathOfWord w) = w := by
  rw [pathWord_eq_reverse, pathOfWord,
    show Quiver.SingleObj.pathEquivList.symm (List.reverse w)
      = Quiver.SingleObj.listToPath (List.reverse w) from rfl,
    Quiver.SingleObj.pathToList_listToPath, List.reverse_reverse]

@[simp] theorem pathOfWord_pathWord (P : Path (star α) (star α)) : pathOfWord (pathWord P) = P := by
  rw [pathOfWord, pathWord_eq_reverse, List.reverse_reverse]
  exact Quiver.SingleObj.pathEquivList.symm_apply_apply P

theorem pathWord_injective :
    Function.Injective (pathWord : Path (star α) (star α) → FreeMonoid α) :=
  Function.LeftInverse.injective pathOfWord_pathWord

theorem pathOfWord_mul (w₁ w₂ : FreeMonoid α) :
    pathOfWord (w₁ * w₂) = (pathOfWord w₁).comp (pathOfWord w₂) :=
  pathWord_injective (by
    rw [pathWord_pathOfWord, pathWord_comp, pathWord_pathOfWord, pathWord_pathOfWord])

/-! ## The presentation -/

variable (rel : FreeMonoid α → FreeMonoid α → Prop)

/-- Two paths are related when their words are. -/
def pathRel : HomRel (Paths (SingleObj α)) := fun _ _ P Q => rel (pathWord P) (pathWord Q)

/-- A path goes to the class of its word. -/
def toPresented : Paths (SingleObj α) ⥤ (SingleObj (PresentedMonoid rel))ᵒᵖ :=
  Paths.lift
    { obj := fun _ => op (star _)
      map := fun {_ _} e => Quiver.Hom.op (PresentedMonoid.of rel (e : α)) }

@[simp] theorem toPresented_map {x y : SingleObj α} (P : Path x y) :
    (toPresented rel).map P = Quiver.Hom.op (PresentedMonoid.mk rel (pathWord P)) := by
  induction P with
  | nil => rfl
  | cons P e ih =>
      dsimp only [toPresented] at ih ⊢
      rw [Paths.lift_cons, ih]
      exact congrArg _ (map_mul _ _ _).symm

/-- The presenting functor, on the quotient. -/
def presentedFunctor : Quotient (pathRel rel) ⥤ (SingleObj (PresentedMonoid rel))ᵒᵖ :=
  Quotient.lift _ (toPresented rel) fun _ _ _ _ h => by
    rw [toPresented_map, toPresented_map, PresentedMonoid.mk_eq_mk_of_rel h]

@[simp] theorem presentedFunctor_map {x y : SingleObj α} (P : Path x y) :
    (presentedFunctor rel).map ((Quotient.functor (pathRel rel)).map P)
      = Quiver.Hom.op (PresentedMonoid.mk rel (pathWord P)) :=
  toPresented_map rel P

/-! ### Faithfulness

The word already determines the class of the path: the letters act on the quotient as the loops
they name, and that action factors through the presented monoid. -/

/-- The basepoint of the quotient. -/
private abbrev base : Quotient (pathRel rel) := (Quotient.functor (pathRel rel)).obj (star α)

/-- A word, as a loop at the basepoint — in the opposite monoid, `End` being `f * g = g ≫ f`. -/
private def loopHom : FreeMonoid α →* (End (base rel))ᵐᵒᵖ where
  toFun w := MulOpposite.op ((Quotient.functor (pathRel rel)).map (pathOfWord w))
  map_one' := congrArg MulOpposite.op ((Quotient.functor (pathRel rel)).map_id _)
  map_mul' w₁ w₂ := by
    rw [← MulOpposite.op_mul, End.mul_def, pathOfWord_mul]
    exact congrArg MulOpposite.op ((Quotient.functor (pathRel rel)).map_comp _ _)

private theorem loopHom_pathWord (P : Path (star α) (star α)) :
    loopHom rel (pathWord P) = MulOpposite.op ((Quotient.functor (pathRel rel)).map P) := by
  change MulOpposite.op ((Quotient.functor (pathRel rel)).map (pathOfWord (pathWord P))) = _
  rw [pathOfWord_pathWord]

private theorem loopHom_rel {w₁ w₂ : FreeMonoid α} (h : rel w₁ w₂) :
    loopHom rel w₁ = loopHom rel w₂ :=
  congrArg MulOpposite.op (Quotient.sound _ (by
    change rel (pathWord (pathOfWord w₁)) (pathWord (pathOfWord w₂))
    rwa [pathWord_pathOfWord, pathWord_pathOfWord]))

private theorem freeMonoidLift_loopHom :
    FreeMonoid.lift (fun a => loopHom rel (FreeMonoid.of a)) = loopHom rel :=
  FreeMonoid.hom_eq fun _ => FreeMonoid.lift_eval_of _ _

/-- The loop action, read on the presented monoid. -/
private def loopLift : PresentedMonoid rel →* (End (base rel))ᵐᵒᵖ :=
  PresentedMonoid.lift _ fun _ _ h => by
    rw [freeMonoidLift_loopHom]; exact loopHom_rel rel h

private theorem loopLift_mk (w : FreeMonoid α) :
    loopLift rel (PresentedMonoid.mk rel w) = loopHom rel w := by
  change FreeMonoid.lift _ w = _
  rw [freeMonoidLift_loopHom]

instance : (presentedFunctor rel).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain rfl : X = star α := Subsingleton.elim _ _
    obtain rfl : Y = star α := Subsingleton.elim _ _
    obtain ⟨P, rfl⟩ := (Quotient.functor (pathRel rel)).map_surjective f
    obtain ⟨Q, rfl⟩ := (Quotient.functor (pathRel rel)).map_surjective g
    have hmk := Quiver.Hom.op_inj ((presentedFunctor_map rel P).symm.trans
      (h.trans (presentedFunctor_map rel Q)))
    have hl := congrArg (loopLift rel) hmk
    rw [loopLift_mk, loopLift_mk, loopHom_pathWord, loopHom_pathWord] at hl
    exact MulOpposite.op_injective hl

instance : (presentedFunctor rel).Full where
  map_surjective {X Y} h := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain rfl : X = star α := Subsingleton.elim _ _
    obtain rfl : Y = star α := Subsingleton.elim _ _
    obtain ⟨w, hw⟩ := PresentedMonoid.surjective_mk h.unop
    refine ⟨(Quotient.functor (pathRel rel)).map (pathOfWord w),
      (presentedFunctor_map rel (pathOfWord w)).trans ?_⟩
    rw [pathWord_pathOfWord, hw]
    rfl

instance : (presentedFunctor rel).EssSurj where
  mem_essImage Y := ⟨base rel, ⟨eqToIso (by
    obtain ⟨Y⟩ := Y
    obtain rfl : Y = star (PresentedMonoid rel) := Subsingleton.elim _ _
    rfl)⟩⟩

instance : (presentedFunctor rel).IsEquivalence where

/-- **A presented monoid is a presented one-object category** — generators the letters, relations
the relators, read on paths. -/
noncomputable def presentedMonoidPresentation :
    Quotient (pathRel rel) ≌ (SingleObj (PresentedMonoid rel))ᵒᵖ :=
  (presentedFunctor rel).asEquivalence

end CategoryTheory.SingleObj
