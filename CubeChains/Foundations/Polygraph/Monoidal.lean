import CubeChains.Foundations.Polygraph.Tensor
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Foundations/Polygraph/Monoidal — the tensor makes `Polygraph` monoidal

A cell of `prod` names a cell of one factor and 0-cells of the other, or — in dimension 2 — an
interchange square naming a 1-cell of each.  Re-bracketing is therefore a bijection on cells in
every dimension, and each coherence law is an identity of pattern matches.

`unitPoly` has one 0-cell and nothing else, so on its side `ProdGen.right`, `ProdRel.right` and
`ProdRel.interchange` are uninhabited; the unitors' inverses are `prodInl`/`prodInr`.

A constructor of `ProdGen`/`ProdRel` needs its ambient polygraph named — `(Q := prod Q R)` —
whenever an argument's type is spelled `Q.V × R.V` rather than `(prod Q R).V`.
-/

universe u

namespace CategoryTheory

namespace Polygraph

open MonoidalCategory

/-! ## The unit -/

/-- One 0-cell, and nothing else. -/
def unitPoly : Polygraph.{u, u, u} where
  V := PUnit
  Gen _ _ := PEmpty
  Rel _ _ := PEmpty
  src r := r.elim
  tgt r := r.elim

/-! ## The associator

On 0-cells `((x, y), z) ↦ (x, (y, z))`; on 1-cells and on 2-cells, re-bracketing:

    .left (.left g y) z         ↦ .left g (y, z)
    .left (.right x h) z        ↦ .right x (.left h z)
    .right (x, y) k             ↦ .right x (.right y k)

    .left z (.left y α)         ↦ .left (y, z) α
    .left z (.right x α)        ↦ .right x (.left z α)
    .left z (.interchange g h)  ↦ .interchange g (.left h z)
    .right (x, y) α             ↦ .right x (.right y α)
    .interchange (.left g y) k  ↦ .interchange g (.right y k)
    .interchange (.right x h) k ↦ .right x (.interchange h k)
-/

section Assoc

variable (P Q R : Polygraph.{u, u, u})

/-- Re-bracketing, on 1-cells. -/
def assocGen : ∀ {a b : (P.V × Q.V) × R.V}, ProdGen (prod P Q) R a b →
    ProdGen P (prod Q R) (a.1.1, (a.1.2, a.2)) (b.1.1, (b.1.2, b.2))
  | _, _, ProdGen.left (ProdGen.left g y) z => ProdGen.left (Q := prod Q R) g (y, z)
  | _, _, ProdGen.left (ProdGen.right x h) z =>
      ProdGen.right (Q := prod Q R) x (ProdGen.left h z)
  | _, _, ProdGen.right (x, y) k => ProdGen.right (Q := prod Q R) x (ProdGen.right y k)

/-- Re-bracketing, on 0-cells and 1-cells. -/
def assocPre : GenObj (ProdGen (prod P Q) R) ⥤q GenObj (ProdGen P (prod Q R)) where
  obj a := ⟨(a.as.1.1, (a.as.1.2, a.as.2))⟩
  map e := assocGen P Q R e

theorem assocPre_mapPath_left_left (y : Q.V) (z : R.V) {x x' : GenObj P.Gen}
    (w : Quiver.Path x x') :
    (assocPre P Q R).mapPath ((prodLeft (prod P Q) R z).mapPath ((prodLeft P Q y).mapPath w))
      = (prodLeft P (prod Q R) (y, z)).mapPath w := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Quiver.Path.cons · _) ih

theorem assocPre_mapPath_left_right (x : P.V) (z : R.V) {y y' : GenObj Q.Gen}
    (w : Quiver.Path y y') :
    (assocPre P Q R).mapPath ((prodLeft (prod P Q) R z).mapPath ((prodRight P Q x).mapPath w))
      = (prodRight P (prod Q R) x).mapPath ((prodLeft Q R z).mapPath w) := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Quiver.Path.cons · _) ih

theorem assocPre_mapPath_right (x : P.V) (y : Q.V) {z z' : GenObj R.Gen}
    (w : Quiver.Path z z') :
    (assocPre P Q R).mapPath ((prodRight (prod P Q) R (x, y)).mapPath w)
      = (prodRight P (prod Q R) x).mapPath ((prodRight Q R y).mapPath w) := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Quiver.Path.cons · _) ih

/-- Re-bracketing. -/
def assocHom : prod (prod P Q) R ⟶ prod P (prod Q R) where
  pre := assocPre P Q R
  two {_ _} α := match α with
    | ProdRel.left z (ProdRel.left y β) => ProdRel.left (Q := prod Q R) (y, z) β
    | ProdRel.left z (ProdRel.right x β) =>
        ProdRel.right (Q := prod Q R) x (ProdRel.left z β)
    | ProdRel.left z (ProdRel.interchange g h) =>
        ProdRel.interchange (Q := prod Q R) g (ProdGen.left h z)
    | ProdRel.right (x, y) β => ProdRel.right (Q := prod Q R) x (ProdRel.right y β)
    | ProdRel.interchange (ProdGen.left g y) k =>
        ProdRel.interchange (Q := prod Q R) g (ProdGen.right y k)
    | ProdRel.interchange (ProdGen.right x h) k =>
        ProdRel.right (Q := prod Q R) x (ProdRel.interchange h k)
  src_two := by
    rintro _ _ (⟨z, (⟨y, β⟩ | ⟨x, β⟩ | ⟨g, h⟩)⟩ | ⟨⟨x, y⟩, β⟩ | ⟨(⟨g, y⟩ | ⟨x, h⟩), k⟩)
    · exact (assocPre_mapPath_left_left P Q R y z (P.src β)).symm
    · exact (assocPre_mapPath_left_right P Q R x z (Q.src β)).symm
    · rfl
    · exact (assocPre_mapPath_right P Q R x y (R.src β)).symm
    · rfl
    · rfl
  tgt_two := by
    rintro _ _ (⟨z, (⟨y, β⟩ | ⟨x, β⟩ | ⟨g, h⟩)⟩ | ⟨⟨x, y⟩, β⟩ | ⟨(⟨g, y⟩ | ⟨x, h⟩), k⟩)
    · exact (assocPre_mapPath_left_left P Q R y z (P.tgt β)).symm
    · exact (assocPre_mapPath_left_right P Q R x z (Q.tgt β)).symm
    · rfl
    · exact (assocPre_mapPath_right P Q R x y (R.tgt β)).symm
    · rfl
    · rfl

/-- Re-bracketing, the other way, on 1-cells. -/
def assocInvGen : ∀ {a b : P.V × (Q.V × R.V)}, ProdGen P (prod Q R) a b →
    ProdGen (prod P Q) R ((a.1, a.2.1), a.2.2) ((b.1, b.2.1), b.2.2)
  | _, _, ProdGen.left g (y, z) => ProdGen.left (P := prod P Q) (ProdGen.left g y) z
  | _, _, ProdGen.right x (ProdGen.left h z) =>
      ProdGen.left (P := prod P Q) (ProdGen.right x h) z
  | _, _, ProdGen.right x (ProdGen.right y k) => ProdGen.right (P := prod P Q) (x, y) k

/-- Re-bracketing the other way, on 0-cells and 1-cells. -/
def assocInvPre : GenObj (ProdGen P (prod Q R)) ⥤q GenObj (ProdGen (prod P Q) R) where
  obj a := ⟨((a.as.1, a.as.2.1), a.as.2.2)⟩
  map e := assocInvGen P Q R e

theorem assocInvPre_mapPath_left (y : Q.V) (z : R.V) {x x' : GenObj P.Gen}
    (w : Quiver.Path x x') :
    (assocInvPre P Q R).mapPath ((prodLeft P (prod Q R) (y, z)).mapPath w)
      = (prodLeft (prod P Q) R z).mapPath ((prodLeft P Q y).mapPath w) := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Quiver.Path.cons · _) ih

theorem assocInvPre_mapPath_right_left (x : P.V) (z : R.V) {y y' : GenObj Q.Gen}
    (w : Quiver.Path y y') :
    (assocInvPre P Q R).mapPath ((prodRight P (prod Q R) x).mapPath ((prodLeft Q R z).mapPath w))
      = (prodLeft (prod P Q) R z).mapPath ((prodRight P Q x).mapPath w) := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Quiver.Path.cons · _) ih

theorem assocInvPre_mapPath_right_right (x : P.V) (y : Q.V) {z z' : GenObj R.Gen}
    (w : Quiver.Path z z') :
    (assocInvPre P Q R).mapPath ((prodRight P (prod Q R) x).mapPath ((prodRight Q R y).mapPath w))
      = (prodRight (prod P Q) R (x, y)).mapPath w := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Quiver.Path.cons · _) ih

/-- Re-bracketing, the other way. -/
def assocInvHom : prod P (prod Q R) ⟶ prod (prod P Q) R where
  pre := assocInvPre P Q R
  two {_ _} α := match α with
    | ProdRel.left (y, z) β => ProdRel.left (P := prod P Q) z (ProdRel.left y β)
    | ProdRel.right x (ProdRel.left z β) =>
        ProdRel.left (P := prod P Q) z (ProdRel.right x β)
    | ProdRel.right x (ProdRel.right y β) => ProdRel.right (P := prod P Q) (x, y) β
    | ProdRel.right x (ProdRel.interchange h k) =>
        ProdRel.interchange (P := prod P Q) (ProdGen.right x h) k
    | ProdRel.interchange g (ProdGen.left h z) =>
        ProdRel.left (P := prod P Q) z (ProdRel.interchange g h)
    | ProdRel.interchange g (ProdGen.right y k) =>
        ProdRel.interchange (P := prod P Q) (ProdGen.left g y) k
  src_two := by
    rintro _ _ (⟨⟨y, z⟩, β⟩ | ⟨x, (⟨z, β⟩ | ⟨y, β⟩ | ⟨h, k⟩)⟩ | ⟨g, (⟨h, z⟩ | ⟨y, k⟩)⟩)
    · exact (assocInvPre_mapPath_left P Q R y z (P.src β)).symm
    · exact (assocInvPre_mapPath_right_left P Q R x z (Q.src β)).symm
    · exact (assocInvPre_mapPath_right_right P Q R x y (R.src β)).symm
    · rfl
    · rfl
    · rfl
  tgt_two := by
    rintro _ _ (⟨⟨y, z⟩, β⟩ | ⟨x, (⟨z, β⟩ | ⟨y, β⟩ | ⟨h, k⟩)⟩ | ⟨g, (⟨h, z⟩ | ⟨y, k⟩)⟩)
    · exact (assocInvPre_mapPath_left P Q R y z (P.tgt β)).symm
    · exact (assocInvPre_mapPath_right_left P Q R x z (Q.tgt β)).symm
    · exact (assocInvPre_mapPath_right_right P Q R x y (R.tgt β)).symm
    · rfl
    · rfl
    · rfl

/-- **The tensor is associative.** -/
def assoc : prod (prod P Q) R ≅ prod P (prod Q R) where
  hom := assocHom P Q R
  inv := assocInvHom P Q R
  hom_inv_id := by
    refine Hom.ext' (Prefunctor.ext' (fun _ => rfl) ?_) ?_
    · rintro ⟨⟨⟨_, _⟩, _⟩⟩ ⟨⟨⟨_, _⟩, _⟩⟩ (⟨(⟨_, _⟩ | ⟨_, _⟩), _⟩ | ⟨_, _⟩) <;> rfl
    · rintro _ _ (⟨_, (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩)⟩ | ⟨⟨_, _⟩, _⟩ | ⟨(⟨_, _⟩ | ⟨_, _⟩), _⟩) <;> rfl
  inv_hom_id := by
    refine Hom.ext' (Prefunctor.ext' (fun _ => rfl) ?_) ?_
    · rintro ⟨⟨_, _, _⟩⟩ ⟨⟨_, _, _⟩⟩ (⟨_, _⟩ | ⟨_, (⟨_, _⟩ | ⟨_, _⟩)⟩) <;> rfl
    · rintro _ _ (⟨⟨_, _⟩, _⟩ | ⟨_, (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩)⟩ | ⟨_, (⟨_, _⟩ | ⟨_, _⟩)⟩) <;> rfl

end Assoc

/-! ## The unitors -/

section Unitor

variable (P : Polygraph.{u, u, u})

/-- Deleting the unit coordinate, on 1-cells. -/
def unitorRightGen : ∀ {a b : P.V × unitPoly.{u}.V}, ProdGen P unitPoly.{u} a b → P.Gen a.1 b.1
  | _, _, ProdGen.left g _ => g
  | _, _, ProdGen.right _ h => PEmpty.elim h

/-- Deleting the unit coordinate, on 0-cells and 1-cells. -/
def unitorRightPre : GenObj (ProdGen P unitPoly.{u}) ⥤q GenObj P.Gen where
  obj a := ⟨a.as.1⟩
  map e := unitorRightGen P e

theorem unitorRightPre_mapPath (y : unitPoly.{u}.V) {x x' : GenObj P.Gen} (w : Quiver.Path x x') :
    (unitorRightPre P).mapPath ((prodLeft P unitPoly.{u} y).mapPath w) = w := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Quiver.Path.cons · _) ih

/-- Deleting the unit coordinate. -/
def unitorRightHom : prod P unitPoly.{u} ⟶ P where
  pre := unitorRightPre P
  two {_ _} α := match α with
    | ProdRel.left _ β => β
    | ProdRel.right _ β => PEmpty.elim β
    | ProdRel.interchange _ h => PEmpty.elim h
  src_two := by
    rintro _ _ (⟨y, β⟩ | ⟨_, β⟩ | ⟨_, h⟩)
    · exact (unitorRightPre_mapPath P y (P.src β)).symm
    · exact PEmpty.elim β
    · exact PEmpty.elim h
  tgt_two := by
    rintro _ _ (⟨y, β⟩ | ⟨_, β⟩ | ⟨_, h⟩)
    · exact (unitorRightPre_mapPath P y (P.tgt β)).symm
    · exact PEmpty.elim β
    · exact PEmpty.elim h

/-- **The unit is a right unit.** -/
def unitorRight : prod P unitPoly.{u} ≅ P where
  hom := unitorRightHom P
  inv := prodInl P unitPoly.{u} PUnit.unit
  hom_inv_id := by
    refine Hom.ext' (Prefunctor.ext' (fun _ => rfl) ?_) ?_
    · rintro ⟨⟨_, _⟩⟩ ⟨⟨_, _⟩⟩ (⟨_, _⟩ | ⟨_, h⟩)
      · rfl
      · exact PEmpty.elim h
    · rintro _ _ (⟨_, _⟩ | ⟨_, β⟩ | ⟨_, h⟩)
      · rfl
      · exact PEmpty.elim β
      · exact PEmpty.elim h
  inv_hom_id :=
    Hom.ext' (Prefunctor.ext' (fun _ => rfl) (fun _ _ _ => rfl)) (fun _ => HEq.rfl)

/-- Deleting the unit coordinate, on 1-cells. -/
def unitorLeftGen : ∀ {a b : unitPoly.{u}.V × P.V}, ProdGen unitPoly.{u} P a b → P.Gen a.2 b.2
  | _, _, ProdGen.left g _ => PEmpty.elim g
  | _, _, ProdGen.right _ h => h

/-- Deleting the unit coordinate, on 0-cells and 1-cells. -/
def unitorLeftPre : GenObj (ProdGen unitPoly.{u} P) ⥤q GenObj P.Gen where
  obj a := ⟨a.as.2⟩
  map e := unitorLeftGen P e

theorem unitorLeftPre_mapPath (x : unitPoly.{u}.V) {y y' : GenObj P.Gen} (w : Quiver.Path y y') :
    (unitorLeftPre P).mapPath ((prodRight unitPoly.{u} P x).mapPath w) = w := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Quiver.Path.cons · _) ih

/-- Deleting the unit coordinate. -/
def unitorLeftHom : prod unitPoly.{u} P ⟶ P where
  pre := unitorLeftPre P
  two {_ _} α := match α with
    | ProdRel.left _ β => PEmpty.elim β
    | ProdRel.right _ β => β
    | ProdRel.interchange g _ => PEmpty.elim g
  src_two := by
    rintro _ _ (⟨_, β⟩ | ⟨x, β⟩ | ⟨g, _⟩)
    · exact PEmpty.elim β
    · exact (unitorLeftPre_mapPath P x (P.src β)).symm
    · exact PEmpty.elim g
  tgt_two := by
    rintro _ _ (⟨_, β⟩ | ⟨x, β⟩ | ⟨g, _⟩)
    · exact PEmpty.elim β
    · exact (unitorLeftPre_mapPath P x (P.tgt β)).symm
    · exact PEmpty.elim g

/-- **The unit is a left unit.** -/
def unitorLeft : prod unitPoly.{u} P ≅ P where
  hom := unitorLeftHom P
  inv := prodInr unitPoly.{u} P PUnit.unit
  hom_inv_id := by
    refine Hom.ext' (Prefunctor.ext' (fun _ => rfl) ?_) ?_
    · rintro ⟨⟨_, _⟩⟩ ⟨⟨_, _⟩⟩ (⟨g, _⟩ | ⟨_, _⟩)
      · exact PEmpty.elim g
      · rfl
    · rintro _ _ (⟨_, β⟩ | ⟨_, _⟩ | ⟨g, _⟩)
      · exact PEmpty.elim β
      · rfl
      · exact PEmpty.elim g
  inv_hom_id :=
    Hom.ext' (Prefunctor.ext' (fun _ => rfl) (fun _ _ _ => rfl)) (fun _ => HEq.rfl)

end Unitor

/-! ## The coherence laws -/

theorem assoc_naturality {P P' Q Q' R R' : Polygraph.{u, u, u}} (f : P ⟶ P') (g : Q ⟶ Q')
    (h : R ⟶ R') :
    prodMap (prodMap f g) h ≫ (assoc P' Q' R').hom
      = (assoc P Q R).hom ≫ prodMap f (prodMap g h) := by
  refine Hom.ext' (Prefunctor.ext' (fun _ => rfl) ?_) ?_
  · rintro ⟨⟨⟨_, _⟩, _⟩⟩ ⟨⟨⟨_, _⟩, _⟩⟩ (⟨(⟨_, _⟩ | ⟨_, _⟩), _⟩ | ⟨_, _⟩) <;> rfl
  · rintro _ _ (⟨_, (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩)⟩ | ⟨⟨_, _⟩, _⟩ | ⟨(⟨_, _⟩ | ⟨_, _⟩), _⟩) <;> rfl

theorem unitorLeft_naturality {P Q : Polygraph.{u, u, u}} (f : P ⟶ Q) :
    prodMap (𝟙 unitPoly.{u}) f ≫ (unitorLeft Q).hom = (unitorLeft P).hom ≫ f := by
  refine Hom.ext' (Prefunctor.ext' (fun _ => rfl) ?_) ?_
  · rintro ⟨⟨_, _⟩⟩ ⟨⟨_, _⟩⟩ (⟨g, _⟩ | ⟨_, _⟩)
    · exact PEmpty.elim g
    · rfl
  · rintro _ _ (⟨_, β⟩ | ⟨_, _⟩ | ⟨g, _⟩)
    · exact PEmpty.elim β
    · rfl
    · exact PEmpty.elim g

theorem unitorRight_naturality {P Q : Polygraph.{u, u, u}} (f : P ⟶ Q) :
    prodMap f (𝟙 unitPoly.{u}) ≫ (unitorRight Q).hom = (unitorRight P).hom ≫ f := by
  refine Hom.ext' (Prefunctor.ext' (fun _ => rfl) ?_) ?_
  · rintro ⟨⟨_, _⟩⟩ ⟨⟨_, _⟩⟩ (⟨_, _⟩ | ⟨_, h⟩)
    · rfl
    · exact PEmpty.elim h
  · rintro _ _ (⟨_, _⟩ | ⟨_, β⟩ | ⟨_, h⟩)
    · rfl
    · exact PEmpty.elim β
    · exact PEmpty.elim h

theorem prod_triangle (P Q : Polygraph.{u, u, u}) :
    (assoc P unitPoly.{u} Q).hom ≫ prodMap (𝟙 P) (unitorLeftHom Q)
      = prodMap (unitorRightHom P) (𝟙 Q) := by
  refine Hom.ext' (Prefunctor.ext' (fun _ => rfl) ?_) ?_
  · rintro ⟨⟨⟨_, _⟩, _⟩⟩ ⟨⟨⟨_, _⟩, _⟩⟩ (⟨(⟨_, _⟩ | ⟨_, e⟩), _⟩ | ⟨_, _⟩)
    · rfl
    · exact PEmpty.elim e
    · rfl
  · rintro _ _ (⟨_, (⟨_, _⟩ | ⟨_, e⟩ | ⟨_, e⟩)⟩ | ⟨⟨_, _⟩, _⟩ | ⟨(⟨_, _⟩ | ⟨_, e⟩), _⟩)
    · rfl
    · exact PEmpty.elim e
    · exact PEmpty.elim e
    · rfl
    · rfl
    · exact PEmpty.elim e

theorem prod_pentagon (P Q R S : Polygraph.{u, u, u}) :
    prodMap (assoc P Q R).hom (𝟙 S) ≫ (assoc P (prod Q R) S).hom
        ≫ prodMap (𝟙 P) (assoc Q R S).hom
      = (assoc (prod P Q) R S).hom ≫ (assoc P Q (prod R S)).hom := by
  refine Hom.ext' (Prefunctor.ext' (fun _ => rfl) ?_) ?_
  · rintro ⟨⟨⟨⟨_, _⟩, _⟩, _⟩⟩ ⟨⟨⟨⟨_, _⟩, _⟩, _⟩⟩
      (⟨(⟨(⟨_, _⟩ | ⟨_, _⟩), _⟩ | ⟨_, _⟩), _⟩ | ⟨_, _⟩) <;> rfl
  · rintro _ _ (⟨_, (⟨_, (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩)⟩ | ⟨⟨_, _⟩, _⟩ | ⟨(⟨_, _⟩ | ⟨_, _⟩), _⟩)⟩
      | ⟨⟨⟨_, _⟩, _⟩, _⟩ | ⟨(⟨(⟨_, _⟩ | ⟨_, _⟩), _⟩ | ⟨_, _⟩), _⟩) <;> rfl

/-! ## The monoidal category -/

instance monoidalStruct : MonoidalCategoryStruct Polygraph.{u, u, u} where
  tensorObj P Q := prod P Q
  whiskerLeft P _ _ f := prodMap (𝟙 P) f
  whiskerRight f Q := prodMap f (𝟙 Q)
  tensorHom f g := prodMap f g
  tensorUnit := unitPoly
  associator P Q R := assoc P Q R
  leftUnitor P := unitorLeft P
  rightUnitor P := unitorRight P

instance monoidal : MonoidalCategory Polygraph.{u, u, u} :=
  .ofTensorHom
    (id_tensorHom_id := fun P Q => prodMap_id P Q)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => (prodMap_comp f₁ g₁ f₂ g₂).symm)
    (associator_naturality := fun f₁ f₂ f₃ => assoc_naturality f₁ f₂ f₃)
    (leftUnitor_naturality := fun f => unitorLeft_naturality f)
    (rightUnitor_naturality := fun f => unitorRight_naturality f)
    (pentagon := prod_pentagon)
    (triangle := prod_triangle)

/-- The monoidal structure is `prod` on the nose; likewise every other field. -/
theorem tensorObj_eq (P Q : Polygraph.{u, u, u}) : P ⊗ Q = prod P Q := rfl

end Polygraph

end CategoryTheory
