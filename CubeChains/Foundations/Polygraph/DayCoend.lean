import CubeChains.Foundations.Polygraph.Day
import Mathlib.CategoryTheory.Limits.Shapes.End

/-!
# Foundations/Polygraph/DayCoend — the convolution is the promonoidal coend

`dayObj` is given by a `Σ`-formula; here it is exhibited as the coend

  `(F ⊛ G) c  =  ∫^(a,b) pro c a b × F a × G b`,

for the promonoidal profunctor `pro c a b = Σ s : Split c, (s.fst ⟶ a) × (s.snd ⟶ b)`.
Both halves of the universal property are co-Yoneda: the identity-legged splitting `⟨s, 𝟙, 𝟙⟩`
generates, and dinaturality along `(l, r)` slides a pair of legs off the profunctor onto the
cells.  `ULift` is universe bookkeeping: `PolyShape` is a `Type 0` category.
-/

universe u

namespace CategoryTheory

open Opposite Limits

namespace PolyShape

/-- **The promonoidal profunctor's cells**: a splitting of `c`, with a leg out of each factor. -/
abbrev Pro (c a b : PolyShape) : Type :=
  Σ s : Split c, (s.fst ⟶ a) × (s.snd ⟶ b)

namespace Pro

variable {c'' c' c a a' a'' b b' b'' : PolyShape}

/-- Post-compose the legs: the covariant action. -/
def push (f : a ⟶ a') (g : b ⟶ b') (T : Pro c a b) : Pro c a' b' :=
  ⟨T.1, T.2.1 ≫ f, T.2.2 ≫ g⟩

/-- Restrict the splitting along a face and absorb the comparison legs: the contravariant
action.  `Split.res`'s value is taken as one argument, so the motive stays non-dependent. -/
def pull (w : c' ⟶ c) (T : Pro c a b) : Pro c' a b :=
  push T.2.1 T.2.2 (Split.res w T.1)

@[simp] theorem push_id (T : Pro c a b) : push (𝟙 a) (𝟙 b) T = T := by
  simp [push]

@[simp] theorem push_push (f : a ⟶ a') (g : b ⟶ b') (f' : a' ⟶ a'') (g' : b' ⟶ b'')
    (T : Pro c a b) : push f' g' (push f g T) = push (f ≫ f') (g ≫ g') T := by
  simp [push]

@[simp] theorem pull_id (T : Pro c a b) : pull (𝟙 c) T = T := by
  simp [pull, push]

theorem pull_pull (u : c'' ⟶ c') (v : c' ⟶ c) (T : Pro c a b) :
    pull (u ≫ v) T = pull u (pull v T) := by
  rw [pull, Split.res_comp]
  simp [pull, push]

theorem pull_push (w : c' ⟶ c) (f : a ⟶ a') (g : b ⟶ b') (T : Pro c a b) :
    pull w (push f g T) = push f g (pull w T) := by
  simp [pull, push]

end Pro

end PolyShape

namespace Polygraph

open PolyShape

/-! ## The profunctor -/

/-- **The promonoidal profunctor**, contravariant in the shape by `Split.res` and covariant in
the two factors by post-composition. -/
def dayProfunctor : PolyShapeᵒᵖ ⥤ (PolyShape × PolyShape) ⥤ Type u where
  obj X :=
    { obj := fun k => ULift.{u} (Pro X.unop k.1 k.2)
      map := fun f => ↾fun T => .up (Pro.push f.1 f.2 T.down)
      map_id := fun _ => TypeCat.homEquiv.injective (funext fun _ => by simp)
      map_comp := fun _ _ => TypeCat.homEquiv.injective (funext fun _ => by simp) }
  map w :=
    { app := fun _ => ↾fun T => .up (Pro.pull w.unop T.down)
      naturality := fun _ _ _ =>
        TypeCat.homEquiv.injective (funext fun _ => by simp [Pro.pull_push]) }
  map_id _ := NatTrans.ext (funext fun _ =>
    TypeCat.homEquiv.injective (funext fun _ => by simp))
  map_comp _ _ := NatTrans.ext (funext fun _ =>
    TypeCat.homEquiv.injective (funext fun _ => by simp [Pro.pull_pull]))

@[simp] theorem dayProfunctor_obj_map {X : PolyShapeᵒᵖ} {k k' : PolyShape × PolyShape}
    (f : k ⟶ k') (T : ULift.{u} (Pro X.unop k.1 k.2)) :
    (dayProfunctor.obj X).map f T = .up (Pro.push f.1 f.2 T.down) := rfl

@[simp] theorem dayProfunctor_map_app {X Y : PolyShapeᵒᵖ} (w : X ⟶ Y)
    (k : PolyShape × PolyShape) (T : ULift.{u} (Pro X.unop k.1 k.2)) :
    (dayProfunctor.map w).app k T = .up (Pro.pull w.unop T.down) := rfl

/-! ## The integrand -/

variable (F G : PolyShapeᵒᵖ ⥤ Type u) (c : PolyShape)

/-- The integrand of the Day coend at `c`: `(a, b) ↦ pro c a b × F a × G b`. -/
def dayIntegrand : (PolyShape × PolyShape)ᵒᵖ ⥤ (PolyShape × PolyShape) ⥤ Type u where
  obj j :=
    { obj := fun k => ULift.{u} (Pro c k.1 k.2) × F.obj (op j.unop.1) × G.obj (op j.unop.2)
      map := fun f => ↾fun z => ((dayProfunctor.obj (op c)).map f z.1, z.2)
      map_id := fun _ => TypeCat.homEquiv.injective (funext fun _ => by simp)
      map_comp := fun _ _ => TypeCat.homEquiv.injective (funext fun _ => by simp) }
  map w :=
    { app := fun _ => ↾fun z =>
        (z.1, F.map (w.unop.1).op z.2.1, G.map (w.unop.2).op z.2.2)
      naturality := fun _ _ _ => TypeCat.homEquiv.injective (funext fun _ => by simp) }
  map_id _ := NatTrans.ext (funext fun _ =>
    TypeCat.homEquiv.injective (funext fun _ => by simp))
  map_comp _ _ := NatTrans.ext (funext fun _ =>
    TypeCat.homEquiv.injective (funext fun _ => by simp))

@[simp] theorem dayIntegrand_obj_map {j : (PolyShape × PolyShape)ᵒᵖ}
    {k k' : PolyShape × PolyShape} (f : k ⟶ k')
    (z : ULift.{u} (Pro c k.1 k.2) × F.obj (op j.unop.1) × G.obj (op j.unop.2)) :
    ((dayIntegrand F G c).obj j).map f z = (.up (Pro.push f.1 f.2 z.1.down), z.2) := rfl

@[simp] theorem dayIntegrand_map_app {j j' : (PolyShape × PolyShape)ᵒᵖ} (w : j ⟶ j')
    (k : PolyShape × PolyShape)
    (z : ULift.{u} (Pro c k.1 k.2) × F.obj (op j.unop.1) × G.obj (op j.unop.2)) :
    ((dayIntegrand F G c).map w).app k z =
      (z.1, F.map (w.unop.1).op z.2.1, G.map (w.unop.2).op z.2.2) := rfl

/-! ## The cowedge, and its universal property -/

/-- Dinaturality of `dayPull`: absorbing a pair of legs into the cells is post-composing them
onto the splitting. -/
theorem dayPull_push {a b a' b' : PolyShape} (T : Pro c a b) (l : a ⟶ a') (r : b ⟶ b')
    (x : F.obj (op a')) (y : G.obj (op b')) :
    dayPull F G (Pro.push l r T) x y = dayPull F G T (F.map l.op x) (G.map r.op y) := by
  simp only [dayPull, Pro.push, op_comp, Functor.map_comp]
  rfl

/-- **The cowedge of the Day coend**: a splitting with legs acts on a pair of cells. -/
def dayCowedge : Cowedge (dayIntegrand F G c) :=
  Cowedge.mk ((dayObj F G).obj (op c))
    (fun _ => ↾fun z => dayPull F G z.1.down z.2.1 z.2.2)
    (by
      rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨l, r⟩
      refine TypeCat.homEquiv.injective (funext fun z => ?_)
      obtain ⟨T, x, y⟩ := z
      simpa using (dayPull_push F G c T.down l r x y).symm)

@[simp] theorem dayCowedge_π (k : PolyShape × PolyShape)
    (z : ULift.{u} (Pro c k.1 k.2) × F.obj (op k.1) × G.obj (op k.2)) :
    (dayCowedge F G c).π k z = dayPull F G z.1.down z.2.1 z.2.2 := rfl

/-- **The convolution is the coend**: `(F ⊛ G) c = ∫^(a,b) pro c a b × F a × G b`.  The descent
of a cowedge takes `⟨s, x, y⟩` to its leg at `(s.fst, s.snd)` on the identity-legged splitting. -/
def dayIsCoend : IsColimit (dayCowedge F G c) :=
  Multicofork.IsColimit.mk _
    (fun E => ↾fun z => E.π (z.1.fst, z.1.snd) (⟨⟨z.1, 𝟙 _, 𝟙 _⟩⟩, z.2.1, z.2.2))
    (fun E k => TypeCat.homEquiv.injective (funext fun z => by
      obtain ⟨⟨⟨s, l, r⟩⟩, x, y⟩ := z
      exact types_congr_hom
        (Cowedge.condition E (i := (s.fst, s.snd)) (j := k) (l, r)) (⟨⟨s, 𝟙 _, 𝟙 _⟩⟩, x, y)))
    (fun E m hm => TypeCat.homEquiv.injective (funext fun z => by
      obtain ⟨s, x, y⟩ := z
      have h : m (dayPull F G (⟨s, 𝟙 _, 𝟙 _⟩ : Pro c s.fst s.snd) x y)
          = E.π (s.fst, s.snd) (⟨⟨s, 𝟙 _, 𝟙 _⟩⟩, x, y) :=
        types_congr_hom (hm (s.fst, s.snd)) (⟨⟨s, 𝟙 _, 𝟙 _⟩⟩, x, y)
      simpa [dayPull] using h))

/-- The convolution, identified with mathlib's coend. -/
noncomputable def dayObjIsoCoend : (dayObj F G).obj (op c) ≅ coend (dayIntegrand F G c) :=
  IsColimit.coconePointUniqueUpToIso (dayIsCoend F G c) (colimit.isColimit _)

end Polygraph

end CategoryTheory
