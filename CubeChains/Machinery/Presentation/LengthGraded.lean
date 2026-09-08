import CubeChains.Machinery.Presentation.Pi
import CubeChains.Machinery.Presentation.Monoid
import CubeChains.Machinery.Presentation.Opposite

/-!
# Machinery/Presentation/LengthGraded — 2-cells that change the word length

An **interchange** square has the same two letters on both sides, so its two words have the same
length.  A polygraph whose 2-cells never relate two words of equal length therefore receives no map
*out of* a tensor with two factors carrying 1-cells: the square has nowhere to go.  That is the
whole obstruction, and `LengthGraded` is the hypothesis that carries it.

`Hom` reflects it, `comap` preserves it, and `Polygraph.pi` inherits it exactly when the index is a
subsingleton — one factor, hence no square.
-/

universe t w u' w₂

namespace CategoryTheory

/-! ## Word length -/

theorem Polygraph.length_mapPath {V W : Type*} [Quiver V] [Quiver W] (π : V ⥤q W) {x y : V}
    (p : Quiver.Path x y) : (π.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simpa [Prefunctor.mapPath] using ih

theorem MonoidPoly.length_word {S : Type} {rels : FreeMonoid S → FreeMonoid S → Prop}
    {x y : GenObj (monoidGen rels)} (P : Quiver.Path x y) : (word P).length = P.length := by
  induction P with
  | nil => rfl
  | cons P e ih =>
      rw [word_cons, FreeMonoid.length_mul, Quiver.Path.length_cons, ih, FreeMonoid.length_of]

namespace Polygraph

/-- **A polygraph whose 2-cells never relate two words of the same length.** -/
def LengthGraded (P : Polygraph.{w, u', w₂}) : Prop :=
  ∀ {x y : GenObj P.Gen} (α : P.Rel x y), (P.src α).length ≠ (P.tgt α).length

theorem LengthGraded.of_hom {P : Polygraph.{w, u', w₂}} {Q : Polygraph} (F : Hom P Q)
    (h : LengthGraded Q) : LengthGraded P := fun α hα =>
  h (F.two α) (by rw [F.src_two, F.tgt_two, length_mapPath, length_mapPath]; exact hα)

theorem LengthGraded.comap {P : Polygraph.{w, u', w₂}} {V : Type*} {Gen : V → V → Type*}
    (π : GenObj Gen ⥤q GenObj P.Gen) (h : LengthGraded P) :
    LengthGraded (P.comap Gen π) := fun α hα =>
  h α.cell (by rw [← α.src_eq, ← α.tgt_eq, length_mapPath, length_mapPath]; exact hα)

theorem length_revPath {V : Type u'} {Gen : V → V → Type w} {x y : GenObj (opGen Gen)} :
    ∀ (u : Quiver.Path x y), (revPath u).length = u.length := by
  intro u
  induction u with
  | nil => rfl
  | cons u e ih =>
      rw [revPath_cons, Quiver.Path.length_comp, Quiver.Path.length_cons, ih,
        show (Quiver.Hom.toPath (opHom e)).length = 1 from rfl]
      omega

theorem LengthGraded.op {P : Polygraph.{w, u', w₂}} (h : LengthGraded P) : LengthGraded P.op :=
  fun α hα => h α (by rw [← length_revPath (P.src α), ← length_revPath (P.tgt α)]; exact hα)

/-! ## The tensor -/

section Pi

variable {ι : Type t} [DecidableEq ι] (P : ι → Polygraph.{w, u', w₂})

theorem length_piPath (i : ι) {A B : GenObj (P i).Gen} (u : Quiver.Path A B) :
    ∀ (X Y : ∀ j, (P j).V) (hs : Shift P i A.as B.as X Y),
      (piPath P i u X Y hs).length = u.length := by
  induction u with
  | nil =>
      intro X Y hs
      obtain rfl : X = Y := hs.eq_of
      rw [piPath_nil]
      rfl
  | @cons M B u e ih =>
      intro X Y hs
      simp only [piPath, Quiver.Path.length_cons, ih]

/-- **A tensor over a subsingleton index has no interchange**, so it inherits length grading. -/
theorem LengthGraded.pi [Subsingleton ι] (h : ∀ i, LengthGraded (P i)) :
    LengthGraded (Polygraph.pi P) := by
  rintro x y (⟨i, α, hs⟩ | ⟨hij⟩) hα
  · refine h i α ?_
    have hp : (piPath P i ((P i).src α) _ _ hs).length
        = (piPath P i ((P i).tgt α) _ _ hs).length := hα
    rwa [length_piPath, length_piPath] at hp
  · exact hij (Subsingleton.elim _ _)

end Pi

end Polygraph

end CategoryTheory
