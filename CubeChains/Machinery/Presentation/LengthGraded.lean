import CubeChains.Machinery.Presentation.Coproduct
import CubeChains.Machinery.Presentation.Product
import CubeChains.Machinery.Presentation.Monoid
import CubeChains.Machinery.Presentation.Opposite

/-!
# Machinery/Presentation/LengthGraded — 2-cells that change the word length

An **interchange** square has the same two letters on both sides, so its two words have the same
length.  A polygraph whose 2-cells never relate two words of equal length therefore receives no map
*out of* a tensor with two factors carrying 1-cells: the square has nowhere to go.  That is the
whole obstruction, and `LengthGraded` is the hypothesis that carries it.

`Hom` reflects it and `comap` preserves it; a tensor with a 1-cell in each factor never has it.
-/

universe wp up w₂p wq uq w₂q w u u' w₂

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

/-- **A coproduct is length-graded when its legs are** — a 2-cell is a leg's, included. -/
theorem LengthGraded.coprod {ι : Type u} {P : ι → Polygraph.{u, u, u}}
    (h : ∀ i, LengthGraded (P i)) : LengthGraded (Polygraph.coprod P) := by
  rintro _ _ ⟨(α : (P _).Rel _ _)⟩ hα
  exact h _ α ((Polygraph.length_mapPath _ _).symm.trans
    (hα.trans (Polygraph.length_mapPath _ _)))

/-! ## The tensor -/

/-- **A 1-cell in each factor spans an interchange square**, whose two sides are words of the same
length — so nothing length-graded receives a map out of such a tensor. -/
theorem not_lengthGraded_prod {P : Polygraph.{wp, up, w₂p}} {Q : Polygraph.{wq, uq, w₂q}}
    {x x' : P.V} (g : P.Gen x x') {y y' : Q.V} (h : Q.Gen y y') :
    ¬ LengthGraded (prod P Q) :=
  fun hL => hL (ProdRel.interchange g h) rfl

end Polygraph

end CategoryTheory
