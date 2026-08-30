import CubeChains.Precubical.Basic.Bipointed
import CubeChains.Machinery.Localization.ElementsProd
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Precubical/Basic/BipointedProd — binary products of bi-pointed precubical sets

The levelwise product of the underlying presheaves, based at the paired vertices, is the binary
product of `BPSet`.  Recording it as an `IsLimit` is what makes `X ⟶ K ⨯ L` a *pair* of maps, with
`prod.lift`/`prod.hom_ext` and their naturality supplied by mathlib.  The cone here is computable
and its universal property definitional, so callers who want that spell `X.prod Y` rather than
mathlib's chosen `X ⨯ Y`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryOfElements

namespace PrecubicalSet

/-- The levelwise product of two precubical sets — the diagonal into the external product, so
`(X.prod Y).cells n = X.cells n × Y.cells n` with coordinatewise restriction. -/
def prod (X Y : PrecubicalSet) : PrecubicalSet := Functor.diag _ ⋙ extProd X Y

@[simp] theorem prod_obj (X Y : PrecubicalSet) (b : Boxᵒᵖ) :
    (X.prod Y).obj b = (X.obj b × Y.obj b) := rfl

@[simp] theorem prod_map_apply (X Y : PrecubicalSet) {a b : Boxᵒᵖ} (f : a ⟶ b)
    (p : (X.prod Y).obj a) : (X.prod Y).map f p = (X.map f p.1, Y.map f p.2) := rfl

end PrecubicalSet

namespace BPSet

/-- The product of two bi-pointed sets: the levelwise product of the presheaves, based at the
paired vertices. -/
def prod (X Y : BPSet) : BPSet where
  toPsh := X.toPsh.prod Y.toPsh
  init := (X.init, Y.init)
  final := (X.final, Y.final)

@[simp] theorem prod_toPsh (X Y : BPSet) : (X.prod Y).toPsh = X.toPsh.prod Y.toPsh := rfl
@[simp] theorem prod_init (X Y : BPSet) : (X.prod Y).init = (X.init, Y.init) := rfl
@[simp] theorem prod_final (X Y : BPSet) : (X.prod Y).final = (X.final, Y.final) := rfl

/-- The first projection of the levelwise product. -/
def prodFst (X Y : BPSet) : X.prod Y ⟶ X where
  hom := { app := fun _ => ↾Prod.fst, naturality := fun _ _ _ => rfl }
  app_init := rfl
  app_final := rfl

/-- The second projection of the levelwise product. -/
def prodSnd (X Y : BPSet) : X.prod Y ⟶ Y where
  hom := { app := fun _ => ↾Prod.snd, naturality := fun _ _ _ => rfl }
  app_init := rfl
  app_final := rfl

/-- The map into the levelwise product induced by a pair of maps. -/
def prodLift {W X Y : BPSet} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X.prod Y where
  hom :=
    { app := fun b => ↾fun w => (f.hom.app b w, g.hom.app b w)
      naturality := fun a b h => by
        apply ConcreteCategory.hom_ext; intro w
        simp only [types_comp_apply, TypeCat.ofHom_apply]
        exact Prod.ext (NatTrans.naturality_apply f.hom h w)
          (NatTrans.naturality_apply g.hom h w) }
  app_init := Prod.ext f.app_init g.app_init
  app_final := Prod.ext f.app_final g.app_final

@[simp] theorem prodLift_fst {W X Y : BPSet} (f : W ⟶ X) (g : W ⟶ Y) :
    prodLift f g ≫ prodFst X Y = f := rfl

@[simp] theorem prodLift_snd {W X Y : BPSet} (f : W ⟶ X) (g : W ⟶ Y) :
    prodLift f g ≫ prodSnd X Y = g := rfl

/-- A map into the levelwise product is its two components. -/
theorem prod_hom_ext {W X Y : BPSet} {u v : W ⟶ X.prod Y}
    (h₁ : u ≫ prodFst X Y = v ≫ prodFst X Y) (h₂ : u ≫ prodSnd X Y = v ≫ prodSnd X Y) :
    u = v := by
  refine hom_ext (NatTrans.ext_apply fun b w => ?_)
  exact Prod.ext (congrArg (fun t : W ⟶ X => t.hom.app b w) h₁)
    (congrArg (fun t : W ⟶ Y => t.hom.app b w) h₂)

/-- The binary fan on the levelwise product. -/
def prodFan (X Y : BPSet) : BinaryFan X Y := BinaryFan.mk (prodFst X Y) (prodSnd X Y)

/-- …and it is a limit: `BPSet` has binary products. -/
def prodFanIsLimit (X Y : BPSet) : IsLimit (prodFan X Y) :=
  BinaryFan.isLimitMk (fun s => prodLift s.fst s.snd) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h₁ h₂ => prod_hom_ext (by rw [h₁, prodLift_fst]) (by rw [h₂, prodLift_snd]))

instance hasBinaryProduct (X Y : BPSet) : HasBinaryProduct X Y :=
  HasLimit.mk ⟨prodFan X Y, prodFanIsLimit X Y⟩

instance : HasBinaryProducts BPSet := hasBinaryProducts_of_hasLimit_pair _

end BPSet
