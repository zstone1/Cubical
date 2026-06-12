import CubeChains.Wedge
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Endomorphism

/-!
# The cube chain category `Ch K` and the functor `Ch` (ClaudeSetup.md §5, §7)

Objects of `Ch K` are cube chains, presented (via §3) as bi-pointed maps
`□^∨(dims) ⟶ K`.  A morphism `a ⟶ b` is a bi-pointed map of wedges
`φ : □^∨(dimSeq a) ⟶ □^∨(dimSeq b)` making the triangle over `K` commute,
`φ ≫ b = a`.  `Ch : BPSet ⥤ Cat` sends `K ↦ Ch K` and `f : K ⟶ L` to
post-composition; the **lifting lemma** is mathlib's `Functor.mapAut`.
-/

open CategoryTheory CategoryTheory.Limits

namespace ChainCat

/-- An object of `Ch K`: a dimension sequence with a bi-pointed map of the serial
wedge into `K` (equivalently, a cube chain). -/
structure Obj (K : BPSet) where
  /-- The dimension sequence. -/
  dims : List ℕ+
  /-- The classifying bi-pointed map `□^∨(dims) ⟶ K`. -/
  map : BPSet.serialWedge dims ⟶ K

/-- A morphism of `Ch K`: a bi-pointed map of wedges commuting over `K`. -/
@[ext]
structure Hom {K : BPSet} (a b : Obj K) where
  /-- The underlying wedge map. -/
  φ : BPSet.serialWedge a.dims ⟶ BPSet.serialWedge b.dims
  /-- The triangle over `K` commutes. -/
  w : φ ≫ b.map = a.map

noncomputable instance (K : BPSet) : Category (Obj K) where
  Hom a b := Hom a b
  id a := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.φ ≫ g.φ, by rw [Category.assoc, g.w, f.w]⟩
  id_comp f := Hom.ext (Category.id_comp _)
  comp_id f := Hom.ext (Category.comp_id _)
  assoc f g h := Hom.ext (Category.assoc _ _ _)

@[simp] theorem id_φ {K : BPSet} (a : Obj K) : Hom.φ (𝟙 a) = 𝟙 _ := rfl

@[simp] theorem comp_φ {K : BPSet} {a b c : Obj K} (f : a ⟶ b) (g : b ⟶ c) :
    Hom.φ (f ≫ g) = Hom.φ f ≫ Hom.φ g := rfl

@[ext] theorem hom_ext' {K : BPSet} {a b : Obj K} {f g : a ⟶ b}
    (h : Hom.φ f = Hom.φ g) : f = g := Hom.ext h

/-- Post-composition functor `Ch K ⥤ Ch L` induced by `f : K ⟶ L`. -/
noncomputable def pushforward {K L : BPSet} (f : K ⟶ L) : Obj K ⥤ Obj L where
  obj a := ⟨a.dims, a.map ≫ f⟩
  map {a b} g := ⟨@Hom.φ K a b g, by rw [← Category.assoc, @Hom.w K a b g]⟩
  map_id a := rfl
  map_comp _ _ := rfl

@[simp] theorem pushforward_map_φ {K L : BPSet} (f : K ⟶ L) {a b : Obj K} (g : a ⟶ b) :
    Hom.φ ((pushforward f).map g) = Hom.φ g := rfl

/-- `pushforward (𝟙 K)` is the identity functor (post-composition by `𝟙` is
definitional, since `≫` in `BPSet` is componentwise in `Type`). -/
theorem pushforward_id (K : BPSet) : pushforward (𝟙 K) = 𝟭 (Obj K) := rfl

/-- `pushforward` respects composition (definitional, by associativity of `≫`). -/
theorem pushforward_comp {K L M : BPSet} (f : K ⟶ L) (g : L ⟶ M) :
    pushforward (f ≫ g) = pushforward f ⋙ pushforward g := rfl

end ChainCat

/-- The cube chain functor `Ch : BPSet ⥤ Cat`: `K ↦ Ch K`, `f ↦` post-composition. -/
noncomputable def Ch : BPSet ⥤ Cat where
  obj K := Cat.of (ChainCat.Obj K)
  map f := (ChainCat.pushforward f).toCatHom
  map_id K := Cat.ext (ChainCat.pushforward_id K)
  map_comp f g := Cat.ext (ChainCat.pushforward_comp f g)

/-- **Lifting lemma (ClaudeSetup.md §7).** Every automorphism of a bi-pointed
precubical set `K` lifts to an automorphism of `Ch K`, as a group homomorphism.
This is the functoriality of `Ch`, packaged by `Functor.mapAut`. -/
noncomputable def Aut.liftToCh (K : BPSet) : Aut K →* Aut (Ch.obj K) :=
  Ch.mapAut K
