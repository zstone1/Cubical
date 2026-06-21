import CubeChains.Foundations.Wedge
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Endomorphism

/-!
# Chains/Category

The cube-chain category and the functor `Ch : BPSet ⥤ Cat`: `ChainCat.Obj`/`Hom`,
post-composition functoriality, and the **lifting lemma** `Aut.liftToCh`
(an `Aut K` lifts to `Aut (Ch K)`, via mathlib's `Functor.mapAut`).

**Layer:** Chains.  **Imports:** `Foundations.Wedge`, mathlib `Cat`/`Endomorphism`.
A morphism `a ⟶ b` is a bi-pointed wedge map `φ` with `φ ≫ b.map = a.map`.

Objects of `Ch K` are cube chains, presented (via §3) as bi-pointed maps
`□^∨(dims) ⟶ K`.  A morphism `a ⟶ b` is a bi-pointed map of wedges
`φ : □^∨(dimSeq a) ⟶ □^∨(dimSeq b)` making the triangle over `K` commute,
`φ ≫ b = a`.  `Ch : BPSet ⥤ Cat` sends `K ↦ Ch K` and `f : K ⟶ L` to
post-composition; the **lifting lemma** is mathlib's `Functor.mapAut`.
-/

open CategoryTheory CategoryTheory.Limits Opposite

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

/-- The lift acts on a chain by post-composing its classifying map (the dimension
sequence is untouched).  This is definitional, since `Ch.map` is post-composition. -/
@[simp] theorem ChainCat.liftToCh_hom_obj {K : BPSet} (σ : Aut K) (a : ChainCat.Obj K) :
    (Aut.liftToCh K σ).hom.toFunctor.obj a = ⟨a.dims, a.map ≫ σ.hom⟩ := rfl

/-- The lift leaves the underlying wedge map of a morphism unchanged. -/
@[simp] theorem ChainCat.liftToCh_hom_map_φ {K : BPSet} (σ : Aut K) {a b : ChainCat.Obj K}
    (g : a ⟶ b) : ChainCat.Hom.φ ((Aut.liftToCh K σ).hom.toFunctor.map g) = ChainCat.Hom.φ g :=
  rfl

/-- An automorphism `Φ` of `Ch K` is **orientation-preserving** if it preserves the
dimension sequence of every chain (ClaudeSetup.md §7).

**[RESEARCH] this definition is provisional and may need strengthening** (e.g.
compatibility with altitude); it is isolated here so it is easy to revise. -/
def OrientationPreserving {K : BPSet} (Φ : Aut (Ch.obj K)) : Prop :=
  ∀ a : ChainCat.Obj K, (Φ.hom.toFunctor.obj a).dims = a.dims

/-- **Lifts are orientation-preserving (unconditional).**  The automorphism of
`Ch K` induced by an automorphism of `K` preserves every dimension sequence — it
only post-composes the classifying maps.  This is the strengthening of the lifting
lemma promised in §7, and needs no side conditions on `K`. -/
theorem Aut.liftToCh_orientationPreserving {K : BPSet} (σ : Aut K) :
    OrientationPreserving (Aut.liftToCh K σ) := fun _ => rfl

/-- **Joint surjectivity of chains.**  Every cell of `K` is realised by some chain:
it lies in the image of that chain's classifying wedge map.  This is the geometric
input to faithfulness of the lift below; it holds for accessible `K`
(`Conjectures.chainsJointlySurjective_of_accessible`). -/
def ChainsJointlySurjective (K : BPSet) : Prop :=
  ∀ {n : ℕ} (c : K.toPsh.cells n),
    ∃ (a : ChainCat.Obj K) (x : (BPSet.serialWedge a.dims).toPsh.cells n),
      a.map.hom.app (op (Box.ob n)) x = c

/-- **Faithfulness of the lift, from joint surjectivity.**  If every cell of `K`
lies on some chain, then `Aut.liftToCh K` is injective: distinct automorphisms of
`K` induce distinct automorphisms of `Ch K`.

The action of the lift is read off the classifying maps — `liftToCh σ`
post-composes a chain's map by `σ` (`liftToCh_hom_obj`).  So if `liftToCh σ` and
`liftToCh τ` agree, then `a.map ≫ σ = a.map ≫ τ` for every chain `a`; evaluating at
a cell `c = a.map x` (joint surjectivity) gives `σ c = τ c`.  Hence `σ = τ`. -/
theorem Aut.liftToCh_injective_of_jointlySurjective {K : BPSet}
    (h : ChainsJointlySurjective K) : Function.Injective (Aut.liftToCh K) := by
  intro σ τ hστ
  have key : ∀ a : ChainCat.Obj K, a.map ≫ σ.hom = a.map ≫ τ.hom := by
    intro a
    have hobj := congrArg (fun (Φ : Aut (Ch.obj K)) => Φ.hom.toFunctor.obj a) hστ
    simp only [ChainCat.liftToCh_hom_obj] at hobj
    injection hobj
  apply Iso.ext
  apply BPSet.hom_ext
  ext bop c
  obtain ⟨a, x, hx⟩ := h (n := bop.unop.dim) c
  rw [← hx]
  exact congrArg (fun (f : _ ⟶ K) => f.hom.app (op (Box.ob bop.unop.dim)) x) (key a)
