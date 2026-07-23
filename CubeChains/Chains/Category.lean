import CubeChains.Chains.WedgeMap
import CubeChains.Foundations.Wedge
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Endomorphism

/-!
# Chains/Category

Objects of `Ch K` are cube chains, presented (via §3) as bi-pointed maps
`⋁dims ⟶ K`.  A morphism `a ⟶ b` is a bi-pointed map of wedges
`φ : ⋁(dimSeq a) ⟶ ⋁(dimSeq b)` making the triangle over `K` commute,
`φ ≫ b = a`.  `Ch : BPSet ⥤ Cat` sends `K ↦ Ch K` and `f : K ⟶ L` to
post-composition; the **lifting lemma** `Aut.liftToCh` (an `Aut K` lifts to
`Aut (Ch K)`) is mathlib's `Functor.mapAut`.
-/

open CategoryTheory CategoryTheory.Limits Opposite BPSet CubeChain

namespace ChainCat

/-- An object of `Ch K`: a dimension sequence with a bi-pointed map of the serial
wedge into `K` (equivalently, a cube chain). -/
structure Obj (K : BPSet) where
  /-- The dimension sequence. -/
  dims : List ℕ+
  /-- The classifying bi-pointed map `⋁dims ⟶ K`. -/
  map : ⋁dims ⟶ K

/-- A morphism of `Ch K`: a bi-pointed map of wedges commuting over `K`. -/
@[ext]
structure Hom {K : BPSet} (a b : Obj K) where
  /-- The underlying wedge map. -/
  φ : ⋁a.dims ⟶ ⋁b.dims
  /-- The triangle over `K` commutes. -/
  w : φ ≫ b.map = a.map

instance (K : BPSet) : Category (Obj K) where
  Hom a b := Hom a b
  id a := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.φ ≫ g.φ, by rw [Category.assoc, g.w, f.w]⟩
  id_comp f := Hom.ext (Category.id_comp _)
  comp_id f := Hom.ext (Category.comp_id _)
  assoc f g h := Hom.ext (Category.assoc _ _ _)

@[simp] theorem id_φ {K : BPSet} (a : Obj K) : Hom.φ (𝟙 a) = 𝟙 _ := rfl

@[simp] theorem comp_φ {K : BPSet} {a b c : Obj K} (f : a ⟶ b) (g : b ⟶ c) :
    Hom.φ (f ≫ g) = Hom.φ f ≫ Hom.φ g := rfl

/-- `Ch K` — the cube-chain category of `K`.  Notation, so it also prints. -/
notation:max "Ch " K:max => ChainCat.Obj K

/-- `fᵂ` — the presheaf map underlying a chain morphism's wedge map (`f.φ.hom`).  Notation, so the
elaborated term is unchanged: `blockIdx fᵂ i` is `blockIdx f.φ.hom i` on the nose. -/
notation:max f "ᵂ" => BPSet.Hom.hom (ChainCat.Hom.φ f)

/-- A bead of a chain (an index into its dimension sequence). -/
abbrev Bead {K : BPSet} (a : Ch K) : Type := Fin a.dims.length

/-- The dimension of a bead — the number of events it fires at once. -/
abbrev beadDim {K : BPSet} (a : Ch K) (i : Bead a) : ℕ := (a.dims.get i : ℕ)

@[ext] theorem hom_ext' {K : BPSet} {a b : Obj K} {f g : a ⟶ b}
    (h : Hom.φ f = Hom.φ g) : f = g := Hom.ext h

/-- Two chains agree when their dimension sequences do and their classifying maps agree across
the induced `⋁`-reindexing.  (The `dims` field is not a subsingleton, so a plain `congrArg` only
covers the case where the sequences are syntactically equal.) -/
theorem Obj.mk_eq_mk {K : BPSet} {d d' : List ℕ+} (h : d = d') {m : ⋁d ⟶ K} {m' : ⋁d' ⟶ K}
    (hm : m = eqToHom (congrArg BPSet.serialWedge h) ≫ m') :
    (⟨d, m⟩ : Obj K) = ⟨d', m'⟩ := by
  subst h
  rw [hm, eqToHom_refl, Category.id_comp]

/-- Converse of `Obj.mk_eq_mk`: read a chain-object equality back as a `dims` equality plus a
transported map equality. -/
theorem Obj.eq_mk_of_eq {K : BPSet} {d d' : List ℕ+} {m : ⋁d ⟶ K} {m' : ⋁d' ⟶ K}
    (e : (⟨d, m⟩ : Obj K) = ⟨d', m'⟩) :
    ∃ h : d = d', m = eqToHom (congrArg BPSet.serialWedge h) ≫ m' := by
  injection e with hd hm
  subst hd
  exact ⟨rfl, by simpa using eq_of_heq hm⟩

/-- Post-composition functor `Ch K ⥤ Ch L` induced by `f : K ⟶ L`. -/
def pushforward {K L : BPSet} (f : K ⟶ L) : Obj K ⥤ Obj L where
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

/-! ## A chain object *is* its cube list

`Ch K` is presented as a dimension sequence plus a map out of the serial wedge, but the map
determines the sequence: what is left is a list of cubes composable from `init` to `final`.
Naming that equivalence once lets downstream constructions work on lists, where they are
one-liners, instead of rediscovering `wedgeToCubes_dims`/`_inj`/`wedgeDesc` at each call site. -/

/-- A **cube list** of `K`: cubes composable from `init` to `final`. -/
def CubeList (K : BPSet) : Type :=
  {cs : List (Σ n : ℕ+, K.cells (n : ℕ)) // IsCubeChain K.init cs K.final}

namespace CubeList

/-- The dimension sequence a cube list realises. -/
def dims (cs : CubeList K) : List ℕ+ := cs.1.map (·.1)

@[ext] theorem ext {cs ds : CubeList K} (h : cs.1 = ds.1) : cs = ds := Subtype.ext h

end CubeList

/-- Two chains with the same cube list are equal — the map is determined by the cubes it reads. -/
theorem Obj.eq_of_wedgeToCubes {c d : Ch K}
    (h : wedgeToCubes ⟨c.dims, c.map.hom⟩ = wedgeToCubes ⟨d.dims, d.map.hom⟩) : c = d := by
  obtain ⟨cd, cm⟩ := c
  obtain ⟨dd, dm⟩ := d
  have hdims : cd = dd := by
    rw [← wedgeToCubes_dims cd cm.hom, ← wedgeToCubes_dims dd dm.hom, h]
  subst hdims
  exact hom_ext (wedgeToCubes_inj cd cm.hom dm.hom h (cm.app_init.trans dm.app_init.symm)) ▸ rfl

/-- **A chain object is its cube list.**  Both round trips hold on the nose. -/
def chCubes (K : BPSet) : Ch K ≃ CubeList K where
  toFun c :=
    ⟨wedgeToCubes ⟨c.dims, c.map.hom⟩, by
      have h0 := wedgeToCubes_isCubeChain c.dims c.map.hom
      rwa [c.map.app_init, c.map.app_final] at h0⟩
  invFun cs := ⟨cs.dims, wedgeDescHom cs.1 cs.2⟩
  left_inv _ := Obj.eq_of_wedgeToCubes (wedgeToCubes_wedgeDescHom _ _)
  right_inv cs := CubeList.ext (wedgeToCubes_wedgeDescHom cs.1 cs.2)

@[simp] theorem chCubes_val (c : Ch K) : (chCubes K c).1 = wedgeToCubes ⟨c.dims, c.map.hom⟩ := rfl

@[simp] theorem chCubes_dims (c : Ch K) : (chCubes K c).dims = c.dims :=
  wedgeToCubes_dims c.dims c.map.hom

@[simp] theorem chCubes_symm_dims (cs : CubeList K) : ((chCubes K).symm cs).dims = cs.dims := rfl

end ChainCat

/-- The cube chain functor `BPSet ⥤ Cat`: `K ↦ Ch K`, `f ↦` post-composition.  (Named apart from
the `Ch K` notation, which is the *object type*; `chFunctor.obj K` is the bundled `Cat`.) -/
def chFunctor : BPSet ⥤ Cat where
  obj K := Cat.of (Ch K)
  map f := (ChainCat.pushforward f).toCatHom
  map_id K := Cat.ext (ChainCat.pushforward_id K)
  map_comp f g := Cat.ext (ChainCat.pushforward_comp f g)

/-- **Lifting lemma.** Every automorphism of a bi-pointed
precubical set `K` lifts to an automorphism of `Ch K`, as a group homomorphism.
This is the functoriality of `Ch`, packaged by `Functor.mapAut`. -/
def Aut.liftToCh (K : BPSet) : Aut K →* Aut (chFunctor.obj K) :=
  chFunctor.mapAut K

/-- The lift acts on a chain by post-composing its classifying map (the dimension
sequence is untouched).  This is definitional, since `Ch.map` is post-composition. -/
@[simp] theorem ChainCat.liftToCh_hom_obj {K : BPSet} (σ : Aut K) (a : Ch K) :
    (Aut.liftToCh K σ).hom.toFunctor.obj a = ⟨a.dims, a.map ≫ σ.hom⟩ := rfl

/-- The lift leaves the underlying wedge map of a morphism unchanged. -/
@[simp] theorem ChainCat.liftToCh_hom_map_φ {K : BPSet} (σ : Aut K) {a b : Ch K}
    (g : a ⟶ b) : ChainCat.Hom.φ ((Aut.liftToCh K σ).hom.toFunctor.map g) = ChainCat.Hom.φ g :=
  rfl

/-- An automorphism `Φ` of `Ch K` is **orientation-preserving** if it preserves the
dimension sequence of every chain. -/
def OrientationPreserving {K : BPSet} (Φ : Aut (chFunctor.obj K)) : Prop :=
  ∀ a : Ch K, (Φ.hom.toFunctor.obj a).dims = a.dims

/-- **Lifts are orientation-preserving.**  The automorphism of `Ch K` induced by an
automorphism of `K` preserves every dimension sequence — it only post-composes the
classifying maps.  Needs no side conditions on `K`. -/
theorem Aut.liftToCh_orientationPreserving {K : BPSet} (σ : Aut K) :
    OrientationPreserving (Aut.liftToCh K σ) := fun _ => rfl

/-- **Joint surjectivity of chains.**  Every cell of `K` is realised by some chain:
it lies in the image of that chain's classifying wedge map.  This is the geometric
input to faithfulness of the lift below; it holds for accessible `K`. -/
def ChainsJointlySurjective (K : BPSet) : Prop :=
  ∀ {n : ℕ} (c : K.cells n),
    ∃ (a : Ch K) (x : (⋁a.dims).cells n),
      a.map.hom⟪n⟫ x = c

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
  have key : ∀ a : Ch K, a.map ≫ σ.hom = a.map ≫ τ.hom := by
    intro a
    have hobj := congrArg (fun (Φ : Aut (chFunctor.obj K)) => Φ.hom.toFunctor.obj a) hστ
    simp only [ChainCat.liftToCh_hom_obj] at hobj
    injection hobj
  apply Iso.ext
  apply hom_ext
  ext bop c
  obtain ⟨a, x, hx⟩ := h (n := bop.unop.dim) c
  rw [← hx]
  exact congrArg (fun (f : _ ⟶ K) => f.hom⟪bop.unop.dim⟫ x) (key a)
