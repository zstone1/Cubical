import CubeChains.Precubical.Chains.WedgeMap
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Endomorphism

/-!
# Precubical/Chains/Category

Objects of `Ch K` are cube chains, presented as bi-pointed maps `⋁dims ⟶ K`; a morphism is a
bi-pointed map of wedges making the triangle over `K` commute.  `chFunctor : BPSet ⥤ Cat` sends
`f : K ⟶ L` to post-composition, so an `Aut K` lifts to an `Aut (Ch K)` by mathlib's
`Functor.mapAut`.
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

The map determines the dimension sequence, so what is left of a `Ch K` object is exactly a
`CubeChain K` — cubes composable from `init` to `final`.  Naming that equivalence once lets
downstream constructions work on cube lists instead of rediscovering `beadCell_inj`/`wedgeDesc`. -/

/-- Two chains with the same cube list are equal — the map is determined by the beads it reads. -/
theorem Obj.eq_of_toList {c d : Ch K}
    (h : (beadCell c.map.hom).toList = (beadCell d.map.hom).toList) : c = d := by
  obtain ⟨cd, cm⟩ := c
  obtain ⟨dd, dm⟩ := d
  obtain rfl : cd = dd := congrArg Sigma.fst (Beads.sigma_eq_of_toList_eq h)
  exact hom_ext (beadCell_inj cd cm.hom dm.hom (Beads.toList_injective h)
    (cm.app_init.trans dm.app_init.symm)) ▸ rfl

/-- **A chain object is its cube chain.**  Both round trips hold on the nose; `Beads.ofList` is
the one place the flat view's shape transport is paid. -/
def chCubes (K : BPSet) : Ch K ≃ CubeChain K where
  toFun c :=
    ⟨(beadCell c.map.hom).toList, by
      have h0 := beadCell_isCubeChain c.dims c.map.hom
      rwa [c.map.app_init, c.map.app_final] at h0⟩
  invFun cs := ⟨_, wedgeDescHom (Beads.ofList cs.cubes) (by rw [Beads.toList_ofList]; exact cs.2)⟩
  left_inv _ := Obj.eq_of_toList (by
    simp only [CubeChain.cubes, beadCell_wedgeDescHom, Beads.toList_ofList])
  right_inv _ := CubeChain.eq_of_cubes (by
    simp only [CubeChain.cubes, beadCell_wedgeDescHom, Beads.toList_ofList])

@[simp] theorem chCubes_val (c : Ch K) : (chCubes K c).cubes = (beadCell c.map.hom).toList := rfl

@[simp] theorem chCubes_dims (c : Ch K) : (chCubes K c).dims = c.dims :=
  Beads.map_fst_toList _

@[simp] theorem chCubes_symm_dims (cs : CubeChain K) : ((chCubes K).symm cs).dims = cs.dims := rfl

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

