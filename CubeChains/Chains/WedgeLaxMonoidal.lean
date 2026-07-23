import CubeChains.Foundations.WedgeMonoidal
import CubeChains.Chains.Split
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat

/-!
# Chains/WedgeLaxMonoidal — `chFunctor` is lax monoidal `(BPSet, ∨) ⥤ (Cat, ×)`

The tensorator is `chConcat` (unconditional); the unit comparison is `chUnit`.  Strong monoidal
(`chSegal`) holds only under `AdmitsAltitude`, so globally this is lax.

`chConcat` transports `⊗ₘ` along the append iso (`Chains/Segal`), so each coherence square below
is the matching `MonoidalTransport` lemma fed the append iso's own coherence — objects via
`tensorTransport_assoc_refl`, morphisms via `tensorTransport_assoc`.
-/

open CategoryTheory MonoidalCategory ChainCat BPSet

namespace ChainCat

attribute [local instance] ChainCat.wedgeMonoidal

/-- Two chain morphisms are `HEq` when their objects agree and their underlying wedge maps do. -/
theorem chain_hom_hext {K : BPSet} {a a' b b' : Ch K} (ha : a = a') (hb : b = b')
    {f : a ⟶ b} {g : a' ⟶ b'} (hφ : HEq (Hom.φ f) (Hom.φ g)) : HEq f g := by
  subst ha; subst hb
  exact heq_of_eq (hom_ext' (eq_of_heq hφ))

/-- Concatenating on the left with the empty chain leaves a morphism's wedge map unchanged
(the left factor `□⁰` contributes no dimensions, so `[] ++ b.dims = b.dims`). -/
theorem concatHomφ_nil_left {K : BPSet} {b b' : Ch K} (g : b ⟶ b') :
    concatHomφ (𝟙 (default : Ch (□0))) g = Hom.φ g :=
  tensorTransport_leftUnitor (Hom.φ g)

/-- Concatenating on the right with the empty chain leaves a morphism's wedge map unchanged, up to
the `append_nil` reindexing (`HEq` because the domain/codomain types differ). -/
theorem concatHomφ_nil_right {K : BPSet} {b b' : Ch K} (g : b ⟶ b') :
    HEq (Hom.φ g) (concatHomφ g (𝟙 (default : Ch (□0)))) := by
  refine HEq.symm ((conj_eqToHom_iff_heq (concatHomφ g (𝟙 (default : Ch (□0)))) (Hom.φ g)
    (congrArg BPSet.serialWedge (List.append_nil b.dims))
    (congrArg BPSet.serialWedge (List.append_nil b'.dims))).mp ?_)
  have key : concatHomφ g (𝟙 (default : Ch (□0)))
        ≫ eqToHom (congrArg BPSet.serialWedge (List.append_nil b'.dims))
      = eqToHom (congrArg BPSet.serialWedge (List.append_nil b.dims)) ≫ Hom.φ g :=
    tensorTransport_rightUnit _ _ (serialWedgeAppendIso_right_unitality b.dims)
      (serialWedgeAppendIso_right_unitality b'.dims) (Hom.φ g)
  exact ((comp_eqToHom_iff _ _ _).mp key).trans (Category.assoc _ _ _)

/-- **Associativity of the chain-morphism concatenation**, across the `List.append_assoc`
reindexing: `concatHomφ` transports `⊗ₘ` along the append iso, so this is
`tensorTransport_assoc` fed `serialWedgeAppendIso_assoc` on both sides. -/
theorem concatHomφ_assoc {X Y Z : BPSet} {a a' : Ch X} {b b' : Ch Y} {c c' : Ch Z}
    (fa : a ⟶ a') (fb : b ⟶ b') (fc : c ⟶ c') :
    HEq (concatHomφ ((chConcat X Y).map ((fa, fb) : (a, b) ⟶ (a', b'))) fc)
        (concatHomφ fa ((chConcat Y Z).map ((fb, fc) : (b, c) ⟶ (b', c')))) := by
  refine (conj_eqToHom_iff_heq
    (concatHomφ ((chConcat X Y).map ((fa, fb) : (a, b) ⟶ (a', b'))) fc)
    (concatHomφ fa ((chConcat Y Z).map ((fb, fc) : (b, c) ⟶ (b', c'))))
    (congrArg BPSet.serialWedge (List.append_assoc a.dims b.dims c.dims))
    (congrArg BPSet.serialWedge (List.append_assoc a'.dims b'.dims c'.dims))).mp ?_
  have key : concatHomφ ((chConcat X Y).map ((fa, fb) : (a, b) ⟶ (a', b'))) fc
        ≫ eqToHom (congrArg BPSet.serialWedge (List.append_assoc a'.dims b'.dims c'.dims))
      = eqToHom (congrArg BPSet.serialWedge (List.append_assoc a.dims b.dims c.dims))
        ≫ concatHomφ fa ((chConcat Y Z).map ((fb, fc) : (b, c) ⟶ (b', c'))) :=
    tensorTransport_assoc _ _ _ _ _ _ _ _
      (serialWedgeAppendIso_assoc a.dims b.dims c.dims)
      (serialWedgeAppendIso_assoc a'.dims b'.dims c'.dims) fa.φ fb.φ fc.φ
  exact ((comp_eqToHom_iff _ _ _).mp key).trans (Category.assoc _ _ _)

end ChainCat


/-! ### Lax-monoidal coherence laws for `chFunctor`

The fields of the `LaxMonoidal` instance below, each extracted so the instance is a thin assembly.
The tensorator is `μ X Y = chConcat X Y`, the unit `ε` is the terminal chain; the squares are
checked object-wise (`Cat.ext` + `Functor.hext`), each object leg a `MonoidalTransport` lemma. -/

/-- Tensorator naturality in the left factor. -/
theorem chConcat_μ_natural_left {X Y : BPSet} (f : X ⟶ Y) (X' : BPSet) :
    chFunctor.map f ▷ chFunctor.obj X' ≫ (chConcat Y X').toCatHom
      = (chConcat X X').toCatHom ≫ chFunctor.map (f ▷ X') := by
  apply Cat.ext
  have hob : ∀ ax : Ch X × Ch X',
      (chConcat Y X').obj (⟨ax.1.dims, ax.1.map ≫ f⟩, ax.2)
        = (pushforward (f ▷ X')).obj ((chConcat X X').obj ax) := by
    intro ⟨a, x⟩
    exact congrArg (ChainCat.Obj.mk (a.dims ++ x.dims))
      (tensorTransport_comp_whiskerRight _ a.map x.map f).symm
  exact Functor.hext hob (fun ax ax' g => chain_hom_hext (hob ax) (hob ax') HEq.rfl)

/-- Tensorator naturality in the right factor. -/
theorem chConcat_μ_natural_right {X Y : BPSet} (X' : BPSet) (f : X ⟶ Y) :
    chFunctor.obj X' ◁ chFunctor.map f ≫ (chConcat X' Y).toCatHom
      = (chConcat X' X).toCatHom ≫ chFunctor.map (X' ◁ f) := by
  apply Cat.ext
  have hob : ∀ xa : Ch X' × Ch X,
      (chConcat X' Y).obj (xa.1, ⟨xa.2.dims, xa.2.map ≫ f⟩)
        = (pushforward (X' ◁ f)).obj ((chConcat X' X).obj xa) := by
    intro ⟨x, a⟩
    exact congrArg (ChainCat.Obj.mk (x.dims ++ a.dims))
      (tensorTransport_comp_whiskerLeft _ x.map a.map f).symm
  exact Functor.hext hob (fun xa xa' g => chain_hom_hext (hob xa) (hob xa') HEq.rfl)

/-- Associativity of the tensorator. -/
theorem chConcat_associativity (X Y Z : BPSet) :
    (chConcat X Y).toCatHom ▷ chFunctor.obj Z ≫ (chConcat (wedge2 X Y) Z).toCatHom
        ≫ chFunctor.map (α_ X Y Z).hom
      = (α_ (chFunctor.obj X) (chFunctor.obj Y) (chFunctor.obj Z)).hom
        ≫ chFunctor.obj X ◁ (chConcat Y Z).toCatHom ≫ (chConcat X (wedge2 Y Z)).toCatHom := by
  apply Cat.ext
  have hob : ∀ (a : Ch X) (b : Ch Y) (c : Ch Z),
      (ChainCat.Obj.mk ((a.dims ++ b.dims) ++ c.dims)
          (concatChainMap (wedge2 X Y) Z ⟨a.dims ++ b.dims, concatChainMap X Y a b⟩ c
            ≫ (α_ X Y Z).hom) : Ch (wedge2 X (wedge2 Y Z)))
        = ChainCat.Obj.mk (a.dims ++ (b.dims ++ c.dims))
            (concatChainMap X (wedge2 Y Z) a ⟨b.dims ++ c.dims, concatChainMap Y Z b c⟩) :=
    fun a b c => ChainCat.Obj.mk_eq_mk (List.append_assoc a.dims b.dims c.dims)
      (tensorTransport_assoc_refl _ _ _ _
        (serialWedgeAppendIso_assoc a.dims b.dims c.dims) a.map b.map c.map)
  refine Functor.hext (fun o => ?_) (fun o o' g => ?_)
  · obtain ⟨⟨a, b⟩, c⟩ := o
    exact hob a b c
  · obtain ⟨⟨a, b⟩, c⟩ := o
    obtain ⟨⟨a', b'⟩, c'⟩ := o'
    obtain ⟨⟨fa, fb⟩, fc⟩ := g
    exact chain_hom_hext (hob a b c) (hob a' b' c') (ChainCat.concatHomφ_assoc fa fb fc)

/-- Left unitality. -/
theorem chConcat_left_unitality (X : BPSet) :
    (λ_ (chFunctor.obj X)).hom
      = (Cat.fromChosenTerminalEquiv.symm (default : Ch (□0))).toCatHom ▷ chFunctor.obj X
        ≫ (chConcat (𝟙_ BPSet) X).toCatHom ≫ chFunctor.map (λ_ X).hom := by
  apply Cat.ext
  have hob : ∀ tx : ↥(𝟙_ Cat) × Ch X, tx.2
      = (pushforward (λ_ X).hom).obj ((chConcat (□0) X).obj (default, tx.2)) := by
    intro ⟨t, x⟩
    exact congrArg (ChainCat.Obj.mk x.dims) (tensorTransport_leftUnitor x.map).symm
  refine Functor.hext hob (fun o o' g => chain_hom_hext (hob o) (hob o') ?_)
  exact heq_of_eq (concatHomφ_nil_left g.2).symm

/-- Right unitality. -/
theorem chConcat_right_unitality (X : BPSet) :
    (ρ_ (chFunctor.obj X)).hom
      = chFunctor.obj X ◁ (Cat.fromChosenTerminalEquiv.symm (default : Ch (□0))).toCatHom
        ≫ (chConcat X (𝟙_ BPSet)).toCatHom ≫ chFunctor.map (ρ_ X).hom := by
  apply Cat.ext
  have hob : ∀ xt : Ch X × ↥(𝟙_ Cat), xt.1
      = (pushforward (ρ_ X).hom).obj ((chConcat X (□0)).obj (xt.1, default)) := by
    intro ⟨x, t⟩
    refine ChainCat.Obj.mk_eq_mk (List.append_nil x.dims).symm ?_
    have key : concatChainMap X (□0) x default ≫ (ρ_ X).hom
        = serialWedgeNilBP x.dims ≫ x.map :=
      tensorTransport_rightUnit_refl _ (serialWedgeAppendIso_right_unitality x.dims) x.map
    change x.map = eqToHom (congrArg BPSet.serialWedge (List.append_nil x.dims).symm)
      ≫ concatChainMap X (□0) x default ≫ (ρ_ X).hom
    rw [key]
    simp [serialWedgeNilBP]
  refine Functor.hext hob (fun o o' g => chain_hom_hext (hob o) (hob o') ?_)
  exact ChainCat.concatHomφ_nil_right g.1

instance : chFunctor.LaxMonoidal where
  ε := (Cat.fromChosenTerminalEquiv.symm (default : Ch (□0))).toCatHom
  μ X Y := (chConcat X Y).toCatHom
  μ_natural_left := chConcat_μ_natural_left
  μ_natural_right := chConcat_μ_natural_right
  associativity := chConcat_associativity
  left_unitality := chConcat_left_unitality
  right_unitality := chConcat_right_unitality
