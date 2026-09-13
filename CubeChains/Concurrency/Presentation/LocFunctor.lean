import CubeChains.Concurrency.Presentation.ElementsFibration
import CubeChains.Machinery.Presentation.Localize

/-!
# Concurrency/Presentation/LocFunctor — the localized base, as a functor of `K`

`wedgeHoms` is Yoneda restricted along `serialWedgeInclusion`, hence a functor of `K`; `pushforward`
preserves merges, so the localization is a functor of `K` too.  A presentation by refinements
presents `(Ch K)ᵒᵖ`, so the side every presentation reads is the opposite one.
-/

open CategoryTheory Opposite BPSet CubeChains

namespace ChainCat

/-- `⋁- ⟶ K`, naturally in `K`. -/
def wedgeHomsFunctor : BPSet ⥤ ((Ch Zbp)ᵒᵖ ⥤ Type) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj serialWedgeInclusion.op

/-- **A map of `K` neither creates nor destroys a merge** — `W` is monotonicity of the coordinate
map, which reads the wedge map alone. -/
theorem W_pushforward_iff {K K' : BPSet} (f : K ⟶ K') {a b : Ch K} (g : a ⟶ b) :
    W K' ((ChainCat.pushforward f).map g) ↔ W K g :=
  (W_iff_monotone_coordMap _).trans (W_iff_monotone_coordMap g).symm

/-- **`Ch f`, localized.** -/
noncomputable def chLocMap {K K' : BPSet} (f : K ⟶ K') :
    (W K).Localization ⥤ (W K').Localization :=
  MorphismProperty.localizedMap (W K) (W K') (ChainCat.pushforward f)
    fun g hg => (W_pushforward_iff f g).mpr hg

theorem chLocMap_id (K : BPSet) : chLocMap (𝟙 K) = 𝟭 _ :=
  MorphismProperty.localizedMap_id (W K) fun _ hg => hg

theorem chLocMap_comp {K K' K'' : BPSet} (f : K ⟶ K') (g : K' ⟶ K'') :
    chLocMap (f ≫ g) = chLocMap f ⋙ chLocMap g :=
  MorphismProperty.localizedMap_comp (W K) (W K') (W K'') (ChainCat.pushforward f)
    (ChainCat.pushforward g) (fun u hu => (W_pushforward_iff f u).mpr hu)
    (fun u hu => (W_pushforward_iff g u).mpr hu)
    fun u hu => (W_pushforward_iff g _).mpr ((W_pushforward_iff f u).mpr hu)

/-! ## …on the side a presentation reads

A presentation of `Ch K` by refinements presents `(Ch K)ᵒᵖ`, so the class and its localization live
there too; the pushforward is the same functor, reversed. -/

/-- **`Ch f`, localized on the opposite.** -/
noncomputable def chLocOpMap {K K' : BPSet} (f : K ⟶ K') :
    ((W K).op).Localization ⥤ ((W K').op).Localization :=
  MorphismProperty.localizedMap ((W K).op) ((W K').op) (ChainCat.pushforward f).op
    fun g hg => (W_pushforward_iff f g.unop).mpr hg

theorem Q_comp_chLocOpMap {K K' : BPSet} (f : K ⟶ K') :
    ((W K).op).Q ⋙ chLocOpMap f = (ChainCat.pushforward f).op ⋙ ((W K').op).Q :=
  MorphismProperty.Q_comp_localizedMap ((W K).op) ((W K').op) (ChainCat.pushforward f).op
    fun g hg => (W_pushforward_iff f g.unop).mpr hg

theorem chLocOpMap_id (K : BPSet) : chLocOpMap (𝟙 K) = 𝟭 _ :=
  MorphismProperty.localizedMap_id ((W K).op) fun _ hg => hg

theorem chLocOpMap_comp {K K' K'' : BPSet} (f : K ⟶ K') (g : K' ⟶ K'') :
    chLocOpMap (f ≫ g) = chLocOpMap f ⋙ chLocOpMap g :=
  MorphismProperty.localizedMap_comp ((W K).op) ((W K').op) ((W K'').op)
    (ChainCat.pushforward f).op (ChainCat.pushforward g).op
    (fun u hu => (W_pushforward_iff f u.unop).mpr hu)
    (fun u hu => (W_pushforward_iff g u.unop).mpr hu)
    fun u hu => (W_pushforward_iff g _).mpr ((W_pushforward_iff f u.unop).mpr hu)

/-- **The localized base, as a functor of `K`.** -/
noncomputable def chLocOpFunctor : BPSet ⥤ Cat where
  obj K := Cat.of (((W K).op).Localization)
  map f := (chLocOpMap f).toCatHom
  map_id K := Cat.ext (chLocOpMap_id K)
  map_comp f g := Cat.ext (chLocOpMap_comp f g)

@[simp] theorem chLocOpFunctor_map {K K' : BPSet} (f : K ⟶ K') :
    chLocOpFunctor.map f = (chLocOpMap f).toCatHom := rfl

end ChainCat
