import CubeChains.Concurrency.Presentation.GarsideFamily
import CubeChains.Machinery.Presentation.Localize

/-!
# Concurrency/Presentation/GarsideFunctor — the Garside polygraph is a functor on `BPSet`

`wedgeHoms` is Yoneda restricted along `serialWedgeInclusion`, hence a functor of `K`; a colimit
over `Ch Z` is a functor of the presheaf indexing its copies (`elementsColim`); and the
Garside polygraph is the composite.  A map of `K` re-indexes the copies without moving any chain, so
the family is never consulted.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits

namespace ChainCat

/-- `⋁- ⟶ K`, naturally in `K`. -/
def wedgeHomsFunctor : BPSet ⥤ ((Ch Zbp)ᵒᵖ ⥤ Type) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj serialWedgeInclusion.op

@[simp] theorem wedgeHomsFunctor_obj (K : BPSet) : wedgeHomsFunctor.obj K = wedgeHoms K := rfl

/-- **A map of `K` moves an element without moving its chain** — the copies of the colimit are
re-indexed and nothing else. -/
def chainElt {K K' : BPSet} (f : K ⟶ K') :
    ((wedgeHoms K).Elements)ᵒᵖ ⥤ ((wedgeHoms K').Elements)ᵒᵖ :=
  elementsReindex (wedgeHomsFunctor.map f)

theorem W_pushforward {K K' : BPSet} (f : K ⟶ K') {a b : Ch K} {g : a ⟶ b} (hg : W K g) :
    W K' ((ChainCat.pushforward f).map g) :=
  (W_iff_monotone_coordMap _).mpr ((W_iff_monotone_coordMap g).mp hg)

/-- **`Ch f`, localized.** -/
noncomputable def chLocMap {K K' : BPSet} (f : K ⟶ K') :
    (W K).Localization ⥤ (W K').Localization :=
  MorphismProperty.localizedMap (W K) (W K') (ChainCat.pushforward f)
    fun _ hg => W_pushforward f hg

@[simp] theorem chLocMap_obj_Q {K K' : BPSet} (f : K ⟶ K') (a : Ch K) :
    (chLocMap f).obj ((W K).Q.obj a) = (W K').Q.obj ((ChainCat.pushforward f).obj a) := rfl

theorem chLocMap_id (K : BPSet) : chLocMap (𝟙 K) = 𝟭 _ :=
  MorphismProperty.localizedMap_id (W K) fun _ hg => hg

theorem chLocMap_comp {K K' K'' : BPSet} (f : K ⟶ K') (g : K' ⟶ K'') :
    chLocMap (f ≫ g) = chLocMap f ⋙ chLocMap g :=
  MorphismProperty.localizedMap_comp (W K) (W K') (W K'') (ChainCat.pushforward f)
    (ChainCat.pushforward g) (fun _ hg => W_pushforward f hg) (fun _ hg => W_pushforward g hg)
    fun _ hg => W_pushforward g (W_pushforward f hg)

/-! ## …on the side a presentation reads

A presentation of `Ch K` by refinements presents `(Ch K)ᵒᵖ`, so the class and its localization live
there too; the pushforward is the same functor, reversed. -/

/-- **`Ch f`, localized on the opposite.** -/
noncomputable def chLocOpMap {K K' : BPSet} (f : K ⟶ K') :
    ((W K).op).Localization ⥤ ((W K').op).Localization :=
  MorphismProperty.localizedMap ((W K).op) ((W K').op) (ChainCat.pushforward f).op
    fun _ hg => W_pushforward f hg

theorem Q_comp_chLocOpMap {K K' : BPSet} (f : K ⟶ K') :
    ((W K).op).Q ⋙ chLocOpMap f = (ChainCat.pushforward f).op ⋙ ((W K').op).Q :=
  MorphismProperty.Q_comp_localizedMap ((W K).op) ((W K').op) (ChainCat.pushforward f).op
    fun _ hg => W_pushforward f hg

theorem chLocOpMap_id (K : BPSet) : chLocOpMap (𝟙 K) = 𝟭 _ :=
  MorphismProperty.localizedMap_id ((W K).op) fun _ hg => hg

theorem chLocOpMap_comp {K K' K'' : BPSet} (f : K ⟶ K') (g : K' ⟶ K'') :
    chLocOpMap (f ≫ g) = chLocOpMap f ⋙ chLocOpMap g :=
  MorphismProperty.localizedMap_comp ((W K).op) ((W K').op) ((W K'').op)
    (ChainCat.pushforward f).op (ChainCat.pushforward g).op (fun _ hg => W_pushforward f hg)
    (fun _ hg => W_pushforward g hg) fun _ hg => W_pushforward g (W_pushforward f hg)

/-- **The localized base, as a functor of `K`.** -/
noncomputable def chLocOpFunctor : BPSet ⥤ Cat where
  obj K := Cat.of (((W K).op).Localization)
  map f := (chLocOpMap f).toCatHom
  map_id K := Cat.ext (chLocOpMap_id K)
  map_comp f g := Cat.ext (chLocOpMap_comp f g)

@[simp] theorem chLocOpFunctor_map {K K' : BPSet} (f : K ⟶ K') :
    chLocOpFunctor.map f = (chLocOpMap f).toCatHom := rfl

/-! ## The chain polygraph, as a functor -/

/-- **The Garside polygraph is a functor on `BPSet`** — the copies, re-indexed. -/
noncomputable def garsideFunctor : BPSet ⥤ Polygraph.{0, 0, 0} :=
  wedgeHomsFunctor ⋙ elementsColim garsideFam

@[simp] theorem garsideFunctor_obj (K : BPSet) : garsideFunctor.obj K = garsidePoly K := rfl

/-- **The Garside polygraph on a map of `K`.** -/
noncomputable def garsideMap {K K' : BPSet} (f : K ⟶ K') : garsidePoly K ⟶ garsidePoly K' :=
  garsideFunctor.map f

@[simp] theorem garsideFunctor_map {K K' : BPSet} (f : K ⟶ K') :
    garsideFunctor.map f = garsideMap f := rfl

/-- **…and it is the colimit's own comparison**: a copy goes to the copy it is re-indexed to. -/
theorem ι_garsideMap {K K' : BPSet} (f : K ⟶ K') (c : ((wedgeHoms K).Elements)ᵒᵖ) :
    colimit.ι (elementsPoly (wedgeHoms K) garsideFam) c ≫ garsideMap f
      = colimit.ι (elementsPoly (wedgeHoms K') garsideFam) ((chainElt f).obj c) :=
  ι_elementsColim garsideFam (wedgeHomsFunctor.map f) c

/-- **A 0-cell stays in its copy** — a tuple of bead simples is not moved by a map of `K`. -/
theorem garsideMap_ιV {K K' : BPSet} (f : K ⟶ K') (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a : (garsideFam.obj (eltBase (wedgeHoms K) c)).V) :
    (garsideMap f).pre.obj (ιV K garsideFam c a) = ιV K' garsideFam ((chainElt f).obj c) a :=
  elementsColim_map_pre_obj garsideFam (wedgeHomsFunctor.map f) c a

end ChainCat
