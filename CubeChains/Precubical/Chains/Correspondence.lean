import CubeChains.Precubical.Chains.Basic
import CubeChains.Precubical.Chains.WedgeMap
import CubeChains.Precubical.Chains.Refine
import CubeChains.Precubical.Chains.Category
import CubeChains.Concurrency.Grading.BlockDecomp
import CubeChains.Precubical.Basic.Altitude
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Precubical/Chains/Correspondence

The chain↔wedge-map correspondence

`equivWedgeHom : CubeChain K ≃ Σ dims, (⋁dims ⟶ K)`

built from `wedgeDesc`/`beadCell` (`Precubical/Chains/WedgeMap.lean`) and the flat-view bridge
`Beads.toList`/`Beads.ofList` (`Precubical/Chains/Basic.lean`), lifted to an equivalence of
categories `equivWedgeCat : RefineObj K ≌ Ch K` under `NonSelfLinked` +
`AdmitsAltitude`, via thinness (`Quiver.IsThin`) and `descent_mono`.
-/

open CategoryTheory CategoryTheory.Limits Opposite StdCube BPSet

namespace CubeChain

variable {K : BPSet}

/-- **Bi-pointed maps out of a serial wedge are determined by their beads.**
The initial-vertex side condition of `beadCell_inj` is automatic for bi-pointed maps
(both send `init ↦ K.init`, via `app_init`). -/
theorem bpset_hom_ext_of_beadCell {d : List ℕ+} {f g : ⋁d ⟶ K}
    (h : beadCell f.hom = beadCell g.hom) : f = g :=
  hom_ext (beadCell_inj d f.hom g.hom h (f.app_init.trans g.app_init.symm))

/-- **The map↔chain correspondence.**  Cube chains in `K` are exactly bi-pointed maps out of a
serial wedge — `chCubes` with the chain object unbundled into its two fields. -/
def equivWedgeHom (K : BPSet) : CubeChain K ≃ Σ dims : List ℕ+, (⋁dims ⟶ K) :=
  (ChainCat.chCubes K).symm.trans
    { toFun := fun a => ⟨a.dims, a.map⟩
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-! ### Lifting `equivWedgeHom` to the categories

The object maps are the object equivalence (`wedgeDescHom`/`beadCell`).  The
morphism maps split asymmetrically:

* The **backward** map `wedge ⥤ refine` (`wedgeToRefineMap`) needs no side condition
  on `K`: a wedge map preserves cell dimension (it is a natural transformation of
  presheaves), so each positive-dimensional `a`-block lands in a *unique* `b`-block
  as a genuine face, giving the reindexing and the inclusion; monotonicity is then
  forced by the cube's vertex order.

* The **forward** map `refine ⥤ wedge` (`refineWedgeMap`) needs `NonSelfLinked` +
  `AdmitsAltitude`.  A `ChainRefine` records, per `x`-block, a face inclusion into a
  `y`-block satisfying `inclSpec` *in `K`*, but nothing forces consecutive inclusions
  to meet at the shared junction *inside the wedge* `⋁y.dims` — and `K`'s descent map
  need not be injective on vertices, so junction agreement in `K` does not transfer
  to the wedge.  Both hypotheses are needed, and *within-cube* non-self-linkedness
  (every cube has distinct vertices) is not enough:

  1. `K = □²` with the corners `(1,0) ~ (0,1)` identified; `y = [c]` the 2-cube;
     `x = [bottom edge, top edge]`.  Then `[bottom, top]` is a chain in `K` (the two
     middle corners agree) but is the "broken" path, not a subdivision of the square.
     Excluded by `NonSelfLinked` (the 2-cube's canonical map folds two corners).

  2. `K =` two 2-cubes `c₀, c₁` glued in a chain, with additionally `c₀(1,0) ~
     c₁(1,0)`.  Each cube keeps 4 distinct vertices, yet `x = [bottom edge of c₀,
     right edge of c₁]` is a valid `ChainRefine` (`f = [0,1]`) whose inclusions do
     **not** meet at the `c₀/c₁` junction.  Excluded by `AdmitsAltitude`: the directed
     cycle `c₀(1,0) → e → c₀(1,0)` forces an altitude that is at once `+2` and `0`.

  Non-self-linkedness embeds each cube (controlling *same-block* junctions), the
  altitude rules out directed cycles (controlling *cross-block* junctions), and
  together they make every chain's descent map **injective on vertices** — which
  lifts each junction equality `K.vertex₁ (x-cubeᵢ) = K.vertex₀ (x-cubeᵢ₊₁)` back
  into `⋁y.dims`, discharging the forward functor's cocone condition. -/

/-! #### Thinness of `Ch K` (the wedge side)

`Ch K` is a poset (`hom`-sets are subsingletons), which makes the morphism part of
the equivalence essentially free.  A morphism is pinned by its block restrictions
(`serialWedge_hom_ext`), each of which composes with the target descent map to
`a.map`; once that descent map is injective on cells they agree.  The injectivity is
the one substantial input. -/

/-- **Altitude lower bound for a descent map.**  Every cell of `⋁cubes` has, after
descending into `K`, altitude at least that of the chain's start vertex `a`.  Induction
on the chain: head cells are faces of `c₀` (altitude `≥ alt c₀ = alt a`), tail cells
recurse (and `alt (vertex₁ c₀) ≥ alt (vertex₀ c₀) = alt a`). -/
theorem descent_alt_ge (alt : ∀ n, K.cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude K.toPsh alt) :
    ∀ (a b : K.cells 0) {d : List ℕ+} (c : Beads K.toPsh d)
      (hch : IsCubeChain a c.toList b) {m : ℕ} (z : (⋁d).cells m),
      alt 0 a ≤ alt m ((wedgeDesc a b c hch).hom⟪m⟫ z)
  | a, b, [], c, hch, m, z => by
      rw [show (wedgeDesc a b c hch).hom⟪m⟫ z
          = (K.toPsh.cubeMap a)⟪m⟫ z from rfl,
        PrecubicalSet.alt_cubeMap alt hax]
      omega
  | a, b, n :: rest, c, hch, m, z => by
      rcases wedge2_cell_cases (□(n : ℕ)) _ m z with ⟨x, hx⟩ | ⟨y, hy⟩
      · rw [← hx, wedgeDesc_inl_app,
          show (yonedaEquiv.symm (c 0))⟪m⟫ x
            = (K.toPsh.cubeMap (c 0))⟪m⟫ x from rfl,
          PrecubicalSet.alt_cubeMap alt hax,
          show alt 0 a = alt ((n :: rest).get 0 : ℕ) (c 0) from by
            rw [← hch.1, PrecubicalSet.alt_vertex₀ alt hax]]
        omega
      · rw [← hy, wedgeDesc_inr_app]
        refine le_trans ?_ (descent_alt_ge alt hax (K.toPsh.vertex₁ (c 0)) b c.tail hch.2 y)
        rw [PrecubicalSet.alt_vertex₁ alt hax, ← hch.1, PrecubicalSet.alt_vertex₀ alt hax]
        omega

/-- **The descent map of a chain is pointwise injective** under `NonSelfLinked` +
altitude.  Induction on the chain (`inl`/`inr` cell split): `inl/inl` closes by
`NonSelfLinked`, `inr/inr` by the inductive hypothesis, and the cross cases by the
**altitude separation** — a positive head-face has altitude `< alt (vertex₁ c₀)` while
every tail cell has altitude `≥ alt (vertex₁ c₀)`, so a collision forces `m = 0` and
(by `trueCount = n ⟹` top vertex + `wedge2_glue` + the inductive hypothesis) the two
cells to be the shared junction. -/
theorem descent_app_inj (h₁ : K.NonSelfLinked) (alt : ∀ n, K.cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude K.toPsh alt) :
    ∀ (a b : K.cells 0) {d : List ℕ+} (c : Beads K.toPsh d)
      (hch : IsCubeChain a c.toList b) (m : ℕ),
      Function.Injective ((wedgeDesc a b c hch).hom⟪m⟫)
  | a, _, [], _, _, m => fun _ _ huv => h₁ 0 a m huv
  | a, b, n :: rest, c, hch, m => by
      -- The cross case (head face `inl xu` collides with tail cell `inr yv`).
      have cross : ∀ (xu : (□(n : ℕ)).cells m) (yv : (⋁rest).cells m),
          (K.toPsh.cubeMap (c 0))⟪m⟫ xu
            = (wedgeDesc (K.toPsh.vertex₁ (c 0)) b c.tail hch.2).hom⟪m⟫ yv →
          (Glue.inl (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫ xu
            = (Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫ yv := by
        intro xu yv hcc
        have h1 := PrecubicalSet.alt_cubeMap alt hax (c 0) xu
        have h3 := descent_alt_ge alt hax (K.toPsh.vertex₁ (c 0)) b c.tail hch.2 yv
        have h4 := PrecubicalSet.alt_vertex₁ alt hax (c 0)
        have hT := trueCount_le (ev xu)
        rw [hcc] at h1
        simp only [List.get_cons_zero] at h1 h3 h4
        have hd : (▫(n : ℕ)).dim = (n : ℕ) := rfl
        have hd2 : (Opposite.unop (Opposite.op ▫m)).dim = m := rfl
        have hn1 : 0 < (n : ℕ) := n.2
        have hm : m = 0 ∧ trueCount (ev xu) = (n : ℕ) := by omega
        obtain ⟨hm0, htop⟩ := hm
        subst hm0
        have hxu : xu = (□(n : ℕ)).final := by
          have hev : ev xu = constVertex (n : ℕ) true :=
            trueCount_eq_top _ htop
          have hxu' : xu = canonicalMap (ev xu) :=
            ((cubeRepr (stdPre (n : ℕ)) 0).left_inv xu).symm
          rw [hxu', hev]; rfl
        have hyv : yv = (⋁rest).init := by
          apply descent_app_inj h₁ alt hax (K.toPsh.vertex₁ (c 0)) b c.tail hch.2 0
          rw [← hcc, hxu]
          exact (wedgeDesc_init (K.toPsh.vertex₁ (c 0)) b c.tail hch.2).symm
        rw [hxu, hyv]
        exact wedge2_glue (□(n : ℕ)) (⋁rest)
      intro u v huv
      rcases wedge2_cell_cases (□(n : ℕ)) _ m u with ⟨xu, hxu⟩ | ⟨yu, hyu⟩ <;>
        rcases wedge2_cell_cases (□(n : ℕ)) _ m v with ⟨xv, hxv⟩ | ⟨yv, hyv⟩
      · rw [← hxu, ← hxv, wedgeDesc_inl_app, wedgeDesc_inl_app] at huv
        rw [← hxu, ← hxv, h₁ (n : ℕ) (c 0) m huv]
      · rw [← hxu, ← hyv, wedgeDesc_inl_app, wedgeDesc_inr_app] at huv
        rw [← hxu, ← hyv]
        exact cross xu yv huv
      · rw [← hyu, ← hxv, wedgeDesc_inr_app, wedgeDesc_inl_app] at huv
        rw [← hyu, ← hxv]
        exact (cross xv yu huv.symm).symm
      · rw [← hyu, ← hyv, wedgeDesc_inr_app, wedgeDesc_inr_app] at huv
        rw [← hyu, ← hyv, descent_app_inj h₁ alt hax (K.toPsh.vertex₁ (c 0)) b c.tail hch.2 m huv]

/-- A chain's descent map `⋁b.dims ⟶ K` is a monomorphism (equivalently, injective on
cells in every dimension — `Mono` in the presheaf topos is pointwise injectivity).

Both side conditions are needed: `NonSelfLinked` controls collisions *within* a
block, while `AdmitsAltitude` rules out the directed cycles that would let two
*different* blocks carry a common positive cell — the two-squares set of the section
docstring is `NonSelfLinked` but carries no altitude, and there a single shared edge
has two preimages, breaking injectivity (and thinness) outright. -/
theorem wedgeDesc_mono (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (a b' : K.cells 0) {d : List ℕ+} (c : Beads K.toPsh d)
    (hch : IsCubeChain a c.toList b') : Mono (wedgeDesc a b' c hch).hom := by
  obtain ⟨alt, hax, _⟩ := h₂
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨X⟩
  rw [mono_iff_injective]
  exact descent_app_inj h₁ alt hax a b' c hch X.dim

/-- A chain's descent map `⋁b.dims ⟶ K` is a monomorphism: `b.map` is the descent of its own
beads (`bpset_hom_ext_of_beadCell`), which is mono by `wedgeDesc_mono`. -/
theorem descent_mono (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) (b : Ch K) :
    Mono b.map.hom := by
  have hch : IsCubeChain K.init (beadCell b.map.hom).toList K.final := by
    have h := beadCell_isCubeChain b.dims b.map.hom
    rwa [b.map.app_init, b.map.app_final] at h
  have key : b.map = wedgeDescHom (beadCell b.map.hom) hch :=
    bpset_hom_ext_of_beadCell (beadCell_wedgeDescHom _ hch).symm
  have hmono : Mono (wedgeDescHom (beadCell b.map.hom) hch).hom :=
    wedgeDesc_mono h₁ h₂ K.init K.final _ hch
  rwa [← congrArg BPSet.Hom.hom key] at hmono

/-- **`Ch K` is thin** under `NonSelfLinked` + `AdmitsAltitude`: any two morphisms
`a ⟶ b` agree.  Mechanical given `descent_mono`: both `φ`s compose with `b.map` to
`a.map`, so they cancel against the monomorphism `b.map`.  (The altitude, beyond
`NonSelfLinked`, is what this `Mono`-cancellation route needs.) -/
theorem chainCat_hom_subsingleton (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (a b : Ch K) : Subsingleton (a ⟶ b) := by
  haveI := descent_mono h₁ h₂ b
  refine ⟨fun f g => ?_⟩
  apply ChainCat.hom_ext'
  apply hom_ext
  have hf : (ChainCat.Hom.φ f).hom ≫ b.map.hom = a.map.hom := congrArg BPSet.Hom.hom f.w
  have hg : (ChainCat.Hom.φ g).hom ≫ b.map.hom = a.map.hom := congrArg BPSet.Hom.hom g.w
  rw [← cancel_mono b.map.hom, hf, hg]

/-- Object part of the forward functor `refine ⥤ wedge`: a chain `↦` its dimension
sequence together with its descent map. -/
def refineToWedgeObj (x : RefineObj K.init K.final) : Ch K where
  dims := x.dims
  map := wedgeDescHom x.cubes x.isChain

/-- The beads `x` induces inside `⋁y.dims`: bead `i` of `x` sent into bead `f i` of `y`
along the recorded inclusion `f.incl i`, read as a cell via Yoneda. -/
def inducedCell {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    Beads (⋁y.dims).toPsh x.dims :=
  fun i => yonedaEquiv (yoneda.map (f.incl i) ≫ ιᵂ y.dims (f.refinement i))

/-- `y`'s descent map sends the `i`-th induced cell back to the `i`-th cube of `x`
(the `inclSpec` computation): restricting to bead `f i` via `ι_comp_wedgeDescHom` gives
`y`-cube `f i`, and pulling back along `f.incl i` gives `x`-cube `i`. -/
theorem refineToWedgeObj_map_inducedCell {x y : RefineObj K.init K.final} (f : x ⟶ y)
    (i : Fin x.dims.length) :
    (wedgeDescHom y.cubes y.isChain).hom⟪((x.dims.get i : ℕ))⟫ (inducedCell f i) = x.cubes i := by
  refine (yonedaEquiv_comp _ _).symm.trans ?_
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (yoneda.map (f.incl i) ≫ ·)
    (ι_comp_wedgeDescHom y.cubes y.isChain (f.refinement i))).trans ?_
  rw [yonedaEquiv_symm_naturality_left, f.inclSpec i]

/-- Pushing the induced beads of `f` through `y`'s descent map recovers `x`'s cubes. -/
theorem inducedCell_push {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    (inducedCell f).push (wedgeDescHom y.cubes y.isChain).hom = x.cubes :=
  funext (refineToWedgeObj_map_inducedCell f)

/-- The induced cells form a chain in `⋁y.dims`, from its initial to its final
vertex.  Reflected through `y`'s descent map `D_y`: that map is injective
(`descent_mono`), commutes with `vertex₀`/`vertex₁`
(`PrecubicalSet.map_vertex₀`/`map_vertex₁`), and
sends the induced cells to `x`'s cubes (`refineToWedgeObj_map_inducedCell`), so the
chain property descends from `x.isChain` via `isCubeChain_of_map_injective`.  (The
empty case is covered too: `K.init = K.final` forces `D_y init = D_y final`, hence
`init = final` in the wedge.) -/
theorem inducedChain (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    IsCubeChain (⋁y.dims).init (inducedCell f).toList (⋁y.dims).final := by
  have hmono : Mono (refineToWedgeObj y).map.hom := descent_mono h₁ h₂ (refineToWedgeObj y)
  have hinj : ∀ n, Function.Injective ((wedgeDescHom y.cubes y.isChain).hom⟪n⟫) :=
    fun n => (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app _).mp hmono (op ▫n))
  refine isCubeChain_of_map_injective (wedgeDescHom y.cubes y.isChain).hom hinj
    (inducedCell f).toList _ _ ?_
  rw [← Beads.toList_push, inducedCell_push f,
    (wedgeDescHom y.cubes y.isChain).app_init, (wedgeDescHom y.cubes y.isChain).app_final]
  exact x.isChain

/-- The wedge map `⋁x.dims ⟶ ⋁y.dims` induced by a refinement `f : x ⟶ y`: the descent of the
induced beads into `⋁y.dims`.

`ChainRefine` carries the face inclusions as **data**, so bead `i` of `x` includes into bead
`f i` of `y` by `inducedCell`; these assemble through `wedgeDesc` once they form a chain
(`inducedChain`, the only `descent_mono` dependency here). -/
def refineWedgeMap (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f : x ⟶ y) : ⋁x.dims ⟶ ⋁y.dims :=
  wedgeDescHom (inducedCell f) (inducedChain h₁ h₂ f)

/-- The induced wedge map commutes over `K` (the triangle of `ChainCat.Hom`): both sides read
off the same beads — `refineWedgeMap f ≫ y.descent` reads off (via `beadCell_push`) to the
induced cells pushed by `y`'s descent, which are the `x`-cubes. -/
theorem refineWedgeMap_w (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    refineWedgeMap h₁ h₂ f ≫ (refineToWedgeObj y).map = (refineToWedgeObj x).map :=
  bpset_hom_ext_of_beadCell <| by
    rw [comp_hom, beadCell_push, refineWedgeMap, beadCell_wedgeDescHom]
    change (inducedCell f).push (wedgeDescHom y.cubes y.isChain).hom
      = beadCell (wedgeDescHom x.cubes x.isChain).hom
    rw [inducedCell_push, beadCell_wedgeDescHom]

/-- The forward functor `refine ⥤ wedge`.  Functoriality is free from thinness of
`Ch K` (`chainCat_hom_subsingleton`): the two laws are equalities of morphisms in a
category whose hom-sets are subsingletons. -/
def refineToWedge (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    RefineObj K.init K.final ⥤ Ch K :=
  haveI : Quiver.IsThin (Ch K) := chainCat_hom_subsingleton h₁ h₂
  { obj := refineToWedgeObj
    map f := ⟨refineWedgeMap h₁ h₂ f, refineWedgeMap_w h₁ h₂ f⟩
    map_id _ := Subsingleton.elim _ _
    map_comp _ _ := Subsingleton.elim _ _ }

/-- The `i`-th induced cell lies in block `f.refinement i` of `⋁y.dims` (it is the
Yoneda image of `f.incl i` along that block's inclusion `ι`). -/
theorem inducedCell_mem_block {x y : RefineObj K.init K.final} (f : x ⟶ y)
    (i : Fin x.dims.length) :
    ∃ c, (ιᵂ y.dims (f.refinement i))⟪((x.dims.get i : ℕ))⟫ c = inducedCell f i :=
  ⟨yonedaEquiv (yoneda.map (f.incl i)), (yonedaEquiv_comp _ _).symm⟩

/-- **Block index is determined**: two refinements `f g : x ⟶ y` send each `x`-block to
the same `y`-block.  The induced wedge maps agree (`Ch K` is thin, `descent_mono`), so
the induced cells agree; block-uniqueness of the serial wedge then pins the index. -/
theorem refinement_eq (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f g : x ⟶ y) (i : Fin x.dims.length) :
    f.refinement i = g.refinement i := by
  have hwedge : refineWedgeMap h₁ h₂ f = refineWedgeMap h₁ h₂ g :=
    congrArg ChainCat.Hom.φ
      (Subsingleton.elim (h := chainCat_hom_subsingleton h₁ h₂ _ _)
        ((refineToWedge h₁ h₂).map f) ((refineToWedge h₁ h₂).map g))
  have hcell : inducedCell f = inducedCell g := by
    have h := congrArg (fun m : ⋁x.dims ⟶ ⋁y.dims => beadCell m.hom) hwedge
    simpa only [refineWedgeMap, beadCell_wedgeDescHom] using h
  obtain ⟨cf, hcf⟩ := inducedCell_mem_block f i
  obtain ⟨cg, hcg⟩ := inducedCell_mem_block g i
  exact serialWedge_block_unique y.dims (x.dims.get i).2 _ _ (inducedCell f i)
    ⟨cf, hcf⟩ ⟨cg, hcg.trans (congrFun hcell.symm i)⟩

/-- **The refinement category is thin** under `NonSelfLinked` + `AdmitsAltitude`.  The
block index is forced by `refinement_eq` (the induced wedge map is unique because `Ch K` is
thin); substituting it makes the two `incl` families *homogeneous*, and then `NonSelfLinked`
forces them equal (`incl i` is recovered from `K.map (incl i).op (y-cube) = x-cube`, the
`y`-cube's canonical map being injective). -/
theorem refineObj_hom_subsingleton (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (x y : RefineObj K.init K.final) : Subsingleton (x ⟶ y) := by
  refine ⟨fun f g => ?_⟩
  have href : f.refinement = g.refinement := funext (refinement_eq h₁ h₂ f g)
  obtain ⟨_, _, incf, sf⟩ := f
  obtain ⟨_, _, incg, sg⟩ := g
  obtain rfl := href
  refine ChainRefine.ext rfl (heq_of_eq (funext fun i => ?_))
  refine h₁ _ (y.cubes _) _ ?_
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply, yonedaEquiv_symm_app_apply,
    ← sf i, ← sg i]

/-- Object part of the backward functor `wedge ⥤ refine`: a wedge map `↦` the beads read off it. -/
def wedgeToRefineObj (a : Ch K) : RefineObj K.init K.final where
  dims := a.dims
  cubes := beadCell a.map.hom
  isChain := by
    have h := beadCell_isCubeChain a.dims a.map.hom
    rwa [a.map.app_init, a.map.app_final] at h

/-- **Block data assembles into a refinement**: a monotone reindexing of `a`-beads into `b`-beads,
with face inclusions along which the `b`-cubes pull back to the `a`-cubes. -/
def refineOfBlocks {a b : Ch K} (R : ChainCat.Bead a → ChainCat.Bead b) (hR : Monotone R)
    (incl : ∀ i, ▫((a.dims.get i : ℕ)) ⟶ ▫((b.dims.get (R i) : ℕ)))
    (hincl : ∀ i, beadCell a.map.hom i = K.toPsh.map (incl i).op (beadCell b.map.hom (R i))) :
    wedgeToRefineObj a ⟶ wedgeToRefineObj b where
  refinement := R
  refinementMono := hR
  incl := incl
  inclSpec := hincl

/-- The refinement read off a wedge-map morphism: its block decomposition, ordered by the serial
wedge's *own* altitude (`serialWedge_blockIdx_monotone` needs no hypothesis on `K`). -/
def wedgeToRefineMap {a b : Ch K} (g : a ⟶ b) :
    wedgeToRefineObj a ⟶ wedgeToRefineObj b :=
  refineOfBlocks (blockIdx gᵂ)
      (fun _ _ hij => serialWedge_blockIdx_monotone gᵂ (ChainCat.Hom.φ g).app_init hij)
      (blockFace gᵂ) <| fun i => by
    have hw : gᵂ ≫ b.map.hom = a.map.hom := by
      have h := congrArg BPSet.Hom.hom g.w; rwa [comp_hom] at h
    rw [← hw]; exact beadCell_comp_block gᵂ b.map.hom i

/-- The backward functor `wedge ⥤ refine`.  Functoriality is free from thinness of
the refinement category (`refineObj_hom_subsingleton`). -/
def wedgeToRefine (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    Ch K ⥤ RefineObj K.init K.final :=
  haveI : Quiver.IsThin (RefineObj K.init K.final) := refineObj_hom_subsingleton h₁ h₂
  { obj := wedgeToRefineObj
    map g := wedgeToRefineMap g
    map_id _ := Subsingleton.elim _ _
    map_comp _ _ := Subsingleton.elim _ _ }

/-- A refinement object at a given shape is determined by its beads (`isChain` is a `Prop`). -/
theorem RefineObj.ext' {a b : K.cells 0} {d : List ℕ+} {c c' : Beads K.toPsh d}
    {h : IsCubeChain a c.toList b} {h' : IsCubeChain a c'.toList b} (e : c = c') :
    (⟨d, c, h⟩ : RefineObj a b) = ⟨d, c', h'⟩ := by subst e; rfl

/-- **Unit round-trip (strict).**  Reading the beads back off a chain's descent map
recovers the chain on the nose — `wedgeToRefine ⋙ refineToWedge` is the identity on
objects. -/
theorem wedgeToRefineObj_refineToWedgeObj (x : RefineObj K.init K.final) :
    wedgeToRefineObj (refineToWedgeObj x) = x := by
  obtain ⟨d, c, hc⟩ := x
  exact RefineObj.ext' (beadCell_wedgeDescHom c hc)

/-- **Counit round-trip (strict).**  Descending the beads read off a wedge map `a` recovers
`a` on the nose — the shapes agree by construction, and the two classifying maps read off the
same beads.  An *equality* of `Ch K` objects, so the counit is an `eqToIso` just like the unit. -/
theorem refineToWedgeObj_wedgeToRefineObj (a : Ch K) :
    refineToWedgeObj (wedgeToRefineObj a) = a := by
  obtain ⟨d, m⟩ := a
  exact congrArg (ChainCat.Obj.mk d) (bpset_hom_ext_of_beadCell (beadCell_wedgeDescHom _ _))

/-- **The refine ≌ wedge equivalence.**  `refineToWedge`/`wedgeToRefine` are mutually
inverse: both round trips are strict equalities of objects
(`wedgeToRefineObj_refineToWedgeObj`, `refineToWedgeObj_wedgeToRefineObj`), so unit and counit
are `eqToIso`s; all naturality and the triangle coherence are free from thinness. -/
def equivWedgeCat (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    RefineObj K.init K.final ≌ Ch K :=
  haveI : Quiver.IsThin (RefineObj K.init K.final) := refineObj_hom_subsingleton h₁ h₂
  haveI : Quiver.IsThin (Ch K) := chainCat_hom_subsingleton h₁ h₂
  { functor := refineToWedge h₁ h₂
    inverse := wedgeToRefine h₁ h₂
    unitIso := NatIso.ofComponents
      (fun x => eqToIso (wedgeToRefineObj_refineToWedgeObj x).symm)
      (fun _ => Subsingleton.elim _ _)
    counitIso := NatIso.ofComponents
      (fun a => eqToIso (refineToWedgeObj_wedgeToRefineObj a))
      (fun _ => Subsingleton.elim _ _)
    functor_unitIso_comp _ := Subsingleton.elim _ _ }

end CubeChain
