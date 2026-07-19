import CubeChains.Chains.Basic
import CubeChains.Chains.WedgeMap
import CubeChains.Chains.Refine
import CubeChains.Chains.Category
import CubeChains.Chains.BlockDecomp
import CubeChains.Foundations.Altitude
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Chains/Correspondence

The chain↔wedge-map correspondence

`equivWedgeHom : CubeChain K ≃ Σ dims, (⋁dims ⟶ K)`

built from `wedgeDesc`/`wedgeToCubes` (`Chains/WedgeMap.lean`) and the chain bridge
`isCubeChain`/`ofIsCubeChain` (`Chains/Basic.lean`), lifted to an equivalence of
categories `equivWedgeCat : RefineObj K ≌ Ch K` under `NonSelfLinked` +
`AdmitsAltitude`, via thinness (`Quiver.IsThin`) and `descent_mono`.
-/

open CategoryTheory CategoryTheory.Limits Opposite StdCube BPSet

namespace CubeChain

variable {K : BPSet}

/-- **Bi-pointed maps out of a serial wedge are determined by the cubes they read off.**
The initial-vertex side condition of `wedgeToCubes_inj` is automatic for bi-pointed maps
(both send `init ↦ K.init`, via `app_init`). -/
theorem bpset_hom_ext_of_wedgeToCubes {dims : List ℕ+}
    {f g : ⋁dims ⟶ K}
    (h : wedgeToCubes ⟨dims, f.hom⟩ = wedgeToCubes ⟨dims, g.hom⟩) : f = g :=
  hom_ext (wedgeToCubes_inj dims f.hom g.hom h (f.app_init.trans g.app_init.symm))

/-- The wedge map classifying a chain (forward map of the §3 correspondence). -/
def wedgeOfChain (C : CubeChain K) :
    Σ dims : List ℕ+, (⋁dims ⟶ K) :=
  ⟨C.dims, wedgeDescHom _ (isCubeChain C)⟩

/-- The chain read off a wedge map (inverse map). -/
def chainOfWedge (φ : Σ dims : List ℕ+, (⋁dims ⟶ K)) :
    CubeChain K :=
  ofIsCubeChain (wedgeToCubes ⟨φ.1, φ.2.hom⟩) <| by
    have h := wedgeToCubes_isCubeChain φ.1 φ.2.hom
    rwa [φ.2.app_init, φ.2.app_final] at h

theorem chainOfWedge_wedgeOfChain (C : CubeChain K) : chainOfWedge (wedgeOfChain C) = C := by
  apply eq_of_cubes
  change wedgeToCubes (K := K)
      ⟨C.cubes.map (·.1), (wedgeDesc K.init K.final C.cubes (isCubeChain C)).hom⟩
    = C.cubes
  exact wedgeToCubes_wedgeDesc K.init K.final C.cubes (isCubeChain C)

theorem chainOfWedge_injective : Function.Injective (chainOfWedge (K := K)) := by
  rintro ⟨dims₁, ψ₁⟩ ⟨dims₂, ψ₂⟩ heq
  have hcubes : wedgeToCubes ⟨dims₁, ψ₁.hom⟩ = wedgeToCubes ⟨dims₂, ψ₂.hom⟩ := by
    have := congrArg CubeChain.cubes heq
    simpa only [chainOfWedge, ofIsCubeChain] using this
  obtain rfl : dims₁ = dims₂ := by
    rw [← wedgeToCubes_dims dims₁ ψ₁.hom, ← wedgeToCubes_dims dims₂ ψ₂.hom, hcubes]
  exact (Sigma.mk.injEq ..).mpr ⟨rfl, heq_of_eq (bpset_hom_ext_of_wedgeToCubes hcubes)⟩

/-- **The map↔chain correspondence.**  Cube chains in `K` are
exactly bi-pointed maps out of a serial wedge: forward is the descent map
(`wedgeOfChain`), inverse reads the cubes off (`chainOfWedge`). -/
def equivWedgeHom (K : BPSet) :
    CubeChain K ≃ Σ dims : List ℕ+, (⋁dims ⟶ K) where
  toFun := wedgeOfChain
  invFun := chainOfWedge
  left_inv := chainOfWedge_wedgeOfChain
  right_inv φ := chainOfWedge_injective (chainOfWedge_wedgeOfChain (chainOfWedge φ))

/-! ### Lifting `equivWedgeHom` to the categories

The object maps are the object equivalence (`wedgeOfChain`/`chainOfWedge`).  The
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
    ∀ (a b : K.cells 0) (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
      (hch : IsCubeChain a cubes b) {m : ℕ}
      (z : (⋁(cubes.map (·.1))).cells m),
      alt 0 a ≤ alt m ((wedgeDesc a b cubes hch).hom⟪m⟫ z)
  | a, b, [], hch, m, z => by
      rw [show (wedgeDesc a b [] hch).hom⟪m⟫ z
          = (K.toPsh.cubeMap a)⟪m⟫ z from rfl,
        PrecubicalSet.alt_cubeMap alt hax]
      omega
  | a, b, ⟨n, c⟩ :: rest, hch, m, z => by
      rcases wedge2_cell_cases (□(n : ℕ)) _ m z with ⟨x, hx⟩ | ⟨y, hy⟩
      · rw [← hx, wedgeDesc_inl_app,
          show (yonedaEquiv.symm c)⟪m⟫ x
            = (K.toPsh.cubeMap c)⟪m⟫ x from rfl,
          PrecubicalSet.alt_cubeMap alt hax,
          show alt 0 a = alt (n : ℕ) c from by rw [← hch.1, PrecubicalSet.alt_vertex₀ alt hax]]
        omega
      · rw [← hy, wedgeDesc_inr_app]
        refine le_trans ?_ (descent_alt_ge alt hax (K.toPsh.vertex₁ c) b rest hch.2 y)
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
    ∀ (a b : K.cells 0) (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
      (hch : IsCubeChain a cubes b) (m : ℕ),
      Function.Injective ((wedgeDesc a b cubes hch).hom⟪m⟫)
  | a, b, [], hch, m => fun u v huv => h₁ 0 a m huv
  | a, b, ⟨n, c⟩ :: rest, hch, m => by
      -- The cross case (head face `inl xu` collides with tail cell `inr yv`).
      have cross : ∀ (xu : (□(n : ℕ)).cells m)
          (yv : (⋁(rest.map (·.1))).cells m),
          (K.toPsh.cubeMap c)⟪m⟫ xu
            = (wedgeDesc (K.toPsh.vertex₁ c) b rest hch.2).hom⟪m⟫ yv →
          (Glue.inl (□(n : ℕ)).finalVertex
              (⋁(rest.map (·.1))).initVertex)⟪m⟫ xu
            = (Glue.inr (□(n : ℕ)).finalVertex
              (⋁(rest.map (·.1))).initVertex)⟪m⟫ yv := by
        intro xu yv hcc
        have h1 := PrecubicalSet.alt_cubeMap alt hax c xu
        have h3 := descent_alt_ge alt hax (K.toPsh.vertex₁ c) b rest hch.2 yv
        have h4 := PrecubicalSet.alt_vertex₁ alt hax c
        have hT := trueCount_le (ev xu)
        rw [hcc] at h1
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
        have hyv : yv = (⋁(rest.map (·.1))).init := by
          apply descent_app_inj h₁ alt hax (K.toPsh.vertex₁ c) b rest hch.2 0
          rw [← hcc, hxu]
          exact (wedgeDesc_init (K.toPsh.vertex₁ c) b rest hch.2).symm
        rw [hxu, hyv]
        exact wedge2_glue (□(n : ℕ)) (⋁(rest.map (·.1)))
      intro u v huv
      rcases wedge2_cell_cases (□(n : ℕ)) _ m u with ⟨xu, hxu⟩ | ⟨yu, hyu⟩ <;>
        rcases wedge2_cell_cases (□(n : ℕ)) _ m v with ⟨xv, hxv⟩ | ⟨yv, hyv⟩
      · rw [← hxu, ← hxv, wedgeDesc_inl_app, wedgeDesc_inl_app] at huv
        rw [← hxu, ← hxv, h₁ (n : ℕ) c m huv]
      · rw [← hxu, ← hyv, wedgeDesc_inl_app, wedgeDesc_inr_app] at huv
        rw [← hxu, ← hyv]
        exact cross xu yv huv
      · rw [← hyu, ← hxv, wedgeDesc_inr_app, wedgeDesc_inl_app] at huv
        rw [← hyu, ← hxv]
        exact (cross xv yu huv.symm).symm
      · rw [← hyu, ← hyv, wedgeDesc_inr_app, wedgeDesc_inr_app] at huv
        rw [← hyu, ← hyv, descent_app_inj h₁ alt hax (K.toPsh.vertex₁ c) b rest hch.2 m huv]

/-- Reading cubes off a map precomposed with a domain `eqToHom` (a `dims`-transport)
ignores the transport. -/
theorem wedgeToCubes_eqToHom {d₁ d₂ : List ℕ+} (h : d₁ = d₂)
    (φ : (⋁d₂).toPsh ⟶ K.toPsh) :
    wedgeToCubes ⟨d₁, eqToHom (congrArg (fun l => (⋁l).toPsh) h) ≫ φ⟩
      = wedgeToCubes ⟨d₂, φ⟩ := by
  subst h; simp

/-- The domain `eqToHom` (`dims`-transport) sends the initial vertex to the initial
vertex. -/
theorem serialWedge_eqToHom_init {d₁ d₂ : List ℕ+} (hd : d₂ = d₁) :
    (eqToHom (congrArg (fun d => (⋁d).toPsh) hd.symm))⟪0⟫
        (⋁d₁).init
      = (⋁d₂).init := by
  subst hd; simp

/-- A chain's descent map `⋁b.dims ⟶ K` is a monomorphism (equivalently, injective on
cells in every dimension — `Mono` in the presheaf topos is pointwise injectivity).

Both side conditions are needed: `NonSelfLinked` controls collisions *within* a
block, while `AdmitsAltitude` rules out the directed cycles that would let two
*different* blocks carry a common positive cell — the two-squares set of the section
docstring is `NonSelfLinked` but carries no altitude, and there a single shared edge
has two preimages, breaking injectivity (and thinness) outright. -/
theorem wedgeDesc_mono (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (a b' : K.cells 0) (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
    (hch : IsCubeChain a cubes b') : Mono (wedgeDesc a b' cubes hch).hom := by
  obtain ⟨alt, hax, _⟩ := h₂
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨X⟩
  rw [mono_iff_injective]
  exact descent_app_inj h₁ alt hax a b' cubes hch X.dim

/-- A chain's descent map `⋁b.dims ⟶ K` is a monomorphism: any `b.map` reads off a
chain (`wedgeToCubes`) and equals that chain's `wedgeDesc` (up to the `dims` transport),
which is mono by `wedgeDesc_mono`. -/
theorem descent_mono (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) (b : Ch K) :
    Mono b.map.hom := by
  have hch : IsCubeChain K.init (wedgeToCubes ⟨b.dims, b.map.hom⟩) K.final := by
    have h := wedgeToCubes_isCubeChain b.dims b.map.hom
    rwa [b.map.app_init, b.map.app_final] at h
  have hdims : (wedgeToCubes ⟨b.dims, b.map.hom⟩).map (·.1) = b.dims :=
    wedgeToCubes_dims b.dims b.map.hom
  -- `wedgeDescHom` (not `wedgeDesc … .hom`) so the composite's codomain is spelled
  -- `K.toPsh`, not `(K.repoint K.init K.final).toPsh`; `rw` is syntactic.
  have key : b.map.hom = eqToHom (congrArg (fun d => (⋁d).toPsh) hdims.symm)
      ≫ (wedgeDescHom (wedgeToCubes ⟨b.dims, b.map.hom⟩) hch).hom := by
    refine wedgeToCubes_inj b.dims _ _ ?_ ?_
    · rw [wedgeToCubes_eqToHom hdims.symm]
      exact (wedgeToCubes_wedgeDesc K.init K.final _ hch).symm
    · rw [b.map.app_init, NatTrans.comp_app_apply, serialWedge_eqToHom_init hdims]
      exact (wedgeDesc_init K.init K.final (wedgeToCubes ⟨b.dims, b.map.hom⟩) hch).symm
  rw [key]
  haveI : Mono (wedgeDescHom (wedgeToCubes ⟨b.dims, b.map.hom⟩) hch).hom :=
    wedgeDesc_mono h₁ h₂ K.init K.final _ hch
  infer_instance

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
sequence together with its descent map (this is `wedgeOfChain`, repackaged). -/
def refineToWedgeObj (x : RefineObj K.init K.final) : Ch K where
  dims := x.cubes.map (·.1)
  map := wedgeDescHom x.cubes x.isChain

/-- `rfl`, but `refineToWedgeObj` is a plain `def`: lemmas about `(refineToWedgeObj x).map`
mention its domain as `⋁(refineToWedgeObj x).dims`, so a goal phrased with `x.cubes.map (·.1)`
must be folded back before they will match. -/
theorem refineToWedgeObj_dims (x : RefineObj K.init K.final) :
    (refineToWedgeObj x).dims = x.cubes.map (·.1) := rfl

/-- The `i`-th induced cell of `⋁y.dims`: block `i` of `x` sent into block `f i`
of `y` along the recorded inclusion `f.incl i`, read as a cell via Yoneda.  The
`eqToHom` bridges the `List.get`/`map` mismatch between the dimension `f.incl i`
records (`(y.cubes.get (f i)).1`) and the one the wedge inclusion `ι` uses
(`(y.dims).get (f i)`). -/
def inducedCell {x y : RefineObj K.init K.final} (f : x ⟶ y)
    (i : Fin x.cubes.length) :
    (⋁(y.cubes.map (·.1))).cells ((x.cubes.get i).1 : ℕ) :=
  let j : Fin (y.cubes.map (·.1)).length := (f.refinement i).cast (by rw [List.length_map])
  have hdim : (y.cubes.get (f.refinement i)).1 = (y.cubes.map (·.1)).get j := by simp [j]
  yonedaEquiv (yoneda.map (f.incl i) ≫
    eqToHom (congrArg (fun n : ℕ+ => (□(n : ℕ)).toPsh) hdim) ≫
    ιᵂ (y.cubes.map (·.1)) j)

/-- The chain of induced cells inside `⋁y.dims`: `x`'s blocks, each carried into
its target `y`-block by the recorded inclusion.  Its dimension sequence is `x.dims`
(`inducedCubeList_dims`). -/
def inducedCubeList {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    List (Σ n : ℕ+, (⋁(y.cubes.map (·.1))).cells (n : ℕ)) :=
  List.ofFn (fun i : Fin x.cubes.length => ⟨(x.cubes.get i).1, inducedCell f i⟩)

/-- The induced chain has the same dimension sequence as `x`. -/
theorem inducedCubeList_dims {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    (inducedCubeList f).map (·.1) = x.cubes.map (·.1) := by
  rw [inducedCubeList, List.map_ofFn]
  conv_rhs => rw [← List.ofFn_get x.cubes, List.map_ofFn]
  rfl

/-- `y`'s descent map sends the `i`-th induced cell back to the `i`-th cube of `x`
(the `inclSpec` computation): restricting to block `f i` via `ι_comp_wedgeDesc` gives
`y`-cube `f i`, and pulling back along `f.incl i` gives `x`-cube `i`. -/
theorem refineToWedgeObj_map_inducedCell {x y : RefineObj K.init K.final} (f : x ⟶ y)
    (i : Fin x.cubes.length) :
    (refineToWedgeObj y).map.hom⟪((x.cubes.get i).1 : ℕ)⟫ (inducedCell f i)
      = (x.cubes.get i).2 := by
  simp only [inducedCell, refineToWedgeObj]
  refine (yonedaEquiv_comp _ _).symm.trans ?_
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  simp only [Category.assoc]
  -- `erw`: the block-restriction pattern is present verbatim, but its `≫` carries the middle
  -- object as `(□m).toPsh` where the goal spells it `yoneda.obj ▫m` — defeq, not syntactic.
  erw [eqToHom_ι_comp_wedgeDescHom y.cubes y.isChain (f.refinement i) (by simp)]
  rw [yonedaEquiv_symm_naturality_left, f.inclSpec i]

/-- **Chain reflection through an injective bi-pointed map.**  If `φ : A ⟶ B` is
injective on cells in every dimension and the `φ`-images of a cube list form a chain
in `B`, then the cubes themselves form a chain in `A`.  (Used with `φ` a chain's
descent map, injective by `descent_mono`.) -/
theorem isCubeChain_of_map_injective {A B : BPSet} (φ : A ⟶ B)
    (hinj : ∀ n, Function.Injective (φ.hom⟪n⟫)) :
    ∀ (cubes : List (Σ n : ℕ+, A.cells (n : ℕ))) (a b : A.cells 0),
      IsCubeChain (φ.hom⟪0⟫ a)
        (cubes.map (fun c => ⟨c.1, φ.hom⟪(c.1 : ℕ)⟫ c.2⟩))
        (φ.hom⟪0⟫ b) →
      IsCubeChain a cubes b
  | [], a, b, h => hinj 0 h
  | ⟨n, c⟩ :: rest, a, b, h => by
      obtain ⟨h1, h2⟩ := h
      refine ⟨hinj 0 (by rw [PrecubicalSet.map_vertex₀]; exact h1), ?_⟩
      refine isCubeChain_of_map_injective φ hinj rest (A.toPsh.vertex₁ c) b ?_
      rw [PrecubicalSet.map_vertex₁]; exact h2

/-- Pushing each induced cell of `f` through `y`'s descent map recovers `x`'s cubes.
Shared between `inducedChain` and `refineWedgeMap_w` (where it descends the chain /
its commuting triangle, respectively). -/
theorem inducedCubeList_map_descent {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    (inducedCubeList f).map
      (fun c => ⟨c.1, (refineToWedgeObj y).map.hom⟪(c.1 : ℕ)⟫ c.2⟩)
        = x.cubes := by
  rw [inducedCubeList, List.map_ofFn]
  simp only [Function.comp_def, refineToWedgeObj_map_inducedCell]
  exact List.ofFn_get x.cubes

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
    IsCubeChain (⋁(y.cubes.map (·.1))).init (inducedCubeList f)
      (⋁(y.cubes.map (·.1))).final := by
  have hmono : Mono (refineToWedgeObj y).map.hom := descent_mono h₁ h₂ (refineToWedgeObj y)
  have hinj : ∀ n, Function.Injective ((refineToWedgeObj y).map.hom⟪n⟫) :=
    fun n => (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app _).mp hmono (op ▫n))
  have hpush := inducedCubeList_map_descent f
  refine isCubeChain_of_map_injective (refineToWedgeObj y).map hinj (inducedCubeList f) _ _ ?_
  -- `app_init`/`app_final` mention the domain as `⋁(refineToWedgeObj y).dims`; folding the goal
  -- back to that spelling is a dependent rewrite (the motive is ill-typed), so `erw` it is.
  erw [(refineToWedgeObj y).map.app_init, (refineToWedgeObj y).map.app_final, hpush]
  exact x.isChain

/-- The wedge map `⋁x.dims ⟶ ⋁y.dims` induced by a refinement `f : x ⟶ y`:
the descent of the induced chain (`inducedCubeList`) into `⋁y.dims`, transported
along `inducedCubeList_dims` to have domain `⋁x.dims`.

`ChainRefine` carries the face inclusions as **data**, so block `i` of `x` includes
into block `f i` of `y` by `inducedCell`; these assemble through `wedgeDesc` once they
form a chain (`inducedChain`, the only `descent_mono` dependency here). -/
def refineWedgeMap (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    ⋁(x.cubes.map (·.1)) ⟶ ⋁(y.cubes.map (·.1)) :=
  eqToHom (congrArg BPSet.serialWedge (inducedCubeList_dims f).symm) ≫
    wedgeDescHom (inducedCubeList f) (inducedChain h₁ h₂ f)

/-- The underlying map of a `BPSet` `eqToHom` is the `eqToHom` of the underlying
presheaf equality. -/
theorem bpset_eqToHom_hom {A B : BPSet} (h : A = B) :
    (eqToHom h).hom = eqToHom (congrArg BPSet.toPsh h) := by
  subst h; simp

/-- The induced wedge map commutes over `K` (the triangle of `ChainCat.Hom`).
By `wedgeToCubes_inj` both sides read off the same
cubes — `refineWedgeMap f ≫ y.descent` reads off (via `wedgeToCubes_wedgeDesc_comp`)
to the induced cells pushed by `y`'s descent, which are the `x`-cubes
(`refineToWedgeObj_map_inducedCell`); the `eqToHom` domain transport is stripped by
`wedgeToCubes_eqToHom`. -/
theorem refineWedgeMap_w (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    refineWedgeMap h₁ h₂ f ≫ (refineToWedgeObj y).map = (refineToWedgeObj x).map := by
  have hpush := inducedCubeList_map_descent f
  apply bpset_hom_ext_of_wedgeToCubes
  rw [show (refineToWedgeObj x).map.hom
        = (wedgeDesc K.init K.final x.cubes x.isChain).hom from rfl,
    wedgeToCubes_wedgeDesc K.init K.final x.cubes x.isChain, refineWedgeMap]
  simp only [comp_hom, bpset_eqToHom_hom, Category.assoc]
  refine (wedgeToCubes_eqToHom (inducedCubeList_dims f).symm
    ((wedgeDescHom (K := ⋁(y.cubes.map (·.1))) (inducedCubeList f) (inducedChain h₁ h₂ f)).hom
      ≫ (refineToWedgeObj y).map.hom)).trans ?_
  exact (wedgeToCubes_wedgeDesc_comp _ _ _ _ _).trans hpush

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

/-- Reading the cubes off the induced wedge map recovers the induced cube list: the
domain `eqToHom` transport is stripped by `wedgeToCubes_eqToHom`, then
`wedgeToCubes_wedgeDesc`. -/
theorem refineWedgeMap_wedgeToCubes (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    wedgeToCubes ⟨x.cubes.map (·.1), (refineWedgeMap h₁ h₂ f).hom⟩ = inducedCubeList f := by
  rw [refineWedgeMap]
  simp only [comp_hom, bpset_eqToHom_hom]
  rw [wedgeToCubes_eqToHom (inducedCubeList_dims f).symm
    (wedgeDescHom (K := ⋁(y.cubes.map (·.1))) (inducedCubeList f) (inducedChain h₁ h₂ f)).hom]
  exact wedgeToCubes_wedgeDesc _ _ (inducedCubeList f) (inducedChain h₁ h₂ f)

/-- The `i`-th induced cell lies in block `f.refinement i` of `⋁y.dims` (it is the
Yoneda image of `f.incl i` along that block's inclusion `ι`). -/
theorem inducedCell_mem_block {x y : RefineObj K.init K.final} (f : x ⟶ y)
    (i : Fin x.cubes.length) :
    ∃ c, (ιᵂ (y.cubes.map (·.1))
        ((f.refinement i).cast (by rw [List.length_map])))⟪((x.cubes.get i).1 : ℕ)⟫
          c = inducedCell f i := by
  refine ⟨yonedaEquiv (yoneda.map (f.incl i) ≫ eqToHom
    (congrArg (fun n : ℕ+ => (□(n : ℕ)).toPsh)
      (show (y.cubes.get (f.refinement i)).1
          = (y.cubes.map (·.1)).get ((f.refinement i).cast (by rw [List.length_map]))
        from by simp))), ?_⟩
  rw [inducedCell, ← yonedaEquiv_comp, Category.assoc]

/-- **Block index is determined**: two refinements `f g : x ⟶ y` send each `x`-block to
the same `y`-block.  The induced wedge maps agree (`Ch K` is thin, `descent_mono`), so
the induced cells agree; block-uniqueness of the serial wedge then pins the index. -/
theorem refinement_eq (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f g : x ⟶ y) (i : Fin x.cubes.length) :
    f.refinement i = g.refinement i := by
  have hwedge : refineWedgeMap h₁ h₂ f = refineWedgeMap h₁ h₂ g :=
    congrArg ChainCat.Hom.φ
      (Subsingleton.elim (h := chainCat_hom_subsingleton h₁ h₂ _ _)
        ((refineToWedge h₁ h₂).map f) ((refineToWedge h₁ h₂).map g))
  have hlist : inducedCubeList f = inducedCubeList g := by
    rw [← refineWedgeMap_wedgeToCubes h₁ h₂ f, ← refineWedgeMap_wedgeToCubes h₁ h₂ g, hwedge]
  have hcell : inducedCell f i = inducedCell g i := by
    have hi := congrFun (List.ofFn_inj.mp hlist) i
    simpa using hi
  obtain ⟨cf, hcf⟩ := inducedCell_mem_block f i
  obtain ⟨cg, hcg⟩ := inducedCell_mem_block g i
  have hcast : ((f.refinement i).cast (by rw [List.length_map]) :
        Fin (y.cubes.map (·.1)).length)
      = (g.refinement i).cast (by rw [List.length_map]) :=
    serialWedge_block_unique (y.cubes.map (·.1)) (x.cubes.get i).1.2 _ _ (inducedCell f i)
      ⟨cf, hcf⟩ ⟨cg, hcg.trans hcell.symm⟩
  exact Fin.ext (by simpa using congrArg Fin.val hcast)

/-- Applying a type-level `eqToHom` to an element is `HEq`-identity. -/
theorem eqToHom_type_apply {X Y : Type} (h : X = Y) (a : X) : (eqToHom h) a ≍ a := by
  subst h; rfl

/-- **Transporting a cell along a `Box`-object equality** (`K.map (eqToHom h).op`) returns
any heterogeneously-equal cell: it is the `HEq`-identity through `eqToHom_op`/`eqToHom_map`.
This packages the dependent-type bookkeeping shared by the `incl`/`inclSpec` transports. -/
theorem map_eqToHom_op_cell {A B : Box} (h : A = B) {x : K.toPsh.obj (op B)}
    {y : K.toPsh.obj (op A)} (hxy : x ≍ y) : K.toPsh.map (eqToHom h).op x = y := by
  rw [eqToHom_op, eqToHom_map]
  exact eq_of_heq (HEq.trans (eqToHom_type_apply _ _) hxy)

/-- **The refinement category is thin** under `NonSelfLinked` + `AdmitsAltitude`.  The
block index is forced by `refinement_eq` (the induced wedge map is unique because
`Ch K` is thin); the inclusion `Box` morphism is then forced by `NonSelfLinked`
(`incl i` is recovered as `K.map (incl i).op (y-cube) = x-cube`, the `y`-cube's
canonical map being injective), with the codomain transport closed via
`eqToHom_type_apply` + `comp_eqToHom_heq`. -/
theorem refineObj_hom_subsingleton (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (x y : RefineObj K.init K.final) : Subsingleton (x ⟶ y) := by
  refine ⟨fun f g => ?_⟩
  have href : f.refinement = g.refinement := funext (refinement_eq h₁ h₂ f g)
  refine ChainRefine.ext href (Function.hfunext rfl fun i i' hii => ?_)
  obtain rfl := eq_of_heq hii
  have hri : f.refinement i = g.refinement i := refinement_eq h₁ h₂ f g i
  have hcod : ▫((y.cubes.get (g.refinement i)).1 : ℕ)
      = ▫((y.cubes.get (f.refinement i)).1 : ℕ) := by rw [hri]
  -- `incl` is forced by `NonSelfLinked` once the block index agrees (`hri`); the
  -- transport `K.map (eqToHom hcod).op (y-cube f) = y-cube g` is the only remaining
  -- (dependent-type) step.
  have htrans : K.toPsh.map (eqToHom hcod).op (y.cubes.get (f.refinement i)).2
      = (y.cubes.get (g.refinement i)).2 :=
    map_eqToHom_op_cell hcod (by rw [hri])
  have key : f.incl i = g.incl i ≫ eqToHom hcod := by
    apply h₁ ((y.cubes.get (f.refinement i)).1 : ℕ) (y.cubes.get (f.refinement i)).2
    rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply, yonedaEquiv_symm_app_apply,
      ← f.inclSpec i, op_comp, K.toPsh.map_comp, types_comp_apply, htrans, ← g.inclSpec i]
  rw [key]
  exact comp_eqToHom_heq _ _

/-- Object part of the backward functor `wedge ⥤ refine`: a wedge map `↦` the cubes
read off it (this is `chainOfWedge`, repackaged). -/
def wedgeToRefineObj (a : Ch K) : RefineObj K.init K.final where
  cubes := wedgeToCubes ⟨a.dims, a.map.hom⟩
  isChain := by
    have h := wedgeToCubes_isCubeChain a.dims a.map.hom
    rwa [a.map.app_init, a.map.app_final] at h

/-- The refinement read off a wedge-map morphism `g : a ⟶ b`.  From
`g.φ : ⋁a.dims ⟶ ⋁b.dims`, each positive `a`-block `ιᵢ ≫ g.φ` is a positive cell of
`⋁b.dims`, which lies in a **unique** `b`-block as a face: `serialWedge_cell_exists`
gives the block `r i` and the cell, and
`serialWedge_block_unique`/`serialWedge_ι_app_injective` make `r i` and the `Box`
inclusion well-defined; `inclSpec` then follows from naturality of `yonedaEquiv`
(precisely the data the forward `inducedCell` packs, run backwards).

Monotonicity of `r` needs no hypothesis on `K`: it is the *serial wedge's own* altitude
(`serialWedge_blockIdx_prefix_bound`) that orders the blocks, via the dimension prefix sum. -/
def wedgeToRefineMap {a b : Ch K} (g : a ⟶ b) :
    wedgeToRefineObj a ⟶ wedgeToRefineObj b := by
  change ChainRefine K.init K.final (wedgeToCubes ⟨a.dims, a.map.hom⟩)
    (wedgeToCubes ⟨b.dims, b.map.hom⟩)
  have hla := wedgeToCubes_length a.dims a.map.hom
  have hlb := wedgeToCubes_length b.dims b.map.hom
  have hw : gᵂ ≫ b.map.hom = a.map.hom := by
    have h := congrArg BPSet.Hom.hom g.w; rwa [comp_hom] at h
  -- Block extraction: the named, computable block data of `BlockDecomp`.
  let R : ChainCat.Bead a → ChainCat.Bead b := blockIdx gᵂ
  let incl0 : ∀ i' : ChainCat.Bead a,
      ▫((a.dims.get i' : ℕ)) ⟶ ▫((b.dims.get (R i') : ℕ)) := blockFace gᵂ
  have spec : ∀ i' : ChainCat.Bead a,
      ιᵂ a.dims i' ≫ gᵂ = yoneda.map (incl0 i') ≫ ιᵂ b.dims (R i') := blockFace_spec gᵂ
  -- Read-off cube identifications.
  have wac := wedgeToCubes_get a.dims a.map.hom
  have wbc := wedgeToCubes_get b.dims b.map.hom
  have hAget : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
      ((wedgeToCubes ⟨a.dims, a.map.hom⟩).get i).1 = a.dims.get (i.cast hla) :=
    fun i => congrArg Sigma.fst (wac i)
  have hBget : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
      ((wedgeToCubes ⟨b.dims, b.map.hom⟩).get ((R (i.cast hla)).cast hlb.symm)).1
        = b.dims.get (R (i.cast hla)) := by
    intro i
    have hcast : ((R (i.cast hla)).cast hlb.symm).cast hlb = R (i.cast hla) :=
      Fin.ext (by simp only [Fin.val_cast])
    rw [congrArg Sigma.fst (wbc ((R (i.cast hla)).cast hlb.symm)), hcast]
  -- The key (P): the read-off `a`-cube is the read-off `b`-cube pulled back along `incl0`.
  have hP : ∀ i' : ChainCat.Bead a,
      yonedaEquiv (ιᵂ a.dims i' ≫ a.map.hom)
        = K.toPsh.map (incl0 i').op
            (yonedaEquiv (ιᵂ b.dims (R i') ≫ b.map.hom)) := by
    intro i'
    have hcomp : yoneda.map (incl0 i') ≫ ιᵂ b.dims (R i') ≫ b.map.hom
        = ιᵂ a.dims i' ≫ a.map.hom := by
      calc yoneda.map (incl0 i') ≫ ιᵂ b.dims (R i') ≫ b.map.hom
          = (yoneda.map (incl0 i') ≫ ιᵂ b.dims (R i')) ≫ b.map.hom :=
            (Category.assoc _ _ _).symm
        _ = (ιᵂ a.dims i' ≫ gᵂ) ≫ b.map.hom :=
            congrArg (· ≫ b.map.hom) (spec i').symm
        _ = ιᵂ a.dims i' ≫ gᵂ ≫ b.map.hom := Category.assoc _ _ _
        _ = ιᵂ a.dims i' ≫ a.map.hom :=
            congrArg (ιᵂ a.dims i' ≫ ·) hw
    refine (congrArg yonedaEquiv hcomp.symm).trans ?_
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, map_yonedaEquiv]
  -- eqToHom transports relating the read-off cubes to the primed (`a.dims`/`b.dims`) cubes.
  have hX : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
      K.toPsh.map (eqToHom (congrArg (fun m : ℕ+ => ▫(m : ℕ)) (hAget i))).op
          (yonedaEquiv (ιᵂ a.dims (i.cast hla) ≫ a.map.hom))
        = ((wedgeToCubes ⟨a.dims, a.map.hom⟩).get i).2 :=
    fun i => map_eqToHom_op_cell _ (by rw [wac i])
  have hY : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
      K.toPsh.map (eqToHom (congrArg (fun m : ℕ+ => ▫(m : ℕ)) (hBget i).symm)).op
          ((wedgeToCubes ⟨b.dims, b.map.hom⟩).get ((R (i.cast hla)).cast hlb.symm)).2
        = yonedaEquiv (ιᵂ b.dims (R (i.cast hla)) ≫ b.map.hom) := by
    intro i
    have hcast : ((R (i.cast hla)).cast hlb.symm).cast hlb = R (i.cast hla) :=
      Fin.ext (by simp)
    exact map_eqToHom_op_cell _ (by rw [wbc ((R (i.cast hla)).cast hlb.symm), hcast])
  refine
    { chainx := (wedgeToRefineObj a).isChain
      chainy := (wedgeToRefineObj b).isChain
      refinement := fun i => (R (i.cast hla)).cast hlb.symm
      incl := fun i =>
        eqToHom (congrArg (fun m : ℕ+ => ▫(m : ℕ)) (hAget i))
          ≫ incl0 (i.cast hla)
          ≫ eqToHom (congrArg (fun m : ℕ+ => ▫(m : ℕ)) (hBget i).symm)
      refinementMono := ?mono
      inclSpec := ?spec }
  case spec =>
    intro i
    rw [op_comp, op_comp, K.toPsh.map_comp, K.toPsh.map_comp, types_comp_apply,
      types_comp_apply, hY i, ← hP (i.cast hla), hX i]
  case mono =>
    -- The prefix sums see only the dimension sequences, which every read-off out of a
    -- given wedge shares — so the wedge's own bound transfers to the `K`-side read-offs.
    have hdA : ∀ n, dimPrefixSum (wedgeToCubes ⟨a.dims, gᵂ⟩) n
        = dimPrefixSum (wedgeToCubes ⟨a.dims, a.map.hom⟩) n :=
      fun n => dimPrefixSum_congr ((wedgeToCubes_dims a.dims gᵂ).trans
        (wedgeToCubes_dims a.dims a.map.hom).symm) n
    have hdB : ∀ n, dimPrefixSum (wedgeToCubes ⟨b.dims, 𝟙 (⋁b.dims).toPsh⟩) n
        = dimPrefixSum (wedgeToCubes ⟨b.dims, b.map.hom⟩) n :=
      fun n => dimPrefixSum_congr ((wedgeToCubes_dims b.dims _).trans
        (wedgeToCubes_dims b.dims b.map.hom).symm) n
    have hbound : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
        dimPrefixSum (wedgeToCubes ⟨b.dims, b.map.hom⟩) (R (i.cast hla)).val
            ≤ dimPrefixSum (wedgeToCubes ⟨a.dims, a.map.hom⟩) i.val
          ∧ dimPrefixSum (wedgeToCubes ⟨a.dims, a.map.hom⟩) i.val
            < dimPrefixSum (wedgeToCubes ⟨b.dims, b.map.hom⟩) ((R (i.cast hla)).val + 1) := by
      intro i
      have h := serialWedge_blockIdx_prefix_bound gᵂ (ChainCat.Hom.φ g).app_init (i.cast hla)
      rw [hdA, hdB, hdB] at h
      simpa only [Fin.val_cast] using h
    -- Monotonicity of `R` (hence of `refinement`) from the bounds, via the dimension
    -- prefix-sum being monotone.
    intro i j hij
    rw [Fin.le_def] at hij ⊢
    simp only [Fin.val_cast]
    by_contra hcon
    simp only [not_le] at hcon
    have hb1 := (hbound i).1
    have hb2 := (hbound j).2
    have hmA := dimPrefixSum_mono (wedgeToCubes ⟨a.dims, a.map.hom⟩) hij
    have hmB := dimPrefixSum_mono (wedgeToCubes ⟨b.dims, b.map.hom⟩)
      (show (R (j.cast hla)).val + 1 ≤ (R (i.cast hla)).val by omega)
    omega

/-- **`wedgeToRefineMap`'s reindexing is `blockIdx`** (modulo the read-off length transports).
The block-membership facts a caller needs then come straight from `blockFace_spec` /
`blockIdx_eq_of_factor`, rather than from this functor. -/
theorem wedgeToRefineMap_refinement {a b : Ch K} (g : a ⟶ b)
    (i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length) :
    ((wedgeToRefineMap g).refinement i).cast (wedgeToCubes_length b.dims b.map.hom)
      = blockIdx gᵂ (i.cast (wedgeToCubes_length a.dims a.map.hom)) := rfl

/-- The backward functor `wedge ⥤ refine`.  Functoriality is free from thinness of
the refinement category (`refineObj_hom_subsingleton`). -/
noncomputable def wedgeToRefine (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    Ch K ⥤ RefineObj K.init K.final :=
  haveI : Quiver.IsThin (RefineObj K.init K.final) := refineObj_hom_subsingleton h₁ h₂
  { obj := wedgeToRefineObj
    map g := wedgeToRefineMap g
    map_id _ := Subsingleton.elim _ _
    map_comp _ _ := Subsingleton.elim _ _ }

/-- A refinement object is determined by its cube list (`isChain` is a `Prop`). -/
theorem RefineObj.ext' {a b : K.cells 0} {x y : RefineObj a b}
    (h : x.cubes = y.cubes) : x = y := by
  obtain ⟨xc, xh⟩ := x; obtain ⟨yc, _⟩ := y; subst h; rfl

/-- **Unit round-trip (strict).**  Reading the cubes back off a chain's descent map
recovers the chain on the nose — `wedgeToRefine ⋙ refineToWedge` is the identity on
objects. -/
theorem wedgeToRefineObj_refineToWedgeObj (x : RefineObj K.init K.final) :
    wedgeToRefineObj (refineToWedgeObj x) = x :=
  RefineObj.ext' (wedgeToCubes_wedgeDesc K.init K.final x.cubes x.isChain)

/-- **Counit round-trip (strict).**  Descending the cubes read off a wedge map `a` recovers
`a` on the nose: the `dims` agree by `wedgeToCubes_dims`, and across that transport the two
classifying maps read off the same cubes.  An *equality* of `Ch K` objects — no thinness, no
side conditions — so the counit is an `eqToIso` just like the unit. -/
theorem refineToWedgeObj_wedgeToRefineObj (a : Ch K) :
    refineToWedgeObj (wedgeToRefineObj a) = a :=
  ChainCat.Obj.mk_eq_mk (wedgeToCubes_dims a.dims a.map.hom) <| by
    apply bpset_hom_ext_of_wedgeToCubes
    simp only [wedgeToRefineObj]
    rw [comp_hom, bpset_eqToHom_hom,
      wedgeToCubes_eqToHom (wedgeToCubes_dims a.dims a.map.hom) a.map.hom]
    exact wedgeToCubes_wedgeDescHom _ (wedgeToRefineObj a).isChain

/-- **The refine ≌ wedge equivalence.**  `refineToWedge`/`wedgeToRefine` are mutually
inverse: both round trips are strict equalities of objects
(`wedgeToRefineObj_refineToWedgeObj`, `refineToWedgeObj_wedgeToRefineObj`), so unit and counit
are `eqToIso`s; all naturality and the triangle coherence are free from thinness. -/
noncomputable def equivWedgeCat (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
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
