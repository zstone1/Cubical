import CubeChains.Chains.Basic
import CubeChains.Chains.WedgeMap
import CubeChains.Chains.Refine
import CubeChains.Chains.Category
import CubeChains.Foundations.Altitude
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Chains/Correspondence

**[RESULT 1]** The equivalence `equivWedgeCat : RefineObj K ≌ Ch K`
(under `NonSelfLinked` + `AdmitsAltitude`), built on the chain↔wedge-map
correspondence `equivWedgeHom`, with thinness (`Quiver.IsThin`) and `descent_mono`.

**Layer:** Chains.  **Imports:** `Basic`, `WedgeMap`, `Refine`, `Category`, `Foundations.Altitude`.
Sorry-free. `right_inv` comes for free from `left_inv` + `wedgeToCubes_inj`
(the wedge's colimit universal property).

The two constructions of `Chains/WedgeMap.lean` (`wedgeDesc`/`wedgeToCubes`) and
the chain bridge of `Chains/Basic.lean` (`isCubeChain`/`ofIsCubeChain`) assemble
into an equivalence

`equivWedgeHom : CubeChain K ≃ Σ dims, (⋁dims ⟶ K)`.

`left_inv` is direct (reading the cubes back off the descent map recovers them,
and a chain is pinned by its cubes).  `right_inv` then comes for free from
`left_inv` together with injectivity of the inverse map (the wedge's colimit
universal property, `wedgeToCubes_inj`).
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
noncomputable def wedgeOfChain (C : CubeChain K) :
    Σ dims : List ℕ+, (⋁dims ⟶ K) :=
  ⟨C.dims, wedgeDescHom _ (wedgeDesc _ _ _ (isCubeChain C))⟩

/-- The chain read off a wedge map (inverse map). -/
noncomputable def chainOfWedge (φ : Σ dims : List ℕ+, (⋁dims ⟶ K)) :
    CubeChain K :=
  ofIsCubeChain (wedgeToCubes ⟨φ.1, φ.2.hom⟩) <| by
    have h := wedgeToCubes_isCubeChain φ.1 φ.2.hom
    rwa [φ.2.app_init, φ.2.app_final] at h

theorem chainOfWedge_wedgeOfChain (C : CubeChain K) : chainOfWedge (wedgeOfChain C) = C := by
  apply eq_of_cubes
  change wedgeToCubes ⟨C.cubes.map (·.1), (wedgeDesc K.init K.final C.cubes (isCubeChain C)).map⟩
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

/-- **The map↔chain correspondence (ClaudeSetup.md §3).**  Cube chains in `K` are
exactly bi-pointed maps out of a serial wedge: forward is the descent map
(`wedgeOfChain`), inverse reads the cubes off (`chainOfWedge`). -/
noncomputable def equivWedgeHom (K : BPSet) :
    CubeChain K ≃ Σ dims : List ℕ+, (⋁dims ⟶ K) where
  toFun := wedgeOfChain
  invFun := chainOfWedge
  left_inv := chainOfWedge_wedgeOfChain
  right_inv φ := chainOfWedge_injective (chainOfWedge_wedgeOfChain (chainOfWedge φ))

/-! ### Lifting `equivWedgeHom` to the categories  [IN PROGRESS, top-down]

We assemble the intended equivalence

`RefineObj K.init K.final ≌ Ch K`

out of two functors.  The **object** maps are exactly the object equivalence
(`wedgeOfChain`/`chainOfWedge`), with no obstruction.  The **morphism** maps are
where the work is, and they split asymmetrically:

* The **backward** map `wedge ⥤ refine` (`wedgeToRefineMap`) is unconditional:
  a wedge map preserves cell dimension (it is a natural transformation of
  presheaves), so each positive-dimensional `a`-block lands in a *unique* `b`-block
  as a genuine face, giving the reindexing and the inclusion; monotonicity is then
  forced by the cube's vertex order.

* The **forward** map `refine ⥤ wedge` (`refineWedgeMap`) needs a hypothesis on
  `K`.  A `ChainRefine` records, per `x`-block, a face inclusion into a `y`-block
  satisfying `inclSpec` *in `K`*, but nothing forces consecutive inclusions to meet
  at the shared junction *inside the wedge* `⋁y.dims` — and `K`'s descent map
  need not be injective on vertices, so junction agreement in `K` does not transfer
  to the wedge.

  **Two counterexamples** (both *within-cube* non-self-linked, i.e. every cube has
  distinct vertices, yet both break the forward functor):

  1. *Within-cube quotient.*  `K = □²` with the corners `(1,0) ~ (0,1)` identified;
     `y = [c]` the 2-cube; `x = [bottom edge, top edge]`.  Then `[bottom, top]` is a
     chain in `K` (the two middle corners agree) but is the "broken" path, not a
     subdivision of the square.

  2. *Cross-block quotient.*  `K =` two 2-cubes `c₀, c₁` glued in a chain, with
     additionally `c₀(1,0) ~ c₁(1,0)`.  Each cube keeps 4 distinct vertices (so `K`
     *is* within-cube non-self-linked), yet `x = [bottom edge of c₀, right edge of
     c₁]` is a valid `ChainRefine` (`f = [0,1]`) whose inclusions do **not** meet at
     the `c₀/c₁` junction.

  Counterexample 2 shows within-cube non-self-linkedness is *insufficient on its
  own* — but it is excluded by the *other* standing side condition: it does **not**
  `AdmitsAltitude`, since the directed cycle `c₀(1,0) → e → c₀(1,0)` (read off
  `c₀`'s right edge and `c₁`'s bottom edge) forces an altitude that is at once `+2`
  and `0`.  Counterexample 1 is excluded by `NonSelfLinked` (the 2-cube's canonical
  map folds two corners).

  So the operative hypotheses are exactly the existing side conditions
  `BPSet.NonSelfLinked` + `BPSet.AdmitsAltitude` (`Altitude.lean`):
  non-self-linkedness embeds each cube (controlling *same-block* junctions), the
  altitude rules out directed cycles (controlling *cross-block* junctions), and
  together they make every chain's descent map **injective on vertices** — which
  lifts each junction equality `K.vertex₁ (x-cubeᵢ) = K.vertex₀ (x-cubeᵢ₊₁)` back
  into `⋁y.dims`, discharging the forward functor's cocone condition.  The
  forward functor — and hence `equivWedgeCat` — therefore carries these two
  hypotheses. -/

/-! #### Thinness of `Ch K` (the wedge side)

`Ch K` is a poset (`hom`-sets are subsingletons), which makes the morphism part of
the equivalence essentially free.  The reduction is mechanical: a morphism is pinned
by its block restrictions (`serialWedge_hom_ext`), each of which composes with the
target descent map to `a.map`; once that descent map is injective on cells they
agree.  The injectivity is the one genuinely-substantial input. -/

/-- **Altitude lower bound for a descent map.**  Every cell of `⋁cubes` has, after
descending into `K`, altitude at least that of the chain's start vertex `a`.  Induction
on the chain: head cells are faces of `c₀` (altitude `≥ alt c₀ = alt a`), tail cells
recurse (and `alt (vertex₁ c₀) ≥ alt (vertex₀ c₀) = alt a`). -/
theorem descent_alt_ge (alt : ∀ n, K.cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude K.toPsh alt) :
    ∀ (a b : K.cells 0) (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
      (hch : IsCubeChain a cubes b) {m : ℕ}
      (z : (⋁(cubes.map (·.1))).cells m),
      alt 0 a ≤ alt m ((wedgeDesc a b cubes hch).map⟪m⟫ z)
  | a, b, [], hch, m, z => by
      rw [show (wedgeDesc a b [] hch).map⟪m⟫ z
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

set_option maxHeartbeats 600000 in
-- The cross-case `wedge2_glue` step forces an expensive `whnf` defeq on the pushout
-- cells; the descent-map recursion needs ~500k heartbeats, so bump to 600k for headroom.
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
      Function.Injective ((wedgeDesc a b cubes hch).map⟪m⟫)
  | a, b, [], hch, m => fun u v huv => h₁ 0 a m huv
  | a, b, ⟨n, c⟩ :: rest, hch, m => by
      -- The cross case (head face `inl xu` collides with tail cell `inr yv`).
      have cross : ∀ (xu : (□(n : ℕ)).cells m)
          (yv : (⋁(rest.map (·.1))).cells m),
          (K.toPsh.cubeMap c)⟪m⟫ xu
            = (wedgeDesc (K.toPsh.vertex₁ c) b rest hch.2).map⟪m⟫ yv →
          (pushout.inl (□(n : ℕ)).finalVertex
              (⋁(rest.map (·.1))).initVertex)⟪m⟫ xu
            = (pushout.inr (□(n : ℕ)).finalVertex
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
          exact ((wedgeDesc (K.toPsh.vertex₁ c) b rest hch.2).init_spec).symm
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

/-- **[KEY LEMMA — the crux].**  A chain's descent map `⋁b.dims ⟶ K` is a
monomorphism (equivalently, injective on cells in every dimension — `Mono` in the
presheaf topos is pointwise injectivity).

Both side conditions are needed: `NonSelfLinked` controls collisions *within* a
block, while `AdmitsAltitude` rules out the directed cycles that would let two
*different* blocks carry a common positive cell — the two-squares set of the section
docstring is `NonSelfLinked` but carries no altitude, and there a single shared edge
has two preimages, breaking injectivity (and thinness) outright.

Proof structure: `Mono` ⇔ pointwise injective (`NatTrans.mono_iff_mono_app` +
`mono_iff_injective`); reduce a general `b.map` to a `wedgeDesc` via `wedgeToCubes`,
then induct on `b.dims` with `b.map = pushout.desc (cubeMap c₀) (rest descent)`.  A
positive cell of the wedge lies in a **unique block** (`WedgeMap.serialWedge_cell_*`,
now available, no side conditions); `inl/inl` closes by `NonSelfLinked` (each
`cubeMap cᵢ` injective), `inr/inr` by induction, and the cross case `cubeMap c₀ x =
D_rest y` by the **intersection lemma**: a face of `c₀` colliding with the rest-chain
forces the junction vertex.

The altitude-of-faces argument is now discharged (`descent_app_inj`, via the altitude
theory `BPSet.alt_vertex₀`/`alt_vertex₁`/`alt_cubeMap` in `Altitude.lean`); the cross
case is `descent_app_inj`'s altitude separation. -/
theorem wedgeDesc_mono (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (a b' : K.cells 0) (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
    (hch : IsCubeChain a cubes b') : Mono (wedgeDesc a b' cubes hch).map := by
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
  have key : b.map.hom = eqToHom (congrArg (fun d => (⋁d).toPsh) hdims.symm)
      ≫ (wedgeDesc K.init K.final (wedgeToCubes ⟨b.dims, b.map.hom⟩) hch).map := by
    refine wedgeToCubes_inj b.dims _ _ ?_ ?_
    · rw [wedgeToCubes_eqToHom hdims.symm, wedgeToCubes_wedgeDesc]
    · rw [b.map.app_init, NatTrans.comp_app_apply, serialWedge_eqToHom_init hdims]
      exact ((wedgeDesc K.init K.final (wedgeToCubes ⟨b.dims, b.map.hom⟩) hch).init_spec).symm
  rw [key]
  haveI := wedgeDesc_mono h₁ h₂ K.init K.final _ hch
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
noncomputable def refineToWedgeObj (x : RefineObj K.init K.final) : Ch K where
  dims := x.cubes.map (·.1)
  map := wedgeDescHom x.cubes (wedgeDesc K.init K.final x.cubes x.isChain)

/-- The `i`-th induced cell of `⋁y.dims`: block `i` of `x` sent into block `f i`
of `y` along the recorded inclusion `f.incl i`, read as a cell via Yoneda.  The
`eqToHom` bridges the `List.get`/`map` mismatch between the dimension `f.incl i`
records (`(y.cubes.get (f i)).1`) and the one the wedge inclusion `ι` uses
(`(y.dims).get (f i)`). -/
noncomputable def inducedCell {x y : RefineObj K.init K.final} (f : x ⟶ y)
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
noncomputable def inducedCubeList {x y : RefineObj K.init K.final} (f : x ⟶ y) :
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
`y`-cube `f i`, and pulling back along `f.incl i` gives `x`-cube `i`.  `descent_mono`-free. -/
theorem refineToWedgeObj_map_inducedCell {x y : RefineObj K.init K.final} (f : x ⟶ y)
    (i : Fin x.cubes.length) :
    (refineToWedgeObj y).map.hom⟪((x.cubes.get i).1 : ℕ)⟫ (inducedCell f i)
      = (x.cubes.get i).2 := by
  have hy : (refineToWedgeObj y).map.hom = (wedgeDesc K.init K.final y.cubes y.isChain).map := rfl
  simp only [inducedCell, hy]
  erw [← yonedaEquiv_comp]
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  erw [Category.assoc, Category.assoc,
    ι_comp_wedgeDesc K.init K.final y.cubes y.isChain (f.refinement i)]
  simp only [eqToHom_trans_assoc]
  erw [yonedaEquiv_symm_naturality_left, f.inclSpec i]

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
  erw [(refineToWedgeObj y).map.app_init, (refineToWedgeObj y).map.app_final, hpush]
  exact x.isChain

/-- The wedge map `⋁x.dims ⟶ ⋁y.dims` induced by a refinement `f : x ⟶ y`:
the descent of the induced chain (`inducedCubeList`) into `⋁y.dims`, transported
along `inducedCubeList_dims` to have domain `⋁x.dims`.

*(Former Obstruction A.)*  `ChainRefine` carries the face inclusions as **data**, so
block `i` of `x` includes into block `f i` of `y` by `inducedCell`; these assemble
through `wedgeDesc` once they form a chain (`inducedChain`, the only `descent_mono`
dependency here). -/
noncomputable def refineWedgeMap (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    ⋁(x.cubes.map (·.1)) ⟶ ⋁(y.cubes.map (·.1)) :=
  eqToHom (congrArg BPSet.serialWedge (inducedCubeList_dims f).symm) ≫
    wedgeDescHom (inducedCubeList f)
      (wedgeDesc (⋁(y.cubes.map (·.1))).init
        (⋁(y.cubes.map (·.1))).final (inducedCubeList f) (inducedChain h₁ h₂ f))

/-- The underlying map of a `BPSet` `eqToHom` is the `eqToHom` of the underlying
presheaf equality. -/
theorem bpset_eqToHom_hom {A B : BPSet} (h : A = B) :
    (eqToHom h).hom = eqToHom (congrArg BPSet.toPsh h) := by
  subst h; simp

/-- The induced wedge map commutes over `K` (the triangle of `ChainCat.Hom`).
**Independent of `descent_mono`**: by `wedgeToCubes_inj` both sides read off the same
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
        = (wedgeDesc K.init K.final x.cubes x.isChain).map from rfl,
    wedgeToCubes_wedgeDesc K.init K.final x.cubes x.isChain, refineWedgeMap]
  simp only [comp_hom, bpset_eqToHom_hom]
  erw [wedgeToCubes_eqToHom (inducedCubeList_dims f).symm
    ((wedgeDesc (⋁(y.cubes.map (·.1))).init
      (⋁(y.cubes.map (·.1))).final (inducedCubeList f)
        (inducedChain h₁ h₂ f)).map
      ≫ (refineToWedgeObj y).map.hom)]
  erw [wedgeToCubes_wedgeDesc_comp]
  exact hpush

/-- The forward functor `refine ⥤ wedge`.  Functoriality is free from thinness of
`Ch K` (`chainCat_hom_subsingleton`): the two laws are equalities of morphisms in a
category whose hom-sets are subsingletons. -/
noncomputable def refineToWedge (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
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
  erw [wedgeToCubes_eqToHom (inducedCubeList_dims f).symm
    (wedgeDesc (⋁(y.cubes.map (·.1))).init
      (⋁(y.cubes.map (·.1))).final (inducedCubeList f) (inducedChain h₁ h₂ f)).map]
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
  rw [inducedCell]
  erw [← yonedaEquiv_comp]

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
noncomputable def wedgeToRefineObj (a : Ch K) : RefineObj K.init K.final where
  cubes := wedgeToCubes ⟨a.dims, a.map.hom⟩
  isChain := by
    have h := wedgeToCubes_isCubeChain a.dims a.map.hom
    rwa [a.map.app_init, a.map.app_final] at h

/-! ### Chain-altitude arithmetic (for the reindexing monotonicity) -/

/-- Integer prefix-sum of the dimensions of the first `i` cubes of a cube list. -/
def dimPrefixSum (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) (i : ℕ) : ℤ :=
  (((cubes.take i).map (fun c => (c.1 : ℕ))).sum : ℤ)

/-- The dimension prefix-sum is monotone in `i` (all dimensions are nonnegative). -/
theorem dimPrefixSum_mono (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) {i j : ℕ}
    (hij : i ≤ j) : dimPrefixSum cubes i ≤ dimPrefixSum cubes j := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hij
  rw [dimPrefixSum, dimPrefixSum, List.take_add, List.map_append, List.sum_append]
  exact_mod_cast Nat.le_add_right _ _

/-- One-step increment of the dimension prefix-sum. -/
theorem dimPrefixSum_succ (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) {i : ℕ}
    (h : i < cubes.length) :
    dimPrefixSum cubes (i + 1) = dimPrefixSum cubes i + (((cubes.get ⟨i, h⟩).1 : ℕ) : ℤ) := by
  have hsplit : cubes.take (i + 1) = cubes.take i ++ [cubes.get ⟨i, h⟩] := by
    rw [List.get_eq_getElem]; exact List.take_succ_eq_append_getElem h
  rw [dimPrefixSum, dimPrefixSum, hsplit, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  push_cast
  ring

/-- **Altitude gap of a chain = its total dimension.**  For any altitude, the final
vertex of a chain sits `∑ dims` above the initial one — each cube contributes its
dimension via `alt_vertex₀`/`alt_vertex₁` across the junction.  A vertex-level
companion to `isCubeChain_alt_get`. -/
theorem isCubeChain_alt_final (alt : ∀ n, K.cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude K.toPsh alt) :
    ∀ (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) (p q : K.cells 0),
      IsCubeChain p cubes q →
      alt 0 q = alt 0 p + ((cubes.map (fun c => (c.1 : ℕ))).sum : ℤ)
  | [], p, q, h => by
      simp only [List.map_nil, List.sum_nil, Nat.cast_zero, add_zero]
      rw [h]
  | ⟨n, c⟩ :: rest, p, q, h => by
      obtain ⟨hsrc, hrest⟩ := h
      have ih := isCubeChain_alt_final alt hax rest (K.toPsh.vertex₁ c) q hrest
      have h0 := PrecubicalSet.alt_vertex₀ alt hax c
      have h1 := PrecubicalSet.alt_vertex₁ alt hax c
      rw [hsrc] at h0
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      rw [ih, h1, ← h0]; ring

/-- **Cube altitudes along a chain.**  The altitude of the `i`-th cube of a chain from
`p` to `q` is `alt p` plus the prefix-sum of the earlier cubes' dimensions.  (Each step
adds the previous cube's dimension, via `alt_vertex₀`/`alt_vertex₁` and the chain link.) -/
theorem isCubeChain_alt_get (alt : ∀ n, K.cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude K.toPsh alt) :
    ∀ (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) (p q : K.cells 0),
      IsCubeChain p cubes q → ∀ (i : ℕ) (h : i < cubes.length),
      alt _ (cubes.get ⟨i, h⟩).2 = alt 0 p + dimPrefixSum cubes i
  | [], _, _, _, _, h => absurd h (by simp)
  | ⟨n, c⟩ :: rest, p, _, hchain, 0, _ => by
      obtain ⟨h1, _⟩ := hchain
      have hc : alt (n : ℕ) c = alt 0 p := by rw [← h1, PrecubicalSet.alt_vertex₀ alt hax]
      simp only [dimPrefixSum, List.take_zero, List.map_nil, List.sum_nil, Nat.cast_zero, add_zero]
      exact hc
  | ⟨n, c⟩ :: rest, p, q, hchain, k + 1, h => by
      obtain ⟨h1, h2⟩ := hchain
      have hk : k < rest.length := by simpa using h
      have ih := isCubeChain_alt_get alt hax rest (K.toPsh.vertex₁ c) q h2 k hk
      have hc : alt (n : ℕ) c = alt 0 p := by rw [← h1, PrecubicalSet.alt_vertex₀ alt hax]
      have hv1 : alt 0 (K.toPsh.vertex₁ c) = alt 0 p + ((n : ℕ) : ℤ) := by
        rw [PrecubicalSet.alt_vertex₁ alt hax, hc]
      change alt ((rest.get ⟨k, hk⟩).1 : ℕ) (rest.get ⟨k, hk⟩).2
          = alt 0 p + dimPrefixSum (⟨n, c⟩ :: rest) (k + 1)
      rw [ih, hv1]
      simp only [dimPrefixSum, List.take_succ_cons, List.map_cons, List.sum_cons]
      push_cast
      ring

/-- **Obstruction B (reindexing).**  The refinement read off a wedge-map morphism
`g : a ⟶ b`.  From `g.φ : ⋁a.dims ⟶ ⋁b.dims`, each positive `a`-block
`ιᵢ ≫ g.φ` is a positive cell of `⋁b.dims`, which lies in a **unique** `b`-block
as a face: `serialWedge_cell_exists` gives the block `r i` and the cell, and
`serialWedge_block_unique`/`serialWedge_ι_app_injective` make `r i` and the `Box`
inclusion well-defined; `inclSpec` then follows from naturality of `yonedaEquiv`
(precisely the data the forward `inducedCell` packs, run backwards).

**[Remaining gap: monotonicity of `r`.]**  `ChainRefine` requires the reindexing to
be monotone (`r i ≤ r (i+1)` because consecutive `a`-blocks share a junction whose
`g.φ`-image sits between blocks `r i` and `r (i+1)`).  This is the *linear order on
serial-wedge vertices*; the altitude theory (`BPSet.alt_vertex₀`/`alt_vertex₁`, now
proved and used in `descent_mono`) supplies it (junction altitudes strictly increase),
so this is the one remaining assembly. -/
noncomputable def wedgeToRefineMap {a b : Ch K} (g : a ⟶ b)
    (h₂ : K.AdmitsAltitude) :
    wedgeToRefineObj a ⟶ wedgeToRefineObj b := by
  change ChainRefine K.init K.final (wedgeToCubes ⟨a.dims, a.map.hom⟩)
    (wedgeToCubes ⟨b.dims, b.map.hom⟩)
  have hla := wedgeToCubes_length a.dims a.map.hom
  have hlb := wedgeToCubes_length b.dims b.map.hom
  have hw : gᵂ ≫ b.map.hom = a.map.hom := by
    have h := congrArg BPSet.Hom.hom g.w; rwa [comp_hom] at h
  -- Block extraction (`wedgeMap_block`), indexed by `a.dims`.
  let R : ChainCat.Bead a → ChainCat.Bead b := fun i' => (wedgeMap_block gᵂ i').choose
  let incl0 : ∀ i' : ChainCat.Bead a,
      ▫((a.dims.get i' : ℕ)) ⟶ ▫((b.dims.get (R i') : ℕ)) :=
    fun i' => (wedgeMap_block gᵂ i').choose_spec.choose
  have spec : ∀ i' : ChainCat.Bead a,
      ιᵂ a.dims i' ≫ gᵂ
        = yoneda.map (incl0 i') ≫ ιᵂ b.dims (R i') :=
    fun i' => (wedgeMap_block gᵂ i').choose_spec.choose_spec
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
    obtain ⟨alt, hax, halt0⟩ := h₂
    -- The read-off `a`-cube `i` is the read-off `b`-cube `R i'` pulled back along `incl0 i'`;
    -- comparing altitudes (`alt_cubeMap`) gives the cube-altitude relation.
    have altrel : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
        alt _ ((wedgeToCubes ⟨a.dims, a.map.hom⟩).get i).2
          = alt _ ((wedgeToCubes ⟨b.dims, b.map.hom⟩).get ((R (i.cast hla)).cast hlb.symm)).2
              + (trueCount (ev (incl0 (i.cast hla))) : ℤ) := by
      intro i
      have hcast : ((R (i.cast hla)).cast hlb.symm).cast hlb = R (i.cast hla) := Fin.ext (by simp)
      rw [wac i, wbc ((R (i.cast hla)).cast hlb.symm), hcast, hP (i.cast hla)]
      have hc := PrecubicalSet.alt_cubeMap alt hax
        (yonedaEquiv (ιᵂ b.dims (R (i.cast hla)) ≫ b.map.hom)) (incl0 (i.cast hla))
      rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply] at hc
      exact hc
    -- Cube altitudes follow the dimension prefix-sum (`isCubeChain_alt_get`).
    have hAchain : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
        alt _ ((wedgeToCubes ⟨a.dims, a.map.hom⟩).get i).2
          = alt 0 K.init + dimPrefixSum (wedgeToCubes ⟨a.dims, a.map.hom⟩) i.val :=
      fun i => isCubeChain_alt_get alt hax _ K.init K.final
        (wedgeToRefineObj a).isChain i.val i.isLt
    have hBchain : ∀ j : Fin (wedgeToCubes ⟨b.dims, b.map.hom⟩).length,
        alt _ ((wedgeToCubes ⟨b.dims, b.map.hom⟩).get j).2
          = alt 0 K.init + dimPrefixSum (wedgeToCubes ⟨b.dims, b.map.hom⟩) j.val :=
      fun j => isCubeChain_alt_get alt hax _ K.init K.final
        (wedgeToRefineObj b).isChain j.val j.isLt
    -- The block prefix-sum of `a`-cube `i` sits in the `R i'`-th `b`-block.
    have hbound : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
        dimPrefixSum (wedgeToCubes ⟨b.dims, b.map.hom⟩) (R (i.cast hla)).val
            ≤ dimPrefixSum (wedgeToCubes ⟨a.dims, a.map.hom⟩) i.val
          ∧ dimPrefixSum (wedgeToCubes ⟨a.dims, a.map.hom⟩) i.val
            < dimPrefixSum (wedgeToCubes ⟨b.dims, b.map.hom⟩) ((R (i.cast hla)).val + 1) := by
      intro i
      have h1 := altrel i
      rw [hAchain i, hBchain ((R (i.cast hla)).cast hlb.symm)] at h1
      have hrefval : ((R (i.cast hla)).cast hlb.symm).val = (R (i.cast hla)).val := by simp
      rw [hrefval] at h1
      have hRlt : (R (i.cast hla)).val < (wedgeToCubes ⟨b.dims, b.map.hom⟩).length := by
        rw [hlb]; exact (R (i.cast hla)).isLt
      have hgetfst : ((wedgeToCubes ⟨b.dims, b.map.hom⟩).get ⟨(R (i.cast hla)).val, hRlt⟩).1
          = b.dims.get (R (i.cast hla)) :=
        congrArg Sigma.fst (wbc ⟨(R (i.cast hla)).val, hRlt⟩)
      have hsucc := dimPrefixSum_succ (wedgeToCubes ⟨b.dims, b.map.hom⟩) hRlt
      rw [hgetfst] at hsucc
      have htN : trueCount (ev (incl0 (i.cast hla)))
          < (b.dims.get (R (i.cast hla)) : ℕ) := by
        have hle := trueCount_le (ev (incl0 (i.cast hla)))
        have hda : (▫(a.dims.get (i.cast hla) : ℕ)).dim
            = (a.dims.get (i.cast hla) : ℕ) := rfl
        have hdb : (▫(b.dims.get (R (i.cast hla)) : ℕ)).dim
            = (b.dims.get (R (i.cast hla)) : ℕ) := rfl
        have hk : 0 < (a.dims.get (i.cast hla) : ℕ) := (a.dims.get (i.cast hla)).2
        have hN : 0 < (b.dims.get (R (i.cast hla)) : ℕ) := (b.dims.get (R (i.cast hla))).2
        omega
      have htNZ : (trueCount (ev (incl0 (i.cast hla))) : ℤ)
          < (b.dims.get (R (i.cast hla)) : ℕ) := by exact_mod_cast htN
      have hnn : (0 : ℤ) ≤ (trueCount (ev (incl0 (i.cast hla))) : ℤ) :=
        Int.natCast_nonneg _
      exact ⟨by omega, by omega⟩
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

/-- **Spec of `wedgeToRefineMap`'s reindexing.**  The `i`-th source cube is a face of
target block `refinement i`: there is a face cell `x` whose image under the block
inclusion `ι_{refinement i}` is the block restriction `ι_i ≫ g`.  This exposes the
(otherwise tactic-buried) `refinement` field as a *block membership*, so a downstream
caller can identify it with its own block index via `serialWedge_block_unique` /
`blockIdx_eq_of` — e.g. to inherit `blockIdx`-monotonicity from `refinementMono`. -/
theorem wedgeToRefineMap_refinement_spec {a b : Ch K} (g : a ⟶ b)
    (h₂ : K.AdmitsAltitude) (i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length) :
    ∃ x, (ιᵂ b.dims
            (((wedgeToRefineMap g h₂).refinement i).cast
              (wedgeToCubes_length b.dims b.map.hom)))⟪(a.dims.get
            (i.cast (wedgeToCubes_length a.dims a.map.hom)) : ℕ)⟫ x
        = yonedaEquiv (ιᵂ a.dims
            (i.cast (wedgeToCubes_length a.dims a.map.hom)) ≫ gᵂ) := by
  obtain ⟨incl, hspec⟩ := (wedgeMap_block gᵂ
    (i.cast (wedgeToCubes_length a.dims a.map.hom))).choose_spec
  refine ⟨yonedaEquiv (yoneda.map incl), ?_⟩
  -- `refinement i` is *definitionally* the `wedgeMap_block` choice (a structure-literal
  -- field), so the block index below reduces to `hspec`'s and the terminal `rfl` closes it.
  -- `erw` (not `rw`) for the `PrecubicalSet` functor-category composition in `hspec`;
  -- the residual block-index mismatch (`refinement i` vs the `wedgeMap_block` choice) is `rfl`.
  erw [hspec, yonedaEquiv_comp]
  rfl

/-- The backward functor `wedge ⥤ refine`.  Functoriality is free from thinness of
the refinement category (`refineObj_hom_subsingleton`). -/
noncomputable def wedgeToRefine (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    Ch K ⥤ RefineObj K.init K.final :=
  haveI : Quiver.IsThin (RefineObj K.init K.final) := refineObj_hom_subsingleton h₁ h₂
  { obj := wedgeToRefineObj
    map g := wedgeToRefineMap g h₂
    map_id _ := Subsingleton.elim _ _
    map_comp _ _ := Subsingleton.elim _ _ }

/-- A refinement object is determined by its cube list (`isChain` is a `Prop`). -/
theorem RefineObj.ext' {a b : K.cells 0} {x y : RefineObj a b}
    (h : x.cubes = y.cubes) : x = y := by
  obtain ⟨xc, xh⟩ := x; obtain ⟨yc, _⟩ := y; subst h; rfl

/-- **Unit round-trip (strict).**  Reading the cubes back off a chain's descent map
recovers the chain on the nose — `wedgeToRefine ⋙ refineToWedge` is the identity on
objects.  Unconditional (just `wedgeToCubes_wedgeDesc`); this is the unit of the
equivalence. -/
theorem wedgeToRefineObj_refineToWedgeObj (x : RefineObj K.init K.final) :
    wedgeToRefineObj (refineToWedgeObj x) = x :=
  RefineObj.ext' (wedgeToCubes_wedgeDesc K.init K.final x.cubes x.isChain)

/-- **Counit object iso (the `dims`-transport).**  Descending the cubes read off a wedge
map `a` recovers `a` up to the `dims`-transport `eqToHom`; the triangle over `K` commutes
because both maps read off the same cubes (`wedgeToCubes_inj` + `wedgeToCubes_wedgeDesc`),
and the iso laws are free from thinness of `Ch K`. -/
noncomputable def counitObjIso (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (a : Ch K) : refineToWedgeObj (wedgeToRefineObj a) ≅ a :=
  haveI : Quiver.IsThin (Ch K) := chainCat_hom_subsingleton h₁ h₂
  iso_of_both_ways
    { φ := eqToHom (congrArg BPSet.serialWedge (wedgeToCubes_dims a.dims a.map.hom))
      w := by
        apply bpset_hom_ext_of_wedgeToCubes
        rw [comp_hom, bpset_eqToHom_hom]
        erw [wedgeToCubes_eqToHom (wedgeToCubes_dims a.dims a.map.hom) a.map.hom]
        exact (wedgeToCubes_wedgeDesc K.init K.final (wedgeToCubes ⟨a.dims, a.map.hom⟩)
          (wedgeToRefineObj a).isChain).symm }
    { φ := eqToHom (congrArg BPSet.serialWedge (wedgeToCubes_dims a.dims a.map.hom).symm)
      w := by
        apply bpset_hom_ext_of_wedgeToCubes
        rw [comp_hom, bpset_eqToHom_hom]
        erw [wedgeToCubes_eqToHom (wedgeToCubes_dims a.dims a.map.hom).symm
          (refineToWedgeObj (wedgeToRefineObj a)).map.hom]
        exact wedgeToCubes_wedgeDesc K.init K.final (wedgeToCubes ⟨a.dims, a.map.hom⟩)
          (wedgeToRefineObj a).isChain }

/-- **The refine ≌ wedge equivalence.**  `refineToWedge`/`wedgeToRefine` are mutually
inverse: the unit is the strict object round-trip (`wedgeToRefineObj_refineToWedgeObj`),
the counit is the `dims`-transport iso (`counitObjIso`); all naturality and the triangle
coherence are free from thinness of both categories. -/
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
      (fun a => counitObjIso h₁ h₂ a)
      (fun _ => Subsingleton.elim _ _)
    functor_unitIso_comp _ := Subsingleton.elim _ _ }

end CubeChain
