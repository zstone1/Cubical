import CubeChains.Chains.Basic
import CubeChains.Chains.WedgeMap
import CubeChains.Chains.Refine
import CubeChains.Chains.Category
import CubeChains.Altitude
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# The chain ↔ wedge-map correspondence (ClaudeSetup.md §3)

The two constructions of `Chains/WedgeMap.lean` (`wedgeDesc`/`wedgeToCubes`) and
the chain bridge of `Chains/Basic.lean` (`isCubeChain`/`ofIsCubeChain`) assemble
into an equivalence

`equivWedgeHom : CubeChain K ≃ Σ dims, (□^∨(dims) ⟶ K)`.

`left_inv` is direct (reading the cubes back off the descent map recovers them,
and a chain is pinned by its cubes).  `right_inv` then comes for free from
`left_inv` together with injectivity of the inverse map (the wedge's colimit
universal property, `wedgeToCubes_inj`).
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace CubeChain

variable {K : BPSet}

/-- The wedge map classifying a chain (forward map of the §3 correspondence). -/
noncomputable def wedgeOfChain (C : CubeChain K) :
    Σ dims : List ℕ+, (BPSet.serialWedge dims ⟶ K) :=
  ⟨C.dims, wedgeDescHom _ (wedgeDesc _ _ _ (isCubeChain C))⟩

/-- The chain read off a wedge map (inverse map). -/
noncomputable def chainOfWedge (φ : Σ dims : List ℕ+, (BPSet.serialWedge dims ⟶ K)) :
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
  refine (Sigma.mk.injEq ..).mpr ⟨rfl, heq_of_eq (BPSet.hom_ext ?_)⟩
  exact wedgeToCubes_inj dims₁ ψ₁.hom ψ₂.hom hcubes (by rw [ψ₁.app_init, ψ₂.app_init])

/-- **The map↔chain correspondence (ClaudeSetup.md §3).**  Cube chains in `K` are
exactly bi-pointed maps out of a serial wedge: forward is the descent map
(`wedgeOfChain`), inverse reads the cubes off (`chainOfWedge`). -/
noncomputable def equivWedgeHom (K : BPSet) :
    CubeChain K ≃ Σ dims : List ℕ+, (BPSet.serialWedge dims ⟶ K) where
  toFun := wedgeOfChain
  invFun := chainOfWedge
  left_inv := chainOfWedge_wedgeOfChain
  right_inv φ := chainOfWedge_injective (chainOfWedge_wedgeOfChain (chainOfWedge φ))

/-! ### Lifting `equivWedgeHom` to the categories  [IN PROGRESS, top-down]

We assemble the intended equivalence

`RefineObj K.init K.final ≌ ChainCat.Obj K`

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
  at the shared junction *inside the wedge* `□^∨(y.dims)` — and `K`'s descent map
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
  into `□^∨(y.dims)`, discharging the forward functor's cocone condition.  The
  forward functor — and hence `equivWedgeCat` — therefore carries these two
  hypotheses.  Compare the conjectures `Conjectures.hom_subsingleton` (`Ch K` is
  thin under `NonSelfLinked`) and `Conjectures.hom_iff_facewise`. -/

/-! #### Thinness of `Ch K` (the wedge side)

`Ch K` is a poset (`hom`-sets are subsingletons), which makes the morphism part of
the equivalence essentially free.  The reduction is mechanical: a morphism is pinned
by its block restrictions (`serialWedge_hom_ext`), each of which composes with the
target descent map to `a.map`; once that descent map is injective on cells they
agree.  The injectivity is the one genuinely-substantial input. -/

/-- **[KEY LEMMA — the crux].**  A chain's descent map `□^∨(b.dims) ⟶ K` is a
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

**[Remaining gap: the altitude-of-faces argument.]**  `StdCube.canonicalMap`/`cubeRepr`
is now *proved* (`Representable.lean` is sorry-free) and the serial-wedge
cell-decomposition is in place, so the structural reduction above can be carried out.
The one genuinely-open input is the intersection lemma: relating `alt` of a *face*
`(cubeMap c₀).app x` (and of `vertex₀`/`vertex₁`) to the chain's junction altitudes
needs `vertexₑ` expressed as an iterated `faceMap` (via the `canonicalMap` composition
law for `initVertexMap`/`finalVertexMap`), so that the strictly-increasing junction
altitudes separate the blocks.  That altitude theory is the deferred core. -/
theorem descent_mono (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) (b : ChainCat.Obj K) :
    Mono b.map.hom :=
  sorry

/-- **`Ch K` is thin** under `NonSelfLinked` + `AdmitsAltitude`: any two morphisms
`a ⟶ b` agree.  Mechanical given `descent_mono`: both `φ`s compose with `b.map` to
`a.map`, so they cancel against the monomorphism `b.map`.  (Compare
`Conjectures.hom_subsingleton`, stated with `NonSelfLinked` only; the altitude is what
this `Mono`-cancellation route needs.) -/
theorem chainCat_hom_subsingleton (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (a b : ChainCat.Obj K) : Subsingleton (a ⟶ b) := by
  haveI := descent_mono h₁ h₂ b
  refine ⟨fun f g => ?_⟩
  apply ChainCat.hom_ext'
  apply BPSet.hom_ext
  have hf : (ChainCat.Hom.φ f).hom ≫ b.map.hom = a.map.hom := congrArg BPSet.Hom.hom f.w
  have hg : (ChainCat.Hom.φ g).hom ≫ b.map.hom = a.map.hom := congrArg BPSet.Hom.hom g.w
  rw [← cancel_mono b.map.hom, hf, hg]

/-- Object part of the forward functor `refine ⥤ wedge`: a chain `↦` its dimension
sequence together with its descent map (this is `wedgeOfChain`, repackaged). -/
noncomputable def refineToWedgeObj (x : RefineObj K.init K.final) : ChainCat.Obj K where
  dims := x.cubes.map (·.1)
  map := wedgeDescHom x.cubes (wedgeDesc K.init K.final x.cubes x.isChain)

/-- The `i`-th induced cell of `□^∨(y.dims)`: block `i` of `x` sent into block `f i`
of `y` along the recorded inclusion `f.incl i`, read as a cell via Yoneda.  The
`eqToHom` bridges the `List.get`/`map` mismatch between the dimension `f.incl i`
records (`(y.cubes.get (f i)).1`) and the one the wedge inclusion `ι` uses
(`(y.dims).get (f i)`). -/
noncomputable def inducedCell {x y : RefineObj K.init K.final} (f : x ⟶ y)
    (i : Fin x.cubes.length) :
    (BPSet.serialWedge (y.cubes.map (·.1))).toPsh.cells ((x.cubes.get i).1 : ℕ) :=
  let j : Fin (y.cubes.map (·.1)).length := (f.refinement i).cast (by rw [List.length_map])
  have hdim : (y.cubes.get (f.refinement i)).1 = (y.cubes.map (·.1)).get j := by simp [j]
  yonedaEquiv (yoneda.map (f.incl i) ≫
    eqToHom (congrArg (fun n : ℕ+ => (BPSet.cube (n : ℕ)).toPsh) hdim) ≫
    BPSet.serialWedge.ι (y.cubes.map (·.1)) j)

/-- The chain of induced cells inside `□^∨(y.dims)`: `x`'s blocks, each carried into
its target `y`-block by the recorded inclusion.  Its dimension sequence is `x.dims`
(`inducedCubeList_dims`). -/
noncomputable def inducedCubeList {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    List (Σ n : ℕ+, (BPSet.serialWedge (y.cubes.map (·.1))).toPsh.cells (n : ℕ)) :=
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
    (refineToWedgeObj y).map.hom.app (op (Box.ob ((x.cubes.get i).1 : ℕ))) (inducedCell f i)
      = (x.cubes.get i).2 := by
  have hy : (refineToWedgeObj y).map.hom = (wedgeDesc K.init K.final y.cubes y.isChain).map := rfl
  simp only [inducedCell, hy]
  erw [← yonedaEquiv_comp]
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  erw [Category.assoc, Category.assoc,
    ι_comp_wedgeDesc K.init K.final y.cubes y.isChain (f.refinement i)]
  simp only [eqToHom_trans_assoc]
  erw [yonedaEquiv_symm_naturality_left, f.inclSpec i]

/-- A bi-pointed map commutes with `vertex₀` (naturality through `initVertexMap`). -/
theorem map_vertex₀ {A B : BPSet} (φ : A ⟶ B) {n : ℕ} (c : A.toPsh.cells n) :
    φ.hom.app (op (Box.ob 0)) (A.toPsh.vertex₀ c)
      = B.toPsh.vertex₀ (φ.hom.app (op (Box.ob n)) c) :=
  NatTrans.naturality_apply φ.hom (PrecubicalSet.initVertexMap n).op c

/-- A bi-pointed map commutes with `vertex₁` (naturality through `finalVertexMap`). -/
theorem map_vertex₁ {A B : BPSet} (φ : A ⟶ B) {n : ℕ} (c : A.toPsh.cells n) :
    φ.hom.app (op (Box.ob 0)) (A.toPsh.vertex₁ c)
      = B.toPsh.vertex₁ (φ.hom.app (op (Box.ob n)) c) :=
  NatTrans.naturality_apply φ.hom (PrecubicalSet.finalVertexMap n).op c

/-- **Chain reflection through an injective bi-pointed map.**  If `φ : A ⟶ B` is
injective on cells in every dimension and the `φ`-images of a cube list form a chain
in `B`, then the cubes themselves form a chain in `A`.  (Used with `φ` a chain's
descent map, injective by `descent_mono`.) -/
theorem isCubeChain_of_map_injective {A B : BPSet} (φ : A ⟶ B)
    (hinj : ∀ n, Function.Injective (φ.hom.app (op (Box.ob n)))) :
    ∀ (cubes : List (Σ n : ℕ+, A.toPsh.cells (n : ℕ))) (a b : A.toPsh.cells 0),
      IsCubeChain (φ.hom.app (op (Box.ob 0)) a)
        (cubes.map (fun c => ⟨c.1, φ.hom.app (op (Box.ob (c.1 : ℕ))) c.2⟩))
        (φ.hom.app (op (Box.ob 0)) b) →
      IsCubeChain a cubes b
  | [], a, b, h => hinj 0 h
  | ⟨n, c⟩ :: rest, a, b, h => by
      obtain ⟨h1, h2⟩ := h
      refine ⟨hinj 0 (by rw [map_vertex₀]; exact h1), ?_⟩
      refine isCubeChain_of_map_injective φ hinj rest (A.toPsh.vertex₁ c) b ?_
      rw [map_vertex₁]; exact h2

/-- The induced cells form a chain in `□^∨(y.dims)`, from its initial to its final
vertex.  Reflected through `y`'s descent map `D_y`: that map is injective
(`descent_mono`), commutes with `vertex₀`/`vertex₁` (`map_vertex₀`/`map_vertex₁`), and
sends the induced cells to `x`'s cubes (`refineToWedgeObj_map_inducedCell`), so the
chain property descends from `x.isChain` via `isCubeChain_of_map_injective`.  (The
empty case is covered too: `K.init = K.final` forces `D_y init = D_y final`, hence
`init = final` in the wedge.) -/
theorem inducedChain (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    IsCubeChain (BPSet.serialWedge (y.cubes.map (·.1))).init (inducedCubeList f)
      (BPSet.serialWedge (y.cubes.map (·.1))).final := by
  have hmono : Mono (refineToWedgeObj y).map.hom := descent_mono h₁ h₂ (refineToWedgeObj y)
  have hinj : ∀ n, Function.Injective ((refineToWedgeObj y).map.hom.app (op (Box.ob n))) :=
    fun n => (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app _).mp hmono (op (Box.ob n)))
  have hpush : (inducedCubeList f).map
      (fun c => ⟨c.1, (refineToWedgeObj y).map.hom.app (op (Box.ob (c.1 : ℕ))) c.2⟩) = x.cubes := by
    rw [inducedCubeList, List.map_ofFn]
    simp only [Function.comp_def, refineToWedgeObj_map_inducedCell]
    exact List.ofFn_get x.cubes
  refine isCubeChain_of_map_injective (refineToWedgeObj y).map hinj (inducedCubeList f) _ _ ?_
  erw [(refineToWedgeObj y).map.app_init, (refineToWedgeObj y).map.app_final, hpush]
  exact x.isChain

/-- The wedge map `□^∨(x.dims) ⟶ □^∨(y.dims)` induced by a refinement `f : x ⟶ y`:
the descent of the induced chain (`inducedCubeList`) into `□^∨(y.dims)`, transported
along `inducedCubeList_dims` to have domain `□^∨(x.dims)`.

*(Former Obstruction A.)*  `ChainRefine` carries the face inclusions as **data**, so
block `i` of `x` includes into block `f i` of `y` by `inducedCell`; these assemble
through `wedgeDesc` once they form a chain (`inducedChain`, the only `descent_mono`
dependency here). -/
noncomputable def refineWedgeMap (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    BPSet.serialWedge (x.cubes.map (·.1)) ⟶ BPSet.serialWedge (y.cubes.map (·.1)) :=
  eqToHom (congrArg BPSet.serialWedge (inducedCubeList_dims f).symm) ≫
    wedgeDescHom (inducedCubeList f)
      (wedgeDesc (BPSet.serialWedge (y.cubes.map (·.1))).init
        (BPSet.serialWedge (y.cubes.map (·.1))).final (inducedCubeList f) (inducedChain h₁ h₂ f))

/-- Reading cubes off a map precomposed with a domain `eqToHom` (a `dims`-transport)
ignores the transport. -/
theorem wedgeToCubes_eqToHom {d₁ d₂ : List ℕ+} (h : d₁ = d₂)
    (φ : (BPSet.serialWedge d₂).toPsh ⟶ K.toPsh) :
    wedgeToCubes ⟨d₁, eqToHom (congrArg (fun l => (BPSet.serialWedge l).toPsh) h) ≫ φ⟩
      = wedgeToCubes ⟨d₂, φ⟩ := by
  subst h; simp

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
  have hpush : (inducedCubeList f).map
      (fun c => ⟨c.1, (refineToWedgeObj y).map.hom.app (op (Box.ob (c.1 : ℕ))) c.2⟩) = x.cubes := by
    rw [inducedCubeList, List.map_ofFn]
    simp only [Function.comp_def, refineToWedgeObj_map_inducedCell]
    exact List.ofFn_get x.cubes
  apply BPSet.hom_ext
  refine wedgeToCubes_inj (x.cubes.map (·.1)) _ _ ?_ ?_
  · rw [show (refineToWedgeObj x).map.hom
          = (wedgeDesc K.init K.final x.cubes x.isChain).map from rfl,
      wedgeToCubes_wedgeDesc K.init K.final x.cubes x.isChain, refineWedgeMap]
    simp only [BPSet.comp_hom, bpset_eqToHom_hom]
    erw [wedgeToCubes_eqToHom (inducedCubeList_dims f).symm
      ((wedgeDesc (BPSet.serialWedge (y.cubes.map (·.1))).init
        (BPSet.serialWedge (y.cubes.map (·.1))).final (inducedCubeList f)
          (inducedChain h₁ h₂ f)).map
        ≫ (refineToWedgeObj y).map.hom)]
    erw [wedgeToCubes_wedgeDesc_comp]
    exact hpush
  · exact ((refineWedgeMap h₁ h₂ f ≫ (refineToWedgeObj y).map).app_init).trans
      ((refineToWedgeObj x).map.app_init).symm

/-- The forward functor `refine ⥤ wedge`.  Functoriality is free from thinness of
`Ch K` (`chainCat_hom_subsingleton`): the two laws are equalities of morphisms in a
category whose hom-sets are subsingletons. -/
noncomputable def refineToWedge (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    RefineObj K.init K.final ⥤ ChainCat.Obj K where
  obj := refineToWedgeObj
  map f := ⟨refineWedgeMap h₁ h₂ f, refineWedgeMap_w h₁ h₂ f⟩
  map_id _ := Subsingleton.elim (h := chainCat_hom_subsingleton h₁ h₂ _ _) _ _
  map_comp _ _ := Subsingleton.elim (h := chainCat_hom_subsingleton h₁ h₂ _ _) _ _

/-- Reading the cubes off the induced wedge map recovers the induced cube list: the
domain `eqToHom` transport is stripped by `wedgeToCubes_eqToHom`, then
`wedgeToCubes_wedgeDesc`. -/
theorem refineWedgeMap_wedgeToCubes (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f : x ⟶ y) :
    wedgeToCubes ⟨x.cubes.map (·.1), (refineWedgeMap h₁ h₂ f).hom⟩ = inducedCubeList f := by
  rw [refineWedgeMap]
  simp only [BPSet.comp_hom, bpset_eqToHom_hom]
  erw [wedgeToCubes_eqToHom (inducedCubeList_dims f).symm
    (wedgeDesc (BPSet.serialWedge (y.cubes.map (·.1))).init
      (BPSet.serialWedge (y.cubes.map (·.1))).final (inducedCubeList f) (inducedChain h₁ h₂ f)).map]
  exact wedgeToCubes_wedgeDesc _ _ (inducedCubeList f) (inducedChain h₁ h₂ f)

/-- The `i`-th induced cell lies in block `f.refinement i` of `□^∨(y.dims)` (it is the
Yoneda image of `f.incl i` along that block's inclusion `ι`). -/
theorem inducedCell_mem_block {x y : RefineObj K.init K.final} (f : x ⟶ y)
    (i : Fin x.cubes.length) :
    ∃ c, (BPSet.serialWedge.ι (y.cubes.map (·.1))
        ((f.refinement i).cast (by rw [List.length_map]))).app
          (op (Box.ob ((x.cubes.get i).1 : ℕ))) c = inducedCell f i := by
  refine ⟨yonedaEquiv (yoneda.map (f.incl i) ≫ eqToHom
    (congrArg (fun n : ℕ+ => (BPSet.cube (n : ℕ)).toPsh)
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

/-- **The refinement category is thin** under `NonSelfLinked` + `AdmitsAltitude`.  The
block index is forced by `refinement_eq` (the induced wedge map is unique because
`Ch K` is thin); the inclusion `Box` morphism is then forced by `NonSelfLinked`
(`incl i` is recovered as `K.map (incl i).op (y-cube) = x-cube`, and the `y`-cube's
canonical map is injective).  [incl-equality / `HEq` bookkeeping pending.] -/
theorem refineObj_hom_subsingleton (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (x y : RefineObj K.init K.final) : Subsingleton (x ⟶ y) := by
  refine ⟨fun f g => ?_⟩
  have href : f.refinement = g.refinement := funext (refinement_eq h₁ h₂ f g)
  sorry

/-- Object part of the backward functor `wedge ⥤ refine`: a wedge map `↦` the cubes
read off it (this is `chainOfWedge`, repackaged). -/
noncomputable def wedgeToRefineObj (a : ChainCat.Obj K) : RefineObj K.init K.final where
  cubes := wedgeToCubes ⟨a.dims, a.map.hom⟩
  isChain := by
    have h := wedgeToCubes_isCubeChain a.dims a.map.hom
    rwa [a.map.app_init, a.map.app_final] at h

/-- **Obstruction B (reindexing).**  The refinement read off a wedge-map morphism
`g : a ⟶ b`.  From `g.φ : □^∨(a.dims) ⟶ □^∨(b.dims)` we must extract *which*
`b`-block each `a`-block lands in (the monotone reindexing) — `g.φ` a priori sends
an `a`-block to an arbitrary cell of `□^∨(b.dims)`, so isolating a single block
index again leans on how `b.map` separates the blocks. -/
noncomputable def wedgeToRefineMap {a b : ChainCat.Obj K} (g : a ⟶ b) :
    wedgeToRefineObj a ⟶ wedgeToRefineObj b :=
  sorry

/-- The backward functor `wedge ⥤ refine`.  Functoriality is free from thinness of
the refinement category (`refineObj_hom_subsingleton`). -/
noncomputable def wedgeToRefine (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    ChainCat.Obj K ⥤ RefineObj K.init K.final where
  obj := wedgeToRefineObj
  map g := wedgeToRefineMap g
  map_id _ := Subsingleton.elim (h := refineObj_hom_subsingleton h₁ h₂ _ _) _ _
  map_comp _ _ := Subsingleton.elim (h := refineObj_hom_subsingleton h₁ h₂ _ _) _ _

/-- A refinement object is determined by its cube list (`isChain` is a `Prop`). -/
theorem RefineObj.ext' {a b : K.toPsh.cells 0} {x y : RefineObj a b}
    (h : x.cubes = y.cubes) : x = y := by
  obtain ⟨xc, xh⟩ := x; obtain ⟨yc, _⟩ := y; subst h; rfl

/-- **Unit round-trip (strict).**  Reading the cubes back off a chain's descent map
recovers the chain on the nose — `wedgeToRefine ⋙ refineToWedge` is the identity on
objects.  Unconditional (just `wedgeToCubes_wedgeDesc`); this is the unit of the
equivalence. -/
theorem wedgeToRefineObj_refineToWedgeObj (x : RefineObj K.init K.final) :
    wedgeToRefineObj (refineToWedgeObj x) = x :=
  RefineObj.ext' (wedgeToCubes_wedgeDesc K.init K.final x.cubes x.isChain)

/-- **[IN PROGRESS]** `equivWedgeHom` lifts to an equivalence of categories.
*Functoriality of both functors is now discharged via thinness* (`refineToWedge`,
`wedgeToRefine`), and the unit object round-trip holds strictly
(`wedgeToRefineObj_refineToWedgeObj`).  Assembling `Equivalence.mk` still needs: the
two morphism maps (`refineWedgeMap`/`wedgeToRefineMap`, hence `descent_mono`), the
thinness lemmas (`*_hom_subsingleton`, for the free naturality/coherence), and the
counit object round-trip `refineToWedgeObj (wedgeToRefineObj a) = a` — which carries a
dependent-`dims` transport (`a.map : □^∨(a.dims) ⟶ K`), so it is left until the
morphism maps land. -/
noncomputable def equivWedgeCat (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    RefineObj K.init K.final ≌ ChainCat.Obj K :=
  sorry

end CubeChain
