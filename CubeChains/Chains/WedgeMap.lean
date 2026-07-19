import CubeChains.Chains.Basic
import CubeChains.Foundations.Wedge
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# Chains/WedgeMap

Bi-pointed maps out of a serial wedge, `φ : ⋁dims ⟶ K`, and the cube data such a map
carries.  Two constructions, inverse to each other (`Chains/Correspondence.lean`):

* `wedgeDesc` (chain data `→` wedge map): glue the Yoneda classifiers
  `yonedaEquiv.symm cᵢ` of the cubes along the junctions, via `Glue.desc`.
* `wedgeToCubes` (wedge map `→` cube list): read off `cᵢ := yonedaEquiv (ιᵢ ≫ φ)`
  at each block.

Key structural facts: `wedgeToCubes_isCubeChain` (the read-off cubes form a chain) and
`wedgeToCubes_inj` (a wedge map is pinned by its blocks — the colimit universal
property, via `Glue.hom_ext` and Yoneda).  Plus the reusable serial-wedge cell
combinatorics (`serialWedge_block_unique`, `wedge2_*`, `glue0_*`).
-/

open CategoryTheory CategoryTheory.Limits Opposite StdCube BPSet

namespace CubeChain

variable {K : BPSet}

/-! ### The point `□⁰` is rigid, and the wedge inclusions. -/

/-- `□⁰` has only the identity endomorphism (it is the representable point). -/
instance stdPre0_subsingleton : Subsingleton (stdPre 0 ⟶ stdPre 0) := by
  constructor; intro f g; apply PrecubicalConstructions.hom_ext; intro n
  match n with
  | 0     => intro c; apply Subtype.ext; funext i; exact i.elim0
  | (k+1) => intro c; exact absurd c.2 (by simp [noneSet])

instance : Subsingleton ((□0).cells 0) := stdPre0_subsingleton

/-- The initial vertex of `X ∨ Y` is `X.init` pushed in along the left inclusion. -/
theorem wedge2_init' (X Y : BPSet) :
    (wedge2 X Y).init =
      (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ X.init := rfl

/-- The final vertex of `X ∨ Y` is `Y.final` pushed in along the right inclusion. -/
theorem wedge2_final' (X Y : BPSet) :
    (wedge2 X Y).final =
      (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ Y.final := rfl

/-- Evaluate `Glue.desc` after the left inclusion at a point.  Folding into the
`inl ≫ desc` composite (via `change`) sidesteps the dependent rewrite that a bare
`Glue.inl_desc` would trip over. -/
theorem inl_desc_app {W X Y Z : PrecubicalSet} {f : X ⟶ Y} {g : X ⟶ Z}
    {h : Y ⟶ W} {k : Z ⟶ W} {w : f ≫ h = g ≫ k} {o} (y) :
    (Glue.desc h k w).app o ((Glue.inl f g).app o y) = h.app o y := by
  change ((Glue.inl f g) ≫ Glue.desc h k w).app o y = _
  rw [Glue.inl_desc]

/-- Evaluate `Glue.desc` after the right inclusion at a point. -/
theorem inr_desc_app {W X Y Z : PrecubicalSet} {f : X ⟶ Y} {g : X ⟶ Z}
    {h : Y ⟶ W} {k : Z ⟶ W} {w : f ≫ h = g ≫ k} {o} (y) :
    (Glue.desc h k w).app o ((Glue.inr f g).app o y) = k.app o y := by
  change ((Glue.inr f g) ≫ Glue.desc h k w).app o y = _
  rw [Glue.inr_desc]

/-! ### `wedgeDesc`: chain data to a wedge map. -/

/-- A wedge map `⋁cubes ⟶ K` (in `PrecubicalSet`) bundled with where it sends
the wedge's `init`/`final` vertices.  Bundling these invariants is what lets the
`cons` step discharge the pushout's cocone condition from the recursive call (the
`init`-bootstrap). -/
structure WedgeDesc {K : BPSet} (a b : K.cells 0)
    (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) where
  /-- The underlying wedge map. -/
  map : (⋁(cubes.map (·.1))).toPsh ⟶ K.toPsh
  /-- It sends the wedge's initial vertex to `a`. -/
  init_spec : map⟪0⟫ (⋁(cubes.map (·.1))).init = a
  /-- It sends the wedge's final vertex to `b`. -/
  final_spec : map⟪0⟫ (⋁(cubes.map (·.1))).final = b

/-- The inverse direction of the §3 correspondence (chain ↦ wedge map), built by
recursion on the cubes with the `init`/`final` invariants threaded through.  The
block maps are the Yoneda `yonedaEquiv.symm cᵢ`, glued by `Glue.desc`; the
cocone condition at each junction is exactly the recursive `init_spec`. -/
def wedgeDesc {K : BPSet} (a b : K.cells 0) :
    (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) → IsCubeChain a cubes b →
    WedgeDesc a b cubes
  | [], h =>
      { map := yonedaEquiv.symm a
        init_spec := by
          simp only [List.map_nil, serialWedge_nil]
          rw [show (□0).init = 𝟙 ▫0 from Subsingleton.elim _ _]
          exact yonedaEquiv.apply_symm_apply a
        final_spec := by
          simp only [List.map_nil, serialWedge_nil]
          rw [show (□0).final = 𝟙 ▫0 from Subsingleton.elim _ _]
          exact (yonedaEquiv.apply_symm_apply a).trans h }
  | ⟨n, c⟩ :: rest, h =>
      let r := wedgeDesc (K.toPsh.vertex₁ c) b rest h.2
      { map := Glue.desc (yonedaEquiv.symm c) r.map (by
          apply yonedaEquiv.injective
          simp only [yonedaEquiv_comp, finalVertex, initVertex, vertexMap,
            PrecubicalSet.cubeMap, Equiv.apply_symm_apply]
          rw [r.init_spec]; rfl)
        init_spec := by
          simp only [List.map_cons, serialWedge_cons, wedge2_init']
          exact (inl_desc_app _).trans h.1
        final_spec := by
          simp only [List.map_cons, serialWedge_cons, wedge2_final']
          exact (inr_desc_app _).trans r.final_spec }

/-- The bi-pointed map `⋁dims ⟶ K` of a chain, packaged from `wedgeDesc`. -/
def wedgeDescHom {K : BPSet} cubes
  (desc : WedgeDesc K.init K.final cubes) :
  (⋁(List.map (fun x ↦ x.fst) cubes) ⟶ K) where
    hom := desc.map
    app_init := desc.init_spec
    app_final := desc.final_spec

/-! ### `wedgeToCubes`: a wedge map to its cube list. -/

/-- Read the cubes off a (plain) wedge map: the `i`-th cube is the Yoneda
classifier of the `i`-th block restriction. -/
def wedgeToCubes : (dims : List ℕ+) × ((⋁dims).toPsh ⟶ K.toPsh) →
  List (Σ n : ℕ+, K.cells (n : ℕ))
  | ⟨ [], _ ⟩ => []
  | ⟨ x :: rest, hom⟩ =>
    ⟨x, yonedaEquiv (Glue.inl _ _ ≫ hom)⟩
     :: wedgeToCubes ⟨rest, Glue.inr _ _ ≫ hom⟩

/-- The wedge gluing identity: in `X ∨ Y`, the image of `X.final` under the left
inclusion equals the image of `Y.init` under the right inclusion.  This is just
`pushout.condition` pushed through Yoneda. -/
theorem wedge2_glue (X Y : BPSet) :
    (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ X.final
      = (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ Y.init := by
  have h := Glue.condition X.finalVertex Y.initVertex
  simp only [finalVertex, initVertex, vertexMap, PrecubicalSet.cubeMap,
    yonedaEquiv_symm_naturality_right] at h
  exact yonedaEquiv.symm.injective h

/-- **The cubes read off a wedge map form a cube chain.**  Recursion on the
dimension sequence; the head computation uses `vertex₀_yonedaEquiv`/`wedge2_init'`
and the link uses `wedge2_glue`. -/
theorem wedgeToCubes_isCubeChain (dims : List ℕ+)
    (hom : (⋁dims).toPsh ⟶ K.toPsh) :
    IsCubeChain (hom⟪0⟫ (⋁dims).init)
      (wedgeToCubes ⟨dims, hom⟩)
      (hom⟪0⟫ (⋁dims).final) := by
  induction dims with
  | nil =>
      simp only [wedgeToCubes]
      exact congrArg (hom⟪0⟫)
        (Subsingleton.elim ((□0).init) ((□0).final))
  | cons x rest ih =>
      simp only [wedgeToCubes]
      refine ⟨?_, ?_⟩
      · -- `(serialWedge (x::rest)).init` is *defeq* to `inl (cube x).init`, so the
        -- head computation closes definitionally after Yoneda naturality.
        exact PrecubicalSet.vertex₀_yonedaEquiv (Glue.inl _ _ ≫ hom)
      · -- `vertex₁` of the head cube glues (via `wedge2_glue`) onto the right
        -- inclusion, which is exactly the recursive map `inr ≫ hom`.
        have e1 : K.toPsh.vertex₁ (yonedaEquiv (Glue.inl _ _ ≫ hom))
            = (Glue.inr _ _ ≫ hom)⟪0⟫ (⋁rest).init :=
          (PrecubicalSet.vertex₁_yonedaEquiv (Glue.inl _ _ ≫ hom)).trans
            (congrArg (hom⟪0⟫)
              (wedge2_glue (□(x : ℕ)) (⋁rest)))
        have e2 : hom⟪0⟫ (⋁(x :: rest)).final
            = (Glue.inr _ _ ≫ hom)⟪0⟫ (⋁rest).final := rfl
        rw [e1, e2]
        exact ih (Glue.inr _ _ ≫ hom)

/-- Reading the dimensions back off a wedge map recovers the dimension sequence. -/
theorem wedgeToCubes_dims : ∀ (dims : List ℕ+) (hom : (⋁dims).toPsh ⟶ K.toPsh),
    (wedgeToCubes ⟨dims, hom⟩).map (·.1) = dims
  | [], _ => by simp [wedgeToCubes]
  | _ :: rest, hom => by
      simp only [wedgeToCubes, List.map_cons]
      rw [wedgeToCubes_dims rest (Glue.inr _ _ ≫ hom)]

/-- `wedgeToCubes_dims` past the `ℕ+ → ℕ` coercion, as one `List.map`. -/
theorem wedgeToCubes_dimsNat (dims : List ℕ+) (hom : (⋁dims).toPsh ⟶ K.toPsh) :
    (wedgeToCubes ⟨dims, hom⟩).map (fun c => (c.1 : ℕ)) = dims.map (fun d : ℕ+ => (d : ℕ)) := by
  rw [show (fun c : Σ n : ℕ+, K.cells (n : ℕ) => (c.1 : ℕ))
        = (fun d : ℕ+ => (d : ℕ)) ∘ (fun c => c.1) from rfl, ← List.map_map, wedgeToCubes_dims]

/-- **Wedge maps are determined by the cubes they restrict to**, together with
their value on the initial vertex (needed only for the empty wedge `□⁰`).  This is
the colimit universal property of the serial wedge, threaded through
`Glue.hom_ext` and Yoneda. -/
theorem wedgeToCubes_inj : ∀ (dims : List ℕ+) (f g : (⋁dims).toPsh ⟶ K.toPsh),
    wedgeToCubes ⟨dims, f⟩ = wedgeToCubes ⟨dims, g⟩ →
    f⟪0⟫ (⋁dims).init
      = g⟪0⟫ (⋁dims).init → f = g
  | [], f, g, _, hinit => by
      apply yonedaEquiv.injective
      have e : (⋁([] : List ℕ+)).init = 𝟙 ▫0 :=
        Subsingleton.elim (α := (□0).cells 0) _ _
      rw [yonedaEquiv_apply, yonedaEquiv_apply, ← e]
      exact hinit
  | x :: rest, f, g, hcubes, _ => by
      simp only [wedgeToCubes, List.cons.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at hcubes
      obtain ⟨hhead, htail⟩ := hcubes
      have hfg : Glue.inl _ _ ≫ f = Glue.inl _ _ ≫ g := yonedaEquiv.injective hhead
      refine Glue.hom_ext hfg ?_
      refine wedgeToCubes_inj rest _ _ htail ?_
      simp only [NatTrans.comp_app, types_comp_apply]
      rw [← wedge2_glue (□(x : ℕ)) (⋁rest)]
      exact congrArg (fun m => m.app (op ▫0) (□(x : ℕ)).final) hfg

/-- **Uniqueness for the serial wedge** (its colimit universal property, in the
clean `ι`-form): two maps out of `⋁dims` into *any* presheaf `Z` that agree on
every block (after the inclusions `serialWedge.ι`) and on the initial vertex are
equal.  The initial-vertex hypothesis is only needed for the empty wedge `□⁰`; for
nonempty `dims` it follows from the block agreement.  Proved by `Glue.hom_ext`
recursion, exactly mirroring `wedgeToCubes_inj`. -/
theorem serialWedge_hom_ext {Z : PrecubicalSet} :
    ∀ (dims : List ℕ+) (f g : (⋁dims).toPsh ⟶ Z),
      (∀ i, ιᵂ dims i ≫ f = ιᵂ dims i ≫ g) →
      f⟪0⟫ (⋁dims).init
        = g⟪0⟫ (⋁dims).init → f = g
  | [], f, g, _, hinit => by
      apply yonedaEquiv.injective
      have e : (⋁([] : List ℕ+)).init = 𝟙 ▫0 :=
        Subsingleton.elim (α := (□0).cells 0) _ _
      rw [yonedaEquiv_apply, yonedaEquiv_apply, ← e]
      exact hinit
  | x :: rest, f, g, hι, _ => by
      refine Glue.hom_ext ?_ ?_
      · have h0 := hι 0
        simpa only [BPSet.serialWedge.ι, Fin.cases_zero] using h0
      · refine serialWedge_hom_ext rest (Glue.inr _ _ ≫ f) (Glue.inr _ _ ≫ g) ?_ ?_
        · intro j
          have hj := hι j.succ
          simp only [BPSet.serialWedge.ι, Fin.cases_succ] at hj
          rw [Category.assoc, Category.assoc] at hj
          exact hj
        · simp only [NatTrans.comp_app, types_comp_apply]
          rw [← wedge2_glue (□(x : ℕ)) (⋁rest)]
          have h0 := hι 0
          simp only [BPSet.serialWedge.ι, Fin.cases_zero] at h0
          exact congrArg (fun m => m.app (op ▫0) (□(x : ℕ)).final) h0

/-- The head block of the descent map is the Yoneda classifier of the head cube. -/
theorem inl_comp_wedgeDesc (a b : K.cells 0) (n : ℕ+) (c : K.cells (n : ℕ))
    (rest : List (Σ n : ℕ+, K.cells (n : ℕ))) (h : IsCubeChain a (⟨n, c⟩ :: rest) b) :
    Glue.inl (□(n : ℕ)).finalVertex (⋁(rest.map (·.1))).initVertex
        ≫ (wedgeDesc a b (⟨n, c⟩ :: rest) h).map
      = yonedaEquiv.symm c :=
  Glue.inl_desc _ _ _

/-- The tail of the descent map is the descent map of the tail chain. -/
theorem inr_comp_wedgeDesc (a b : K.cells 0) (n : ℕ+) (c : K.cells (n : ℕ))
    (rest : List (Σ n : ℕ+, K.cells (n : ℕ))) (h : IsCubeChain a (⟨n, c⟩ :: rest) b) :
    Glue.inr (□(n : ℕ)).finalVertex (⋁(rest.map (·.1))).initVertex
        ≫ (wedgeDesc a b (⟨n, c⟩ :: rest) h).map
      = (wedgeDesc (K.toPsh.vertex₁ c) b rest h.2).map :=
  Glue.inr_desc _ _ _

/-- Cell-level head rule: the descent map sends an `inl`-cell to the head cube's
Yoneda classifier `yonedaEquiv.symm c`. -/
theorem wedgeDesc_inl_app (a b : K.cells 0) (n : ℕ+) (c : K.cells (n : ℕ))
    (rest : List (Σ n : ℕ+, K.cells (n : ℕ))) (h : IsCubeChain a (⟨n, c⟩ :: rest) b)
    {m : ℕ} (x : (□(n : ℕ)).cells m) :
    (wedgeDesc a b (⟨n, c⟩ :: rest) h).map⟪m⟫
        ((Glue.inl (□(n : ℕ)).finalVertex
          (⋁(rest.map (·.1))).initVertex)⟪m⟫ x)
      = (yonedaEquiv.symm c)⟪m⟫ x :=
  congrArg (fun f : (□(n : ℕ)).toPsh ⟶ K.toPsh => f⟪m⟫ x)
    (inl_comp_wedgeDesc a b n c rest h)

/-- Cell-level tail rule: the descent map sends an `inr`-cell to the tail descent. -/
theorem wedgeDesc_inr_app (a b : K.cells 0) (n : ℕ+) (c : K.cells (n : ℕ))
    (rest : List (Σ n : ℕ+, K.cells (n : ℕ))) (h : IsCubeChain a (⟨n, c⟩ :: rest) b)
    {m : ℕ} (y : (⋁(rest.map (·.1))).cells m) :
    (wedgeDesc a b (⟨n, c⟩ :: rest) h).map⟪m⟫
        ((Glue.inr (□(n : ℕ)).finalVertex
          (⋁(rest.map (·.1))).initVertex)⟪m⟫ y)
      = (wedgeDesc (K.toPsh.vertex₁ c) b rest h.2).map⟪m⟫ y :=
  congrArg (fun f : (⋁(rest.map (·.1))).toPsh ⟶ K.toPsh => f⟪m⟫ y)
    (inr_comp_wedgeDesc a b n c rest h)

/-- **Block-restriction rule for the descent map**: restricting `wedgeDesc` to the
`k`-th block (via `serialWedge.ι`) recovers the Yoneda classifier of the `k`-th cube
(up to the `List.get`/`map` dimension cast).  Proved by induction on `cubes` with
`Fin.cases` on `k`, mirroring the recursions of `serialWedge.ι` and `wedgeDesc`. -/
theorem ι_comp_wedgeDesc : ∀ (a b : K.cells 0)
    (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) (h : IsCubeChain a cubes b)
    (k : Fin cubes.length),
    ιᵂ (cubes.map (·.1)) (k.cast (by rw [List.length_map]))
        ≫ (wedgeDesc a b cubes h).map
      = eqToHom (congrArg (fun m : ℕ+ => (□(m : ℕ)).toPsh)
          (by simp)) ≫ yonedaEquiv.symm (cubes.get k).2
  | a, b, ⟨n, c⟩ :: rest, h, k => by
      refine Fin.cases ?_ (fun k' => ?_) k
      · -- head block: `ι 0 = inl`, `inl ≫ wedgeDesc = yonedaEquiv.symm c`
        simp only [BPSet.serialWedge.ι, List.map_cons, Fin.cast_zero, Fin.cases_zero,
          List.get_cons_zero, eqToHom_refl, Category.id_comp]
        exact inl_comp_wedgeDesc a b n c rest h
      · -- tail block: `ι (k'+1) = ι_rest k' ≫ inr`, recurse
        have hcast : (k'.succ).cast (by rw [List.length_map])
            = ((k'.cast (by rw [List.length_map])).succ :
                Fin ((rest.map (·.1)).length + 1)) := by ext; simp
        simp only [List.map_cons, BPSet.serialWedge.ι]
        refine (congrArg
          (ιᵂ (rest.map (·.1)) (k'.cast (by rw [List.length_map])) ≫ ·)
          (inr_comp_wedgeDesc a b n c rest h)).trans ?_
        exact ι_comp_wedgeDesc (K.toPsh.vertex₁ c) b rest h.2 k'

/-- Reading the cubes back off the descent map recovers the original cubes. -/
theorem wedgeToCubes_wedgeDesc : ∀ (a b : K.cells 0)
    (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) (h : IsCubeChain a cubes b),
    wedgeToCubes ⟨cubes.map (·.1), (wedgeDesc a b cubes h).map⟩ = cubes
  | _, _, [], _ => by simp [wedgeToCubes]
  | a, b, ⟨n, c⟩ :: rest, h => by
      -- `rw` can't see through the `≫`'s implicit middle object (`cube ↑n` vs the
      -- un-reduced head from `wedgeDesc`'s domain), so we build the cons equality
      -- as a term and let `exact` bridge the defeq.
      simp only [List.map_cons, wedgeToCubes]
      rw [List.cons.injEq]
      refine ⟨congrArg (Sigma.mk n) ?_, ?_⟩
      · exact (congrArg yonedaEquiv (inl_comp_wedgeDesc a b n c rest h)).trans
          (Equiv.apply_symm_apply yonedaEquiv c)
      · exact (congrArg (fun hom => wedgeToCubes ⟨rest.map (·.1), hom⟩)
          (inr_comp_wedgeDesc a b n c rest h)).trans
          (wedgeToCubes_wedgeDesc (K.toPsh.vertex₁ c) b rest h.2)

/-- **Reading cubes commutes with post-composition** (naturality of cube-reading):
descending a chain and then mapping along `g : K ⟶ L` reads off the cubes pushed
forward by `g`.  Proved by the same recursion as `wedgeToCubes_wedgeDesc`, using
`inl_comp_wedgeDesc`/`inr_comp_wedgeDesc` and `yonedaEquiv_comp`.  No dimension
transport (the cube list is read at `cubes.map (·.1)` on both sides). -/
theorem wedgeToCubes_wedgeDesc_comp {L : BPSet} (g : K.toPsh ⟶ L.toPsh) :
    ∀ (a b : K.cells 0) (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
      (h : IsCubeChain a cubes b),
    wedgeToCubes ⟨cubes.map (·.1), (wedgeDesc a b cubes h).map ≫ g⟩
      = cubes.map (fun c => ⟨c.1, g⟪(c.1 : ℕ)⟫ c.2⟩)
  | _, _, [], _ => by simp [wedgeToCubes]
  | a, b, ⟨n, c⟩ :: rest, h => by
      simp only [List.map_cons, wedgeToCubes]
      rw [List.cons.injEq]
      refine ⟨congrArg (Sigma.mk n) ?_, ?_⟩
      · refine (congrArg yonedaEquiv
          (((Category.assoc _ _ _).symm).trans
            (congrArg (· ≫ g) (inl_comp_wedgeDesc a b n c rest h)))).trans ?_
        rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
      · refine (congrArg (fun hom => wedgeToCubes ⟨rest.map (·.1), hom⟩)
          (((Category.assoc _ _ _).symm).trans
            (congrArg (· ≫ g) (inr_comp_wedgeDesc a b n c rest h)))).trans ?_
        exact wedgeToCubes_wedgeDesc_comp g (K.toPsh.vertex₁ c) b rest h.2

/-! ### Cell-decomposition of the binary wedge (for `descent_mono`/`wedgeToRefineMap`)

The defining pushout square `□⁰ → X`, `□⁰ → Y` ↠ `X ∨ Y` is preserved by evaluation
at each level `m` (evaluation into the cocomplete category `Type` preserves colimits),
so it is a pushout *in `Type`*.  Since the gluing point `□⁰` has no `m`-cells for
`m ≥ 1`, that pushout is a disjoint union there; at every level it is also a pullback
(the left leg `□⁰ → X` is injective).  These are the structural facts behind "a
positive cell of the wedge lies in a unique block". -/

/-- The `k`-cells of the concrete point `□⁰` are a subsingleton (empty for `k ≥ 1`,
a single vertex for `k = 0`): `Fin 0 → Option Bool` is the empty function. -/
instance stdCube0_cells_subsingleton (k : ℕ) : Subsingleton (Cell 0 k) := by
  constructor
  intro a b
  apply Subtype.ext
  funext i
  exact i.elim0

/-! ### Presheaf-level pushout facts for a gluing at `□⁰`

The following are stated for *arbitrary* vertex maps `f : □⁰ ⟶ A`, `g : □⁰ ⟶ B`
(not just `X.finalVertex`/`Y.initVertex`), since they touch only the underlying
presheaves and the emptiness of positive cells of `□⁰`.  The `wedge2`-shaped
corollaries below are thin specializations at `f := X.finalVertex`,
`g := Y.initVertex`. -/

/-- The pushout square `pushout f g` of two vertex maps `□⁰ ⟶ ·`, transported to
`Type` at level `m` by the colimit-preserving evaluation functor. -/
theorem glue0_isPushout_app {A B : PrecubicalSet}
    (f : yoneda.obj ▫0 ⟶ A) (g : yoneda.obj ▫0 ⟶ B) (m : ℕ) :
    IsPushout (f⟪m⟫) (g⟪m⟫)
      ((Glue.inl f g)⟪m⟫)
      ((Glue.inr f g)⟪m⟫) :=
  (Glue.isPushout f g).map
    (F := (evaluation Boxᵒᵖ Type).obj (op ▫m))

/-- Every `m`-cell of `pushout f g` comes from `A` (via `inl`) or from `B` (via `inr`). -/
theorem glue0_cell_cases {A B : PrecubicalSet}
    (f : yoneda.obj ▫0 ⟶ A) (g : yoneda.obj ▫0 ⟶ B) (m : ℕ)
    (c : PrecubicalSet.cells (Glue.gluePsh f g) m) :
    (∃ x, (Glue.inl f g)⟪m⟫ x = c) ∨
      ∃ y, (Glue.inr f g)⟪m⟫ y = c :=
  Types.eq_or_eq_of_isPushout (glue0_isPushout_app f g m) c

/-- The gluing square is a pullback at every level (a map out of `□⁰` is injective:
`□⁰` has at most one `m`-cell).  Hence the two blocks meet only over the glued point
— the basis for cross-block disjointness of positive cells. -/
theorem glue0_isPullback_app {A B : PrecubicalSet}
    (f : yoneda.obj ▫0 ⟶ A) (g : yoneda.obj ▫0 ⟶ B) (m : ℕ) :
    IsPullback (f⟪m⟫) (g⟪m⟫)
      ((Glue.inl f g)⟪m⟫)
      ((Glue.inr f g)⟪m⟫) := by
  refine Types.isPullback_of_isPushout (glue0_isPushout_app f g m) ?_
  intro a b _
  apply PrecubicalConstructions.hom_ext
  intro n c
  apply Subtype.ext
  funext i
  exact i.elim0

/-- The defining pushout square of `wedge2 X Y`, transported to `Type` at level `m`. -/
theorem wedge2_isPushout_app (X Y : BPSet) (m : ℕ) :
    IsPushout (X.finalVertex⟪m⟫) (Y.initVertex⟪m⟫)
      ((Glue.inl X.finalVertex Y.initVertex)⟪m⟫)
      ((Glue.inr X.finalVertex Y.initVertex)⟪m⟫) :=
  glue0_isPushout_app X.finalVertex Y.initVertex m

/-- Every `m`-cell of `X ∨ Y` comes from `X` (via `inl`) or from `Y` (via `inr`). -/
theorem wedge2_cell_cases (X Y : BPSet) (m : ℕ) (c : (wedge2 X Y).cells m) :
    (∃ x, (Glue.inl X.finalVertex Y.initVertex)⟪m⟫ x = c) ∨
      ∃ y, (Glue.inr X.finalVertex Y.initVertex)⟪m⟫ y = c :=
  glue0_cell_cases X.finalVertex Y.initVertex m c

/-- The wedge square is a pullback at every level. -/
theorem wedge2_isPullback_app (X Y : BPSet) (m : ℕ) :
    IsPullback (X.finalVertex⟪m⟫) (Y.initVertex⟪m⟫)
      ((Glue.inl X.finalVertex Y.initVertex)⟪m⟫)
      ((Glue.inr X.finalVertex Y.initVertex)⟪m⟫) :=
  glue0_isPullback_app X.finalVertex Y.initVertex m

/-! ### Lifting the decomposition to the serial wedge

A *positive-dimensional* cell of `⋁dims` lies in a **unique block**, as a face
of that block's cube.  We first record the head and tail block computation rules for
`serialWedge.ι`, then the block inclusions are injective with pairwise-disjoint
images (`□⁰` contributes no positive cells), and finally every positive cell
factors through exactly one block.  This is the geometric core behind both the
backward functor (`wedgeToRefineMap`) and the embedding theorem (`descent_mono`). -/

/-- The head block inclusion of a serial wedge is the left pushout injection. -/
theorem serialWedge_ι_zero (n : ℕ+) (rest : List ℕ+) :
    ιᵂ (n :: rest) 0
      = Glue.inl (□(n : ℕ)).finalVertex (⋁rest).initVertex :=
  rfl

/-- A later block inclusion of a serial wedge is the tail inclusion followed by the
right pushout injection. -/
theorem serialWedge_ι_succ (n : ℕ+) (rest : List ℕ+) (j : Fin rest.length) :
    ιᵂ (n :: rest) j.succ
      = ιᵂ rest j
        ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex :=
  rfl

/-- Head-block computation rule, at the level of cells. -/
theorem serialWedge_ι_zero_app (n : ℕ+) (rest : List ℕ+) {m : ℕ}
    (x : (□(n : ℕ)).cells m) :
    (ιᵂ (n :: rest) 0)⟪m⟫ x
      = (Glue.inl (□(n : ℕ)).finalVertex
          (⋁rest).initVertex)⟪m⟫ x :=
  rfl

/-- Tail-block computation rule, at the level of cells. -/
theorem serialWedge_ι_succ_app (n : ℕ+) (rest : List ℕ+) (j : Fin rest.length) {m : ℕ}
    (x : (□((rest.get j) : ℕ)).cells m) :
    (ιᵂ (n :: rest) j.succ)⟪m⟫ x
      = (Glue.inr (□(n : ℕ)).finalVertex
          (⋁rest).initVertex)⟪m⟫
            ((ιᵂ rest j)⟪m⟫ x) :=
  rfl

/-- `□⁰` has no positive-dimensional cells: a box morphism `□ᵐ ⟶ □⁰` (`m ≥ 1`)
evaluates to an `m`-cell of the point `stdPre 0`, of which there are none. -/
theorem cube0_cells_isEmpty {m : ℕ} (hm : 1 ≤ m) :
    IsEmpty ((□0).cells m) := by
  constructor
  intro f
  have c : Cell 0 m := ev f
  have hle : (noneSet c.val).card ≤ (Finset.univ : Finset (Fin 0)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [c.prop, Finset.card_univ, Fintype.card_fin] at hle
  omega

/-- A vertex map `□⁰ ⟶ X` is a monomorphism: its domain `□⁰` is a subsingleton at
every level, so the map is pointwise injective. -/
instance vertexMap_mono {X : BPSet} (c : X.cells 0) :
    Mono (yonedaEquiv.symm c : (□0).toPsh ⟶ X.toPsh) := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  rw [mono_iff_injective]
  intro a b _
  have : Subsingleton ((□0).cells k.unop.dim) := by
    rcases Nat.eq_zero_or_pos k.unop.dim with h0 | hpos
    · rw [h0]; exact stdPre0_subsingleton
    · exact (cube0_cells_isEmpty hpos).instSubsingleton
  exact this.elim a b

instance initVertex_mono (X : BPSet) : Mono X.initVertex := by
  rw [initVertex, vertexMap]; exact vertexMap_mono _

instance finalVertex_mono (X : BPSet) : Mono X.finalVertex := by
  rw [finalVertex, vertexMap]; exact vertexMap_mono _

/-- The left wedge injection is a mono (adhesivity + `Z.initVertex` mono). -/
instance wedge2_inl_mono (X Y : BPSet) :
    Mono (Glue.inl X.finalVertex Y.initVertex) :=
  Adhesive.mono_of_isPushout_of_mono_right (Glue.isPushout _ _)

/-- The right wedge injection is a mono (adhesivity + `X.finalVertex` mono). -/
instance wedge2_inr_mono (X Y : BPSet) :
    Mono (Glue.inr X.finalVertex Y.initVertex) :=
  Adhesive.mono_of_isPushout_of_mono_left (Glue.isPushout _ _)

/-- Any vertex map `□⁰ ⟶ Z` is injective **in every dimension** (including `m = 0`),
because its domain `□⁰` is a subsingleton at every level: empty for `m ≥ 1`
(`cube0_cells_isEmpty`), a single vertex for `m = 0` (`stdPre0_subsingleton`).  This
covers both `X.finalVertex` and `Y.initVertex`. -/
theorem vertexMap_app_injective {Z : PrecubicalSet}
    (f : yoneda.obj ▫0 ⟶ Z) {m : ℕ} :
    Function.Injective (f⟪m⟫) := by
  have hsub : Subsingleton ((□0).cells m) := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; exact stdPre0_subsingleton
    · exact (cube0_cells_isEmpty hpos).instSubsingleton
  exact fun a b _ => hsub.elim a b

/-- The left gluing injection is injective **in every dimension** (the glued point
`□⁰` is a mono, `vertexMap_app_injective`, so its pushout is too). -/
theorem glue0_inl_app_injective {A B : PrecubicalSet}
    (f : yoneda.obj ▫0 ⟶ A) (g : yoneda.obj ▫0 ⟶ B) {m : ℕ} :
    Function.Injective ((Glue.inl f g)⟪m⟫) := by
  have h := (glue0_isPushout_app f g m).flip
  have hinj := Types.pushoutCocone_inr_injective_of_isColimit h.isColimit
    (vertexMap_app_injective g)
  rwa [h.cocone_inr] at hinj

/-- The right gluing injection is injective **in every dimension**. -/
theorem glue0_inr_app_injective {A B : PrecubicalSet}
    (f : yoneda.obj ▫0 ⟶ A) (g : yoneda.obj ▫0 ⟶ B) {m : ℕ} :
    Function.Injective ((Glue.inr f g)⟪m⟫) := by
  have h := glue0_isPushout_app f g m
  have hinj := Types.pushoutCocone_inr_injective_of_isColimit h.isColimit
    (vertexMap_app_injective f)
  rwa [h.cocone_inr] at hinj

/-- The two gluing injections have disjoint images on positive cells (the only common
values would come from the glued point `□⁰`, which has none). -/
theorem glue0_inl_ne_inr {A B : PrecubicalSet}
    (f : yoneda.obj ▫0 ⟶ A) (g : yoneda.obj ▫0 ⟶ B) {m : ℕ} (hm : 1 ≤ m)
    (x : A.cells m) (y : B.cells m) :
    (Glue.inl f g)⟪m⟫ x
      ≠ (Glue.inr f g)⟪m⟫ y := by
  intro heq
  obtain ⟨w, _, _⟩ := Types.exists_of_isPullback (glue0_isPullback_app f g m) x y heq
  exact (cube0_cells_isEmpty hm).false w

/-- The left wedge injection is injective **in every dimension** (including vertices). -/
theorem wedge2_inl_app_injective (X Y : BPSet) {m : ℕ} :
    Function.Injective ((Glue.inl X.finalVertex Y.initVertex)⟪m⟫) :=
  glue0_inl_app_injective X.finalVertex Y.initVertex

/-- The right wedge injection is injective **in every dimension** (including vertices). -/
theorem wedge2_inr_app_injective (X Y : BPSet) {m : ℕ} :
    Function.Injective ((Glue.inr X.finalVertex Y.initVertex)⟪m⟫) :=
  glue0_inr_app_injective X.finalVertex Y.initVertex

/-- The two wedge injections have disjoint images on positive cells (the only common
values would come from the glued point `□⁰`, which has none). -/
theorem wedge2_inl_ne_inr (X Y : BPSet) {m : ℕ} (hm : 1 ≤ m)
    (x : X.cells m) (y : Y.cells m) :
    (Glue.inl X.finalVertex Y.initVertex)⟪m⟫ x
      ≠ (Glue.inr X.finalVertex Y.initVertex)⟪m⟫ y :=
  glue0_inl_ne_inr X.finalVertex Y.initVertex hm x y

/-- **Every positive cell of a serial wedge lies in some block.**  By recursion on
`dims`: the empty wedge `□⁰` has no positive cells, and in `□^{n}∨ ⋁rest` a cell
is either in the head cube (block `0`) or in the tail (recurse). -/
theorem serialWedge_cell_exists : ∀ (dims : List ℕ+) {m : ℕ} (_hm : 1 ≤ m)
    (z : (⋁dims).cells m),
    ∃ (i : Fin dims.length) (x : (□((dims.get i) : ℕ)).cells m),
      (ιᵂ dims i)⟪m⟫ x = z
  | [], _, hm, z => ((cube0_cells_isEmpty hm).false z).elim
  | n :: rest, m, hm, z => by
      rcases wedge2_cell_cases (□(n : ℕ)) (⋁rest) m z with
        ⟨x, hx⟩ | ⟨y, hy⟩
      · exact ⟨0, x, by rw [serialWedge_ι_zero_app]; exact hx⟩
      · obtain ⟨j, x', hx'⟩ := serialWedge_cell_exists rest hm y
        refine ⟨j.succ, x', ?_⟩
        rw [serialWedge_ι_succ_app, hx']; exact hy

/-- **The block inclusions are injective in every dimension** (including vertices). -/
theorem serialWedge_ι_app_injective : ∀ (dims : List ℕ+) {m : ℕ}
    (i : Fin dims.length),
    Function.Injective ((ιᵂ dims i)⟪m⟫)
  | [], _, i => i.elim0
  | n :: rest, m, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [serialWedge_ι_zero]; exact wedge2_inl_app_injective _ _
      · intro a b hab
        rw [serialWedge_ι_succ_app, serialWedge_ι_succ_app] at hab
        exact serialWedge_ι_app_injective rest j (wedge2_inr_app_injective _ _ hab)

/-- **Blocks are unique**: a positive cell in block `i` and in block `i'` forces
`i = i'`.  Disjointness of distinct blocks comes from `wedge2_inl_ne_inr` (head vs
tail) and the inductive hypothesis (within the tail). -/
theorem serialWedge_block_unique : ∀ (dims : List ℕ+) {m : ℕ} (_hm : 1 ≤ m)
    (i i' : Fin dims.length) (z : (⋁dims).cells m),
    (∃ x, (ιᵂ dims i)⟪m⟫ x = z) →
    (∃ x', (ιᵂ dims i')⟪m⟫ x' = z) → i = i'
  | [], _, _, i, _, _, _, _ => i.elim0
  | n :: rest, m, hm, i, i', z, hx, hx' => by
      revert hx hx'
      refine Fin.cases ?_ (fun j => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) i'
        · intro _ _; rfl
        · intro hx hx'
          obtain ⟨x, hx⟩ := hx; obtain ⟨x', hx'⟩ := hx'
          rw [serialWedge_ι_zero_app] at hx
          rw [serialWedge_ι_succ_app] at hx'
          exact absurd (hx.trans hx'.symm) (wedge2_inl_ne_inr _ _ hm _ _)
      · refine Fin.cases ?_ (fun j' => ?_) i'
        · intro hx hx'
          obtain ⟨x, hx⟩ := hx; obtain ⟨x', hx'⟩ := hx'
          rw [serialWedge_ι_succ_app] at hx
          rw [serialWedge_ι_zero_app] at hx'
          exact absurd (hx'.trans hx.symm) (wedge2_inl_ne_inr _ _ hm _ _)
        · intro hx hx'
          obtain ⟨x, hx⟩ := hx; obtain ⟨x', hx'⟩ := hx'
          rw [serialWedge_ι_succ_app] at hx
          rw [serialWedge_ι_succ_app] at hx'
          have hinr := wedge2_inr_app_injective (□(n : ℕ)) (⋁rest)
            (hx.trans hx'.symm)
          have hj : j = j' :=
            serialWedge_block_unique rest hm j j' _ ⟨x, rfl⟩ ⟨x', hinr.symm⟩
          rw [hj]

/-- **Block-factoring of a wedge map.**  A wedge map `φ : ⋁ad ⟶ ⋁bd` sends each
(positive) block inclusion `ι_i` to a face of a unique `bd`-block: there is a block `r`
and a `Box` morphism `incl` with `ι_i ≫ φ = yoneda.map incl ≫ ι_r`.  (Existence; the
block `r` is unique by `serialWedge_block_unique`.) -/
theorem wedgeMap_block {ad bd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁bd).toPsh) (i : Fin ad.length) :
    ∃ (r : Fin bd.length) (incl : ▫((ad.get i) : ℕ) ⟶ ▫((bd.get r) : ℕ)),
      ιᵂ ad i ≫ φ = yoneda.map incl ≫ ιᵂ bd r := by
  obtain ⟨r, x, hx⟩ := serialWedge_cell_exists bd (ad.get i).2
    (yonedaEquiv (ιᵂ ad i ≫ φ))
  refine ⟨r, x, ?_⟩
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  exact hx.symm

/-- The read-off cube list has the same length as the dimension sequence. -/
theorem wedgeToCubes_length (dims : List ℕ+) (φ : (⋁dims).toPsh ⟶ K.toPsh) :
    (wedgeToCubes ⟨dims, φ⟩).length = dims.length := by
  conv_rhs => rw [← wedgeToCubes_dims dims φ]
  rw [List.length_map]

/-- **The read-off cube list as an `ofFn`**: the `i`-th cube is the Yoneda classifier of
the `i`-th block restriction `ι_i ≫ φ`.  (Stated as a `List.ofFn` to avoid `Fin`-casts
against the stuck `wedgeToCubes … .length`.) -/
theorem wedgeToCubes_eq_ofFn : ∀ (dims : List ℕ+)
    (φ : (⋁dims).toPsh ⟶ K.toPsh),
    wedgeToCubes ⟨dims, φ⟩
      = List.ofFn (fun i : Fin dims.length =>
          (⟨dims.get i, yonedaEquiv (ιᵂ dims i ≫ φ)⟩
            : Σ n : ℕ+, K.cells (n : ℕ)))
  | [], φ => by simp only [wedgeToCubes, List.ofFn_zero]
  | n :: rest, φ => by
      simp only [wedgeToCubes]
      rw [List.ofFn_succ]
      refine congr_arg₂ List.cons ?_ ?_
      · rfl
      · rw [wedgeToCubes_eq_ofFn rest]
        refine congr_arg List.ofFn (funext fun j => ?_)
        change (⟨rest.get j, yonedaEquiv (ιᵂ rest j ≫ (Glue.inr _ _ ≫ φ))⟩
              : Σ m : ℕ+, K.cells (m : ℕ))
            = ⟨rest.get j, yonedaEquiv ((ιᵂ rest j ≫ Glue.inr _ _) ≫ φ)⟩
        rw [Category.assoc]

/-- The `i`-th read-off cube, indexed by `Fin`: its dimension is `dims.get i` and its
cell is the Yoneda classifier of the `i`-th block restriction `ι_i ≫ φ`.  (The `get`
form of `wedgeToCubes_eq_ofFn`, threading the length cast.) -/
theorem wedgeToCubes_get (dims : List ℕ+) (φ : (⋁dims).toPsh ⟶ K.toPsh)
    (i : Fin (wedgeToCubes ⟨dims, φ⟩).length) :
    (wedgeToCubes ⟨dims, φ⟩).get i
      = ⟨dims.get (i.cast (wedgeToCubes_length dims φ)),
          yonedaEquiv (ιᵂ dims (i.cast (wedgeToCubes_length dims φ)) ≫ φ)⟩ := by
  rw [List.get_eq_getElem, List.getElem_of_eq (wedgeToCubes_eq_ofFn dims φ), List.getElem_ofFn]
  rfl

end CubeChain
