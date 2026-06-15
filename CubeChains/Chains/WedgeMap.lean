import CubeChains.Chains.Basic
import CubeChains.Wedge
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# Wedge maps and the cube data they carry (ClaudeSetup.md §3)

This file is *purely about bi-pointed maps out of a serial wedge*,
`φ : □^∨(dims) ⟶ K`, and the cube data such a map carries.  There are two
constructions, inverse to each other (proved in `Chains/Correspondence.lean`):

* `wedgeDesc` (chain data `→` wedge map): glue the Yoneda classifiers
  `yonedaEquiv.symm cᵢ` of the cubes along the junctions, via `pushout.desc`.
* `wedgeToCubes` (wedge map `→` cube list): read off `cᵢ := yonedaEquiv (ιᵢ ≫ φ)`
  at each block.

The key structural facts are `wedgeToCubes_isCubeChain` (the read-off cubes form
a chain) and `wedgeToCubes_inj` (a wedge map is determined by its restriction to
the blocks — the colimit universal property, via `pushout.hom_ext` and Yoneda).
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace CubeChain

variable {K : BPSet}

/-! ### The point `□⁰` is rigid, and the wedge inclusions. -/

/-- `□⁰` has only the identity endomorphism (it is the representable point). -/
instance stdPre0_subsingleton : Subsingleton (StdCube.stdPre 0 ⟶ StdCube.stdPre 0) := by
  constructor; intro f g; apply PrecubicalConstructions.hom_ext; intro n
  match n with
  | 0     => intro c; apply Subtype.ext; funext i; exact i.elim0
  | (k+1) => intro c; exact absurd c.2 (by simp [StdCube.noneSet])

instance : Subsingleton ((BPSet.cube 0).toPsh.cells 0) := stdPre0_subsingleton

/-- The initial vertex of `X ∨ Y` is `X.init` pushed in along the left inclusion. -/
theorem wedge2_init' (X Y : BPSet) :
    (BPSet.wedge2 X Y).init =
      (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0)) X.init := rfl

/-- The final vertex of `X ∨ Y` is `Y.final` pushed in along the right inclusion. -/
theorem wedge2_final' (X Y : BPSet) :
    (BPSet.wedge2 X Y).final =
      (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob 0)) Y.final := rfl

/-- Evaluate `pushout.desc` after the left inclusion at a point.  Folding into the
`inl ≫ desc` composite (via `change`) sidesteps the dependent rewrite that a bare
`pushout.inl_desc` would trip over. -/
theorem inl_desc_app {W X Y Z : PrecubicalSet} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g]
    {h : Y ⟶ W} {k : Z ⟶ W} {w : f ≫ h = g ≫ k} {o} (y) :
    (pushout.desc h k w).app o ((pushout.inl f g).app o y) = h.app o y := by
  change ((pushout.inl f g) ≫ pushout.desc h k w).app o y = _
  rw [pushout.inl_desc]

/-- Evaluate `pushout.desc` after the right inclusion at a point. -/
theorem inr_desc_app {W X Y Z : PrecubicalSet} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g]
    {h : Y ⟶ W} {k : Z ⟶ W} {w : f ≫ h = g ≫ k} {o} (y) :
    (pushout.desc h k w).app o ((pushout.inr f g).app o y) = k.app o y := by
  change ((pushout.inr f g) ≫ pushout.desc h k w).app o y = _
  rw [pushout.inr_desc]

/-! ### `wedgeDesc`: chain data to a wedge map. -/

/-- A wedge map `□^∨(cubes) ⟶ K` (in `PrecubicalSet`) bundled with where it sends
the wedge's `init`/`final` vertices.  Bundling these invariants is what lets the
`cons` step discharge the pushout's cocone condition from the recursive call (the
`init`-bootstrap). -/
structure WedgeDesc {K : BPSet} (a b : K.toPsh.cells 0)
    (cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))) where
  /-- The underlying wedge map. -/
  map : (BPSet.serialWedge (cubes.map (·.1))).toPsh ⟶ K.toPsh
  /-- It sends the wedge's initial vertex to `a`. -/
  init_spec : map.app (op (Box.ob 0)) (BPSet.serialWedge (cubes.map (·.1))).init = a
  /-- It sends the wedge's final vertex to `b`. -/
  final_spec : map.app (op (Box.ob 0)) (BPSet.serialWedge (cubes.map (·.1))).final = b

/-- The inverse direction of the §3 correspondence (chain ↦ wedge map), built by
recursion on the cubes with the `init`/`final` invariants threaded through.  The
block maps are the Yoneda `yonedaEquiv.symm cᵢ`, glued by `pushout.desc`; the
cocone condition at each junction is exactly the recursive `init_spec`. -/
noncomputable def wedgeDesc {K : BPSet} (a b : K.toPsh.cells 0) :
    (cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))) → IsCubeChain a cubes b →
    WedgeDesc a b cubes
  | [], h =>
      { map := yonedaEquiv.symm a
        init_spec := by
          simp only [List.map_nil, BPSet.serialWedge_nil]
          rw [show (BPSet.cube 0).init = 𝟙 (Box.ob 0) from Subsingleton.elim _ _]
          exact yonedaEquiv.apply_symm_apply a
        final_spec := by
          simp only [List.map_nil, BPSet.serialWedge_nil]
          rw [show (BPSet.cube 0).final = 𝟙 (Box.ob 0) from Subsingleton.elim _ _]
          exact (yonedaEquiv.apply_symm_apply a).trans h }
  | ⟨n, c⟩ :: rest, h =>
      let r := wedgeDesc (K.toPsh.vertex₁ c) b rest h.2
      { map := pushout.desc (yonedaEquiv.symm c) r.map (by
          apply yonedaEquiv.injective
          simp only [yonedaEquiv_comp, BPSet.finalVertex, BPSet.initVertex, BPSet.vertexMap,
            Equiv.apply_symm_apply]
          rw [r.init_spec]; rfl)
        init_spec := by
          simp only [List.map_cons, BPSet.serialWedge_cons, wedge2_init']
          exact (inl_desc_app _).trans h.1
        final_spec := by
          simp only [List.map_cons, BPSet.serialWedge_cons, wedge2_final']
          exact (inr_desc_app _).trans r.final_spec }

/-- The bi-pointed map `□^∨(dims) ⟶ K` of a chain, packaged from `wedgeDesc`. -/
def wedgeDescHom {K : BPSet} cubes
  (desc : WedgeDesc K.init K.final cubes) :
  (BPSet.serialWedge (List.map (fun x ↦ x.fst) cubes) ⟶ K) where
    hom := desc.map
    app_init := desc.init_spec
    app_final := desc.final_spec

/-! ### `wedgeToCubes`: a wedge map to its cube list. -/

/-- Read the cubes off a (plain) wedge map: the `i`-th cube is the Yoneda
classifier of the `i`-th block restriction. -/
noncomputable def wedgeToCubes : (dims : List ℕ+) × ((BPSet.serialWedge dims).toPsh ⟶ K.toPsh) →
  List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))
  | ⟨ [], _ ⟩ => []
  | ⟨ x :: rest, hom⟩ =>
    ⟨x, yonedaEquiv (pushout.inl _ _ ≫ hom)⟩
     :: wedgeToCubes ⟨rest, pushout.inr _ _ ≫ hom⟩

/-- The source extremal vertex of a Yoneda-classified cell, computed by Yoneda
naturality: `vertex₀ (yonedaEquiv f) = f` evaluated at the initial-vertex map. -/
theorem vertex₀_yonedaEquiv {n : ℕ} (f : yoneda.obj (Box.ob n) ⟶ K.toPsh) :
    K.toPsh.vertex₀ (yonedaEquiv f) = f.app (op (Box.ob 0)) (PrecubicalSet.initVertexMap n) := by
  unfold PrecubicalSet.vertex₀
  exact map_yonedaEquiv f (PrecubicalSet.initVertexMap n)

/-- The target extremal vertex of a Yoneda-classified cell. -/
theorem vertex₁_yonedaEquiv {n : ℕ} (f : yoneda.obj (Box.ob n) ⟶ K.toPsh) :
    K.toPsh.vertex₁ (yonedaEquiv f) = f.app (op (Box.ob 0)) (PrecubicalSet.finalVertexMap n) := by
  unfold PrecubicalSet.vertex₁
  exact map_yonedaEquiv f (PrecubicalSet.finalVertexMap n)

/-- The wedge gluing identity: in `X ∨ Y`, the image of `X.final` under the left
inclusion equals the image of `Y.init` under the right inclusion.  This is just
`pushout.condition` pushed through Yoneda. -/
theorem wedge2_glue (X Y : BPSet) :
    (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0)) X.final
      = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob 0)) Y.init := by
  have h := pushout.condition (f := X.finalVertex) (g := Y.initVertex)
  simp only [BPSet.finalVertex, BPSet.initVertex, BPSet.vertexMap,
    yonedaEquiv_symm_naturality_right] at h
  exact yonedaEquiv.symm.injective h

/-- **The cubes read off a wedge map form a cube chain.**  Recursion on the
dimension sequence; the head computation uses `vertex₀_yonedaEquiv`/`wedge2_init'`
and the link uses `wedge2_glue`. -/
theorem wedgeToCubes_isCubeChain (dims : List ℕ+)
    (hom : (BPSet.serialWedge dims).toPsh ⟶ K.toPsh) :
    IsCubeChain (hom.app (op (Box.ob 0)) (BPSet.serialWedge dims).init)
      (wedgeToCubes ⟨dims, hom⟩)
      (hom.app (op (Box.ob 0)) (BPSet.serialWedge dims).final) := by
  induction dims with
  | nil =>
      simp only [wedgeToCubes]
      exact congrArg (hom.app (op (Box.ob 0)))
        (Subsingleton.elim ((BPSet.cube 0).init) ((BPSet.cube 0).final))
  | cons x rest ih =>
      simp only [wedgeToCubes]
      refine ⟨?_, ?_⟩
      · -- `(serialWedge (x::rest)).init` is *defeq* to `inl (cube x).init`, so the
        -- head computation closes definitionally after Yoneda naturality.
        exact vertex₀_yonedaEquiv (pushout.inl _ _ ≫ hom)
      · -- `vertex₁` of the head cube glues (via `wedge2_glue`) onto the right
        -- inclusion, which is exactly the recursive map `inr ≫ hom`.
        have e1 : K.toPsh.vertex₁ (yonedaEquiv (pushout.inl _ _ ≫ hom))
            = (pushout.inr _ _ ≫ hom).app (op (Box.ob 0)) (BPSet.serialWedge rest).init :=
          (vertex₁_yonedaEquiv (pushout.inl _ _ ≫ hom)).trans
            (congrArg (hom.app (op (Box.ob 0)))
              (wedge2_glue (BPSet.cube (x : ℕ)) (BPSet.serialWedge rest)))
        have e2 : hom.app (op (Box.ob 0)) (BPSet.serialWedge (x :: rest)).final
            = (pushout.inr _ _ ≫ hom).app (op (Box.ob 0)) (BPSet.serialWedge rest).final := rfl
        rw [e1, e2]
        exact ih (pushout.inr _ _ ≫ hom)

/-- Reading the dimensions back off a wedge map recovers the dimension sequence. -/
theorem wedgeToCubes_dims : ∀ (dims : List ℕ+) (hom : (BPSet.serialWedge dims).toPsh ⟶ K.toPsh),
    (wedgeToCubes ⟨dims, hom⟩).map (·.1) = dims
  | [], _ => by simp [wedgeToCubes]
  | _ :: rest, hom => by
      simp only [wedgeToCubes, List.map_cons]
      rw [wedgeToCubes_dims rest (pushout.inr _ _ ≫ hom)]

/-- **Wedge maps are determined by the cubes they restrict to**, together with
their value on the initial vertex (needed only for the empty wedge `□⁰`).  This is
the colimit universal property of the serial wedge, threaded through
`pushout.hom_ext` and Yoneda. -/
theorem wedgeToCubes_inj : ∀ (dims : List ℕ+) (f g : (BPSet.serialWedge dims).toPsh ⟶ K.toPsh),
    wedgeToCubes ⟨dims, f⟩ = wedgeToCubes ⟨dims, g⟩ →
    f.app (op (Box.ob 0)) (BPSet.serialWedge dims).init
      = g.app (op (Box.ob 0)) (BPSet.serialWedge dims).init → f = g
  | [], f, g, _, hinit => by
      apply yonedaEquiv.injective
      have e : (BPSet.serialWedge ([] : List ℕ+)).init = 𝟙 (Box.ob 0) :=
        Subsingleton.elim (α := (BPSet.cube 0).toPsh.cells 0) _ _
      rw [yonedaEquiv_apply, yonedaEquiv_apply, ← e]
      exact hinit
  | x :: rest, f, g, hcubes, _ => by
      simp only [wedgeToCubes, List.cons.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at hcubes
      obtain ⟨hhead, htail⟩ := hcubes
      have hfg : pushout.inl _ _ ≫ f = pushout.inl _ _ ≫ g := yonedaEquiv.injective hhead
      refine pushout.hom_ext hfg ?_
      refine wedgeToCubes_inj rest _ _ htail ?_
      simp only [NatTrans.comp_app, types_comp_apply]
      rw [← wedge2_glue (BPSet.cube (x : ℕ)) (BPSet.serialWedge rest)]
      exact congrArg (fun m => m.app (op (Box.ob 0)) (BPSet.cube (x : ℕ)).final) hfg

/-- **Uniqueness for the serial wedge** (its colimit universal property, in the
clean `ι`-form): two maps out of `□^∨(dims)` into *any* presheaf `Z` that agree on
every block (after the inclusions `serialWedge.ι`) and on the initial vertex are
equal.  The initial-vertex hypothesis is only needed for the empty wedge `□⁰`; for
nonempty `dims` it follows from the block agreement.  Proved by `pushout.hom_ext`
recursion, exactly mirroring `wedgeToCubes_inj`. -/
theorem serialWedge_hom_ext {Z : PrecubicalSet} :
    ∀ (dims : List ℕ+) (f g : (BPSet.serialWedge dims).toPsh ⟶ Z),
      (∀ i, BPSet.serialWedge.ι dims i ≫ f = BPSet.serialWedge.ι dims i ≫ g) →
      f.app (op (Box.ob 0)) (BPSet.serialWedge dims).init
        = g.app (op (Box.ob 0)) (BPSet.serialWedge dims).init → f = g
  | [], f, g, _, hinit => by
      apply yonedaEquiv.injective
      have e : (BPSet.serialWedge ([] : List ℕ+)).init = 𝟙 (Box.ob 0) :=
        Subsingleton.elim (α := (BPSet.cube 0).toPsh.cells 0) _ _
      rw [yonedaEquiv_apply, yonedaEquiv_apply, ← e]
      exact hinit
  | x :: rest, f, g, hι, _ => by
      refine pushout.hom_ext ?_ ?_
      · have h0 := hι 0
        simpa only [BPSet.serialWedge.ι, Fin.cases_zero] using h0
      · refine serialWedge_hom_ext rest (pushout.inr _ _ ≫ f) (pushout.inr _ _ ≫ g) ?_ ?_
        · intro j
          have hj := hι j.succ
          simp only [BPSet.serialWedge.ι, Fin.cases_succ] at hj
          rw [Category.assoc, Category.assoc] at hj
          exact hj
        · simp only [NatTrans.comp_app, types_comp_apply]
          rw [← wedge2_glue (BPSet.cube (x : ℕ)) (BPSet.serialWedge rest)]
          have h0 := hι 0
          simp only [BPSet.serialWedge.ι, Fin.cases_zero] at h0
          exact congrArg (fun m => m.app (op (Box.ob 0)) (BPSet.cube (x : ℕ)).final) h0

/-- The head block of the descent map is the Yoneda classifier of the head cube. -/
theorem inl_comp_wedgeDesc (a b : K.toPsh.cells 0) (n : ℕ+) (c : K.toPsh.cells (n : ℕ))
    (rest : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))) (h : IsCubeChain a (⟨n, c⟩ :: rest) b) :
    pushout.inl (BPSet.cube (n : ℕ)).finalVertex (BPSet.serialWedge (rest.map (·.1))).initVertex
        ≫ (wedgeDesc a b (⟨n, c⟩ :: rest) h).map
      = yonedaEquiv.symm c :=
  pushout.inl_desc _ _ _

/-- The tail of the descent map is the descent map of the tail chain. -/
theorem inr_comp_wedgeDesc (a b : K.toPsh.cells 0) (n : ℕ+) (c : K.toPsh.cells (n : ℕ))
    (rest : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))) (h : IsCubeChain a (⟨n, c⟩ :: rest) b) :
    pushout.inr (BPSet.cube (n : ℕ)).finalVertex (BPSet.serialWedge (rest.map (·.1))).initVertex
        ≫ (wedgeDesc a b (⟨n, c⟩ :: rest) h).map
      = (wedgeDesc (K.toPsh.vertex₁ c) b rest h.2).map :=
  pushout.inr_desc _ _ _

/-- Cell-level head rule: the descent map sends an `inl`-cell to the head cube's
Yoneda classifier `yonedaEquiv.symm c`. -/
theorem wedgeDesc_inl_app (a b : K.toPsh.cells 0) (n : ℕ+) (c : K.toPsh.cells (n : ℕ))
    (rest : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))) (h : IsCubeChain a (⟨n, c⟩ :: rest) b)
    {m : ℕ} (x : (BPSet.cube (n : ℕ)).toPsh.cells m) :
    (wedgeDesc a b (⟨n, c⟩ :: rest) h).map.app (op (Box.ob m))
        ((pushout.inl (BPSet.cube (n : ℕ)).finalVertex
          (BPSet.serialWedge (rest.map (·.1))).initVertex).app (op (Box.ob m)) x)
      = (yonedaEquiv.symm c).app (op (Box.ob m)) x :=
  congrArg (fun f : (BPSet.cube (n : ℕ)).toPsh ⟶ K.toPsh => f.app (op (Box.ob m)) x)
    (inl_comp_wedgeDesc a b n c rest h)

/-- Cell-level tail rule: the descent map sends an `inr`-cell to the tail descent. -/
theorem wedgeDesc_inr_app (a b : K.toPsh.cells 0) (n : ℕ+) (c : K.toPsh.cells (n : ℕ))
    (rest : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))) (h : IsCubeChain a (⟨n, c⟩ :: rest) b)
    {m : ℕ} (y : (BPSet.serialWedge (rest.map (·.1))).toPsh.cells m) :
    (wedgeDesc a b (⟨n, c⟩ :: rest) h).map.app (op (Box.ob m))
        ((pushout.inr (BPSet.cube (n : ℕ)).finalVertex
          (BPSet.serialWedge (rest.map (·.1))).initVertex).app (op (Box.ob m)) y)
      = (wedgeDesc (K.toPsh.vertex₁ c) b rest h.2).map.app (op (Box.ob m)) y :=
  congrArg (fun f : (BPSet.serialWedge (rest.map (·.1))).toPsh ⟶ K.toPsh => f.app (op (Box.ob m)) y)
    (inr_comp_wedgeDesc a b n c rest h)

/-- **Block-restriction rule for the descent map**: restricting `wedgeDesc` to the
`k`-th block (via `serialWedge.ι`) recovers the Yoneda classifier of the `k`-th cube
(up to the `List.get`/`map` dimension cast).  Proved by induction on `cubes` with
`Fin.cases` on `k`, mirroring the recursions of `serialWedge.ι` and `wedgeDesc`. -/
theorem ι_comp_wedgeDesc : ∀ (a b : K.toPsh.cells 0)
    (cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))) (h : IsCubeChain a cubes b)
    (k : Fin cubes.length),
    BPSet.serialWedge.ι (cubes.map (·.1)) (k.cast (by rw [List.length_map]))
        ≫ (wedgeDesc a b cubes h).map
      = eqToHom (congrArg (fun m : ℕ+ => (BPSet.cube (m : ℕ)).toPsh)
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
        simp only [List.map_cons, BPSet.serialWedge.ι, hcast, Fin.cases_succ, Category.assoc,
          List.get_cons_succ]
        refine (congrArg
          (BPSet.serialWedge.ι (rest.map (·.1)) (k'.cast (by rw [List.length_map])) ≫ ·)
          (inr_comp_wedgeDesc a b n c rest h)).trans ?_
        exact ι_comp_wedgeDesc (K.toPsh.vertex₁ c) b rest h.2 k'

/-- Reading the cubes back off the descent map recovers the original cubes. -/
theorem wedgeToCubes_wedgeDesc : ∀ (a b : K.toPsh.cells 0)
    (cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))) (h : IsCubeChain a cubes b),
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
    ∀ (a b : K.toPsh.cells 0) (cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ)))
      (h : IsCubeChain a cubes b),
    wedgeToCubes ⟨cubes.map (·.1), (wedgeDesc a b cubes h).map ≫ g⟩
      = cubes.map (fun c => ⟨c.1, g.app (op (Box.ob (c.1 : ℕ))) c.2⟩)
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
instance stdCube0_cells_subsingleton (k : ℕ) : Subsingleton (StdCube.cells 0 k) := by
  constructor
  intro a b
  apply Subtype.ext
  funext i
  exact i.elim0

/-- The defining pushout square of `wedge2 X Y`, transported to `Type` at level `m`
by the colimit-preserving evaluation functor. -/
theorem wedge2_isPushout_app (X Y : BPSet) (m : ℕ) :
    IsPushout (X.finalVertex.app (op (Box.ob m))) (Y.initVertex.app (op (Box.ob m)))
      ((pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob m)))
      ((pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob m))) :=
  (IsPushout.of_hasPushout X.finalVertex Y.initVertex).map
    (F := (evaluation Boxᵒᵖ Type).obj (op (Box.ob m)))

/-- Every `m`-cell of `X ∨ Y` comes from `X` (via `inl`) or from `Y` (via `inr`). -/
theorem wedge2_cell_cases (X Y : BPSet) (m : ℕ) (c : (BPSet.wedge2 X Y).toPsh.cells m) :
    (∃ x, (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob m)) x = c) ∨
      ∃ y, (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob m)) y = c :=
  Types.eq_or_eq_of_isPushout (wedge2_isPushout_app X Y m) c

/-- The wedge square is a pullback at every level (`□⁰ → X` is injective: `□⁰` has at
most one `m`-cell).  Hence the two blocks meet only over the glued point — the basis
for cross-block disjointness of positive cells. -/
theorem wedge2_isPullback_app (X Y : BPSet) (m : ℕ) :
    IsPullback (X.finalVertex.app (op (Box.ob m))) (Y.initVertex.app (op (Box.ob m)))
      ((pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob m)))
      ((pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob m))) := by
  refine Types.isPullback_of_isPushout (wedge2_isPushout_app X Y m) ?_
  intro a b _
  apply PrecubicalConstructions.hom_ext
  intro n c
  apply Subtype.ext
  funext i
  exact i.elim0

/-! ### Lifting the decomposition to the serial wedge

A *positive-dimensional* cell of `□^∨(dims)` lies in a **unique block**, as a face
of that block's cube.  We first record the head and tail block computation rules for
`serialWedge.ι`, then the block inclusions are injective with pairwise-disjoint
images (`□⁰` contributes no positive cells), and finally every positive cell
factors through exactly one block.  This is the geometric core behind both the
backward functor (`wedgeToRefineMap`) and the embedding theorem (`descent_mono`). -/

/-- The head block inclusion of a serial wedge is the left pushout injection. -/
theorem serialWedge_ι_zero (n : ℕ+) (rest : List ℕ+) :
    BPSet.serialWedge.ι (n :: rest) 0
      = pushout.inl (BPSet.cube (n : ℕ)).finalVertex (BPSet.serialWedge rest).initVertex :=
  rfl

/-- A later block inclusion of a serial wedge is the tail inclusion followed by the
right pushout injection. -/
theorem serialWedge_ι_succ (n : ℕ+) (rest : List ℕ+) (j : Fin rest.length) :
    BPSet.serialWedge.ι (n :: rest) j.succ
      = BPSet.serialWedge.ι rest j
        ≫ pushout.inr (BPSet.cube (n : ℕ)).finalVertex (BPSet.serialWedge rest).initVertex :=
  rfl

/-- Head-block computation rule, at the level of cells. -/
theorem serialWedge_ι_zero_app (n : ℕ+) (rest : List ℕ+) {m : ℕ}
    (x : (BPSet.cube (n : ℕ)).toPsh.cells m) :
    (BPSet.serialWedge.ι (n :: rest) 0).app (op (Box.ob m)) x
      = (pushout.inl (BPSet.cube (n : ℕ)).finalVertex
          (BPSet.serialWedge rest).initVertex).app (op (Box.ob m)) x :=
  rfl

/-- Tail-block computation rule, at the level of cells. -/
theorem serialWedge_ι_succ_app (n : ℕ+) (rest : List ℕ+) (j : Fin rest.length) {m : ℕ}
    (x : (BPSet.cube ((rest.get j) : ℕ)).toPsh.cells m) :
    (BPSet.serialWedge.ι (n :: rest) j.succ).app (op (Box.ob m)) x
      = (pushout.inr (BPSet.cube (n : ℕ)).finalVertex
          (BPSet.serialWedge rest).initVertex).app (op (Box.ob m))
            ((BPSet.serialWedge.ι rest j).app (op (Box.ob m)) x) :=
  rfl

/-- `□⁰` has no positive-dimensional cells: a box morphism `□ᵐ ⟶ □⁰` (`m ≥ 1`)
evaluates to an `m`-cell of the point `stdPre 0`, of which there are none. -/
theorem cube0_cells_isEmpty {m : ℕ} (hm : 1 ≤ m) :
    IsEmpty ((BPSet.cube 0).toPsh.cells m) := by
  constructor
  intro f
  have c : StdCube.cells 0 m := StdCube.ev f
  have hle : (StdCube.noneSet c.val).card ≤ (Finset.univ : Finset (Fin 0)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [c.prop, Finset.card_univ, Fintype.card_fin] at hle
  omega

/-- The image-vertex map `□⁰ ⟶ X` is injective on positive cells (its domain has
none). -/
theorem finalVertex_app_injective (X : BPSet) {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (X.finalVertex.app (op (Box.ob m))) :=
  fun a _ _ => ((cube0_cells_isEmpty hm).false a).elim

theorem initVertex_app_injective (X : BPSet) {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (X.initVertex.app (op (Box.ob m))) :=
  fun a _ _ => ((cube0_cells_isEmpty hm).false a).elim

/-- The left wedge injection is injective on positive cells. -/
theorem wedge2_inl_app_injective (X Y : BPSet) {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective ((pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob m))) := by
  have h := (wedge2_isPushout_app X Y m).flip
  have hinj := Types.pushoutCocone_inr_injective_of_isColimit h.isColimit
    (initVertex_app_injective Y hm)
  rwa [h.cocone_inr] at hinj

/-- The right wedge injection is injective on positive cells. -/
theorem wedge2_inr_app_injective (X Y : BPSet) {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective ((pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob m))) := by
  have h := wedge2_isPushout_app X Y m
  have hinj := Types.pushoutCocone_inr_injective_of_isColimit h.isColimit
    (finalVertex_app_injective X hm)
  rwa [h.cocone_inr] at hinj

/-- The two wedge injections have disjoint images on positive cells (the only common
values would come from the glued point `□⁰`, which has none). -/
theorem wedge2_inl_ne_inr (X Y : BPSet) {m : ℕ} (hm : 1 ≤ m)
    (x : X.toPsh.cells m) (y : Y.toPsh.cells m) :
    (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob m)) x
      ≠ (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob m)) y := by
  intro heq
  obtain ⟨w, _, _⟩ := Types.exists_of_isPullback (wedge2_isPullback_app X Y m) x y heq
  exact (cube0_cells_isEmpty hm).false w

/-- **Every positive cell of a serial wedge lies in some block.**  By recursion on
`dims`: the empty wedge `□⁰` has no positive cells, and in `□^{n}∨ □^∨(rest)` a cell
is either in the head cube (block `0`) or in the tail (recurse). -/
theorem serialWedge_cell_exists : ∀ (dims : List ℕ+) {m : ℕ} (_hm : 1 ≤ m)
    (z : (BPSet.serialWedge dims).toPsh.cells m),
    ∃ (i : Fin dims.length) (x : (BPSet.cube ((dims.get i) : ℕ)).toPsh.cells m),
      (BPSet.serialWedge.ι dims i).app (op (Box.ob m)) x = z
  | [], _, hm, z => ((cube0_cells_isEmpty hm).false z).elim
  | n :: rest, m, hm, z => by
      rcases wedge2_cell_cases (BPSet.cube (n : ℕ)) (BPSet.serialWedge rest) m z with
        ⟨x, hx⟩ | ⟨y, hy⟩
      · exact ⟨0, x, by rw [serialWedge_ι_zero_app]; exact hx⟩
      · obtain ⟨j, x', hx'⟩ := serialWedge_cell_exists rest hm y
        refine ⟨j.succ, x', ?_⟩
        rw [serialWedge_ι_succ_app, hx']; exact hy

/-- **The block inclusions are injective on positive cells.** -/
theorem serialWedge_ι_app_injective : ∀ (dims : List ℕ+) {m : ℕ} (_hm : 1 ≤ m)
    (i : Fin dims.length),
    Function.Injective ((BPSet.serialWedge.ι dims i).app (op (Box.ob m)))
  | [], _, _, i => i.elim0
  | n :: rest, m, hm, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [serialWedge_ι_zero]; exact wedge2_inl_app_injective _ _ hm
      · intro a b hab
        rw [serialWedge_ι_succ_app, serialWedge_ι_succ_app] at hab
        exact serialWedge_ι_app_injective rest hm j (wedge2_inr_app_injective _ _ hm hab)

/-- **Blocks are unique**: a positive cell in block `i` and in block `i'` forces
`i = i'`.  Disjointness of distinct blocks comes from `wedge2_inl_ne_inr` (head vs
tail) and the inductive hypothesis (within the tail). -/
theorem serialWedge_block_unique : ∀ (dims : List ℕ+) {m : ℕ} (_hm : 1 ≤ m)
    (i i' : Fin dims.length) (z : (BPSet.serialWedge dims).toPsh.cells m),
    (∃ x, (BPSet.serialWedge.ι dims i).app (op (Box.ob m)) x = z) →
    (∃ x', (BPSet.serialWedge.ι dims i').app (op (Box.ob m)) x' = z) → i = i'
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
          have hinr := wedge2_inr_app_injective (BPSet.cube (n : ℕ)) (BPSet.serialWedge rest) hm
            (hx.trans hx'.symm)
          have hj : j = j' :=
            serialWedge_block_unique rest hm j j' _ ⟨x, rfl⟩ ⟨x', hinr.symm⟩
          rw [hj]

/-- **Block-factoring of a wedge map.**  A wedge map `φ : □^∨(ad) ⟶ □^∨(bd)` sends each
(positive) block inclusion `ι_i` to a face of a unique `bd`-block: there is a block `r`
and a `Box` morphism `incl` with `ι_i ≫ φ = yoneda.map incl ≫ ι_r`.  (Existence; the
block `r` is unique by `serialWedge_block_unique`.) -/
theorem wedgeMap_block {ad bd : List ℕ+}
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge bd).toPsh) (i : Fin ad.length) :
    ∃ (r : Fin bd.length) (incl : Box.ob ((ad.get i) : ℕ) ⟶ Box.ob ((bd.get r) : ℕ)),
      BPSet.serialWedge.ι ad i ≫ φ = yoneda.map incl ≫ BPSet.serialWedge.ι bd r := by
  obtain ⟨r, x, hx⟩ := serialWedge_cell_exists bd (ad.get i).2
    (yonedaEquiv (BPSet.serialWedge.ι ad i ≫ φ))
  refine ⟨r, x, ?_⟩
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  exact hx.symm

/-- The read-off cube list has the same length as the dimension sequence. -/
theorem wedgeToCubes_length (dims : List ℕ+) (φ : (BPSet.serialWedge dims).toPsh ⟶ K.toPsh) :
    (wedgeToCubes ⟨dims, φ⟩).length = dims.length := by
  conv_rhs => rw [← wedgeToCubes_dims dims φ]
  rw [List.length_map]

/-- **The read-off cube list as an `ofFn`**: the `i`-th cube is the Yoneda classifier of
the `i`-th block restriction `ι_i ≫ φ`.  (Stated as a `List.ofFn` to avoid `Fin`-casts
against the stuck `wedgeToCubes … .length`.) -/
theorem wedgeToCubes_eq_ofFn : ∀ (dims : List ℕ+)
    (φ : (BPSet.serialWedge dims).toPsh ⟶ K.toPsh),
    wedgeToCubes ⟨dims, φ⟩
      = List.ofFn (fun i : Fin dims.length =>
          (⟨dims.get i, yonedaEquiv (BPSet.serialWedge.ι dims i ≫ φ)⟩
            : Σ n : ℕ+, K.toPsh.cells (n : ℕ)))
  | [], φ => by simp only [wedgeToCubes, List.ofFn_zero]
  | n :: rest, φ => by
      simp only [wedgeToCubes]
      rw [List.ofFn_succ]
      refine congr_arg₂ List.cons ?_ ?_
      · rfl
      · rw [wedgeToCubes_eq_ofFn rest]
        refine congr_arg List.ofFn (funext fun j => ?_)
        change (⟨rest.get j, yonedaEquiv (BPSet.serialWedge.ι rest j ≫ (pushout.inr _ _ ≫ φ))⟩
              : Σ m : ℕ+, K.toPsh.cells (m : ℕ))
            = ⟨rest.get j, yonedaEquiv ((BPSet.serialWedge.ι rest j ≫ pushout.inr _ _) ≫ φ)⟩
        rw [Category.assoc]

/-- The `i`-th read-off cube, indexed by `Fin`: its dimension is `dims.get i` and its
cell is the Yoneda classifier of the `i`-th block restriction `ι_i ≫ φ`.  (The `get`
form of `wedgeToCubes_eq_ofFn`, threading the length cast.) -/
theorem wedgeToCubes_get (dims : List ℕ+) (φ : (BPSet.serialWedge dims).toPsh ⟶ K.toPsh)
    (i : Fin (wedgeToCubes ⟨dims, φ⟩).length) :
    (wedgeToCubes ⟨dims, φ⟩).get i
      = ⟨dims.get (i.cast (wedgeToCubes_length dims φ)),
          yonedaEquiv (BPSet.serialWedge.ι dims (i.cast (wedgeToCubes_length dims φ)) ≫ φ)⟩ := by
  rw [List.get_eq_getElem, List.getElem_of_eq (wedgeToCubes_eq_ofFn dims φ), List.getElem_ofFn]
  rfl

end CubeChain
