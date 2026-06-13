import CubeChains.Chains.Basic
import CubeChains.Wedge
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
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

end CubeChain
