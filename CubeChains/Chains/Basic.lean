import CubeChains.Bipointed
import CubeChains.Wedge
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Cube chains (ClaudeSetup.md §4)

For a bi-pointed precubical set `K`, a *cube chain* is a sequence of cubes of
positive dimension running from `K.init` to `K.final`, each cube's target vertex
being the next cube's source vertex.

We use the *junction-vertex* representation: alongside the cubes we store the
`l + 1` junction vertices `vtx : Fin (dims.length + 1) → cells 0`, with
`vtx 0 = init`, `vtx last = final`, and `cube i` running from `vtx i.castSucc`
to `vtx i.succ`.  This handles the empty chain uniformly (it forces
`init = final`) and makes the link condition `vertex₁ (cube i) = vertex₀
(cube (i+1))` a theorem rather than a field.
-/


open CategoryTheory CategoryTheory.Limits Opposite

/-- A cube chain in a bi-pointed precubical set `K`: a list of cubes, each
carrying its own positive dimension as a dependent pair `⟨n, c⟩ : Σ n : ℕ+,
cells n`, together with the junction vertices tying them from `init` to `final`.
The dimension sequence is then the projection `cubes.map (·.1)`. -/
structure CubeChain (K : BPSet) where
  /-- The cubes of the chain, each with its (positive) dimension. -/
  cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))
  /-- The `l + 1` junction vertices. -/
  vtx : Fin (cubes.length + 1) → K.toPsh.cells 0
  /-- The first junction vertex is the initial cell. -/
  vtx_zero : vtx 0 = K.init
  /-- The last junction vertex is the final cell. -/
  vtx_last : vtx (Fin.last cubes.length) = K.final
  /-- The source vertex of the `i`-th cube is junction `i`. -/
  cube_src : ∀ i : Fin cubes.length, K.toPsh.vertex₀ (cubes.get i).2 = vtx i.castSucc
  /-- The target vertex of the `i`-th cube is junction `i + 1`. -/
  cube_tgt : ∀ i : Fin cubes.length, K.toPsh.vertex₁ (cubes.get i).2 = vtx i.succ

def IsCubeChain {K : PrecubicalSet} (a : K.cells 0) :
    List (Σ n : ℕ+, K.cells (n : ℕ)) → K.cells 0 → Prop
  | [],            b => a = b
  | ⟨_, c⟩ :: rest, b => K.vertex₀ c = a ∧ IsCubeChain (K.vertex₁ c) rest b

/-- General-endpoints version: a list of cubes with junction vertices `vtx` and
the source/target conditions forms an `IsCubeChain` from `vtx 0` to `vtx last`.
Keeping the endpoints general (rather than fixing `K.init`/`K.final`) is exactly
what makes the induction hypothesis strong enough. -/
theorem isCubeChain_aux {K : BPSet}
    (cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ)))
    (vtx : Fin (cubes.length + 1) → K.toPsh.cells 0)
    (hsrc : ∀ i : Fin cubes.length, K.toPsh.vertex₀ (cubes.get i).2 = vtx i.castSucc)
    (htgt : ∀ i : Fin cubes.length, K.toPsh.vertex₁ (cubes.get i).2 = vtx i.succ) :
    IsCubeChain (vtx 0) cubes (vtx (Fin.last cubes.length)) := by
  induction cubes with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨n, c⟩ := hd
      refine ⟨by simpa using hsrc 0, ?_⟩
      have hstart : K.toPsh.vertex₁ c = vtx (Fin.succ 0) := htgt 0
      rw [hstart]
      have key := ih (vtx ∘ Fin.succ)
        (fun i => by rw [Function.comp_apply, Fin.succ_castSucc]; exact hsrc i.succ)
        (fun i => by rw [Function.comp_apply]; exact htgt i.succ)
      simp only [Function.comp_apply, Fin.succ_last] at key
      exact key

theorem isCubeChain {K : BPSet} (C : CubeChain K) :
    IsCubeChain K.init C.cubes K.final := by
  have h := isCubeChain_aux C.cubes C.vtx C.cube_src C.cube_tgt
  rw [C.vtx_last, C.vtx_zero] at h
  exact h

namespace CubeChain
open CategoryTheory CategoryTheory.Limits


variable {K : BPSet}

/-- The dimension sequence of a chain: the dimensions of its cubes. -/
def dims (c : CubeChain K) : List ℕ+ := c.cubes.map (·.1)

/-- The `i`-th cube of the chain. -/
def cube (c : CubeChain K) (i : Fin c.cubes.length) :
    K.toPsh.cells ((c.cubes.get i).1 : ℕ) := (c.cubes.get i).2

/-- The dimension sequence of a chain (alias for `dims`). -/
def dimSeq (c : CubeChain K) : List ℕ+ := c.dims

/-- The total length of a chain: the sum of its dimensions. -/
def length (c : CubeChain K) : ℕ := (c.cubes.map (fun x => (x.1 : ℕ))).sum

@[simp] theorem dimSeq_eq (c : CubeChain K) : c.dimSeq = c.dims := rfl

@[simp] theorem dims_length (c : CubeChain K) : c.dims.length = c.cubes.length := by
  simp [dims]

/-- The link condition: the target vertex of consecutive cubes matches the source
vertex of the next.  This is automatic in the junction-vertex representation. -/
theorem link (c : CubeChain K) (i : Fin c.cubes.length) (h : i.val + 1 < c.cubes.length) :
    K.toPsh.vertex₁ (c.cubes.get i).2 = K.toPsh.vertex₀ (c.cubes.get ⟨i.val + 1, h⟩).2 := by
  have hfin : Fin.succ i = Fin.castSucc (⟨i.val + 1, h⟩ : Fin c.cubes.length) := by
    apply Fin.ext; simp
  rw [c.cube_tgt i, c.cube_src ⟨i.val + 1, h⟩, hfin]

/-- An empty chain forces `init = final` (the trivial point chain). -/
theorem init_eq_final_of_nil (c : CubeChain K) (h : c.cubes.length = 0) :
    K.init = K.final := by
  have hfin : (0 : Fin (c.cubes.length + 1)) = Fin.last c.cubes.length := by
    apply Fin.ext; simp [h]
  rw [← c.vtx_zero, ← c.vtx_last, hfin]

/-! **The map↔chain correspondence (ClaudeSetup.md §3 workhorse; PZ §2).**

A cube chain in `K` is the same data as a *bi-pointed* map out of the
corresponding serial wedge,
`φ : □^∨(n₁,…,n_l) ⟶ K`
(recall bi-pointed maps preserve `init` and `final`).  The map `φ` corresponding
to a chain `C = (c₁,…,c_l)` is determined by sending the top cell `u_{nᵢ}` of the
`i`-th block to `cᵢ` (`φ(u_{nᵢ}) = cᵢ`); the junction vertices then go to
`C.vtx`.

We bundle the dimension sequence on both sides: the right-hand `Σ` of bi-pointed
wedge maps is precisely the underlying data of `ChainCat.Obj K` (`Chains/Category.lean`).

* Forward (`φ ↦ C`): read off `cᵢ := φ(u_{nᵢ})` (evaluate at the block top cells)
  and the junction vertices; the chain conditions follow because `φ` commutes
  with faces and preserves `init`/`final`.
* Inverse (`C ↦ φ`): the universal property of the wedge (a pushout) glues the
  block maps `canonicalMap cᵢ : □^{nᵢ} ⟶ K`, agreeing at the junctions.

**Statement only — proof intended for the project owner.** -/

/-- `□⁰` has only the identity endomorphism (it is the representable point). -/
instance stdPre0_subsingleton : Subsingleton (StdCube.stdPre 0 ⟶ StdCube.stdPre 0) := by
  constructor; intro f g; apply PrecubicalConstructions.hom_ext; intro n
  match n with
  | 0     => intro c; apply Subtype.ext; funext i; exact i.elim0
  | (k+1) => intro c; exact absurd c.2 (by simp [StdCube.noneSet])

instance : Subsingleton ((BPSet.cube 0).toPsh.cells 0) := stdPre0_subsingleton

theorem wedge2_init' (X Y : BPSet) :
    (BPSet.wedge2 X Y).init =
      (pushout.inl (BPSet.vertexMap _ X.final) (BPSet.vertexMap _ Y.init)).app _ X.init := rfl

theorem wedge2_final' (X Y : BPSet) :
    (BPSet.wedge2 X Y).final =
      (pushout.inr (BPSet.vertexMap _ X.final) (BPSet.vertexMap _ Y.init)).app _ Y.final := rfl

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
          simp only [yonedaEquiv_comp, BPSet.vertexMap, Equiv.apply_symm_apply]
          rw [r.init_spec]; rfl)
        init_spec := by
          simp only [List.map_cons, BPSet.serialWedge_cons, wedge2_init']
          rw [← h.1]
          change (pushout.inl _ _ ≫ pushout.desc (yonedaEquiv.symm c) r.map _).app _
              ((BPSet.cube n).init) = _
          rw [pushout.inl_desc]; rfl
        final_spec := by
          simp only [List.map_cons, BPSet.serialWedge_cons, wedge2_final']
          change (pushout.inr _ _ ≫ pushout.desc (yonedaEquiv.symm c) r.map _).app _
              ((BPSet.serialWedge (rest.map (·.1))).final) = _
          rw [pushout.inr_desc]
          exact r.final_spec }

def wedgeDescHom {K : BPSet} cubes
  (desc : WedgeDesc K.init K.final cubes) :
  (BPSet.serialWedge (List.map (fun x ↦ x.fst) cubes) ⟶ K) where
    hom := desc.map
    app_init := desc.init_spec
    app_final := desc.final_spec

noncomputable def wedgeToCubes : (dims : List ℕ+) × ((BPSet.serialWedge dims).toPsh ⟶ K.toPsh) →
  List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))
  | ⟨ [], _ ⟩ => []
  | ⟨ x :: rest, hom⟩ =>
    ⟨x, yonedaEquiv (pushout.inl _ _ ≫ hom)⟩
     :: wedgeToCubes ⟨rest, pushout.inr _ _ ≫ hom⟩

/-! ### Reading a wedge map back off as a chain (the inverse direction).

The key fact is `wedgeToCubes_isCubeChain`: the cubes read off a wedge map
`φ : □^∨(dims) ⟶ K` form an `IsCubeChain` from `φ(init)` to `φ(final)`.  This
carries *all* the Yoneda/pushout content in a single induction.  The remaining
work — turning that folded `IsCubeChain` into the junction-vertex `CubeChain`
fields — is pure list/`Fin` bookkeeping (`isCubeChain_link_nat`,
`isCubeChain_last`, `isCubeChain_vtx_zero`, `isCubeChain_vtx_tgt`) with no wedges
in sight. -/

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
    (pushout.inl (BPSet.vertexMap X.toPsh X.final) (BPSet.vertexMap Y.toPsh Y.init)).app
        (op (Box.ob 0)) X.final
      = (pushout.inr (BPSet.vertexMap X.toPsh X.final) (BPSet.vertexMap Y.toPsh Y.init)).app
        (op (Box.ob 0)) Y.init := by
  have h := pushout.condition (f := BPSet.vertexMap X.toPsh X.final)
    (g := BPSet.vertexMap Y.toPsh Y.init)
  simp only [BPSet.vertexMap, yonedaEquiv_symm_naturality_right] at h
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

/-- The link condition, extracted from a folded `IsCubeChain` (pure list/`Fin`
bookkeeping; recursion on the cube list). -/
theorem isCubeChain_link_nat :
    ∀ (a b : K.toPsh.cells 0) (cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ)))
      (_ : IsCubeChain a cubes b) (i : ℕ) (hi : i + 1 < cubes.length),
      K.toPsh.vertex₁ (cubes.get ⟨i, Nat.lt_of_succ_lt hi⟩).2 =
      K.toPsh.vertex₀ (cubes.get ⟨i + 1, hi⟩).2
  | _, _, [], _, _, hi => by simp at hi
  | _, _, ⟨_, _⟩ :: [], _, 0, hi => by simp at hi
  | _, _, ⟨_, _⟩ :: ⟨_, _⟩ :: _, h, 0, _ => (h.2.1).symm
  | _, _, ⟨_, c⟩ :: tl, h, i + 1, hi =>
      isCubeChain_link_nat (K.toPsh.vertex₁ c) _ tl h.2 i
        (by simp only [List.length_cons] at hi; omega)

/-- The last cube of a chain ends at the chain's final vertex. -/
theorem isCubeChain_last :
    ∀ (a b : K.toPsh.cells 0) (cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ)))
      (_ : IsCubeChain a cubes b) (i : ℕ) (hi : i < cubes.length) (_ : i + 1 = cubes.length),
      K.toPsh.vertex₁ (cubes.get ⟨i, hi⟩).2 = b
  | _, _, [], _, _, hi, _ => by simp at hi
  | _, _, ⟨_, _⟩ :: [], h, 0, _, _ => h.2
  | _, _, ⟨_, _⟩ :: ⟨_, _⟩ :: _, _, 0, _, hlast => by simp only [List.length_cons] at hlast; omega
  | _, _, ⟨_, c⟩ :: tl, h, i + 1, hi, hlast =>
      isCubeChain_last (K.toPsh.vertex₁ c) _ tl h.2 i
        (by simp only [List.length_cons] at hi; omega)
        (by simp only [List.length_cons] at hlast; omega)

/-- The junction-vertex `vtx 0 = init` condition, derived from a folded
`IsCubeChain` (the chain's junction vertices are read off as `vertex₀` of each
cube, with the final junction being `b`). -/
theorem isCubeChain_vtx_zero (a b : K.toPsh.cells 0)
    (cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))) (h : IsCubeChain a cubes b) :
    Fin.lastCases b (fun j => K.toPsh.vertex₀ (cubes.get j).2)
      (0 : Fin (cubes.length + 1)) = a := by
  cases cubes with
  | nil =>
      simp only [List.length_nil]
      rw [show (0 : Fin (0 + 1)) = Fin.last 0 from by apply Fin.ext; simp, Fin.lastCases_last]
      exact h.symm
  | cons hd tl =>
      obtain ⟨n, c⟩ := hd
      simp only [List.length_cons]
      rw [show (0 : Fin (tl.length + 1 + 1)) = Fin.castSucc 0 from by apply Fin.ext; simp,
          Fin.lastCases_castSucc]
      exact h.1

/-- The junction-vertex `cube_tgt` condition: the `i`-th cube's target is the
`(i+1)`-th junction.  Splits (via `Fin.lastCases` on `i`) into the last-cube case
(`isCubeChain_last`) and the link case (`isCubeChain_link_nat`). -/
theorem isCubeChain_vtx_tgt (a b : K.toPsh.cells 0)
    (cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))) (h : IsCubeChain a cubes b) :
    ∀ i : Fin cubes.length,
      K.toPsh.vertex₁ (cubes.get i).2 =
        Fin.lastCases b (fun j => K.toPsh.vertex₀ (cubes.get j).2) i.succ := by
  cases cubes with
  | nil => exact fun i => i.elim0
  | cons hd tl =>
      intro i
      induction i using Fin.lastCases with
      | last =>
          simp only [List.length_cons, Fin.succ_last, Fin.lastCases_last]
          have hlen : tl.length < (hd :: tl).length := by simp
          have e : (Fin.last tl.length : Fin (hd :: tl).length) = ⟨tl.length, hlen⟩ := by
            apply Fin.ext; simp
          rw [e]
          exact isCubeChain_last a b (hd :: tl) h tl.length hlen (by simp)
      | cast j =>
          simp only [List.length_cons, Fin.succ_castSucc, Fin.lastCases_castSucc]
          have hlt : j.val + 1 < (hd :: tl).length := by
            have := j.isLt; simp only [List.length_cons]; omega
          have e1 : (Fin.castSucc j : Fin (hd :: tl).length)
              = ⟨j.val, Nat.lt_of_succ_lt hlt⟩ := by apply Fin.ext; simp
          have e2 : (Fin.succ j : Fin (hd :: tl).length) = ⟨j.val + 1, hlt⟩ := by
            apply Fin.ext; simp
          rw [e1, e2]
          exact isCubeChain_link_nat a b (hd :: tl) h j.val hlt

/-- `vtx 0 = K.init` for the chain read off a *bi-pointed* wedge map. -/
theorem wtc_vtx_zero (dims : List ℕ+) (ψ : BPSet.serialWedge dims ⟶ K) :
    Fin.lastCases K.final
        (fun j => K.toPsh.vertex₀ ((wedgeToCubes ⟨dims, ψ.hom⟩).get j).2)
        (0 : Fin ((wedgeToCubes ⟨dims, ψ.hom⟩).length + 1)) = K.init := by
  have hchain := wedgeToCubes_isCubeChain dims ψ.hom
  rw [ψ.app_init, ψ.app_final] at hchain
  exact isCubeChain_vtx_zero K.init K.final _ hchain

/-- `cube_tgt` for the chain read off a bi-pointed wedge map. -/
theorem wtc_cube_tgt (dims : List ℕ+) (ψ : BPSet.serialWedge dims ⟶ K) :
    ∀ i : Fin (wedgeToCubes ⟨dims, ψ.hom⟩).length,
      K.toPsh.vertex₁ ((wedgeToCubes ⟨dims, ψ.hom⟩).get i).2 =
        Fin.lastCases K.final
          (fun j => K.toPsh.vertex₀ ((wedgeToCubes ⟨dims, ψ.hom⟩).get j).2) i.succ := by
  have hchain := wedgeToCubes_isCubeChain dims ψ.hom
  rw [ψ.app_init, ψ.app_final] at hchain
  exact isCubeChain_vtx_tgt K.init K.final _ hchain

/-- **The map↔chain correspondence (ClaudeSetup.md §3).**  Cube chains in `K` are
exactly bi-pointed maps out of a serial wedge.  Forward: bundle the descent map
(`wedgeDescHom`).  Inverse: read the cubes off (`wedgeToCubes`) with the junction
vertices being their source extremal vertices.  The round-trip laws are left
open (`sorry`). -/
noncomputable def equivWedgeHom (K : BPSet) :
    CubeChain K ≃ Σ dims : List ℕ+, (BPSet.serialWedge dims ⟶ K) where
  toFun C := ⟨C.dims, wedgeDescHom _ (wedgeDesc _ _ _ (isCubeChain C))⟩
  invFun := fun ⟨dims, ψ⟩ =>
    { cubes := wedgeToCubes ⟨dims, ψ.hom⟩
      vtx := fun i => Fin.lastCases K.final
        (fun j => K.toPsh.vertex₀ ((wedgeToCubes ⟨dims, ψ.hom⟩).get j).2) i
      vtx_zero := wtc_vtx_zero dims ψ
      vtx_last := by simp
      cube_src := by intro i; simp
      cube_tgt := wtc_cube_tgt dims ψ }
  left_inv C := sorry
  right_inv φ := sorry


end CubeChain
