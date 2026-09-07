import CubeChains.Precubical.Chains.Basic
import CubeChains.Precubical.Wedge.Wedge
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# Precubical/Chains/WedgeMap

Bi-pointed maps out of a serial wedge, `φ : ⋁d ⟶ K`, and the cube data such a map carries —
at the *given* shape `d` (`Beads K.toPsh d`), never a recomputed one.  Two constructions,
inverse to each other (`Precubical/Chains/Correspondence.lean`):

* `beadCell` (wedge map `→` beads): read off `cᵢ := yonedaEquiv (ιᵢ ≫ φ)` at each block.
* `wedgeDesc` (beads `→` wedge map): glue the Yoneda classifiers `yonedaEquiv.symm cᵢ`
  along the junctions, via `Glue.desc`.

Key structural facts: `beadCell_isCubeChain` (the read-off beads form a chain) and
`serialWedge_hom_ext` (the colimit universal property, via `Glue.hom_ext` and Yoneda),
whose bead form is `beadCell_inj`.  Plus the reusable serial-wedge cell
combinatorics (`serialWedge_block_unique`, `glue0_*`).
-/

open CategoryTheory CategoryTheory.Limits Opposite StdCube BPSet

namespace CubeChain

variable {K : BPSet}

/-! ### The wedge inclusions.  (`□⁰`'s rigidity is `BPSet.stdPre0_subsingleton`.) -/

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

/-! ### Beads of a wedge map

A map out of `⋁d` is its list of beads: bead `i` is the cell classifying the restriction
`ιᵂ d i ≫ φ`, and every bead is the image of the tautological one (`beadCell_eq_tautBead`), so
reading beads is post-composition. -/

/-- The tautological cell of bead `i` — the bead inclusion read as a cell of `⋁d`. -/
def tautBead (d : List ℕ+) (i : Fin d.length) : (⋁d).cells (d.get i : ℕ) := yonedaEquiv (ιᵂ d i)

/-- **The beads of a wedge map** — bead `i` is the cell classifying the block restriction
`ιᵂ d i ≫ φ`, so the shape `d` is carried, not recomputed. -/
def beadCell {X : PrecubicalSet} {d : List ℕ+} (φ : (⋁d).toPsh ⟶ X) : Beads X d :=
  fun i => yonedaEquiv (ιᵂ d i ≫ φ)

/-- **A bead is the image of the tautological bead.** -/
theorem beadCell_eq_tautBead {X : PrecubicalSet} {d : List ℕ+} (φ : (⋁d).toPsh ⟶ X)
    (i : Fin d.length) : beadCell φ i = φ⟪(d.get i : ℕ)⟫ (tautBead d i) :=
  yonedaEquiv_comp (ιᵂ d i) φ

@[simp] theorem beadCell_id (d : List ℕ+) (i : Fin d.length) :
    beadCell (𝟙 (⋁d).toPsh) i = tautBead d i := congrArg yonedaEquiv (Category.comp_id _)

/-- Reading a bead commutes with post-composition. -/
theorem beadCell_comp {X Y : PrecubicalSet} {d : List ℕ+} (φ : (⋁d).toPsh ⟶ X) (ψ : X ⟶ Y)
    (i : Fin d.length) : beadCell (φ ≫ ψ) i = ψ⟪(d.get i : ℕ)⟫ (beadCell φ i) :=
  congrArg yonedaEquiv (Category.assoc _ _ _).symm

/-- Reading beads commutes with post-composition — `beadCell_comp`, bundled. -/
theorem beadCell_push {X Y : PrecubicalSet} {d : List ℕ+} (φ : (⋁d).toPsh ⟶ X) (ψ : X ⟶ Y) :
    beadCell (φ ≫ ψ) = (beadCell φ).push ψ :=
  funext (beadCell_comp φ ψ)

/-- Bead `i+1` of `⋁(n :: rest)` is bead `i` of the tail — the recursion the wedge runs on. -/
theorem beadCell_succ {X : PrecubicalSet} {n : ℕ+} {rest : List ℕ+}
    (φ : (⋁(n :: rest)).toPsh ⟶ X) (i : Fin rest.length) :
    beadCell φ i.succ = beadCell (Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex ≫ φ) i :=
  congrArg yonedaEquiv (Category.assoc _ _ _)

/-- Bead `i+1` of `⋁(n :: rest)` reads the tail map — the recursion, packaged as `Beads.tail`. -/
theorem beadCell_tail {X : PrecubicalSet} {n : ℕ+} {rest : List ℕ+}
    (φ : (⋁(n :: rest)).toPsh ⟶ X) :
    (beadCell φ).tail = beadCell (Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex ≫ φ) :=
  funext (beadCell_succ φ)

/-- The wedge gluing identity: in `X ∨ Y`, the image of `X.final` under the left
inclusion equals the image of `Y.init` under the right inclusion.  This is just
`pushout.condition` pushed through Yoneda. -/
theorem wedge2_glue (X Y : BPSet) :
    (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ X.final
      = (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ Y.init := by
  have h := Glue.condition X.finalVertex Y.initVertex
  simp only [finalVertex, initVertex, vertexOf, vertexMap, PrecubicalSet.cubeMap,
    yonedaEquiv_symm_naturality_right] at h
  exact yonedaEquiv.symm.injective h

/-- **The beads of a wedge map form a cube chain.**  Recursion on the dimension sequence; the
head computation uses `vertexEnd_yonedaEquiv`, and the link uses `wedge2_glue`. -/
theorem beadCell_isCubeChain : ∀ (d : List ℕ+) (φ : (⋁d).toPsh ⟶ K.toPsh),
    IsCubeChain (φ⟪0⟫ (⋁d).init) (beadCell φ).toList (φ⟪0⟫ (⋁d).final)
  | [], φ => congrArg (φ⟪0⟫) (Subsingleton.elim ((□0).init) ((□0).final))
  | n :: rest, φ => by
      rw [Beads.toList_cons, beadCell_tail]
      refine ⟨?_, ?_⟩
      · -- `(⋁(n::rest)).init` is *defeq* to `inl (□n).init`, so the head computation
        -- closes definitionally after Yoneda naturality.
        exact PrecubicalSet.vertexEnd_yonedaEquiv false (Glue.inl _ _ ≫ φ)
      · -- the head cube's target vertex glues (via `wedge2_glue`) onto the right inclusion,
        -- which is exactly the recursive map `inr ≫ φ`.  The rewrite runs in the recursive
        -- hypothesis, not the goal: `(n :: rest).length` vs `rest.length + 1` makes the goal's
        -- `beadCell φ 0` a different *spelling*, which `kabstract` will not match.
        have e1 : K.toPsh.vertexEnd true (beadCell φ 0)
            = (Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex ≫ φ)⟪0⟫ (⋁rest).init :=
          (PrecubicalSet.vertexEnd_yonedaEquiv true (Glue.inl _ _ ≫ φ)).trans
            (congrArg (φ⟪0⟫) (wedge2_glue (□(n : ℕ)) (⋁rest)))
        have key := beadCell_isCubeChain rest
          (Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex ≫ φ)
        rw [← e1] at key
        exact key

/-! ### `wedgeDesc`: chain data to a wedge map. -/

/-- The inverse direction of the §3 correspondence (chain ↦ wedge map): the Yoneda
classifiers `yonedaEquiv.symm cᵢ` of the beads, glued along the junctions by
`Glue.desc` — the serial wedge's pushout universal property, applied recursively.

Re-pointing the target at `(a, b)` is what makes the recursion self-contained: the
`cons` step's cocone condition *is* the tail map's `app_init`, since
`(K.repoint (vertexEnd true c) b).init` is `vertexEnd true c` by `rfl`. -/
def wedgeDesc {K : BPSet} (a b : K.cells 0) {d : List ℕ+} (c : Beads K.toPsh d)
    (h : IsCubeChain a c.toList b) : (⋁d ⟶ K.repoint a b) :=
  match d, c, h with
  | [], _, h =>
      { hom := yonedaEquiv.symm a
        app_init := by
          change (yonedaEquiv.symm a)⟪0⟫ (□0).init = a
          rw [show (□0).init = 𝟙 ▫0 from Subsingleton.elim _ _]
          exact yonedaEquiv.apply_symm_apply a
        app_final := by
          change (yonedaEquiv.symm a)⟪0⟫ (□0).final = b
          rw [show (□0).final = 𝟙 ▫0 from Subsingleton.elim _ _]
          exact (yonedaEquiv.apply_symm_apply a).trans h }
  | _ :: _, c, h =>
      let r := wedgeDesc (K.toPsh.vertexEnd true (c 0)) b c.tail h.2
      { hom := Glue.desc (yonedaEquiv.symm (c 0)) r.hom (by
          apply yonedaEquiv.injective
          simp only [yonedaEquiv_comp, finalVertex, initVertex, vertexOf, vertexMap,
            PrecubicalSet.cubeMap, Equiv.apply_symm_apply]
          exact r.app_init.symm)
        app_init := (inl_desc_app _).trans h.1
        app_final := (inr_desc_app _).trans r.app_final }

/-- The descent map sends the wedge's initial vertex to the chain's start. -/
theorem wedgeDesc_init {K : BPSet} (a b : K.cells 0) {d : List ℕ+} (c : Beads K.toPsh d)
    (h : IsCubeChain a c.toList b) : (wedgeDesc a b c h).hom⟪0⟫ (⋁d).init = a :=
  (wedgeDesc a b c h).app_init

/-- The bi-pointed map `⋁d ⟶ K` of a chain: `wedgeDesc` at `K`'s own endpoints
(`K.repoint K.init K.final` is `K` by structure eta). -/
def wedgeDescHom {K : BPSet} {d : List ℕ+} (c : Beads K.toPsh d)
    (h : IsCubeChain K.init c.toList K.final) : (⋁d ⟶ K) :=
  wedgeDesc K.init K.final c h

/-- **Uniqueness for the serial wedge** (its colimit universal property, in the
clean `ι`-form): two maps out of `⋁dims` into *any* presheaf `Z` that agree on
every block (after the inclusions `serialWedge.ι`) and on the initial vertex are
equal.  The initial-vertex hypothesis is only needed for the empty wedge `□⁰`; for
nonempty `dims` it follows from the block agreement. -/
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

/-- The head block of the descent map is the Yoneda classifier of the head bead. -/
theorem inl_comp_wedgeDesc (a b : K.cells 0) {n : ℕ+} {rest : List ℕ+}
    (c : Beads K.toPsh (n :: rest)) (h : IsCubeChain a c.toList b) :
    Glue.inl (□(n : ℕ)).finalVertex (⋁rest).initVertex ≫ (wedgeDesc a b c h).hom
      = yonedaEquiv.symm (c 0) :=
  Glue.inl_desc _ _ _

/-- The tail of the descent map is the descent map of the tail chain. -/
theorem inr_comp_wedgeDesc (a b : K.cells 0) {n : ℕ+} {rest : List ℕ+}
    (c : Beads K.toPsh (n :: rest)) (h : IsCubeChain a c.toList b) :
    Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex ≫ (wedgeDesc a b c h).hom
      = (wedgeDesc (K.toPsh.vertexEnd true (c 0)) b c.tail h.2).hom :=
  Glue.inr_desc _ _ _

/-- Cell-level head rule: the descent map sends an `inl`-cell to the head bead's
Yoneda classifier. -/
theorem wedgeDesc_inl_app (a b : K.cells 0) {n : ℕ+} {rest : List ℕ+}
    (c : Beads K.toPsh (n :: rest)) (h : IsCubeChain a c.toList b) {m : ℕ}
    (x : (□(n : ℕ)).cells m) :
    (wedgeDesc a b c h).hom⟪m⟫
        ((Glue.inl (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫ x)
      = (yonedaEquiv.symm (c 0))⟪m⟫ x :=
  congrArg (fun f : (□(n : ℕ)).toPsh ⟶ K.toPsh => f⟪m⟫ x) (inl_comp_wedgeDesc a b c h)

/-- Cell-level tail rule: the descent map sends an `inr`-cell to the tail descent. -/
theorem wedgeDesc_inr_app (a b : K.cells 0) {n : ℕ+} {rest : List ℕ+}
    (c : Beads K.toPsh (n :: rest)) (h : IsCubeChain a c.toList b) {m : ℕ} (y : (⋁rest).cells m) :
    (wedgeDesc a b c h).hom⟪m⟫
        ((Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫ y)
      = (wedgeDesc (K.toPsh.vertexEnd true (c 0)) b c.tail h.2).hom⟪m⟫ y :=
  congrArg (fun f : (⋁rest).toPsh ⟶ K.toPsh => f⟪m⟫ y) (inr_comp_wedgeDesc a b c h)

/-- **Block-restriction rule for the descent map**: restricting `wedgeDesc` to bead `k`
(via `serialWedge.ι`) recovers that bead's Yoneda classifier.  Induction on the shape with
`Fin.cases` on `k`, mirroring the recursions of `serialWedge.ι` and `wedgeDesc`. -/
theorem ι_comp_wedgeDesc : ∀ (a b : K.cells 0) {d : List ℕ+} (c : Beads K.toPsh d)
    (h : IsCubeChain a c.toList b) (k : Fin d.length),
    ιᵂ d k ≫ (wedgeDesc a b c h).hom = yonedaEquiv.symm (c k)
  | a, b, _ :: _, c, h, k => by
      refine Fin.cases ?_ (fun k' => ?_) k
      · -- head block: `ι 0 = inl`, `inl ≫ wedgeDesc = yonedaEquiv.symm (c 0)`
        simpa only [BPSet.serialWedge.ι, Fin.cases_zero] using inl_comp_wedgeDesc a b c h
      · -- tail block: `ι (k'+1) = ι_rest k' ≫ inr`, recurse
        simp only [BPSet.serialWedge.ι, Fin.cases_succ, Category.assoc]
        exact (congrArg (ιᵂ _ k' ≫ ·) (inr_comp_wedgeDesc a b c h)).trans
          (ι_comp_wedgeDesc _ b c.tail h.2 k')

/-- `ι_comp_wedgeDesc` spelled through `wedgeDescHom`, so that the composite's middle
object reads `K.toPsh` rather than `(K.repoint K.init K.final).toPsh` (`rw` is syntactic). -/
theorem ι_comp_wedgeDescHom {d : List ℕ+} (c : Beads K.toPsh d)
    (h : IsCubeChain K.init c.toList K.final) (k : Fin d.length) :
    ιᵂ d k ≫ (wedgeDescHom c h).hom = yonedaEquiv.symm (c k) :=
  ι_comp_wedgeDesc K.init K.final c h k

/-- **Reading the beads back off the descent map recovers them** — the descent/read-off round
trip, on the nose and with no dimension transport. -/
@[simp] theorem beadCell_wedgeDesc (a b : K.cells 0) {d : List ℕ+} (c : Beads K.toPsh d)
    (h : IsCubeChain a c.toList b) : beadCell (wedgeDesc a b c h).hom = c :=
  funext fun k => (congrArg yonedaEquiv (ι_comp_wedgeDesc a b c h k)).trans
    (yonedaEquiv.apply_symm_apply (c k))

/-- `beadCell_wedgeDesc` spelled through `wedgeDescHom` (target `K`, not `K.repoint …`). -/
@[simp] theorem beadCell_wedgeDescHom {d : List ℕ+} (c : Beads K.toPsh d)
    (h : IsCubeChain K.init c.toList K.final) : beadCell (wedgeDescHom c h).hom = c :=
  beadCell_wedgeDesc K.init K.final c h

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

Stated for *arbitrary* vertex maps `f : □⁰ ⟶ A`, `g : □⁰ ⟶ B` (not just
`X.finalVertex`/`Y.initVertex`), since they touch only the underlying presheaves and the
emptiness of positive cells of `□⁰`; the wedge is the case `f := X.finalVertex`,
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

instance vertexOf_mono (X : BPSet) (ε : Bool) : Mono (X.vertexOf ε) := vertexMap_mono _

/-- Restated at the two named spellings: instance search does not unfold `initVertex`. -/
instance initVertex_mono (X : BPSet) : Mono X.initVertex := vertexOf_mono X false

instance finalVertex_mono (X : BPSet) : Mono X.finalVertex := vertexOf_mono X true

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

/-- **Every positive cell of a serial wedge lies in some block.**  By recursion on
`dims`: the empty wedge `□⁰` has no positive cells, and in `□^{n}∨ ⋁rest` a cell
is either in the head cube (block `0`) or in the tail (recurse). -/
theorem serialWedge_cell_exists : ∀ (dims : List ℕ+) {m : ℕ} (_hm : 1 ≤ m)
    (z : (⋁dims).cells m),
    ∃ (i : Fin dims.length) (x : (□((dims.get i) : ℕ)).cells m),
      (ιᵂ dims i)⟪m⟫ x = z
  | [], _, hm, z => ((cube0_cells_isEmpty hm).false z).elim
  | n :: rest, m, hm, z => by
      rcases glue0_cell_cases (□(n : ℕ)).finalVertex (⋁rest).initVertex m z with
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
      · rw [serialWedge_ι_zero]; exact glue0_inl_app_injective _ _
      · intro a b hab
        rw [serialWedge_ι_succ_app, serialWedge_ι_succ_app] at hab
        exact serialWedge_ι_app_injective rest j (glue0_inr_app_injective _ _ hab)

/-- **Blocks are unique**: a positive cell in block `i` and in block `i'` forces
`i = i'`.  Disjointness of distinct blocks comes from `glue0_inl_ne_inr` (head vs
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
          exact absurd (hx.trans hx'.symm) (glue0_inl_ne_inr _ _ hm _ _)
      · refine Fin.cases ?_ (fun j' => ?_) i'
        · intro hx hx'
          obtain ⟨x, hx⟩ := hx; obtain ⟨x', hx'⟩ := hx'
          rw [serialWedge_ι_succ_app] at hx
          rw [serialWedge_ι_zero_app] at hx'
          exact absurd (hx'.trans hx.symm) (glue0_inl_ne_inr _ _ hm _ _)
        · intro hx hx'
          obtain ⟨x, hx⟩ := hx; obtain ⟨x', hx'⟩ := hx'
          rw [serialWedge_ι_succ_app] at hx
          rw [serialWedge_ι_succ_app] at hx'
          have hinr := glue0_inr_app_injective (□(n : ℕ)).finalVertex (⋁rest).initVertex
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
  obtain ⟨r, x, hx⟩ := serialWedge_cell_exists bd (ad.get i).2 (beadCell φ i)
  refine ⟨r, x, ?_⟩
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  exact hx.symm

/-- **Wedge maps are determined by their beads**, together with their value on the initial
vertex (needed only for the empty wedge `□⁰`). -/
theorem beadCell_inj (d : List ℕ+) (f g : (⋁d).toPsh ⟶ K.toPsh)
    (hbeads : beadCell f = beadCell g)
    (hinit : f⟪0⟫ (⋁d).init = g⟪0⟫ (⋁d).init) : f = g :=
  serialWedge_hom_ext d f g (fun i => yonedaEquiv.injective (congrFun hbeads i)) hinit

end CubeChain
