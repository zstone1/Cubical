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
at the *given* shape `d` (`Beads K.toPsh d`), never a recomputed one.  `beadCell` reads off
`cᵢ := yonedaEquiv (ιᵢ ≫ φ)` at each block; `wedgeDesc` glues the Yoneda classifiers back along
the junctions via `Glue.desc`; they are mutually inverse.

The structural facts are `beadCell_isCubeChain` (the read-off beads form a chain) and
`serialWedge_hom_ext` (the colimit universal property), whose bead form is `beadCell_inj`.

Dually, a positive cell of `⋁d` lies in a unique block, computably: `serialWedgeCell` is a
retraction of the block inclusions, whence the block data `blockIdx`/`blockFace` of a wedge map.
-/

open CategoryTheory CategoryTheory.Limits Opposite StdCube BPSet

namespace CubeChain

variable {K : BPSet}

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
        app_init := (comp_app_cell (Glue.inl_desc _ _ _) 0 _).trans h.1
        app_final := (comp_app_cell (Glue.inr_desc _ _ _) 0 _).trans r.app_final }

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

/-! ### Cell-decomposition of a gluing at `□⁰`

Evaluation at level `m` preserves colimits, so the defining pushout square of `Glue.gluePsh` is a
pushout *in `Type`*; `□⁰` has no `m`-cells for `m ≥ 1`, so there the pushout is a disjoint union,
and at every level it is also a pullback (a map out of `□⁰` is injective).  That is "a positive
cell of the wedge lies in a unique block".

Stated for *arbitrary* vertex maps `f : □⁰ ⟶ A`, `g : □⁰ ⟶ B`: only the emptiness of positive
cells of `□⁰` is used, and the wedge is the case `f := X.finalVertex`, `g := Y.initVertex`. -/

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
  exact (BPSet.cube0_hom_subsingleton m).elim a b

/-! ### Lifting the decomposition to the serial wedge

A *positive-dimensional* cell of `⋁dims` lies in a **unique block**, as a face of that block's
cube: the block inclusions are injective with pairwise-disjoint images, since `□⁰` contributes no
positive cells. -/

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

/-- `□⁰` has no positive-dimensional cells: a box morphism only lowers dimension. -/
theorem cube0_cells_isEmpty {m : ℕ} (hm : 1 ≤ m) : IsEmpty ((□0).cells m) :=
  ⟨fun f => absurd (boxHom_dim_le f) (by omega)⟩

/-- **`□⁰` is a subsingleton at every level** — empty above dimension `0`, one vertex at it. -/
instance cube0_cells_subsingleton (m : ℕ) : Subsingleton ((□0).cells m) :=
  BPSet.cube0_hom_subsingleton m

/-- Any vertex map `□⁰ ⟶ Z` is injective **in every dimension**, covering both `X.finalVertex` and
`Y.initVertex`. -/
theorem vertexMap_app_injective {Z : PrecubicalSet}
    (f : yoneda.obj ▫0 ⟶ Z) {m : ℕ} :
    Function.Injective (f⟪m⟫) := fun a b _ => (cube0_cells_subsingleton m).elim a b

/-- A vertex map `□⁰ ⟶ X` is a monomorphism: its domain is a subsingleton at every level, so the
map is pointwise injective. -/
instance vertexMap_mono {X : BPSet} (c : X.cells 0) :
    Mono (yonedaEquiv.symm c : (□0).toPsh ⟶ X.toPsh) := by
  rw [NatTrans.mono_iff_mono_app]
  exact fun k => (mono_iff_injective _).mpr (vertexMap_app_injective _)

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

-- The block a positive cell of `⋁dims` lies in, together with the face of that block's cube it
-- is — read off the `Glue` `Quot`, hence computable.
unseal Glue.gluePsh Glue.inl Glue.inr in
def serialWedgeCell : (dims : List ℕ+) → {m : ℕ} → 1 ≤ m → (⋁dims).cells m →
    Σ i : Fin dims.length, (□((dims.get i) : ℕ)).cells m
  | [], _, hm, c => ((cube0_cells_isEmpty hm).false c).elim
  | _ :: rest, m, hm, c =>
      Quot.lift
        (fun x => match x with
          | Sum.inl a => ⟨0, a⟩
          | Sum.inr b => let r := serialWedgeCell rest hm b; ⟨r.1.succ, r.2⟩)
        (by intro _ _ r; obtain ⟨s⟩ := r
            exact ((cube0_cells_isEmpty hm).false s).elim)
        c

theorem serialWedgeCell_zero {n : ℕ+} {rest : List ℕ+} {m : ℕ} (hm : 1 ≤ m)
    (x : (□(n : ℕ)).cells m) :
    serialWedgeCell (n :: rest) hm
        ((Glue.inl (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫ x)
      = ⟨0, x⟩ := by
  show serialWedgeCell (n :: rest) hm ((Glue.inl _ _).app (op ▫m) x) = ⟨0, x⟩
  rw [Glue.inl_app]; rfl

theorem serialWedgeCell_succ {n : ℕ+} {rest : List ℕ+} {m : ℕ} (hm : 1 ≤ m)
    (y : (⋁rest).cells m) :
    serialWedgeCell (n :: rest) hm
        ((Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫ y)
      = ⟨(serialWedgeCell rest hm y).1.succ, (serialWedgeCell rest hm y).2⟩ := by
  show serialWedgeCell (n :: rest) hm ((Glue.inr _ _).app (op ▫m) y) = _
  rw [Glue.inr_app]; rfl

/-- **`serialWedgeCell` is a genuine decomposition**: the reported face of the reported block
recovers the cell. -/
theorem serialWedgeCell_spec :
    ∀ (dims : List ℕ+) {m : ℕ} (hm : 1 ≤ m) (c : (⋁dims).cells m),
      (ιᵂ dims (serialWedgeCell dims hm c).1)⟪m⟫ (serialWedgeCell dims hm c).2 = c
  | [], _, hm, c => ((cube0_cells_isEmpty hm).false c).elim
  | n :: rest, m, hm, c => by
      rcases glue0_cell_cases (□(n : ℕ)).finalVertex (⋁rest).initVertex m c with ⟨x, hx⟩ | ⟨y, hy⟩
      · rw [← hx, serialWedgeCell_zero]
        exact serialWedge_ι_zero_app n rest x
      · rw [← hy, serialWedgeCell_succ,
          serialWedge_ι_succ_app n rest (serialWedgeCell rest hm y).1
            (serialWedgeCell rest hm y).2]
        exact congrArg
          ((Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫)
          (serialWedgeCell_spec rest hm y)

/-- **`serialWedgeCell` inverts the block inclusions**, so the block a cell lies in is unique. -/
theorem serialWedgeCell_ι : ∀ (dims : List ℕ+) {m : ℕ} (hm : 1 ≤ m) (i : Fin dims.length)
    (x : (□((dims.get i) : ℕ)).cells m),
      serialWedgeCell dims hm ((ιᵂ dims i)⟪m⟫ x) = ⟨i, x⟩
  | [], _, _, i, _ => i.elim0
  | n :: rest, m, hm, i, x => by
      induction i using Fin.cases with
      | zero => rw [serialWedge_ι_zero_app, serialWedgeCell_zero]
      | succ j => rw [serialWedge_ι_succ_app, serialWedgeCell_succ, serialWedgeCell_ι rest hm j]

/-- **Every positive cell of a serial wedge lies in some block.** -/
theorem serialWedge_cell_exists (dims : List ℕ+) {m : ℕ} (hm : 1 ≤ m) (z : (⋁dims).cells m) :
    ∃ (i : Fin dims.length) (x : (□((dims.get i) : ℕ)).cells m),
      (ιᵂ dims i)⟪m⟫ x = z :=
  ⟨_, _, serialWedgeCell_spec dims hm z⟩

/-- **Blocks are unique**: a positive cell in block `i` and in block `i'` forces `i = i'` —
both readings are computed by the retraction `serialWedgeCell`. -/
theorem serialWedge_block_unique (dims : List ℕ+) {m : ℕ} (hm : 1 ≤ m)
    (i i' : Fin dims.length) (z : (⋁dims).cells m)
    (hx : ∃ x, (ιᵂ dims i)⟪m⟫ x = z) (hx' : ∃ x', (ιᵂ dims i')⟪m⟫ x' = z) : i = i' := by
  obtain ⟨x, hx⟩ := hx; obtain ⟨x', hx'⟩ := hx'
  refine congrArg Sigma.fst
    (?_ : (⟨i, x⟩ : Σ j : Fin dims.length, (□((dims.get j) : ℕ)).cells m) = ⟨i', x'⟩)
  rw [← serialWedgeCell_ι dims hm i x, ← serialWedgeCell_ι dims hm i' x', hx, hx']

/-! ### The block data of a wedge map

Bead `i` of `φ : ⋁ad ⟶ ⋁cd` is a `Box`-face of a single `cd`-bead: `blockIdx` names that bead and
`blockFace` the face, both computed by `serialWedgeCell`.  Where the block *sits* is a prefix-sum
fact and lives with the boundaries. -/

/-- The **target block index** of source bead `i` under a wedge map `φ`: the `cd`-block that the
restriction `ι_i ≫ φ` factors through. -/
def blockIdx {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    Fin cd.length :=
  (serialWedgeCell cd (ad.get i).pos (beadCell φ i)).1

/-- The **face inclusion** of source bead `i` under a wedge map `φ`: the `Box`
morphism `□^{ad.get i} ⟶ □^{cd.get (blockIdx φ i)}` witnessing that `ι_i ≫ φ` lands
in a face of the target block. -/
def blockFace {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    ▫((ad.get i) : ℕ) ⟶ ▫((cd.get (blockIdx φ i)) : ℕ) :=
  (serialWedgeCell cd (ad.get i).pos (beadCell φ i)).2

/-- Defining factorization of the block data (`r := blockIdx φ i`):

      □^{ad.get i}  --ι_i-->  □^∨(ad)
           |                     |
   blockFace φ i                 φ
           v                     v
      □^{cd.get r}  --ι_r-->  □^∨(cd)
-/
theorem blockFace_spec {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    ιᵂ ad i ≫ φ
      = yoneda.map (blockFace φ i) ≫ ιᵂ cd (blockIdx φ i) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  exact (serialWedgeCell_spec cd (ad.get i).pos (beadCell φ i)).symm

/-- …read on cells: **post-composition happens in the target bead.**  Bead `i` of `φ ≫ ψ` is
bead `blockIdx φ i` of `ψ`, restricted along the block face. -/
theorem beadCell_comp_block {ad cd : List ℕ+} {X : PrecubicalSet}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (ψ : (⋁cd).toPsh ⟶ X) (i : Fin ad.length) :
    beadCell (φ ≫ ψ) i = X.map (blockFace φ i).op (beadCell ψ (blockIdx φ i)) := by
  have h : ιᵂ ad i ≫ (φ ≫ ψ)
      = yoneda.map (blockFace φ i) ≫ (ιᵂ cd (blockIdx φ i) ≫ ψ) := by
    rw [← Category.assoc, blockFace_spec φ i]; exact Category.assoc _ _ _
  exact (congrArg yonedaEquiv h).trans
    (yonedaEquiv_naturality (ιᵂ cd (blockIdx φ i) ≫ ψ) (blockFace φ i)).symm

/-- …and at `ψ = 𝟙`: **a wedge map's bead is a face of the target bead it lands in.** -/
theorem blockFace_spec_cell {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    beadCell φ i = (⋁cd).toPsh.map (blockFace φ i).op (tautBead cd (blockIdx φ i)) := by
  simpa only [Category.comp_id, beadCell_id] using beadCell_comp_block φ (𝟙 _) i

/-- If `ι_i ≫ φ = g ≫ ι_r` for any face `g`, then `r = blockIdx φ i`. -/
theorem blockIdx_eq_of_factor {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length)
    (r : Fin cd.length) (g : ▫((ad.get i) : ℕ) ⟶ ▫((cd.get r) : ℕ))
    (h : ιᵂ ad i ≫ φ = yoneda.map g ≫ ιᵂ cd r) :
    r = blockIdx φ i := by
  have hc : beadCell φ i = (ιᵂ cd r)⟪((ad.get i : ℕ+) : ℕ)⟫ g := by
    have hy := congrArg yonedaEquiv h
    rwa [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at hy
  change r = (serialWedgeCell cd (ad.get i).pos (beadCell φ i)).1
  rw [hc, serialWedgeCell_ι]

/-- **Block-factoring of a wedge map**, with the block index forgotten — the decomposed form, so
that a caller who knows the block can `subst` it instead of transporting along it. -/
theorem wedgeMap_block {ad bd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁bd).toPsh) (i : Fin ad.length) :
    ∃ (r : Fin bd.length) (incl : ▫((ad.get i) : ℕ) ⟶ ▫((bd.get r) : ℕ)),
      ιᵂ ad i ≫ φ = yoneda.map incl ≫ ιᵂ bd r :=
  ⟨_, _, blockFace_spec φ i⟩

/-- **Wedge maps are determined by their beads**, together with their value on the initial
vertex (needed only for the empty wedge `□⁰`). -/
theorem beadCell_inj (d : List ℕ+) (f g : (⋁d).toPsh ⟶ K.toPsh)
    (hbeads : beadCell f = beadCell g)
    (hinit : f⟪0⟫ (⋁d).init = g⟪0⟫ (⋁d).init) : f = g :=
  serialWedge_hom_ext d f g (fun i => yonedaEquiv.injective (congrFun hbeads i)) hinit

end CubeChain
