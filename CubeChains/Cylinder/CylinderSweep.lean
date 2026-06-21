import CubeChains.Cylinder.CylinderRefineCore

/-!
# Cylinder/CylinderSweep

The total multi-block sweep `sweepR` (a list-indexed fence-staircase).
This builds the cylinder's homotopy `sweepR` on an arbitrary source chain, on top of the geometry
core (`CylinderRefineCore`).

The junction-bridge staircase lifts blocks `k → 1` through prism-cube cospans, sharing each
junction edge `eᵢ` between the two bridges touching `sᵢ`.  It is packaged as:

* `BlockRec`/`BlockConsec` — a block of the source chain bundled with all its endpoint data, and
  the block-list consistency predicate;
* `leftPush`/`rightPush`/`tailTarget`/`apexHead` and the staircase arrows (`topArrow`/`botArrow*`/
  `topCofaceFirst`) — the per-block prism-lift pieces, whiskered by fixed prefix/suffix;
* `sweepTail`/`sweepFirst` — the prefix-carrying list recursion that runs the staircase;
* `blocksOf`/`blockConsec_blocksOf` and the source/target identifications
  (`leftPush_blocksOf`/`rightPush_blocksOf`), assembling the total homotopy
  `sweepR c a : (pushforwardBP leftLeg).obj a ⟶ (pushforwardBP rightLeg).obj a` in `DPathGrpdR K`.

See `CylinderRefine.lean` for the deliverable `cylToPointedR` built on `sweepR`.

**Layer:** Cylinder.  **Imports:** `Cylinder/CylinderRefineCore`.
-/

open CategoryTheory Opposite
open Operations
open CubeChain

variable {K : BPSet}

/-! ## 8.5. The total multi-block sweep `sweepR` (list-indexed staircase)

The junction-bridge staircase lifts blocks `k → 1` through apexes/bridges.  The **total** `sweepR`
runs that staircase for an arbitrary source chain, indexed by the block list.  To keep every
staircase object inside the *global* fence `RefineObj K.init K.final` we package each block with
*all* of its endpoint data into a `BlockRec`, and recurse on the **suffix** of blocks while
carrying a fixed left prefix `pre : RefineObj K.init mL` (the already-fixed left faces) and the
vertical edge over the split junction.

The recursion `sweepTail` produces, for a fixed prefix `pre` ending at the split junction's
*left* leg-image `mL` and a list of remaining blocks (a `c.src`-chain from the split junction to
`final`):

    pre.append (leftPush blocks)  ⟶  pre.append (edge.append (rightPush blocks))

i.e. it sweeps the *tail* across the interval, leaving the prefix on the left leg and inserting
the split-junction vertical `edge : mL → mR` to bridge the level gap.  At the top level the
prefix is empty (`pre = ε·`, mL = init) and the edge is the *initial* self-loop, which collapses,
so the result is the genuine `ℓ·a ⟶ r·a`.  Each recursion step lifts the *first* remaining block
through its prism cospan, exactly mirroring §8's interior arrows. -/

namespace CylMapR

open CubeChain

/-- A **block record**: one block of the source chain together with every endpoint condition the
staircase needs — the block cell `cell`, its left/right leg-image junction vertices `uL/vL`
(`false`-face) and `uR/vR` (`true`-face), the initial/final source junction 0-cells `s₀/s₁`
(`vertex₀/₁ cell`), and the leg-face / prism / edge endpoint equalities.  Bundling these makes the
recursion's transport bookkeeping a matter of *projecting* fields rather than re-deriving vertex
equalities. -/
structure BlockRec (c : CylMapR K) where
  /-- The block dimension. -/
  m : ℕ+
  /-- The source cube cell of this block. -/
  cell : c.src.toPsh.cells (m : ℕ)
  /-- Left leg-image of the block's *initial* junction (`vertex₀` of the `false`-face). -/
  uL : K.toPsh.cells 0
  /-- Left leg-image of the block's *final* junction (`vertex₁` of the `false`-face). -/
  vL : K.toPsh.cells 0
  /-- Right leg-image of the block's *initial* junction. -/
  uR : K.toPsh.cells 0
  /-- Right leg-image of the block's *final* junction. -/
  vR : K.toPsh.cells 0
  /-- The block's initial source junction 0-cell. -/
  s₀ : c.src.toPsh.cells 0
  /-- The block's final source junction 0-cell. -/
  s₁ : c.src.toPsh.cells 0
  hs₀ : c.src.toPsh.vertex₀ cell = s₀
  hs₁ : c.src.toPsh.vertex₁ cell = s₁
  /-- `lc`: left face initial vertex. -/
  hiL : K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh)) = uL
  /-- `lc`: left face final vertex. -/
  hfL : K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh)) = vL
  /-- `rc`: right face initial vertex. -/
  hiR : K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh)) = uR
  /-- `rc`: right face final vertex. -/
  hfR : K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh)) = vR

namespace BlockRec

variable {c : CylMapR K}

/-- The `false`-leg face of a block, as a single-cube chain `uL → vL`. -/
noncomputable def lc (B : BlockRec c) : RefineObj (K := K) B.uL B.vL :=
  refineEndG false (c.blockQ B.cell) B.hiL B.hfL

/-- The `true`-leg face of a block, as a single-cube chain `uR → vR`. -/
noncomputable def rc (B : BlockRec c) : RefineObj (K := K) B.uR B.vR :=
  refineEndG true (c.blockQ B.cell) B.hiR B.hfR

/-- The prism cube of a block, as a single-cube chain `uL → vR`. -/
noncomputable def R (B : BlockRec c) : RefineObj (K := K) B.uL B.vR :=
  refinePrismG (c.blockQ B.cell) B.hiL B.hfR

end BlockRec

end CylMapR

/-! ## 8.6. The total list-indexed sweep `sweepTail`/`sweepR`

The junction-bridge staircase is run for an arbitrary block list `bs : List (BlockRec c)` in a
**prefix-carrying** recursion `sweepTail`, living in the *sub-fence*
`RefineObj mL K.final` (from the split junction's left leg-image `mL` to `final`).  For a non-empty
list it produces

    leftPush mL bs  ⟶  edge.append (rightPush mR bs)

where `leftPush`/`rightPush` are the right-fold appends of the blocks' `lc`/`rc` faces (starting at
`mL`/`mR`), and `edge : mL → mR` is the vertical junction edge over the split junction's source
0-cell.  At the cons step the *first* block is lifted through its prism cospan (the two §8 bridge
cofaces, whiskered by an `rc`-suffix), and the tail is recursed and re-whiskered by the
`lc`-prefix via `FreeGroupoid.map (RefineObj.appendLeft _)` (`of_comp_map` makes this a per-arrow
whisker).  Every object identity in the recursion is `RefineObj.ext''` (cube lists agree by
`List.append_assoc` / singleton `++`), promoted to an `eqToHom`. -/

namespace CylMapR

open CubeChain

variable {c : CylMapR K}

/-- **Block-list consistency**: the blocks `bs` form a genuine source chain starting at the split
junction whose two leg-images are `mL` (left) and `mR` (right), and whose final block closes at
`K.final` on both legs.  Recursively: the head block `B` has `B.uL = mL`, `B.uR = mR`; the next
block's initial junction equals `B`'s final (`B.s₁ = next.s₀`) and its leg-images match
(`B.vL = next.uL`, `B.vR = next.uR`); the last block has `B.vL = B.vR = K.final`. -/
def BlockConsec : (bs : List (BlockRec c)) → (mL mR : K.toPsh.cells 0) → Prop
  | [], mL, mR => mL = K.final ∧ mR = K.final
  | B :: rest, mL, mR =>
      B.uL = mL ∧ B.uR = mR ∧
      -- the vertical edge over the head's initial junction `s₀` runs `mL → mR`
      K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = mL ∧
      K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = mR ∧
      (match rest with
       | [] => B.vL = K.final ∧ B.vR = K.final
       | B' :: _ => B.vL = B'.uL ∧ B.vR = B'.uR ∧ B.s₁ = B'.s₀) ∧
      BlockConsec rest B.vL B.vR

/-- The right-fold of the blocks' `false`-leg (`lc`) faces into one chain `mL → K.final`.  The
start vertex is kept *explicit* (as `mL`, tied to `B.uL` by consistency) so the cube list comes
out free of `▸`-transport — `leftPush_cubes` reads it off as a plain `List.map`. -/
noncomputable def leftPush (bs : List (BlockRec c)) (mL mR : K.toPsh.cells 0)
    (h : BlockConsec bs mL mR) : RefineObj (K := K) mL K.final where
  cubes := bs.map (fun B => ⟨B.m, yonedaEquiv (c.blockQ B.cell ≫ (endpoint false).app K.toPsh)⟩)
  isChain := by
    induction bs generalizing mL mR with
    | nil => obtain ⟨rfl, _⟩ := h; rfl
    | cons B rest ih =>
        obtain ⟨huL, _, _, _, _, hrec⟩ := h
        refine ⟨by rw [B.hiL, huL], ?_⟩
        have hlink : K.toPsh.vertex₁ (yonedaEquiv (c.blockQ B.cell ≫ (endpoint false).app K.toPsh))
            = B.vL := B.hfL
        rw [hlink]; exact ih B.vL B.vR hrec

/-- The right-fold of the blocks' `true`-leg (`rc`) faces into one chain `mR → K.final`. -/
noncomputable def rightPush (bs : List (BlockRec c)) (mL mR : K.toPsh.cells 0)
    (h : BlockConsec bs mL mR) : RefineObj (K := K) mR K.final where
  cubes := bs.map (fun B => ⟨B.m, yonedaEquiv (c.blockQ B.cell ≫ (endpoint true).app K.toPsh)⟩)
  isChain := by
    induction bs generalizing mL mR with
    | nil => obtain ⟨_, rfl⟩ := h; rfl
    | cons B rest ih =>
        obtain ⟨_, huR, _, _, _, hrec⟩ := h
        refine ⟨by rw [B.hiR, huR], ?_⟩
        have hlink : K.toPsh.vertex₁ (yonedaEquiv (c.blockQ B.cell ≫ (endpoint true).app K.toPsh))
            = B.vR := B.hfR
        rw [hlink]; exact ih B.vL B.vR hrec

/-- The cubes of `leftPush` are exactly the `List.map` of the blocks' `lc` cells (definitional). -/
@[simp] theorem leftPush_cubes (bs : List (BlockRec c)) (mL mR : K.toPsh.cells 0)
    (h : BlockConsec bs mL mR) :
    (leftPush bs mL mR h).cubes
      = bs.map (fun B => (⟨B.m, yonedaEquiv (c.blockQ B.cell ≫ (endpoint false).app K.toPsh)⟩ :
          Σ n : ℕ+, K.toPsh.cells (n : ℕ))) := rfl

/-- The cubes of `rightPush` are exactly the `List.map` of the blocks' `rc` cells (definitional). -/
@[simp] theorem rightPush_cubes (bs : List (BlockRec c)) (mL mR : K.toPsh.cells 0)
    (h : BlockConsec bs mL mR) :
    (rightPush bs mL mR h).cubes
      = bs.map (fun B => (⟨B.m, yonedaEquiv (c.blockQ B.cell ≫ (endpoint true).app K.toPsh)⟩ :
          Σ n : ℕ+, K.toPsh.cells (n : ℕ))) := rfl

/-! ### The cons decompositions and the staircase target

`leftPush (B::rest)` splits as `B.lc.append (leftPush rest)` and `rightPush (B::rest)` as
`B.rc.append (rightPush rest)`, both as on-the-nose `RefineObj` equalities (`ext''`, the cube lists
agree by `List.map_cons`).  These are the recursion's object identities. -/

/-- `leftPush (B::rest) = B.lc.append (leftPush rest)` (the head `lc` prepended). -/
theorem leftPush_cons (B : BlockRec c) (rest : List (BlockRec c)) (mL mR : K.toPsh.cells 0)
    (h : BlockConsec (B :: rest) mL mR) (huL : B.uL = mL) (hrec : BlockConsec rest B.vL B.vR) :
    leftPush (B :: rest) mL mR h
      = huL ▸ (B.lc.append (leftPush rest B.vL B.vR hrec)) := by
  apply RefineObj.ext''
  cases huL
  simp only [leftPush_cubes, List.map_cons, RefineObj.append_cubes, BlockRec.lc, refineEndG,
    leftPush_cubes, List.singleton_append]

/-- `rightPush (B::rest) = B.rc.append (rightPush rest)` (the head `rc` prepended). -/
theorem rightPush_cons (B : BlockRec c) (rest : List (BlockRec c)) (mL mR : K.toPsh.cells 0)
    (h : BlockConsec (B :: rest) mL mR) (huR : B.uR = mR) (hrec : BlockConsec rest B.vL B.vR) :
    rightPush (B :: rest) mL mR h
      = huR ▸ (B.rc.append (rightPush rest B.vL B.vR hrec)) := by
  apply RefineObj.ext''
  cases huR
  simp only [rightPush_cubes, List.map_cons, RefineObj.append_cubes, BlockRec.rc, refineEndG,
    rightPush_cubes, List.singleton_append]

/-- The **vertical junction edge over a block's initial junction**, as a chain `mL → mR`, when
its endpoints are the split junction's two leg-images (`BlockConsec`'s edge fields). -/
noncomputable def BlockRec.edge0 (B : BlockRec c) {mL mR : K.toPsh.cells 0}
    (hEi : K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = mL)
    (hEf : K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = mR) :
    RefineObj (K := K) mL mR :=
  refineEdgeG c B.s₀ hEi hEf

/-- **The staircase target of `sweepTail`.**  For a non-empty list it is the split-junction
vertical edge `mL → mR` followed by the right-leg push of the blocks (`mR → final`), i.e.
`edge.append (rightPush bs)`; for the empty list it is just `rightPush []` (the empty chain at
`final`).  This is the right-hand object of the sub-fence homotopy. -/
noncomputable def tailTarget : (bs : List (BlockRec c)) → (mL mR : K.toPsh.cells 0) →
    BlockConsec bs mL mR → RefineObj (K := K) mL K.final
  | [], mL, _, h => ⟨[], by obtain ⟨rfl, _⟩ := h; rfl⟩
  | B :: rest, mL, mR, h =>
      (B.edge0 h.2.2.1 h.2.2.2.1).append (rightPush (B :: rest) mL mR h)

/-! ### The apex and the two arrows into it (per-block prism lift, list-generic)

For the head block `B` lifted over its prism cube, the apex is `B.R.append (rightPush rest)` (the
prism cube of `B`, with the right-leg push of the remaining blocks suffixed).  The two staircase
arrows into the apex are the §8 bridge cofaces whiskered by the fixed `rightPush rest` suffix
(`ChainRefine.append · (𝟙 _)`):

* the **top/bridge arrow** `tailTarget (B::rest) → apex`, from the `[e,rc]` bridge
  `refineBridgeCoface` over `B`'s *initial* junction `s₀`;
* the **bottom/mirror arrow** `B.lc.append (tailTarget rest) → apex`, from the `[lc,e]` mirror
  bridge `refineBridgeCofaceR` over `B`'s *final* junction `s₁` (when `rest ≠ []`) or the single
  bottom coface `refineCofaceG false` (when `rest = []`, `B` the last block — final edge absent). -/

/-- The apex object for lifting the head block `B`: its prism cube suffixed by the remaining
blocks' right-leg push. -/
noncomputable def apexHead (B : BlockRec c) (rest : List (BlockRec c))
    {mL mR : K.toPsh.cells 0} (h : BlockConsec (B :: rest) mL mR) :
    RefineObj (K := K) mL K.final :=
  h.1 ▸ B.R.append (rightPush rest B.vL B.vR h.2.2.2.2.2)

/-- **The top/bridge arrow into the apex** (substituted form `mL = B.uL`, `mR = B.uR`): the
`[e,rc]` bridge coface over `B`'s *initial* junction `s₀`, whiskered by the `rightPush rest`
suffix.  Source `refineBridgeSrc c B.cell B.s₀ ≫ suffix`, target `B.R ≫ suffix = apex`. -/
noncomputable def topArrow (B : BlockRec c) (rest : List (BlockRec c))
    (hEi : K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = B.uL)
    (hEf : K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = B.uR)
    (hrec : BlockConsec rest B.vL B.vR) :
    (refineBridgeSrc c B.cell B.s₀ hEi (B.hiR.trans hEf.symm) B.hfR).append
        (rightPush rest B.vL B.vR hrec)
      ⟶ B.R.append (rightPush rest B.vL B.vR hrec) :=
  ChainRefine.append
    (refineBridgeCoface c B.cell B.s₀ B.hs₀ hEi (B.hiR.trans hEf.symm) B.hfR B.hiL B.hfR)
    (𝟙 (rightPush rest B.vL B.vR hrec))

/-- The edge-over-`B.s₁` initial-vertex equality, extracted from the *next* block's
`BlockConsec` edge field (over `B'.s₀ = B.s₁`).  Only `rest = B' :: _`. -/
theorem next_edge_init (B B' : BlockRec c) (tl : List (BlockRec c))
    (hmatch : B.vL = B'.uL ∧ B.vR = B'.uR ∧ B.s₁ = B'.s₀)
    (hrec : BlockConsec (B' :: tl) B.vL B.vR) :
    K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₁))) = B.vL := by
  rw [hmatch.2.2]; exact hrec.2.2.1

/-- The edge-over-`B.s₁` final-vertex equality (dual of `next_edge_init`). -/
theorem next_edge_final (B B' : BlockRec c) (tl : List (BlockRec c))
    (hmatch : B.vL = B'.uL ∧ B.vR = B'.uR ∧ B.s₁ = B'.s₀)
    (hrec : BlockConsec (B' :: tl) B.vL B.vR) :
    K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₁))) = B.vR := by
  rw [hmatch.2.2]; exact hrec.2.2.2.1

/-- **The bottom/mirror arrow into the apex** (interior case `rest = B' :: tl`): the `[lc,e]`
mirror-bridge coface over `B`'s *final* junction `s₁`, whiskered by the `rightPush rest` suffix.
Source `refineBridgeSrcR c B.cell B.s₁ ≫ suffix`, target `B.R ≫ suffix = apex`. -/
noncomputable def botArrowCons (B B' : BlockRec c) (tl : List (BlockRec c))
    (hmatch : B.vL = B'.uL ∧ B.vR = B'.uR ∧ B.s₁ = B'.s₀)
    (hrec : BlockConsec (B' :: tl) B.vL B.vR) :
    (refineBridgeSrcR c B.cell B.s₁ B.hiL
        ((next_edge_init B B' tl hmatch hrec).trans B.hfL.symm)
        (next_edge_final B B' tl hmatch hrec)).append (rightPush (B' :: tl) B.vL B.vR hrec)
      ⟶ B.R.append (rightPush (B' :: tl) B.vL B.vR hrec) :=
  ChainRefine.append
    (refineBridgeCofaceR c B.cell B.s₁ B.hs₁ B.hiL
      ((next_edge_init B B' tl hmatch hrec).trans B.hfL.symm)
      (next_edge_final B B' tl hmatch hrec) B.hiL B.hfR)
    (𝟙 (rightPush (B' :: tl) B.vL B.vR hrec))

/-- **The bottom arrow into the apex** (terminal case `rest = []`, `B` the last block): the single
bottom coface `B.lc → B.R` (the final junction's edge is absent).  Here `B.vL = B.vR = K.final`,
so `B.lc` and `B.R` both close at `final`; the arrow is `refineCofaceG false`. -/
noncomputable def botArrowNil (B : BlockRec c) (hvL : B.vL = K.final) (hvR : B.vR = K.final) :
    (refineEndG false (c.blockQ B.cell) B.hiL (B.hfL.trans (hvL.trans hvR.symm)))
      ⟶ (refinePrismG (c.blockQ B.cell) B.hiL B.hfR) :=
  refineCofaceG false (c.blockQ B.cell) B.hiL (B.hfL.trans (hvL.trans hvR.symm)) B.hiL B.hfR

/-! ### The cons-step head sweep `headSweep`

Given the head block `B`, the apex `B.R.append (rightPush rest)`, and the recursive tail homotopy
`tail : leftPush rest ⟶ tailTarget rest`, produce the head's contribution to the staircase:

    leftPush (B::rest)  ⟶  tailTarget (B::rest)

namely `eqToHom ≫ (lift of tail by appendLeft B.lc) ≫ eqToHom ≫ of(botArrow) ≫ inv(of(topArrow)) ≫
eqToHom`.  The object `eqToHom`s are `RefineObj.ext''` cube-list identities (append-assoc / the two
bridge presentations / the `leftPush`/`rightPush` cons splits). -/

/-- The two object-bridge equalities the cons step needs, branch `rest = B' :: tl`. -/
theorem midEq_cons (B B' : BlockRec c) (tl : List (BlockRec c))
    (hmatch : B.vL = B'.uL ∧ B.vR = B'.uR ∧ B.s₁ = B'.s₀)
    (hrec : BlockConsec (B' :: tl) B.vL B.vR) :
    B.lc.append (tailTarget (B' :: tl) B.vL B.vR hrec)
      = (refineBridgeSrcR c B.cell B.s₁ B.hiL
          ((next_edge_init B B' tl hmatch hrec).trans B.hfL.symm)
          (next_edge_final B B' tl hmatch hrec)).append (rightPush (B' :: tl) B.vL B.vR hrec) := by
  apply RefineObj.ext''
  simp only [RefineObj.append_cubes, tailTarget, BlockRec.lc, BlockRec.edge0, refineEndG,
    refineEdgeG, refineBridgeSrcR, rightPush_cubes, List.cons_append, List.nil_append]
  rw [hmatch.2.2]

/-- The top-source object bridge (substituted form `mL = B.uL`, `mR = B.uR`): `tailTarget (B::rest)`
equals the `[e,rc]` bridge over `B.s₀` suffixed by `rightPush rest`.  Uses `rightPush_cons` + the
bridge presentation (`ext''`). -/
theorem tgtEq_cons (B : BlockRec c) (rest : List (BlockRec c))
    (h : BlockConsec (B :: rest) B.uL B.uR)
    (hEi : K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = B.uL)
    (hEf : K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = B.uR)
    (hrec : BlockConsec rest B.vL B.vR) :
    tailTarget (B :: rest) B.uL B.uR h
      = (refineBridgeSrc c B.cell B.s₀ hEi (B.hiR.trans hEf.symm) B.hfR).append
          (rightPush rest B.vL B.vR hrec) := by
  apply RefineObj.ext''
  simp only [tailTarget, BlockRec.edge0, refineEdgeG, refineBridgeSrc,
    RefineObj.append_cubes, rightPush_cubes, List.map_cons, List.cons_append, List.nil_append]

/-- The source object bridge: `leftPush (B::rest)` (substituted) equals `B.lc.append (leftPush
rest)`.  Specialisation of `leftPush_cons` with `huL = rfl`. -/
theorem srcEq_cons (B : BlockRec c) (rest : List (BlockRec c))
    (h : BlockConsec (B :: rest) B.uL B.uR) (hrec : BlockConsec rest B.vL B.vR) :
    leftPush (B :: rest) B.uL B.uR h = B.lc.append (leftPush rest B.vL B.vR hrec) :=
  leftPush_cons B rest B.uL B.uR h rfl hrec

/-- The bottom-source object bridge, branch `rest = []`: `B.lc.append (tailTarget [])` equals the
`false`-face single-cube chain suffixed by the empty `rightPush`. -/
theorem midEq_nil (B : BlockRec c) (hvL : B.vL = K.final) (hvR : B.vR = K.final)
    (hrec : BlockConsec ([] : List (BlockRec c)) B.vL B.vR) :
    B.lc.append (tailTarget [] B.vL B.vR hrec)
      = (refineEndG false (c.blockQ B.cell) B.hiL (B.hfL.trans (hvL.trans hvR.symm))).append
          (rightPush [] B.vL B.vR hrec) := by
  apply RefineObj.ext''
  simp only [RefineObj.append_cubes, tailTarget, BlockRec.lc, refineEndG, rightPush_cubes,
    List.map_nil, List.append_nil]

/-! ### The total tail sweep `sweepTail`

By structural recursion on `bs`.  Cons (`B :: rest`): substitute `mL := B.uL`, `mR := B.uR`, lift
`sweepTail rest` by `FreeGroupoid.map (RefineObj.appendLeft B.lc)`, then splice the head block's
prism cospan via the mirror (`botArrow*`) and top (`topArrow`) arrows.  Object identities are the
`eqToHom`s of `srcEq_cons`/`midEq_*`/`tgtEq_cons` (FreeGroupoid objects are `RefineObj`s, so a
`RefineObj` equality is directly an `eqToHom`). -/
noncomputable def sweepTail : (bs : List (BlockRec c)) → (mL mR : K.toPsh.cells 0) →
    (h : BlockConsec bs mL mR) →
    (FreeGroupoid.of (RefineObj (K := K) mL K.final)).obj (leftPush bs mL mR h)
      ⟶ (FreeGroupoid.of (RefineObj (K := K) mL K.final)).obj (tailTarget bs mL mR h)
  | [], mL, mR, h =>
      eqToHom (congrArg _ (RefineObj.ext'' (by
        simp only [leftPush_cubes, tailTarget, List.map_nil])))
  | B :: rest, mL, mR, h => by
      obtain ⟨huL, huR, hEi, hEf, hmatch, hrec⟩ := h
      subst huL; subst huR
      have hcons : BlockConsec (B :: rest) B.uL B.uR := ⟨rfl, rfl, hEi, hEf, hmatch, hrec⟩
      -- the recursive tail homotopy, lifted by the `lc`-prefix whiskering.  The codomain
      -- `(map (appendLeft B.lc)).obj (tailTarget rest) = B.lc.append (tailTarget rest)` by
      -- `of_comp_map` (rfl); the type ascription forces that defeq at definition time.
      let lifted : (FreeGroupoid.of _).obj (B.lc.append (leftPush rest B.vL B.vR hrec))
          ⟶ (FreeGroupoid.of _).obj (B.lc.append (tailTarget rest B.vL B.vR hrec)) :=
        (FreeGroupoid.map (RefineObj.appendLeft (b := K.final) B.lc)).map
          (sweepTail rest B.vL B.vR hrec)
      -- the top arrow into the apex (always the `[e,rc]` bridge over `s₀`), inverted
      let top := (FreeGroupoid.of _).map (topArrow B rest hEi hEf hrec)
      refine eqToHom (congrArg (FreeGroupoid.of _).obj (srcEq_cons B rest hcons hrec))
        ≫ lifted
        ≫ ?mid ≫ Groupoid.inv top
        ≫ eqToHom (congrArg (FreeGroupoid.of _).obj (tgtEq_cons B rest hcons hEi hEf hrec).symm)
      -- the mirror arrow `B.lc.append (tailTarget rest) → apex`, split on `rest`:
      match rest, hmatch, hrec with
      | [], hmatch, hrec =>
          exact eqToHom (congrArg (FreeGroupoid.of _).obj (midEq_nil B hmatch.1 hmatch.2 hrec))
            ≫ (FreeGroupoid.of _).map
              (ChainRefine.append (botArrowNil B hmatch.1 hmatch.2)
                (𝟙 (rightPush [] B.vL B.vR hrec)))
      | B' :: tl, hmatch, hrec =>
          exact eqToHom (congrArg (FreeGroupoid.of _).obj (midEq_cons B B' tl hmatch hrec))
            ≫ (FreeGroupoid.of _).map (botArrowCons B B' tl hmatch hrec)

/-! ### Decomposing a source chain into `BlockRec`s

A single cube `⟨m, cell⟩` of the source chain `a` gives a `BlockRec` whose four leg-image junction
vertices are *defined* to be the `vertex₀/₁` of the two leg-faces, so all four leg-vertex equalities
are `rfl`.  The list of all cubes of `a` gives `blocksOf a`, and the chain's link/endpoint data
makes it `BlockConsec` over the basepoints. -/

/-- The `BlockRec` of a single source cube `⟨m, cell⟩` (m : ℕ+), with every endpoint *defined* as
the corresponding vertex (so all field equalities are `rfl`). -/
noncomputable def BlockRec.ofCube (c : CylMapR K) (m : ℕ+) (cell : c.src.toPsh.cells (m : ℕ)) :
    BlockRec c where
  m := m
  cell := cell
  uL := K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh))
  vL := K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh))
  uR := K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
  vR := K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
  s₀ := c.src.toPsh.vertex₀ cell
  s₁ := c.src.toPsh.vertex₁ cell
  hs₀ := rfl
  hs₁ := rfl
  hiL := rfl
  hfL := rfl
  hiR := rfl
  hfR := rfl

/-- The **block-list decomposition** of a source chain `a`: each cube becomes a `BlockRec.ofCube`.
This is the list the total sweep is indexed by; `leftPush`/`rightPush` of it recover the two
leg-pushforwards of `a` (`blockQ_face` cube-wise), and (given `BlockConsec`) `sweepTail` sweeps it.
-/
noncomputable def blocksOf (c : CylMapR K)
    (a : RefineObj (K := c.src) c.src.init c.src.final) : List (BlockRec c) :=
  a.cubes.map (fun cb => BlockRec.ofCube c cb.1 cb.2)

/-- The `false`-leg block-face vertices are the *left leg* applied to the source cube's vertices:
`vertex₀(blockQ cell ≫ e_false) = leftLeg.app (vertex₀ cell)` (via `blockQ_face` + naturality).  The
`uL` of `BlockRec.ofCube` therefore equals `leftLeg.app (vertex₀ cell)`. -/
theorem ofCube_uL_eq (c : CylMapR K) {m : ℕ} (cell : c.src.toPsh.cells m) :
    K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh))
      = c.leftLeg.hom.app (op (Box.ob 0)) (c.src.toPsh.vertex₀ cell) :=
  (congrArg K.toPsh.vertex₀ (blockQ_face c cell false)).trans
    (PrecubicalSet.map_vertex₀ c.leftLeg.hom cell).symm

/-- `vertex₁(blockQ cell ≫ e_false) = leftLeg.app (vertex₁ cell)`. -/
theorem ofCube_vL_eq (c : CylMapR K) {m : ℕ} (cell : c.src.toPsh.cells m) :
    K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh))
      = c.leftLeg.hom.app (op (Box.ob 0)) (c.src.toPsh.vertex₁ cell) :=
  (congrArg K.toPsh.vertex₁ (blockQ_face c cell false)).trans
    (PrecubicalSet.map_vertex₁ c.leftLeg.hom cell).symm

/-- `vertex₀(blockQ cell ≫ e_true) = rightLeg.app (vertex₀ cell)`. -/
theorem ofCube_uR_eq (c : CylMapR K) {m : ℕ} (cell : c.src.toPsh.cells m) :
    K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
      = c.rightLeg.hom.app (op (Box.ob 0)) (c.src.toPsh.vertex₀ cell) :=
  (congrArg K.toPsh.vertex₀ (blockQ_face c cell true)).trans
    (PrecubicalSet.map_vertex₀ c.rightLeg.hom cell).symm

/-- `vertex₁(blockQ cell ≫ e_true) = rightLeg.app (vertex₁ cell)`. -/
theorem ofCube_vR_eq (c : CylMapR K) {m : ℕ} (cell : c.src.toPsh.cells m) :
    K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
      = c.rightLeg.hom.app (op (Box.ob 0)) (c.src.toPsh.vertex₁ cell) :=
  (congrArg K.toPsh.vertex₁ (blockQ_face c cell true)).trans
    (PrecubicalSet.map_vertex₁ c.rightLeg.hom cell).symm

/-- `initVertexMap 0 = 𝟙 (Box.ob 0)`: the unique `0`-cell of `□⁰` is its top cell, so the
constant-vertex `canonicalMap` is `canonicalMap (topCell 0) = 𝟙`. -/
theorem initVertexMap_zero : PrecubicalSet.initVertexMap 0 = 𝟙 (Box.ob 0) := by
  rw [PrecubicalSet.initVertexMap,
    show StdCube.constVertex 0 false = StdCube.topCell 0 from
      Subtype.ext (funext (fun i => i.elim0))]
  exact StdCube.canonicalMap_topCell 0

/-- `finalVertexMap 0 = 𝟙 (Box.ob 0)` (dual of `initVertexMap_zero`). -/
theorem finalVertexMap_zero : PrecubicalSet.finalVertexMap 0 = 𝟙 (Box.ob 0) := by
  rw [PrecubicalSet.finalVertexMap,
    show StdCube.constVertex 0 true = StdCube.topCell 0 from
      Subtype.ext (funext (fun i => i.elim0))]
  exact StdCube.canonicalMap_topCell 0

/-- `vertex₀` of a 0-cell is itself (`initVertexMap 0 = 𝟙`). -/
theorem vertex₀_zero_cell {X : PrecubicalSet} (v : X.cells 0) : X.vertex₀ v = v := by
  rw [PrecubicalSet.vertex₀, initVertexMap_zero, op_id, X.map_id_apply]

/-- `vertex₁` of a 0-cell is itself. -/
theorem vertex₁_zero_cell {X : PrecubicalSet} (v : X.cells 0) : X.vertex₁ v = v := by
  rw [PrecubicalSet.vertex₁, finalVertexMap_zero, op_id, X.map_id_apply]

/-- The vertical edge over a source 0-cell `v` runs `leftLeg.app v → rightLeg.app v`
(`prism_vertex₀/₁` + the leg-face reconciliation; `v` a 0-cell so its own `vertex₀/₁` is itself). -/
theorem edge_over_vertex_init (c : CylMapR K) (v : c.src.toPsh.cells 0) :
    K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ v)))
      = c.leftLeg.hom.app (op (Box.ob 0)) v :=
  (prism_vertex₀ (c.blockQ v)).trans
    ((ofCube_uL_eq c v).trans (congrArg _ (vertex₀_zero_cell v)))

theorem edge_over_vertex_final (c : CylMapR K) (v : c.src.toPsh.cells 0) :
    K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ v)))
      = c.rightLeg.hom.app (op (Box.ob 0)) v :=
  (prism_vertex₁ (c.blockQ v)).trans
    ((ofCube_vR_eq c v).trans (congrArg _ (vertex₁_zero_cell v)))

/-- **The block-list of a source chain is `BlockConsec`.**  Over the leg-images of the chain's
start vertex `start`, the `ofCube` blocks of a cube list `cs` forming a chain `start → final`
satisfy `BlockConsec` — every link/edge field is the chain link `vertex₁ cube = vertex₀ next`
pushed through the leg (`ofCube_*_eq` + `map_vertex*_psh` + `edge_over_vertex_*`). -/
theorem blockConsec_blocksOf_aux (c : CylMapR K) :
    ∀ (cs : List (Σ n : ℕ+, c.src.toPsh.cells (n : ℕ))) (start : c.src.toPsh.cells 0)
      (_hchain : IsCubeChain start cs c.src.final),
      BlockConsec (cs.map (fun cb => BlockRec.ofCube c cb.1 cb.2))
        (c.leftLeg.hom.app (op (Box.ob 0)) start) (c.rightLeg.hom.app (op (Box.ob 0)) start)
  | [], start, hchain => by
      -- empty chain: `start = final`, and `leg.app final = K.basepoint`.
      obtain rfl : start = c.src.final := hchain
      exact ⟨c.leftLeg.app_final, c.rightLeg.app_final⟩
  | ⟨m, cell⟩ :: rest, start, hchain => by
      obtain ⟨hsrc, hrest⟩ := hchain
      -- `hsrc : vertex₀ cell = start`, `hrest : IsCubeChain (vertex₁ cell) rest final`.
      have hIH := blockConsec_blocksOf_aux c rest (c.src.toPsh.vertex₁ cell) hrest
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- B.uL = leftLeg.app start
        rw [show (BlockRec.ofCube c m cell).uL
              = K.toPsh.vertex₀ (yonedaEquiv
                  (c.blockQ cell ≫ (endpoint false).app K.toPsh)) from rfl,
          ofCube_uL_eq, hsrc]
      · rw [show (BlockRec.ofCube c m cell).uR
              = K.toPsh.vertex₀ (yonedaEquiv
                  (c.blockQ cell ≫ (endpoint true).app K.toPsh)) from rfl,
          ofCube_uR_eq, hsrc]
      · -- edge over s₀ = vertex₀ cell, init = leftLeg.app start
        rw [show (BlockRec.ofCube c m cell).s₀ = c.src.toPsh.vertex₀ cell from rfl,
          edge_over_vertex_init, hsrc]
      · rw [show (BlockRec.ofCube c m cell).s₀ = c.src.toPsh.vertex₀ cell from rfl,
          edge_over_vertex_final, hsrc]
      · -- the link match, depending on `rest`
        cases rest with
        | nil =>
            refine ⟨?_, ?_⟩
            · -- B.vL = K.final : leftLeg.app (vertex₁ cell), and vertex₁ cell = final
              rw [show (BlockRec.ofCube c m cell).vL
                    = K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh))
                  from rfl, ofCube_vL_eq, (hrest : c.src.toPsh.vertex₁ cell = c.src.final),
                c.leftLeg.app_final]
            · rw [show (BlockRec.ofCube c m cell).vR
                    = K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
                  from rfl, ofCube_vR_eq, (hrest : c.src.toPsh.vertex₁ cell = c.src.final),
                c.rightLeg.app_final]
        | cons hd tl =>
            obtain ⟨n', cell'⟩ := hd
            obtain ⟨hlink, _⟩ := hrest
            -- hlink : vertex₀ cell' = vertex₁ cell
            refine ⟨?_, ?_, ?_⟩
            · rw [show (BlockRec.ofCube c m cell).vL
                    = K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh))
                  from rfl,
                show (BlockRec.ofCube c n' cell').uL
                    = K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell' ≫ (endpoint false).app K.toPsh))
                  from rfl, ofCube_vL_eq, ofCube_uL_eq, hlink]
            · rw [show (BlockRec.ofCube c m cell).vR
                    = K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
                  from rfl,
                show (BlockRec.ofCube c n' cell').uR
                    = K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell' ≫ (endpoint true).app K.toPsh))
                  from rfl, ofCube_vR_eq, ofCube_uR_eq, hlink]
            · -- B.s₁ = B'.s₀ : vertex₁ cell = vertex₀ cell'
              change c.src.toPsh.vertex₁ cell = c.src.toPsh.vertex₀ cell'
              exact hlink.symm
      · -- recursive `BlockConsec rest (leftLeg.app (vertex₁ cell)) (rightLeg.app (vertex₁ cell))`
        -- but the running endpoints must be `B.vL`/`B.vR`; they reduce to the leg-images.
        rw [show (BlockRec.ofCube c m cell).vL
              = K.toPsh.vertex₁ (yonedaEquiv
                  (c.blockQ cell ≫ (endpoint false).app K.toPsh)) from rfl,
          show (BlockRec.ofCube c m cell).vR
              = K.toPsh.vertex₁ (yonedaEquiv
                  (c.blockQ cell ≫ (endpoint true).app K.toPsh)) from rfl,
          ofCube_vL_eq, ofCube_vR_eq]
        exact hIH

/-- The `BlockConsec` of `blocksOf c a` over the basepoints (`leg.app init = K.init` by
`app_init`). -/
theorem blockConsec_blocksOf (c : CylMapR K)
    (a : RefineObj (K := c.src) c.src.init c.src.final) :
    BlockConsec (blocksOf c a) K.init K.init := by
  have h := blockConsec_blocksOf_aux c a.cubes c.src.init a.isChain
  rw [c.leftLeg.app_init, c.rightLeg.app_init] at h
  exact h

/-- **Source identification.**  `leftPush (blocksOf c a)` is exactly the left-leg pushforward
`(pushforwardBP c.leftLeg).obj a`: cube-wise, `yonedaEquiv (blockQ cell ≫ e_false) = leftLeg.app
cell` (`blockQ_face`), so the two `List.map`s coincide. -/
theorem leftPush_blocksOf (c : CylMapR K)
    (a : RefineObj (K := c.src) c.src.init c.src.final) :
    leftPush (blocksOf c a) K.init K.init (blockConsec_blocksOf c a)
      = (Refine.pushforwardBP c.leftLeg).obj a := by
  apply RefineObj.ext''
  rw [leftPush_cubes, Refine.pushforwardBP_obj_cubes, blocksOf, List.map_map]
  apply List.map_congr_left
  intro cb _
  simp only [Function.comp_apply, BlockRec.ofCube, mapCubeHom]
  exact congrArg (fun z => (⟨cb.1, z⟩ : Σ n : ℕ+, K.toPsh.cells (n : ℕ)))
    (blockQ_face c cb.2 false)

/-- **Right-source identification.**  `rightPush (blocksOf c a)` is the right-leg pushforward
`(pushforwardBP c.rightLeg).obj a`. -/
theorem rightPush_blocksOf (c : CylMapR K)
    (a : RefineObj (K := c.src) c.src.init c.src.final) :
    rightPush (blocksOf c a) K.init K.init (blockConsec_blocksOf c a)
      = (Refine.pushforwardBP c.rightLeg).obj a := by
  apply RefineObj.ext''
  rw [rightPush_cubes, Refine.pushforwardBP_obj_cubes, blocksOf, List.map_map]
  apply List.map_congr_left
  intro cb _
  simp only [Function.comp_apply, BlockRec.ofCube, mapCubeHom]
  exact congrArg (fun z => (⟨cb.1, z⟩ : Σ n : ℕ+, K.toPsh.cells (n : ℕ)))
    (blockQ_face c cb.2 true)

/-! ### The top-level sweep `sweepFirst`

The whole-chain sweep lifts the *first* block with a single **top coface** `refineCofaceG true`
(not a bridge): at the basepoint the two leg-images agree (`B.uL = B.uR = K.init`), so there is no
initial vertical edge to bridge — exactly §8's `α₃`.  Hence `sweepFirst` targets `rightPush bs`
directly (no init edge), and the rest of the staircase is `sweepTail rest`.  This is the entry
point the total `sweepR` wraps. -/

/-- The **top single-coface arrow** for the first block (`B.uL = B.uR`): `B.rc → B.R`, whiskered by
the `rightPush rest` suffix.  Source `refineEndG true ≫ suffix`, target `B.R ≫ suffix = apex`. -/
noncomputable def topCofaceFirst (B : BlockRec c) (rest : List (BlockRec c))
    (huLR : B.uL = B.uR) (hrec : BlockConsec rest B.vL B.vR) :
    (refineEndG true (c.blockQ B.cell) (B.hiR.trans huLR.symm) B.hfR).append
        (rightPush rest B.vL B.vR hrec)
      ⟶ B.R.append (rightPush rest B.vL B.vR hrec) :=
  ChainRefine.append
    (refineCofaceG true (c.blockQ B.cell) (B.hiR.trans huLR.symm) B.hfR B.hiL B.hfR)
    (𝟙 (rightPush rest B.vL B.vR hrec))

/-- The right-target object bridge for `sweepFirst`: `rightPush (B::rest)` (started at `B.uL`,
both leg-images agreeing) equals the `true`-face single-cube chain suffixed by `rightPush rest`
(the `refineEndG true` source of `topCofaceFirst`). -/
theorem tgtEqFirst (B : BlockRec c) (rest : List (BlockRec c)) (huLR : B.uL = B.uR)
    (h : BlockConsec (B :: rest) B.uL B.uL) (hrec : BlockConsec rest B.vL B.vR) :
    rightPush (B :: rest) B.uL B.uL h
      = (refineEndG true (c.blockQ B.cell) (B.hiR.trans huLR.symm) B.hfR).append
          (rightPush rest B.vL B.vR hrec) := by
  apply RefineObj.ext''
  simp only [rightPush_cubes, refineEndG, RefineObj.append_cubes, List.map_cons,
    List.singleton_append]

/-- **The top-level whole-chain sweep** `leftPush bs ⟶ rightPush bs` in the global fence
`RefineObj mL final`, for a block list whose first block's two leg-images agree (`mL = mR`, the
basepoint).  Lifts the first block by a top single coface, then runs `sweepTail` on the rest. -/
noncomputable def sweepFirst : (bs : List (BlockRec c)) → (mL : K.toPsh.cells 0) →
    (h : BlockConsec bs mL mL) →
    (FreeGroupoid.of (RefineObj (K := K) mL K.final)).obj (leftPush bs mL mL h)
      ⟶ (FreeGroupoid.of (RefineObj (K := K) mL K.final)).obj (rightPush bs mL mL h)
  | [], mL, h =>
      eqToHom (congrArg _ (RefineObj.ext'' (by
        simp only [leftPush_cubes, rightPush_cubes, List.map_nil])))
  | B :: rest, mL, h => by
      obtain ⟨huL, huR, hEi, hEf, hmatch, hrec⟩ := h
      subst huL
      have huLR : B.uL = B.uR := huR.symm
      have hcons : BlockConsec (B :: rest) B.uL B.uL := ⟨rfl, huR, hEi, hEf, hmatch, hrec⟩
      let lifted : (FreeGroupoid.of _).obj (B.lc.append (leftPush rest B.vL B.vR hrec))
          ⟶ (FreeGroupoid.of _).obj (B.lc.append (tailTarget rest B.vL B.vR hrec)) :=
        (FreeGroupoid.map (RefineObj.appendLeft (b := K.final) B.lc)).map
          (sweepTail rest B.vL B.vR hrec)
      let topc := (FreeGroupoid.of _).map (topCofaceFirst B rest huLR hrec)
      refine eqToHom (congrArg (FreeGroupoid.of _).obj
          (leftPush_cons B rest B.uL B.uL hcons rfl hrec))
        ≫ lifted
        ≫ ?mid ≫ Groupoid.inv topc
        ≫ eqToHom (congrArg (FreeGroupoid.of _).obj (tgtEqFirst B rest huLR hcons hrec).symm)
      match rest, hmatch, hrec with
      | [], hmatch, hrec =>
          exact eqToHom (congrArg (FreeGroupoid.of _).obj (midEq_nil B hmatch.1 hmatch.2 hrec))
            ≫ (FreeGroupoid.of _).map
              (ChainRefine.append (botArrowNil B hmatch.1 hmatch.2)
                (𝟙 (rightPush [] B.vL B.vR hrec)))
      | B' :: tl, hmatch, hrec =>
          exact eqToHom (congrArg (FreeGroupoid.of _).obj (midEq_cons B B' tl hmatch hrec))
            ≫ (FreeGroupoid.of _).map (botArrowCons B B' tl hmatch hrec)

/-! ### Piece 4b — the TOTAL sweep `sweepR`

For an arbitrary source chain `a : RefineObj c.src.init c.src.final`, `sweepR c a` is the homotopy
`(pushforwardBP leftLeg).obj a ⟶ (pushforwardBP rightLeg).obj a` in `DPathGrpdR K`.  It is
`sweepFirst (blocksOf c a)` (the whole-chain staircase) re-based across the two source/target
identifications `leftPush_blocksOf`/`rightPush_blocksOf` (the leg-pushforward equals the
`lc`/`rc`-push of the block decomposition, cube-wise by `blockQ_face`). -/

/-- **The total multi-block sweep** `sweepR c a : (pushforwardBP leftLeg).obj a ⟶
(pushforwardBP rightLeg).obj a` in `DPathGrpdR K` — the cylinder's homotopy on an arbitrary source
chain, the list-indexed junction-bridge staircase of §8.6. -/
noncomputable def sweepR (c : CylMapR K) (a : RefineObj (K := c.src) c.src.init c.src.final) :
    (FreeGroupoid.of (RefineObj (K := K) K.init K.final)).obj
        ((Refine.pushforwardBP c.leftLeg).obj a)
      ⟶ (FreeGroupoid.of (RefineObj (K := K) K.init K.final)).obj
          ((Refine.pushforwardBP c.rightLeg).obj a) :=
  eqToHom (congrArg (FreeGroupoid.of _).obj (leftPush_blocksOf c a).symm)
    ≫ sweepFirst (blocksOf c a) K.init (blockConsec_blocksOf c a)
    ≫ eqToHom (congrArg (FreeGroupoid.of _).obj (rightPush_blocksOf c a))

end CylMapR
