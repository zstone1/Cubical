import CubeChains.Precubical.Segal.Segal
import CubeChains.Precubical.Segal.SegalAltitude
import CubeChains.Precubical.Basic.Altitude
import Mathlib.CategoryTheory.Products.Bifunctor
import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Precubical/Segal/Split — a chain through a wedge is a pair of chains

The one splitting mechanism in the tree.  Three layers:

* **`Split Z A B`** — "`Z` is `A ∨ B`" as data: at every *bead* level a cell of `Z` is a cell of
  `A` or of `B` (`side`, from `Glue.cellSide`: the pushout apex `□0` has no positive cells), and at
  level `0` the blocks meet exactly at the junction (`vertex_inter`).  `wedge2Split` is the wedge's.

* **`Split.chainSplit`** — the *order*: the `A`-beads all come first.  This is the only place
  altitude is used, and the only content `Split` cannot supply.

* **`Split.cubeListEquiv` / `chObjEquiv`** — the interface.
  `CubeChain Z ≃ CubeChain A × CubeChain B`,
  both round trips on the nose, conjugated through `chCubes` to `Ch Z ≃ Ch A × Ch B`.  `chConcat` is
  its inverse (`chConcat_obj_eq`), so both round trips are the equivalence's.
-/
open CategoryTheory CategoryTheory.Limits Opposite BPSet CubeChain

namespace Glue

variable {S A B : PrecubicalSet} (f : S ⟶ A) (g : S ⟶ B)

-- The computable `A`/`B` discriminator on a glued cell at an empty-apex level: the pushout
-- relation has no generators there, so the descent into `A ⊕ B` recovers the `Sum`.
def cellSide (o : Boxᵒᵖ) (he : IsEmpty (S.obj o)) : (gluePsh f g).obj o → A.obj o ⊕ B.obj o :=
  descCell o Sum.inl Sum.inr fun s => (he.false s).elim

theorem cellSide_inl (o : Boxᵒᵖ) (he : IsEmpty (S.obj o)) (x : A.obj o) :
    cellSide f g o he ((inl f g).app o x) = Sum.inl x := descCell_inl o x

theorem cellSide_inr (o : Boxᵒᵖ) (he : IsEmpty (S.obj o)) (y : B.obj o) :
    cellSide f g o he ((inr f g).app o y) = Sum.inr y := descCell_inr o y

unseal gluePsh inl inr in
theorem cellSide_elim (o : Boxᵒᵖ) (he : IsEmpty (S.obj o)) (z : (gluePsh f g).obj o) :
    Sum.elim (fun x => (inl f g).app o x) (fun y => (inr f g).app o y)
      (cellSide f g o he z) = z := by
  induction z using Quot.ind with
  | _ s => cases s <;> rfl

end Glue

namespace ChainCat

variable {Z Z' A B : BPSet}

/-! ## Blocks -/
/-- A **block** of `Z`: an inclusion of `A` with a computable partial inverse on positive cells.
`proj` is never asked about vertices — a wedge's two blocks share one. -/
structure Block (Z A : BPSet) where
  /-- The inclusion of the block. -/
  incl : A.toPsh ⟶ Z.toPsh
  /-- The partial inverse, on bead levels only. -/
  proj : ∀ m : ℕ, 1 ≤ m → Z.cells m → Option (A.cells m)
  /-- Projecting an included cell recovers it. -/
  sec : ∀ (m : ℕ) (hm : 1 ≤ m) (r : A.cells m), proj m hm (incl⟪m⟫ r) = some r

namespace Block

variable (P : Block Z A)

/-- A bead of the block, pushed into `Z`. -/
abbrev push : (Σ n : ℕ+, A.cells (n : ℕ)) → Σ n : ℕ+, Z.cells (n : ℕ) := cubePush P.incl

/-- The beads of a cube list of `Z` that lie in the block, in order; the rest are dropped. -/
def cubes (l : List (Σ n : ℕ+, Z.cells (n : ℕ))) : List (Σ n : ℕ+, A.cells (n : ℕ)) :=
  l.filterMap fun c => (P.proj c.1 c.1.pos c.2).map fun r => ⟨c.1, r⟩

@[simp] theorem cubes_nil : P.cubes [] = [] := rfl

theorem cubes_append (l₁ l₂ : List (Σ n : ℕ+, Z.cells (n : ℕ))) :
    P.cubes (l₁ ++ l₂) = P.cubes l₁ ++ P.cubes l₂ := List.filterMap_append

/-- **Reading one block's beads through another's projection.**  The projection's verdict on each
pushed bead is all that matters, so `cubes_map_push` and the two vanishing lemmas of a splitting
are the same induction. -/
theorem cubes_map_push_eq {B : BPSet} (Q : Block Z B)
    {r : ∀ n : ℕ+, B.cells (n : ℕ) → Option (A.cells (n : ℕ))}
    (h : ∀ (n : ℕ+) (y : B.cells (n : ℕ)), P.proj (n : ℕ) n.pos (Q.incl⟪(n : ℕ)⟫ y) = r n y)
    (l : List (Σ n : ℕ+, B.cells (n : ℕ))) :
    P.cubes (l.map Q.push) = l.filterMap fun c => (r c.1 c.2).map fun z => ⟨c.1, z⟩ := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    rw [List.map_cons, cubes, List.filterMap_cons, List.filterMap_cons]
    have hc : P.proj (Q.push c).1 (Q.push c).1.pos (Q.push c).2 = r c.1 c.2 := h c.1 c.2
    simp only [push] at hc ⊢
    rw [hc]
    cases r c.1 c.2 <;> simpa [cubes] using ih

/-- Reading back the beads one pushed in. -/
@[simp] theorem cubes_map_push (l : List (Σ n : ℕ+, A.cells (n : ℕ))) :
    P.cubes (l.map P.push) = l :=
  (P.cubes_map_push_eq P (fun n r => P.sec (n : ℕ) n.pos r) l).trans (by simp)

end Block

/-! ## Splittings -/

/-- **`Z` is the wedge of `A` and `B`**, as far as chains can see: at every *bead* level a cell of
`Z` is a cell of `A` or a cell of `B` (`side`), while at level `0` the two blocks meet exactly at
the junction (`vertex_inter`), which is `A`'s final vertex and `B`'s initial one.

This is the whole of what the pushout `X ∨ Y` contributes. -/
structure Split (Z A B : BPSet) where
  /-- Inclusion of the left block. -/
  inl : A.toPsh ⟶ Z.toPsh
  /-- Inclusion of the right block. -/
  inr : B.toPsh ⟶ Z.toPsh
  /-- Which block a bead cell lies in. -/
  side : ∀ m : ℕ, 1 ≤ m → Z.cells m → A.cells m ⊕ B.cells m
  side_inl : ∀ (m : ℕ) (hm : 1 ≤ m) (x : A.cells m), side m hm (inl⟪m⟫ x) = Sum.inl x
  side_inr : ∀ (m : ℕ) (hm : 1 ≤ m) (y : B.cells m), side m hm (inr⟪m⟫ y) = Sum.inr y
  elim : ∀ (m : ℕ) (hm : 1 ≤ m) (z : Z.cells m),
    Sum.elim (fun x => inl⟪m⟫ x) (fun y => inr⟪m⟫ y) (side m hm z) = z
  inl_inj : ∀ n : ℕ, Function.Injective (inl⟪n⟫)
  inr_inj : ∀ n : ℕ, Function.Injective (inr⟪n⟫)
  /-- `Z` starts where `A` does. -/
  init_eq : Z.init = inl⟪0⟫ A.init
  /-- `Z` ends where `B` does. -/
  final_eq : Z.final = inr⟪0⟫ B.final
  /-- The junction: `A`'s final vertex is `B`'s initial one. -/
  junction : inl⟪0⟫ A.final = inr⟪0⟫ B.init
  /-- **The blocks meet only at the junction.**  This is the pullback half of the wedge square,
  and it is what pins a chain's crossing point. -/
  vertex_inter : ∀ (u : A.cells 0) (w : B.cells 0),
    inl⟪0⟫ u = inr⟪0⟫ w → u = A.final ∧ w = B.init

namespace Split

variable (S : Split Z A B)

/-- The left block. -/
@[reducible] def left : Block Z A where
  incl := S.inl
  proj m hm z := (S.side m hm z).getLeft?
  sec m hm r := by rw [S.side_inl]; rfl

/-- The right block. -/
@[reducible] def right : Block Z B where
  incl := S.inr
  proj m hm z := (S.side m hm z).getRight?
  sec m hm r := by rw [S.side_inr]; rfl

@[simp] theorem left_incl : S.left.incl = S.inl := rfl
@[simp] theorem right_incl : S.right.incl = S.inr := rfl

/-- **A bead cell is in one block or the other.** -/
theorem cellCases (m : ℕ) (hm : 1 ≤ m) (z : Z.cells m) :
    (∃ x, S.inl⟪m⟫ x = z) ∨ ∃ y, S.inr⟪m⟫ y = z := by
  rcases hs : S.side m hm z with x | y
  · exact Or.inl ⟨x, by have := S.elim m hm z; rwa [hs] at this⟩
  · exact Or.inr ⟨y, by have := S.elim m hm z; rwa [hs] at this⟩

/-- **The two blocks are disjoint on bead cells.** -/
theorem inl_ne_inr (m : ℕ) (hm : 1 ≤ m) (x : A.cells m) (y : B.cells m) :
    S.inl⟪m⟫ x ≠ S.inr⟪m⟫ y := fun h => by
  have h1 : S.side m hm (S.inl⟪m⟫ x) = Sum.inl x := S.side_inl m hm x
  rw [h, S.side_inr] at h1
  exact Sum.inr_ne_inl h1

/-- The left projection does not see a right-block cell. -/
theorem left_proj_inr (m : ℕ) (hm : 1 ≤ m) (y : B.cells m) :
    S.left.proj m hm (S.inr⟪m⟫ y) = none := by
  change (S.side m hm _).getLeft? = none
  rw [S.side_inr]; rfl

/-- The right projection does not see a left-block cell. -/
theorem right_proj_inl (m : ℕ) (hm : 1 ≤ m) (x : A.cells m) :
    S.right.proj m hm (S.inl⟪m⟫ x) = none := by
  change (S.side m hm _).getRight? = none
  rw [S.side_inl]; rfl

/-- Beads of the right block are invisible to the left one. -/
@[simp] theorem left_cubes_map_right_push (l : List (Σ n : ℕ+, B.cells (n : ℕ))) :
    S.left.cubes (l.map S.right.push) = [] :=
  (S.left.cubes_map_push_eq S.right (r := fun _ _ => none)
    (fun n y => S.left_proj_inr (n : ℕ) n.pos y) l).trans (by simp)

/-- Beads of the left block are invisible to the right one. -/
@[simp] theorem right_cubes_map_left_push (l : List (Σ n : ℕ+, A.cells (n : ℕ))) :
    S.right.cubes (l.map S.left.push) = [] :=
  (S.right.cubes_map_push_eq S.left (r := fun _ _ => none)
    (fun n x => S.right_proj_inl (n : ℕ) n.pos x) l).trans (by simp)

end Split

/-! ## The two splittings we use -/
/-- A vertex map `□⁰ ⟶ X` at the point evaluates to the vertex it names. -/
theorem vertexMap_app {X : PrecubicalSet} (c : X.cells 0) (v : (□0).cells 0) :
    (vertexMap X c)⟪0⟫ v = c := by
  rw [vertexMap, PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply,
    show v = 𝟙 ▫0 from Subsingleton.elim _ _, op_id, X.map_id]
  rfl

/-- **The wedge splitting.**  `□0` has no positive cells, so at a bead level the pushout
`X ∨ Y` really is the disjoint union of `X` and `Y`; at level `0` the square is a pullback, so the
two halves meet only at the glued point. -/
def wedge2Split (X Y : BPSet) : Split (X ∨ Y) X Y where
  inl := wedgeInl X Y
  inr := wedgeInr X Y
  side m hm := Glue.cellSide X.finalVertex Y.initVertex (op ▫m) (cube0_cells_isEmpty hm)
  side_inl m hm := Glue.cellSide_inl X.finalVertex Y.initVertex (op ▫m) (cube0_cells_isEmpty hm)
  side_inr m hm := Glue.cellSide_inr X.finalVertex Y.initVertex (op ▫m) (cube0_cells_isEmpty hm)
  elim m hm := Glue.cellSide_elim X.finalVertex Y.initVertex (op ▫m) (cube0_cells_isEmpty hm)
  inl_inj _ := glue0_inl_app_injective X.finalVertex Y.initVertex
  inr_inj _ := glue0_inr_app_injective X.finalVertex Y.initVertex
  init_eq := wedge2_init' X Y
  final_eq := wedge2_final' X Y
  junction := wedge2_glue X Y
  vertex_inter u w h := by
    obtain ⟨p, hp1, hp2⟩ := Types.exists_of_isPullback (glue0_isPullback_app X.finalVertex Y.initVertex 0) u w h
    exact ⟨hp1.symm.trans (vertexMap_app X.final p), hp2.symm.trans (vertexMap_app Y.init p)⟩


namespace Split

variable {Z A B : BPSet} (S : Split Z A B)

/-- **A bead's endpoints stay in its own block**: naturality of `vertexEnd` along the inclusion. -/
theorem vertexEnd_of_eq {V : BPSet} (φ : V.toPsh ⟶ Z.toPsh) (ε : Bool) {m : ℕ} {x : V.cells m}
    {c : Z.cells m} (h : φ⟪m⟫ x = c) :
    Z.toPsh.vertexEnd ε c = φ⟪0⟫ (V.toPsh.vertexEnd ε x) := by
  rw [← h]; exact (PrecubicalSet.map_vertexEnd ε φ x).symm

/-! ### The order argument -/

section Order

variable (alt : ∀ n, Z.cells n → ℤ) (hax : Z.toPsh.IsAltitude alt)

include hax in
/-- Crossing a bead strictly raises altitude, by at least its dimension. -/
private theorem alt_step {n : ℕ+} (c : Z.cells (n : ℕ)) :
    alt 0 (Z.toPsh.vertexEnd true c) > alt 0 (Z.toPsh.vertexEnd false c) := by
  have e1 := PrecubicalSet.alt_vertex₁ alt hax c
  have e0 := PrecubicalSet.alt_vertex₀ alt hax c
  have hn : (1 : ℤ) ≤ ((n : ℕ) : ℤ) := by exact_mod_cast n.2
  omega

include hax in
/-- **Past the junction, everything is on the right.**  A chain starting at a right-block vertex
strictly above the junction's altitude consists entirely of right-block beads. -/
theorem allRight (C : ℤ) (hC : C = alt 0 (S.inl⟪0⟫ A.final)) :
    ∀ (cs : List (Σ n : ℕ+, Z.cells (n : ℕ))) (s t : Z.cells 0) (sy ty : B.cells 0),
      s = S.inr⟪0⟫ sy → t = S.inr⟪0⟫ ty → alt 0 s > C → IsCubeChain s cs t →
      ∃ yc : List (Σ n : ℕ+, B.cells (n : ℕ)),
        IsCubeChain sy yc ty ∧ cs = yc.map S.right.push := by
  intro cs
  induction cs with
  | nil =>
    intro s t sy ty hs ht _ hch
    exact ⟨[], S.inr_inj 0 (hs.symm.trans ((hch : s = t).trans ht)), rfl⟩
  | cons hd rest ih =>
    intro s t sy ty hs ht halt hch
    obtain ⟨n, c⟩ := hd
    obtain ⟨hsrc, htail⟩ := hch
    rcases S.cellCases (n : ℕ) n.pos c with ⟨x, hx⟩ | ⟨y, hy⟩
    · -- a left bead: its source is in both blocks, hence the junction, of altitude exactly `C`
      exfalso
      have hs2 : s = S.inl⟪0⟫ (A.toPsh.vertexEnd false x) :=
        hsrc.symm.trans (vertexEnd_of_eq S.inl false hx)
      obtain ⟨hxfin, _⟩ := S.vertex_inter _ _ (hs2.symm.trans hs)
      have : alt 0 s = C := by rw [hs2, hxfin, hC]
      omega
    · -- a right bead: corestrict and recurse, altitude still strictly above `C`
      have hv0 := vertexEnd_of_eq S.inr false hy
      have hs' := vertexEnd_of_eq S.inr true hy
      obtain ⟨yc', hchain', hmap'⟩ :=
        ih (Z.toPsh.vertexEnd true c) t (B.toPsh.vertexEnd true y) ty hs' ht
          (lt_trans halt (hsrc ▸ alt_step alt hax c)) htail
      refine ⟨⟨n, y⟩ :: yc', ⟨S.inr_inj 0 (hv0.symm.trans (hsrc.trans hs)), hchain'⟩, ?_⟩
      rw [List.map_cons, ← hmap']
      exact congrArg (· :: rest) (Sigma.ext rfl (heq_of_eq hy.symm))

include hax in
/-- **The chain split with a left start.**  Peel left beads until the single junction crossing;
after it, `allRight`. -/
theorem chainSplitFrom (C : ℤ) (hC : C = alt 0 (S.inl⟪0⟫ A.final)) :
    ∀ (cs : List (Σ n : ℕ+, Z.cells (n : ℕ))) (sx : A.cells 0) (s : Z.cells 0),
      s = S.inl⟪0⟫ sx → IsCubeChain s cs Z.final →
      ∃ (xc : List (Σ n : ℕ+, A.cells (n : ℕ))) (yc : List (Σ n : ℕ+, B.cells (n : ℕ))),
        IsCubeChain sx xc A.final ∧ IsCubeChain B.init yc B.final
          ∧ cs = xc.map S.left.push ++ yc.map S.right.push := by
  intro cs
  induction cs with
  | nil =>
    intro sx s hs hch
    obtain ⟨hsx, hyf⟩ :=
      S.vertex_inter _ _ (hs.symm.trans ((hch : s = Z.final).trans S.final_eq))
    exact ⟨[], [], hsx, hyf.symm, rfl⟩
  | cons hd rest ih =>
    intro sx s hs hch
    obtain ⟨n, c⟩ := hd
    obtain ⟨hsrc, htail⟩ := hch
    rcases S.cellCases (n : ℕ) n.pos c with ⟨x, hx⟩ | ⟨y, hy⟩
    · -- still on the left: recurse
      have hv0 := vertexEnd_of_eq S.inl false hx
      have hs' := vertexEnd_of_eq S.inl true hx
      obtain ⟨xc', yc', hchx, hchy, hmap⟩ :=
        ih (A.toPsh.vertexEnd true x) (Z.toPsh.vertexEnd true c) hs' htail
      refine ⟨⟨n, x⟩ :: xc', yc', ⟨S.inl_inj 0 (hv0.symm.trans (hsrc.trans hs)), hchx⟩, hchy, ?_⟩
      rw [List.map_cons, List.cons_append, ← hmap]
      exact congrArg (· :: rest) (Sigma.ext rfl (heq_of_eq hx.symm))
    · -- the single junction crossing; the rest is `allRight`
      have hv0 := vertexEnd_of_eq S.inr false hy
      obtain ⟨hsxfin, hy0⟩ :=
        S.vertex_inter _ _ (hs.symm.trans (hsrc.symm.trans hv0))
      have hs' := vertexEnd_of_eq S.inr true hy
      have halt' : alt 0 (Z.toPsh.vertexEnd true c) > C := by
        have := alt_step alt hax c
        rw [hsrc, hs, hsxfin, ← hC] at this; exact this
      obtain ⟨yc', hchy, hmap⟩ :=
        S.allRight alt hax C hC rest (Z.toPsh.vertexEnd true c) Z.final
          (B.toPsh.vertexEnd true y) B.final hs' S.final_eq halt' htail
      refine ⟨[], ⟨n, y⟩ :: yc', hsxfin, ⟨hy0, hchy⟩, ?_⟩
      rw [List.map_nil, List.nil_append, List.map_cons, ← hmap]
      exact congrArg (· :: rest) (Sigma.ext rfl (heq_of_eq hy.symm))

/-- **A chain through a splitting is a left prefix followed by a right suffix.** -/
theorem chainSplit (h : Z.AdmitsAltitude) (cs : List (Σ n : ℕ+, Z.cells (n : ℕ)))
    (hch : IsCubeChain Z.init cs Z.final) :
    ∃ (xc : List (Σ n : ℕ+, A.cells (n : ℕ))) (yc : List (Σ n : ℕ+, B.cells (n : ℕ))),
      IsCubeChain A.init xc A.final ∧ IsCubeChain B.init yc B.final
        ∧ cs = xc.map S.left.push ++ yc.map S.right.push := by
  obtain ⟨alt, hax, _⟩ := h
  exact S.chainSplitFrom alt hax _ rfl cs A.init Z.init S.init_eq hch

end Order

/-! ### The single interface: cube lists split -/

/-- Pushing the two halves back in and concatenating. -/
def cubeListAppend (xs : CubeChain A) (ys : CubeChain B) : CubeChain Z :=
  ⟨xs.1.map S.left.push ++ ys.1.map S.right.push, by
    refine IsCubeChain.append (v := S.inl⟪0⟫ A.final) ?_ ?_
    · have := isCubeChain_map S.inl xs.1 xs.2
      rwa [← S.init_eq] at this
    · have := isCubeChain_map S.inr ys.1 ys.2
      rwa [← S.final_eq, ← S.junction] at this⟩

/-- **Cube lists split.**  For a splitting whose ambient object admits an altitude, a cube list of
`Z` *is* a pair of cube lists, one in each block — computably, with both round trips on the nose.
Every chain-level splitting downstream is this equivalence, transported. -/
def cubeListEquiv (h : Z.AdmitsAltitude) : CubeChain Z ≃ CubeChain A × CubeChain B where
  toFun cs :=
    (⟨S.left.cubes cs.1, by
        obtain ⟨xc, yc, hx, _, hs⟩ := S.chainSplit h cs.1 cs.2
        rwa [hs, Block.cubes_append, Block.cubes_map_push,
          left_cubes_map_right_push, List.append_nil]⟩,
     ⟨S.right.cubes cs.1, by
        obtain ⟨xc, yc, _, hy, hs⟩ := S.chainSplit h cs.1 cs.2
        rwa [hs, Block.cubes_append, right_cubes_map_left_push,
          Block.cubes_map_push, List.nil_append]⟩)
  invFun p := S.cubeListAppend p.1 p.2
  left_inv cs := Subtype.ext (by
    obtain ⟨xc, yc, _, _, hs⟩ := S.chainSplit h cs.1 cs.2
    change (S.left.cubes cs.1).map S.left.push ++ (S.right.cubes cs.1).map S.right.push = cs.1
    rw [hs, Block.cubes_append, Block.cubes_map_push, left_cubes_map_right_push, List.append_nil,
      Block.cubes_append, right_cubes_map_left_push, Block.cubes_map_push, List.nil_append])
  right_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show S.left.cubes (p.1.1.map S.left.push ++ p.2.1.map S.right.push) = p.1.1
      rw [Block.cubes_append, Block.cubes_map_push, left_cubes_map_right_push, List.append_nil]
    · show S.right.cubes (p.1.1.map S.left.push ++ p.2.1.map S.right.push) = p.2.1
      rw [Block.cubes_append, right_cubes_map_left_push, Block.cubes_map_push, List.nil_append]

/-! ### The chain-object form

Conjugating `cubeListEquiv` through `chCubes` gives the interface everything downstream uses:
`Ch Z ≃ Ch A × Ch B`.  Its inverse is concatenation; at `wedge2Split` that concatenation is the
tensorator `chConcat` itself (`chConcat_obj_eq`), so no second gluing is defined here. -/

variable (h : Z.AdmitsAltitude)

/-- **The chain split.**  A chain of `Z` is a chain of `A` followed by a chain of `B`. -/
def chObjEquiv : Ch Z ≃ Ch A × Ch B :=
  (chCubes Z).trans ((S.cubeListEquiv h).trans ((chCubes A).symm.prodCongr (chCubes B).symm))

/-- The split's gluing (the inverse direction), read in cube-list terms. -/
theorem chCubes_symm_chObjEquiv (p : Ch A) (q : Ch B) :
    chCubes Z ((S.chObjEquiv h).symm (p, q)) = S.cubeListAppend (chCubes A p) (chCubes B q) := by
  rw [chObjEquiv, Equiv.symm_trans_apply, Equiv.apply_symm_apply, Equiv.symm_trans_apply]
  rfl

end Split

variable {X Y : BPSet}

/-! ### `chConcat` on cube lists is `cubeListAppend` -/

/-- **`chConcat` is `cubeListAppend`.**  Reading cubes turns concatenation of chains into the
splitting's own append of cube lists. -/
theorem chCubes_chConcat (a : Ch X) (b : Ch Y) :
    chCubes (X ∨ Y) ((chConcat X Y).obj (a, b))
      = (wedge2Split X Y).cubeListAppend (chCubes X a) (chCubes Y b) :=
  CubeChain.eq_of_cubes <| by
    change (beadCell (d := a.dims ++ b.dims) (concatChainMap X Y a b).hom).toList = _
    rw [beadCell_toList_append a.dims b.dims (concatChainMap X Y a b).hom,
      concatChainMap_inclL X Y a b, concatChainMap_inclR X Y a b,
      beadCell_push, beadCell_push, Beads.toList_push, Beads.toList_push]
    rfl

/-! ### The object split

`splitObj` is the wedge split (`chObjEquiv` at `wedge2Split`); its inverse is
`Split.chObjEquiv` and both round trips are the equivalence's. -/

variable (h : (X ∨ Y).AdmitsAltitude)

/-- **The tensorator is the split's inverse.**  `chConcat` (unconditional) and the split
`chObjEquiv` (conditional) are the two directions of one bijection: gluing is `chConcat.obj`, and
the split undoes it.  This is the one bridge between the tensor formula and the cube-list split. -/
theorem chConcat_obj_eq (a : Ch X) (b : Ch Y) :
    (chConcat X Y).obj (a, b) = ((wedge2Split X Y).chObjEquiv h).symm (a, b) :=
  (chCubes (X ∨ Y)).injective <| by
    rw [chCubes_chConcat, Split.chCubes_symm_chObjEquiv]

/-- **The object split.** -/
def splitObj : Ch (X ∨ Y) ≃ Ch X × Ch Y := (wedge2Split X Y).chObjEquiv h

/-- Forward round-trip: gluing the split back gives the original chain, on the nose. -/
theorem chConcat_obj_splitObj (c : Ch (X ∨ Y)) :
    (chConcat X Y).obj (splitObj h c) = c := by
  rw [chConcat_obj_eq h]
  exact (splitObj h).symm_apply_apply c

/-- Backward round-trip: splitting a concatenation recovers the two halves, on the nose. -/
theorem splitObj_chConcat_obj (a : Ch X) (b : Ch Y) :
    splitObj h ((chConcat X Y).obj (a, b)) = (a, b) := by
  rw [chConcat_obj_eq h]
  exact (splitObj h).apply_symm_apply (a, b)

/-- **A chain of a wedge *is* a concatenation** — the split as a destructuring rather than an
equation, so a caller reasoning about `A : Ch (X ∨ Y)` never meets the transport.  The unbundled
`splitWedgeMorphism` cannot do this: there `l`, `r` depend on `as`, and `as = l.dims ++ r.dims` is
not substitutable. -/
@[elab_as_elim] def splitRec {motive : Ch (X ∨ Y) → Sort*}
    (H : ∀ (l : Ch X) (r : Ch Y), motive ((chConcat X Y).obj (l, r))) (A : Ch (X ∨ Y)) :
    motive A :=
  chConcat_obj_splitObj h A ▸ H (splitObj h A).1 (splitObj h A).2

/-- The same split read off a *bare* wedge map: `as` is an append and the map is the corresponding
concatenation.  A chain of `X ∨ Y` with prescribed `dims` is exactly such a map, so this is
`splitObj` projected, not a second construction. -/
def splitWedgeMorphism (as : List ℕ+) (f : ⋁as ⟶ wedge2 X Y) :
    Σ' (l : Ch X) (r : Ch Y) (heq : as = l.dims ++ r.dims),
      f = eqToHom (congrArg BPSet.serialWedge heq) ≫ concatChainMap X Y l r :=
  let p := splitObj h ⟨as, f⟩
  ⟨p.1, p.2, (congrArg Obj.dims (chConcat_obj_splitObj h (⟨as, f⟩ : Ch (wedge2 X Y)))).symm, by
    obtain ⟨_, hmap⟩ := Obj.eq_mk_of_eq
      (chConcat_obj_splitObj h (⟨as, f⟩ : Ch (wedge2 X Y))).symm
    exact hmap⟩




/-! ## Where the splitting always applies

The altitude hypothesis is not incidental: without it a chain can re-cross the junction and the
statement is false.  The objects where it holds are closed under `∨` and contain the unit, so they
form a monoidal full subcategory — the honest domain of the splitting. -/

/-- Admitting an altitude, as a property of bi-pointed sets. -/
def AdmitsAlt : ObjectProperty BPSet := fun X => BPSet.AdmitsAltitude X

instance : AdmitsAlt.ContainsUnit := ⟨cube_admitsAltitude 0⟩

instance : AdmitsAlt.TensorLE AdmitsAlt AdmitsAlt :=
  ⟨fun _ _ hX hY => wedge2_admitsAltitude hX hY⟩

instance : AdmitsAlt.IsMonoidal where

end ChainCat
