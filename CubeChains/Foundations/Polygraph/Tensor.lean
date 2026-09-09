import CubeChains.Foundations.Polygraph.Day

/-!
# Foundations/Polygraph/Tensor — the tensor of polygraphs, and that it is the convolution

`prod P Q` has 0-cells `P.V × Q.V`, a copy of each factor's 1-cells with the other coordinate
frozen, each factor's 2-cells, **and** an interchange square for every pair of 1-cells.

`dayIso` is why the interchange square is not an axiom: read through `polyToPsh`, the tensor is the
Day convolution for `Split`, and `ProdRel.interchange` is its `Split.square` component — the one
splitting of `cell 2 2` that puts an edge in each factor.
-/

universe wp wq up uq w₂p w₂q u

namespace CategoryTheory

open Opposite PolyShape

namespace Polygraph

variable (P : Polygraph.{wp, up, w₂p}) (Q : Polygraph.{wq, uq, w₂q})

/-! ## The tensor -/

/-- 1-cells of a tensor: one of `P` at a frozen 0-cell of `Q`, or one of `Q` at a frozen 0-cell
of `P`. -/
inductive ProdGen : P.V × Q.V → P.V × Q.V → Type (max wp wq up uq)
  /-- a `P`-generator, with the `Q`-coordinate frozen -/
  | left {x x' : P.V} (g : P.Gen x x') (y : Q.V) : ProdGen (x, y) (x', y)
  /-- a `Q`-generator, with the `P`-coordinate frozen -/
  | right (x : P.V) {y y' : Q.V} (h : Q.Gen y y') : ProdGen (x, y) (x, y')

/-- A `P`-generator as a one-letter word, at a frozen 0-cell of `Q`. -/
abbrev leftLetter (y : Q.V) {x x' : P.V} (g : P.Gen x x') :
    Quiver.Path (⟨(x, y)⟩ : GenObj (ProdGen P Q)) ⟨(x', y)⟩ :=
  Quiver.Hom.toPath (ProdGen.left g y)

/-- A `Q`-generator as a one-letter word, at a frozen 0-cell of `P`. -/
abbrev rightLetter (x : P.V) {y y' : Q.V} (h : Q.Gen y y') :
    Quiver.Path (⟨(x, y)⟩ : GenObj (ProdGen P Q)) ⟨(x, y')⟩ :=
  Quiver.Hom.toPath (ProdGen.right x h)

/-- The copy of `P` at a 0-cell of `Q`. -/
abbrev prodLeft (y : Q.V) : GenObj P.Gen ⥤q GenObj (ProdGen P Q) where
  obj x := ⟨(x.as, y)⟩
  map g := ProdGen.left g y

/-- The copy of `Q` at a 0-cell of `P`. -/
abbrev prodRight (x : P.V) : GenObj Q.Gen ⥤q GenObj (ProdGen P Q) where
  obj y := ⟨(x, y.as)⟩
  map h := ProdGen.right x h

/-- 2-cells of a tensor: each copy's own, **and** the interchange squares. -/
inductive ProdRel : GenObj (ProdGen P Q) → GenObj (ProdGen P Q) → Type (max wp wq up uq w₂p w₂q)
  /-- a `P`-relation, with the `Q`-coordinate frozen -/
  | left (y : Q.V) {x x' : GenObj P.Gen} :
      P.Rel x x' → ProdRel ((prodLeft P Q y).obj x) ((prodLeft P Q y).obj x')
  /-- a `Q`-relation, with the `P`-coordinate frozen -/
  | right (x : P.V) {y y' : GenObj Q.Gen} :
      Q.Rel y y' → ProdRel ((prodRight P Q x).obj y) ((prodRight P Q x).obj y')
  /-- the square two 1-cells in different factors span -/
  | interchange {x x' : P.V} {y y' : Q.V} (g : P.Gen x x') (h : Q.Gen y y') :
      ProdRel ⟨(x, y)⟩ ⟨(x', y')⟩

/-- The source of a tensor 2-cell: a copy's own, included, or a side of the interchange square. -/
def ProdRel.src : ∀ {a b : GenObj (ProdGen P Q)}, ProdRel P Q a b → Quiver.Path a b
  | _, _, .left y α => (prodLeft P Q y).mapPath (P.src α)
  | _, _, .right x α => (prodRight P Q x).mapPath (Q.src α)
  | _, _, .interchange (y := y) (x' := x') g h => (leftLetter P Q y g).comp (rightLetter P Q x' h)

/-- The target of a tensor 2-cell: the other corner. -/
def ProdRel.tgt : ∀ {a b : GenObj (ProdGen P Q)}, ProdRel P Q a b → Quiver.Path a b
  | _, _, .left y α => (prodLeft P Q y).mapPath (P.tgt α)
  | _, _, .right x α => (prodRight P Q x).mapPath (Q.tgt α)
  | _, _, .interchange (x := x) (y' := y') g h => (rightLetter P Q x h).comp (leftLetter P Q y' g)

/-- **The tensor of polygraphs.** -/
def prod : Polygraph.{max wp wq up uq, max up uq, max wp wq up uq w₂p w₂q} where
  V := P.V × Q.V
  Gen := ProdGen P Q
  Rel := ProdRel P Q
  src := ProdRel.src P Q
  tgt := ProdRel.tgt P Q

/-- The copy of `P` at a 0-cell of `Q`, as a morphism of polygraphs. -/
def prodInl (y : Q.V) : Hom P (prod P Q) where
  pre := prodLeft P Q y
  two α := ProdRel.left y α
  src_two _ := rfl
  tgt_two _ := rfl

/-- The copy of `Q` at a 0-cell of `P`, as a morphism of polygraphs. -/
def prodInr (x : P.V) : Hom Q (prod P Q) where
  pre := prodRight P Q x
  two α := ProdRel.right x α
  src_two _ := rfl
  tgt_two _ := rfl

/-! ## Functoriality

Nothing here is a theorem about words: a 1-cell of the tensor is a 1-cell of one factor and a
0-cell of the other, so a pair of morphisms acts on it componentwise, and `src_two` is
`prodLeft ⋙q prodMapPre = pre ⋙q prodLeft` — an equality of prefunctors, on the nose. -/

variable {P Q} {P' : Polygraph.{wp, up, w₂p}} {Q' : Polygraph.{wq, uq, w₂q}}

/-- The 1-cell a pair of morphisms sends a tensor's 1-cell to. -/
def prodMapGen (f : P ⟶ P') (g : Q ⟶ Q') : ∀ {z z' : P.V × Q.V}, ProdGen P Q z z' →
    ProdGen P' Q' ((f.pre.obj ⟨z.1⟩).as, (g.pre.obj ⟨z.2⟩).as)
      ((f.pre.obj ⟨z'.1⟩).as, (g.pre.obj ⟨z'.2⟩).as)
  | _, _, .left c y => ProdGen.left (f.pre.map c) (g.pre.obj ⟨y⟩).as
  | _, _, .right x c => ProdGen.right (f.pre.obj ⟨x⟩).as (g.pre.map c)

/-- The 0-cells and 1-cells a pair of morphisms sends a tensor's to. -/
def prodMapPre (f : P ⟶ P') (g : Q ⟶ Q') : GenObj (ProdGen P Q) ⥤q GenObj (ProdGen P' Q') where
  obj z := ⟨((f.pre.obj ⟨z.as.1⟩).as, (g.pre.obj ⟨z.as.2⟩).as)⟩
  map {_ _} e := prodMapGen f g e

/-- **A factor's word, pushed forward** — a `P`-word at a frozen `Q`-vertex is the pushed-forward
`P`-word at the pushed-forward vertex. -/
theorem prodMapPre_mapPath_left (f : P ⟶ P') (g : Q ⟶ Q') (y : Q.V) {x x' : GenObj P.Gen}
    (w : Quiver.Path x x') :
    (prodMapPre f g).mapPath ((prodLeft P Q y).mapPath w)
      = (prodLeft P' Q' (g.pre.obj ⟨y⟩).as).mapPath (f.pre.mapPath w) := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Quiver.Path.cons · _) ih

theorem prodMapPre_mapPath_right (f : P ⟶ P') (g : Q ⟶ Q') (x : P.V) {y y' : GenObj Q.Gen}
    (w : Quiver.Path y y') :
    (prodMapPre f g).mapPath ((prodRight P Q x).mapPath w)
      = (prodRight P' Q' (f.pre.obj ⟨x⟩).as).mapPath (g.pre.mapPath w) := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Quiver.Path.cons · _) ih

/-- **A pair of morphisms is a morphism of tensors.** -/
def prodMap (f : P ⟶ P') (g : Q ⟶ Q') : prod P Q ⟶ prod P' Q' where
  pre := prodMapPre f g
  two {_ _} α := match α with
    | .left y β => ProdRel.left (g.pre.obj ⟨y⟩).as (f.two β)
    | .right x β => ProdRel.right (f.pre.obj ⟨x⟩).as (g.two β)
    | .interchange c d => ProdRel.interchange (f.pre.map c) (g.pre.map d)
  src_two := by
    rintro _ _ (⟨y, β⟩ | ⟨x, β⟩ | ⟨c, d⟩)
    · exact (congrArg (prodLeft P' Q' _).mapPath (f.src_two β)).trans
        (prodMapPre_mapPath_left f g y (P.src β)).symm
    · exact (congrArg (prodRight P' Q' _).mapPath (g.src_two β)).trans
        (prodMapPre_mapPath_right f g x (Q.src β)).symm
    · rfl
  tgt_two := by
    rintro _ _ (⟨y, β⟩ | ⟨x, β⟩ | ⟨c, d⟩)
    · exact (congrArg (prodLeft P' Q' _).mapPath (f.tgt_two β)).trans
        (prodMapPre_mapPath_left f g y (P.tgt β)).symm
    · exact (congrArg (prodRight P' Q' _).mapPath (g.tgt_two β)).trans
        (prodMapPre_mapPath_right f g x (Q.tgt β)).symm
    · rfl

@[simp] theorem prodMap_pre (f : P ⟶ P') (g : Q ⟶ Q') : (prodMap f g).pre = prodMapPre f g := rfl

theorem prodMap_id (P : Polygraph.{wp, up, w₂p}) (Q : Polygraph.{wq, uq, w₂q}) :
    prodMap (𝟙 P) (𝟙 Q) = 𝟙 (prod P Q) := by
  refine Hom.ext' (Prefunctor.ext' (fun _ => rfl) ?_) ?_
  · rintro ⟨⟨x, y⟩⟩ ⟨⟨x', y'⟩⟩ (⟨c, _⟩ | ⟨_, c⟩) <;> rfl
  · rintro _ _ (⟨y, β⟩ | ⟨x, β⟩ | ⟨c, d⟩) <;> rfl

theorem prodMap_comp {P'' : Polygraph.{wp, up, w₂p}} {Q'' : Polygraph.{wq, uq, w₂q}}
    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    prodMap (f ≫ f') (g ≫ g') = prodMap f g ≫ prodMap f' g' := by
  refine Hom.ext' (Prefunctor.ext' (fun _ => rfl) ?_) ?_
  · rintro ⟨⟨x, y⟩⟩ ⟨⟨x', y'⟩⟩ (⟨c, _⟩ | ⟨_, c⟩) <;> rfl
  · rintro _ _ (⟨y, β⟩ | ⟨x, β⟩ | ⟨c, d⟩) <;> rfl

/-! ## The tensor is the convolution

`Split.cellL`/`cellR` are the two factors' own 2-cells; `Split.square` is `ProdRel.interchange`,
and it is the *only* splitting of a bigon that puts an edge in each factor.

  `Split.pt`      ↦ a 0-cell of each factor
  `Split.edgeL/R` ↦ a 1-cell of one factor at a 0-cell of the other
  `Split.cellL/R` ↦ a 2-cell of one factor at a 0-cell of the other
  `Split.square`  ↦ a 1-cell of each factor: `(g,1)·(1,h) = (1,h)·(g,1)`               -/

section Day

variable (P Q : Polygraph.{u, u, u})

/-- **A convolution cell, read as a cell of the tensor.** -/
def ofDayCells : ∀ {X : PolyShape}, DayCells (cellsPsh P) (cellsPsh Q) X → cellsObj (prod P Q) X
  | _, ⟨.pt, x, y⟩ => ⟨(x.as, y.as)⟩
  | _, ⟨.edgeL, t, y⟩ => ⟨_, _, ProdGen.left t.hom y.as⟩
  | _, ⟨.edgeR, x, t⟩ => ⟨_, _, ProdGen.right x.as t.hom⟩
  | _, ⟨.cellL _ _, c, y⟩ =>
      c.push (prodLeft P Q y.as) (ProdRel.left y.as c.cell) rfl rfl
  | _, ⟨.cellR _ _, x, c⟩ =>
      c.push (prodRight P Q x.as) (ProdRel.right x.as c.cell) rfl rfl
  | _, ⟨.square, t, t'⟩ =>
      { x := ⟨(t.left.as, t'.left.as)⟩
        y := ⟨(t.right.as, t'.right.as)⟩
        cell := ProdRel.interchange t.hom t'.hom
        len_src := rfl
        len_tgt := rfl }

/-- **`Split.square` is `ProdRel.interchange`** — the interchange square is the `edge ⊗ edge`
component of the convolution at `cell 2 2`, not an axiom of the tensor. -/
@[simp] theorem cell_ofDayCells_square (t : Quiver.Total (GenObj P.Gen))
    (t' : Quiver.Total (GenObj Q.Gen)) :
    (ofDayCells P Q ⟨Split.square, t, t'⟩).cell = ProdRel.interchange t.hom t'.hom := rfl

/-- **A cell of the tensor, read as a convolution cell** — a 2-cell is one factor's, or an
interchange square, and the latter forces both boundary lengths to be `2`. -/
def toDayCells : ∀ {X : PolyShape}, cellsObj (prod P Q) X → DayCells (cellsPsh P) (cellsPsh Q) X
  | .pt, z => ⟨.pt, ⟨z.as.1⟩, ⟨z.as.2⟩⟩
  | .edge, ⟨⟨_⟩, ⟨_⟩, .left c y⟩ => ⟨.edgeL, ⟨_, _, c⟩, ⟨y⟩⟩
  | .edge, ⟨⟨_⟩, ⟨_⟩, .right x c⟩ => ⟨.edgeR, ⟨x⟩, ⟨_, _, c⟩⟩
  | .cell m n, ⟨_, _, .left y β, hs, ht⟩ =>
      ⟨.cellL m n, ⟨_, _, β, (Prefunctor.length_mapPath _ _).symm.trans hs,
        (Prefunctor.length_mapPath _ _).symm.trans ht⟩, ⟨y⟩⟩
  | .cell m n, ⟨_, _, .right x β, hs, ht⟩ =>
      ⟨.cellR m n, ⟨x⟩, ⟨_, _, β, (Prefunctor.length_mapPath _ _).symm.trans hs,
        (Prefunctor.length_mapPath _ _).symm.trans ht⟩⟩
  | .cell _ _, ⟨_, _, .interchange c d, hs, ht⟩ =>
      cellCongr (fun m n => DayCells (cellsPsh P) (cellsPsh Q) (.cell m n)) hs ht
        ⟨.square, ⟨_, _, c⟩, ⟨_, _, d⟩⟩

theorem toDayCells_ofDayCells {X : PolyShape} (x : DayCells (cellsPsh P) (cellsPsh Q) X) :
    toDayCells P Q (ofDayCells P Q x) = x := by
  obtain ⟨s, a, b⟩ := x
  cases s <;> simp only [ofDayCells, toDayCells] <;> rfl

theorem ofDayCells_toDayCells {X : PolyShape} (z : cellsObj (prod P Q) X) :
    ofDayCells P Q (toDayCells P Q z) = z := by
  cases X with
  | pt => rfl
  | edge => obtain ⟨⟨_⟩, ⟨_⟩, _ | _⟩ := z <;> rfl
  | cell m n =>
      obtain ⟨_, _, α, hs, ht⟩ := z
      cases α with
      | left => rfl
      | right => rfl
      | interchange c d =>
          obtain rfl : (2 : ℕ) = m := hs
          obtain rfl : (2 : ℕ) = n := ht
          rfl

/-! ### Naturality

At a `cellL`/`cellR` splitting the tensor cell's boundary is the factor's, pushed forward, so its
faces are `ShapedCell.vtx_push`/`edg_push`.  At `square` they are read off `sqVtx`/`sqEdge`, which
is the statement that the interchange square's boundary is the boundary of `□¹ × □¹`. -/

theorem ofDayCells_naturality : ∀ {X Y : PolyShape} (u : X ⟶ Y)
    (x : DayCells (cellsPsh P) (cellsPsh Q) Y),
    ofDayCells P Q (dayCellsMap (cellsPsh P) (cellsPsh Q) u x)
      = cellsMap (prod P Q) u (ofDayCells P Q x) := by
  rintro X Y u ⟨s, a, b⟩
  cases u with
  | id _ => exact congrArg (ofDayCells P Q) (congrFun (dayCellsMap_id _ _ _) _)
  | end_ β =>
      cases s with
      | edgeL => cases β <;> rfl
      | edgeR => cases β <;> rfl
  | vtx v =>
      cases s with
      | cellL m n =>
          exact (ShapedCell.vtx_push (Q := prod P Q) (prodLeft P Q b.as) a
            (ProdRel.left b.as a.cell) rfl rfl v).symm
      | cellR m n =>
          exact (ShapedCell.vtx_push (Q := prod P Q) (prodRight P Q a.as) b
            (ProdRel.right a.as b.cell) rfl rfl v).symm
      | square =>
          induction v using BigonVtx.ind with
          | h w =>
              rcases w with ⟨i, hi⟩ | ⟨j, hj⟩
              · rcases i with _ | _ | _ | i <;> first | omega | rfl
              · rcases j with _ | _ | _ | j <;> first | omega | rfl
  | edg e =>
      cases s with
      | cellL m n =>
          exact (ShapedCell.edg_push (Q := prod P Q) (prodLeft P Q b.as) a
            (ProdRel.left b.as a.cell) rfl rfl e).symm
      | cellR m n =>
          exact (ShapedCell.edg_push (Q := prod P Q) (prodRight P Q a.as) b
            (ProdRel.right a.as b.cell) rfl rfl e).symm
      | square =>
          rcases e with ⟨i, hi⟩ | ⟨j, hj⟩
          · rcases i with _ | _ | i <;> first | omega | rfl
          · rcases j with _ | _ | j <;> first | omega | rfl

/-- **The tensor of polygraphs is the Day convolution for `Split`.**  `ProdRel.interchange` is the
`Split.square` component: it is not an axiom of the tensor, it is the one splitting of `cell 2 2`
that puts an edge in each factor. -/
def dayIso : dayObj (cellsPsh P) (cellsPsh Q) ≅ cellsPsh (prod P Q) :=
  NatIso.ofComponents
    (fun c => { hom := ↾(ofDayCells P Q (X := c.unop))
                inv := ↾(toDayCells P Q (X := c.unop))
                hom_inv_id := congrArg TypeCat.ofHom (funext (toDayCells_ofDayCells P Q))
                inv_hom_id := congrArg TypeCat.ofHom (funext (ofDayCells_toDayCells P Q)) })
    (fun f => congrArg TypeCat.ofHom (funext fun x => ofDayCells_naturality P Q f.unop x))

/-- **The comparison is natural in both factors** — `prodMap` is `dayMap`, read through `dayIso`,
so the tensor's functoriality is the convolution's. -/
theorem dayIso_naturality {P' Q' : Polygraph.{u, u, u}} (f : P ⟶ P') (g : Q ⟶ Q') :
    dayMap (polyToPsh.map f) (polyToPsh.map g) ≫ (dayIso P' Q').hom
      = (dayIso P Q).hom ≫ polyToPsh.map (prodMap f g) := by
  refine NatTrans.ext (funext fun c => TypeCat.homEquiv.injective (funext fun x => ?_))
  obtain ⟨X⟩ := c
  obtain ⟨s, a, b⟩ := x
  cases s <;> rfl

end Day

end Polygraph

end CategoryTheory
