import CubeChains.Foundations.Polygraph.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Foundations/Polygraph/Presheaf — 2-polygraphs are a presheaf topos

Schanuel's theorem, by Carboni–Johnstone's route (*Connected limits, familial representability and
Artin glueing*, MSCS 5 (1995) 441–459; sharp at 2 by Makkai–Zawadowski).  The free-category monad
on quivers is familially representable — a word is its *length* and its letters — so a 2-polygraph
is a quiver glued to a family of 2-cells indexed by a pair of boundary lengths, and the glueing has
a site: `PolyShape`, one point, one edge, and one bigon `cell m n` per pair.

`polyEquivPresheaf : Polygraph.{u, u, u} ≌ (PolyShapeᵒᵖ ⥤ Type u)`, whence all limits and colimits,
computed cellwise.
-/

universe u

namespace CategoryTheory

open Quiver Opposite Limits

/-! ## The bigon

`B m n` is two strings of `m` and `n` edges glued at both ends.  Its vertices are a quotient
because the glueing is genuine: at `n = 0` the two ends of the source string are identified. -/

/-- The glueing of the two strings of a bigon at their endpoints. -/
inductive BigonRel (m n : ℕ) : Fin (m + 1) ⊕ Fin (n + 1) → Fin (m + 1) ⊕ Fin (n + 1) → Prop
  /-- the two strings start together -/
  | start : BigonRel m n (.inl ⟨0, m.succ_pos⟩) (.inr ⟨0, n.succ_pos⟩)
  /-- …and finish together -/
  | finish : BigonRel m n (.inl (Fin.last m)) (.inr (Fin.last n))

/-- The vertices of the bigon `B m n`. -/
def BigonVtx (m n : ℕ) : Type := Quot (BigonRel m n)

/-- The edges of the bigon `B m n`. -/
def BigonEdge (m n : ℕ) : Type := Fin m ⊕ Fin n

namespace BigonVtx

/-- The class of a vertex of one of the two strings. -/
def mk {m n : ℕ} (w : Fin (m + 1) ⊕ Fin (n + 1)) : BigonVtx m n := Quot.mk _ w

/-- A map out of the bigon's vertices is a map on the two strings glued at the ends. -/
def lift {m n : ℕ} {α : Sort*} (f : Fin (m + 1) ⊕ Fin (n + 1) → α)
    (h : ∀ a b, BigonRel m n a b → f a = f b) : BigonVtx m n → α := Quot.lift f h

@[simp] theorem lift_mk {m n : ℕ} {α : Sort*} (f : Fin (m + 1) ⊕ Fin (n + 1) → α) (h) (w) :
    lift f h (mk w) = f w := rfl

@[elab_as_elim] theorem ind {m n : ℕ} {β : BigonVtx m n → Prop} (h : ∀ w, β (mk w)) :
    ∀ v, β v := Quot.ind h

theorem sound {m n : ℕ} {a b : Fin (m + 1) ⊕ Fin (n + 1)} (h : BigonRel m n a b) :
    mk a = mk b := Quot.sound h

/-- The vertex the two strings start at. -/
def start (m n : ℕ) : BigonVtx m n := mk (.inl ⟨0, m.succ_pos⟩)

/-- The vertex the two strings finish at. -/
def finish (m n : ℕ) : BigonVtx m n := mk (.inl (Fin.last m))

theorem start_eq (m n : ℕ) : start m n = mk (.inr ⟨0, n.succ_pos⟩) := sound .start

theorem finish_eq (m n : ℕ) : finish m n = mk (.inr (Fin.last n)) := sound .finish

end BigonVtx

/-- The `b`-endpoint (`false` = source) of an arrow. -/
def _root_.Quiver.Total.endpt {V : Type*} [Quiver V] (b : Bool) (t : Total V) : V :=
  if b then t.right else t.left

theorem _root_.Quiver.Total.hom_heq {V : Type*} [Quiver V] {t u : Total V} (h : t = u) :
    t.hom ≍ u.hom := by cases h; rfl

/-- **An arrow is its endpoints and its 1-cell**, read through equations naming the endpoints. -/
theorem _root_.Quiver.Total.eq_mk {V : Type*} [Quiver V] {t : Total V} {a b : V} (g : a ⟶ b)
    (ha : t.left = a) (hb : t.right = b) (hg : g = Quiver.homOfEq t.hom ha hb) : t = ⟨a, b, g⟩ := by
  subst ha; subst hb; subst hg; rfl

/-- The `b`-endpoint of an edge of the bigon. -/
def bigonEnd (b : Bool) : {m n : ℕ} → BigonEdge m n → BigonVtx m n
  | _, _, .inl i => .mk (.inl (if b then i.succ else i.castSucc))
  | _, _, .inr j => .mk (.inr (if b then j.succ else j.castSucc))

/-! ## The site

The glueing's site: the point, the edge, and one object per bigon.  There are no arrows out of a
`cell`, and the arrows into `cell m n` are exactly the bigon's own cells. -/

/-- The site of 2-polygraphs. -/
inductive PolyShape : Type
  /-- the 0-cell -/
  | pt : PolyShape
  /-- the 1-cell -/
  | edge : PolyShape
  /-- the 2-cell with an `m`-fold source and an `n`-fold target -/
  | cell (m n : ℕ) : PolyShape

namespace PolyShape

/-- The arrows of the site: the two endpoints of an edge, and the cells of a bigon. -/
inductive Hom : PolyShape → PolyShape → Type
  /-- the identity -/
  | id (X : PolyShape) : Hom X X
  /-- an endpoint of the edge -/
  | end_ (b : Bool) : Hom pt edge
  /-- a vertex of a bigon -/
  | vtx {m n : ℕ} (v : BigonVtx m n) : Hom pt (cell m n)
  /-- an edge of a bigon -/
  | edg {m n : ℕ} (e : BigonEdge m n) : Hom edge (cell m n)

/-- Composition: an endpoint of an edge of a bigon is a vertex of that bigon. -/
def comp : {X Y Z : PolyShape} → Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, .id _, g => g
  | _, _, _, .end_ b, .id _ => .end_ b
  | _, _, _, .end_ b, .edg e => .vtx (bigonEnd b e)
  | _, _, _, .vtx v, .id _ => .vtx v
  | _, _, _, .edg e, .id _ => .edg e

instance : SmallCategory PolyShape where
  Hom := Hom
  id := Hom.id
  comp := comp
  id_comp _ := rfl
  comp_id f := by cases f <;> rfl
  assoc f g h := by cases f <;> cases g <;> cases h <;> rfl

end PolyShape

namespace Polygraph

/-! ## The cells of a polygraph, as a presheaf -/

/-- A 2-cell of `P` whose source word has length `m` and target word length `n`. -/
structure ShapedCell (P : Polygraph.{u, u, u}) (m n : ℕ) : Type u where
  /-- the 0-cell the boundary starts at -/
  x : GenObj P.Gen
  /-- the 0-cell the boundary finishes at -/
  y : GenObj P.Gen
  /-- the 2-cell -/
  cell : P.Rel x y
  /-- …whose source word has `m` letters -/
  len_src : (P.src cell).length = m
  /-- …and whose target word has `n` -/
  len_tgt : (P.tgt cell).length = n

namespace ShapedCell

variable {P : Polygraph.{u, u, u}} {m n : ℕ}

/-- The 0-cell of a shaped cell's boundary named by a vertex of the bigon. -/
def vtx (c : ShapedCell P m n) : BigonVtx m n → GenObj P.Gen :=
  BigonVtx.lift (Sum.elim (fun i : Fin (m + 1) => (P.src c.cell).vtx i)
      (fun j : Fin (n + 1) => (P.tgt c.cell).vtx j)) <| by
    rintro _ _ (_ | _)
    · simp
    · simp only [Sum.elim_inl, Sum.elim_inr, Fin.val_last]
      rw [Quiver.Path.vtx_of_le _ c.len_src.le, Quiver.Path.vtx_of_le _ c.len_tgt.le]

/-- The 1-cell of a shaped cell's boundary named by an edge of the bigon. -/
def edg (c : ShapedCell P m n) : BigonEdge m n → Total (GenObj P.Gen)
  | .inl i => (P.src c.cell).edgeAt i (by rw [c.len_src]; exact i.isLt)
  | .inr j => (P.tgt c.cell).edgeAt j (by rw [c.len_tgt]; exact j.isLt)

@[simp] theorem vtx_start (c : ShapedCell P m n) : c.vtx (.start m n) = c.x :=
  Quiver.Path.vtx_zero _

@[simp] theorem vtx_finish (c : ShapedCell P m n) : c.vtx (.finish m n) = c.y :=
  Quiver.Path.vtx_of_le _ c.len_src.le

/-- **The bigon's incidences hold**: the `b`-endpoint of the `e`-th letter is the `e`-th
vertex. -/
theorem endpt_edg (c : ShapedCell P m n) (b : Bool) (e : BigonEdge m n) :
    (c.edg e).endpt b = c.vtx (bigonEnd b e) := by
  cases e with
  | inl i =>
      cases b
      · exact Quiver.Path.left_edgeAt (P.src c.cell) (i : ℕ) _
      · exact Quiver.Path.right_edgeAt (P.src c.cell) (i : ℕ) _
  | inr j =>
      cases b
      · exact Quiver.Path.left_edgeAt (P.tgt c.cell) (j : ℕ) _
      · exact Quiver.Path.right_edgeAt (P.tgt c.cell) (j : ℕ) _

theorem cell_heq {c d : ShapedCell P m n} (h : c = d) : c.cell ≍ d.cell := by cases h; rfl

/-- **A shaped cell is its endpoints and its 2-cell.** -/
theorem ext' {c d : ShapedCell P m n} (hx : c.x = d.x) (hy : c.y = d.y) (hc : c.cell ≍ d.cell) :
    c = d := by
  have key : ∀ {x y x' y' : GenObj P.Gen} (α : P.Rel x y) (β : P.Rel x' y') hs ht hs' ht',
      x = x' → y = y' → α ≍ β →
      (⟨x, y, α, hs, ht⟩ : ShapedCell P m n) = ⟨x', y', β, hs', ht'⟩ := by
    rintro x y _ _ α β hs ht hs' ht' rfl rfl h
    obtain rfl : α = β := eq_of_heq h
    rfl
  exact key c.cell d.cell c.len_src c.len_tgt d.len_src d.len_tgt hx hy hc

end ShapedCell

/-! ## The functor -/

/-- The cells of `P` at a shape. -/
def cellsObj (P : Polygraph.{u, u, u}) : PolyShape → Type u
  | .pt => GenObj P.Gen
  | .edge => Total (GenObj P.Gen)
  | .cell m n => ShapedCell P m n

/-- The face of a cell named by an arrow of the site. -/
def cellsMap (P : Polygraph.{u, u, u}) : {X Y : PolyShape} → (X ⟶ Y) → cellsObj P Y → cellsObj P X
  | _, _, .id _ => _root_.id
  | _, _, .end_ b => Total.endpt b
  | _, _, .vtx v => (ShapedCell.vtx · v)
  | _, _, .edg e => (ShapedCell.edg · e)

theorem cellsMap_comp (P : Polygraph.{u, u, u}) {X Y Z : PolyShape} (u : X ⟶ Y) (v : Y ⟶ Z) :
    cellsMap P (u ≫ v) = cellsMap P u ∘ cellsMap P v := by
  cases u <;> cases v <;> try rfl
  funext c
  exact (ShapedCell.endpt_edg c _ _).symm

/-- **The cells of a polygraph, as a presheaf on `PolyShape`.** -/
def cellsPsh (P : Polygraph.{u, u, u}) : PolyShapeᵒᵖ ⥤ Type u where
  obj s := cellsObj P s.unop
  map f := ↾(cellsMap P f.unop)
  map_id _ := rfl
  map_comp f g := by ext c; exact congrFun (cellsMap_comp P g.unop f.unop) c

/-- The face a morphism of polygraphs sends a cell to. -/
def cellsApp {P Q : Polygraph.{u, u, u}} (F : P ⟶ Q) : (X : PolyShape) → cellsObj P X → cellsObj Q X
  | .pt => F.pre.obj
  | .edge => Total.map F.pre
  | .cell _ _ => fun c =>
      { x := F.pre.obj c.x
        y := F.pre.obj c.y
        cell := F.two c.cell
        len_src := by rw [F.src_two, F.pre.length_mapPath, c.len_src]
        len_tgt := by rw [F.tgt_two, F.pre.length_mapPath, c.len_tgt] }

theorem cellsApp_vtx {P Q : Polygraph.{u, u, u}} (F : P ⟶ Q) {m n : ℕ} (c : ShapedCell P m n)
    (v : BigonVtx m n) : (cellsApp F (.cell m n) c).vtx v = F.pre.obj (c.vtx v) := by
  induction v using BigonVtx.ind with
  | h w =>
      cases w with
      | inl i =>
          change (Q.src (F.two c.cell)).vtx _ = _
          rw [F.src_two]; simp [ShapedCell.vtx]
      | inr j =>
          change (Q.tgt (F.two c.cell)).vtx _ = _
          rw [F.tgt_two]; simp [ShapedCell.vtx]

theorem cellsApp_edg {P Q : Polygraph.{u, u, u}} (F : P ⟶ Q) {m n : ℕ} (c : ShapedCell P m n)
    (e : BigonEdge m n) :
    (cellsApp F (.cell m n) c).edg e = Total.map F.pre (c.edg e) := by
  cases e with
  | inl i =>
      refine (Quiver.Path.edgeAt_congr (F.src_two c.cell) (i : ℕ) _ ?_).trans ?_
      · rw [F.pre.length_mapPath, c.len_src]; exact i.isLt
      · exact Quiver.Path.edgeAt_mapPath F.pre _ _ _ _
  | inr j =>
      refine (Quiver.Path.edgeAt_congr (F.tgt_two c.cell) (j : ℕ) _ ?_).trans ?_
      · rw [F.pre.length_mapPath, c.len_tgt]; exact j.isLt
      · exact Quiver.Path.edgeAt_mapPath F.pre _ _ _ _

/-- **A morphism of polygraphs, as a map of presheaves.** -/
def cellsHom {P Q : Polygraph.{u, u, u}} (F : P ⟶ Q) : cellsPsh P ⟶ cellsPsh Q where
  app s := ↾(cellsApp F s.unop)
  naturality s t f := by
    obtain ⟨X⟩ := s; obtain ⟨Y⟩ := t
    obtain ⟨u⟩ := f
    ext c
    cases u with
    | id _ => rfl
    | end_ b => cases b <;> rfl
    | vtx v => exact (cellsApp_vtx F c v).symm
    | edg e => exact (cellsApp_edg F c e).symm

/-- **The cells of a polygraph**, functorially. -/
def polyToPsh : Polygraph.{u, u, u} ⥤ (PolyShapeᵒᵖ ⥤ Type u) where
  obj := cellsPsh
  map := cellsHom
  map_id P := by
    ext ⟨X⟩ c
    cases X <;> rfl
  map_comp F G := by
    ext ⟨X⟩ c
    cases X <;> rfl

/-! ## Fully faithful

A map of presheaves is a map on 0-, 1- and 2-cells commuting with the boundaries — which is a
morphism of polygraphs, read off the site. -/

section FullyFaithful

variable {P Q : Polygraph.{u, u, u}} (φ : cellsPsh P ⟶ cellsPsh Q)

/-- **Naturality, read at a cell.** -/
theorem app_apply {X Y : PolyShape} (u : X ⟶ Y) (c : cellsObj P Y) :
    φ.app (op X) (cellsMap P u c) = cellsMap Q u (φ.app (op Y) c) :=
  ConcreteCategory.congr_hom (φ.naturality u.op) c

/-- `φ` on 0-cells. -/
def appPt (x : GenObj P.Gen) : GenObj Q.Gen := φ.app (op .pt) x

/-- `φ` on 1-cells. -/
def appEdge (t : Total (GenObj P.Gen)) : Total (GenObj Q.Gen) := φ.app (op .edge) t

/-- `φ` on 2-cells. -/
def appCell {m n : ℕ} (c : ShapedCell P m n) : ShapedCell Q m n := φ.app (op (.cell m n)) c

theorem app_endpt (t : Total (GenObj P.Gen)) (b : Bool) :
    appPt φ (t.endpt b) = (appEdge φ t).endpt b :=
  app_apply φ (.end_ b) t

theorem app_vtx {m n : ℕ} (c : ShapedCell P m n) (v : BigonVtx m n) :
    appPt φ (c.vtx v) = (appCell φ c).vtx v :=
  app_apply φ (.vtx v) c

theorem app_edg {m n : ℕ} (c : ShapedCell P m n) (e : BigonEdge m n) :
    appEdge φ (c.edg e) = (appCell φ c).edg e :=
  app_apply φ (.edg e) c

/-! ### Faithful -/

instance : polyToPsh.{u}.Faithful where
  map_injective {P Q F G} h := by
    have key : ∀ (X : PolyShape) (c : cellsObj P X), cellsApp F X c = cellsApp G X c := fun X c =>
      ConcreteCategory.congr_hom (NatTrans.congr_app h (op X)) c
    have hobj : ∀ x, F.pre.obj x = G.pre.obj x := key .pt
    refine Hom.ext' (Prefunctor.ext' hobj fun x y e => ?_) fun {x y} α => ?_
    · exact eq_of_heq ((Quiver.Total.hom_heq (key .edge ⟨x, y, e⟩)).trans
        (Quiver.homOfEq_heq _ _ _).symm)
    · exact ShapedCell.cell_heq (key (.cell (P.src α).length (P.tgt α).length)
        (⟨x, y, α, rfl, rfl⟩ : ShapedCell P _ _))

/-! ### Full -/

theorem edge_left {x y : GenObj P.Gen} (e : x ⟶ y) :
    (appEdge φ ⟨x, y, e⟩).left = appPt φ x :=
  (app_endpt φ ⟨x, y, e⟩ false).symm

theorem edge_right {x y : GenObj P.Gen} (e : x ⟶ y) :
    (appEdge φ ⟨x, y, e⟩).right = appPt φ y :=
  (app_endpt φ ⟨x, y, e⟩ true).symm

/-- The 1-cell a map of presheaves sends a 1-cell to. -/
def preMapOf {x y : GenObj P.Gen} (e : x ⟶ y) : appPt φ x ⟶ appPt φ y :=
  Quiver.homOfEq (appEdge φ ⟨x, y, e⟩).hom (edge_left φ e) (edge_right φ e)

/-- The map of generating quivers a map of presheaves carries. -/
def preOf : GenObj P.Gen ⥤q GenObj Q.Gen where
  obj := appPt φ
  map := preMapOf φ

theorem app_edge (t : Total (GenObj P.Gen)) : appEdge φ t = Total.map (preOf φ) t :=
  Quiver.Total.eq_mk _ (edge_left φ t.hom) (edge_right φ t.hom) rfl

/-- A 2-cell at its own boundary lengths. -/
def shapedOf {x y : GenObj P.Gen} (α : P.Rel x y) :
    ShapedCell P (P.src α).length (P.tgt α).length := ⟨x, y, α, rfl, rfl⟩

/-- The shaped cell a map of presheaves sends a 2-cell to. -/
def cellOf {x y : GenObj P.Gen} (α : P.Rel x y) :
    ShapedCell Q (P.src α).length (P.tgt α).length := appCell φ (shapedOf α)

theorem cellOf_x {x y : GenObj P.Gen} (α : P.Rel x y) : (cellOf φ α).x = appPt φ x := by
  have h := app_vtx φ (shapedOf α) (BigonVtx.start _ _)
  rw [ShapedCell.vtx_start, ShapedCell.vtx_start] at h
  exact h.symm

theorem cellOf_y {x y : GenObj P.Gen} (α : P.Rel x y) : (cellOf φ α).y = appPt φ y := by
  have h := app_vtx φ (shapedOf α) (BigonVtx.finish _ _)
  rw [ShapedCell.vtx_finish, ShapedCell.vtx_finish] at h
  exact h.symm

/-- A 2-cell read at endpoints named by equations. -/
def relCast {R : Polygraph.{u, u, u}} {a b a' b' : GenObj R.Gen} (γ : R.Rel a b) (ha : a = a')
    (hb : b = b') : R.Rel a' b' := by subst ha; subst hb; exact γ

theorem relCast_heq {R : Polygraph.{u, u, u}} {a b a' b' : GenObj R.Gen} (γ : R.Rel a b)
    (ha : a = a') (hb : b = b') : relCast γ ha hb ≍ γ := by subst ha; subst hb; rfl

theorem src_relCast {R : Polygraph.{u, u, u}} {a b a' b' : GenObj R.Gen} (γ : R.Rel a b)
    (ha : a = a') (hb : b = b') :
    R.src (relCast γ ha hb) = (R.src γ).castPath ha hb := by subst ha; subst hb; rfl

theorem tgt_relCast {R : Polygraph.{u, u, u}} {a b a' b' : GenObj R.Gen} (γ : R.Rel a b)
    (ha : a = a') (hb : b = b') :
    R.tgt (relCast γ ha hb) = (R.tgt γ).castPath ha hb := by subst ha; subst hb; rfl

/-- The 2-cell a map of presheaves sends a 2-cell to. -/
def twoOf {x y : GenObj P.Gen} (α : P.Rel x y) : Q.Rel (appPt φ x) (appPt φ y) :=
  relCast (cellOf φ α).cell (cellOf_x φ α) (cellOf_y φ α)

theorem src_twoOf {x y : GenObj P.Gen} (α : P.Rel x y) :
    Q.src (twoOf φ α) = (preOf φ).mapPath (P.src α) := by
  rw [twoOf, src_relCast]
  refine Quiver.Path.ext_of_coords (P.src α).length ?_ ?_ fun i h h' => ?_
  · rw [Quiver.Path.length_castPath]; exact (cellOf φ α).len_src
  · exact (preOf φ).length_mapPath _
  · have hi : i < (P.src α).length := by
      rwa [Quiver.Path.length_castPath, (cellOf φ α).len_src] at h
    refine (Quiver.Path.edgeAt_castPath _ _ _ i h
      (by rw [(cellOf φ α).len_src]; exact hi)).trans ?_
    refine Eq.trans ?_ (Quiver.Path.edgeAt_mapPath (preOf φ) (P.src α) i hi h').symm
    exact ((app_edg φ (shapedOf α) (.inl ⟨i, hi⟩)).symm.trans (app_edge φ _))

theorem tgt_twoOf {x y : GenObj P.Gen} (α : P.Rel x y) :
    Q.tgt (twoOf φ α) = (preOf φ).mapPath (P.tgt α) := by
  rw [twoOf, tgt_relCast]
  refine Quiver.Path.ext_of_coords (P.tgt α).length ?_ ?_ fun i h h' => ?_
  · rw [Quiver.Path.length_castPath]; exact (cellOf φ α).len_tgt
  · exact (preOf φ).length_mapPath _
  · have hi : i < (P.tgt α).length := by
      rwa [Quiver.Path.length_castPath, (cellOf φ α).len_tgt] at h
    refine (Quiver.Path.edgeAt_castPath _ _ _ i h
      (by rw [(cellOf φ α).len_tgt]; exact hi)).trans ?_
    refine Eq.trans ?_ (Quiver.Path.edgeAt_mapPath (preOf φ) (P.tgt α) i hi h').symm
    exact ((app_edg φ (shapedOf α) (.inr ⟨i, hi⟩)).symm.trans (app_edge φ _))

/-- **A map of presheaves is a morphism of polygraphs.** -/
def homOf : P ⟶ Q where
  pre := preOf φ
  two := twoOf φ
  src_two := src_twoOf φ
  tgt_two := tgt_twoOf φ

theorem map_homOf : polyToPsh.map (homOf φ) = φ := by
  ext ⟨X⟩ c
  cases X with
  | pt => rfl
  | edge => exact (app_edge φ c).symm
  | cell m n =>
      obtain ⟨x, y, α, hs, ht⟩ := c
      subst hs; subst ht
      exact ShapedCell.ext' (cellOf_x φ α).symm (cellOf_y φ α).symm (relCast_heq _ _ _)

instance : polyToPsh.{u}.Full where
  map_surjective φ := ⟨homOf φ, map_homOf φ⟩

end FullyFaithful

/-! ## Essentially surjective

The glueing, read backwards: a presheaf's 0- and 1-cells are a quiver, and each of its 2-cells
carries a bigon's worth of them, which `ofCoords` reassembles into a parallel pair of words. -/

section OfPsh

variable (X : PolyShapeᵒᵖ ⥤ Type u)

/-- The `b`-endpoint of a 1-cell of `X`. -/
def endptOf (b : Bool) (t : X.obj (op .edge)) : X.obj (op .pt) :=
  X.map (Quiver.Hom.op (PolyShape.Hom.end_ b)) t

/-- The bigon vertex of a 2-cell of `X`. -/
def vtxOf {m n : ℕ} (v : BigonVtx m n) (c : X.obj (op (.cell m n))) : X.obj (op .pt) :=
  X.map (Quiver.Hom.op (PolyShape.Hom.vtx v)) c

/-- The bigon edge of a 2-cell of `X`. -/
def edgOf {m n : ℕ} (e : BigonEdge m n) (c : X.obj (op (.cell m n))) : X.obj (op .edge) :=
  X.map (Quiver.Hom.op (PolyShape.Hom.edg e)) c

theorem endpt_edgOf {m n : ℕ} (b : Bool) (e : BigonEdge m n) (c : X.obj (op (.cell m n))) :
    endptOf X b (edgOf X e c) = vtxOf X (bigonEnd b e) c :=
  (ConcreteCategory.congr_hom
    (X.map_comp (Quiver.Hom.op (PolyShape.Hom.edg e))
      (Quiver.Hom.op (PolyShape.Hom.end_ b))) c).symm

/-- The 1-cells of the polygraph a presheaf carries. -/
def genOfPsh (a b : X.obj (op .pt)) : Type u :=
  {t : X.obj (op .edge) // endptOf X false t = a ∧ endptOf X true t = b}

/-- A bigon vertex of a 2-cell of `X`, as a 0-cell. -/
def objOfVtx {m n : ℕ} (v : BigonVtx m n) (c : X.obj (op (.cell m n))) : GenObj (genOfPsh X) :=
  ⟨vtxOf X v c⟩

/-- The `i`-th vertex of a 2-cell's source string, clamped past the end. -/
def srcVtxOf {m n : ℕ} (c : X.obj (op (.cell m n))) (i : ℕ) : GenObj (genOfPsh X) :=
  objOfVtx X (BigonVtx.mk (.inl ⟨min i m, Nat.lt_succ_of_le (Nat.min_le_right i m)⟩)) c

/-- The `j`-th vertex of a 2-cell's target string, clamped past the end. -/
def tgtVtxOf {m n : ℕ} (c : X.obj (op (.cell m n))) (j : ℕ) : GenObj (genOfPsh X) :=
  objOfVtx X (BigonVtx.mk (.inr ⟨min j n, Nat.lt_succ_of_le (Nat.min_le_right j n)⟩)) c

theorem srcVtxOf_of_le {m n : ℕ} (c : X.obj (op (.cell m n))) {i : ℕ} (hi : i ≤ m)
    (h : i < m + 1 := by omega) : srcVtxOf X c i = objOfVtx X (BigonVtx.mk (.inl ⟨i, h⟩)) c :=
  congrArg (fun k : Fin (m + 1) => objOfVtx X (BigonVtx.mk (.inl k)) c)
    (Fin.ext (Nat.min_eq_left hi))

theorem tgtVtxOf_of_le {m n : ℕ} (c : X.obj (op (.cell m n))) {j : ℕ} (hj : j ≤ n)
    (h : j < n + 1 := by omega) : tgtVtxOf X c j = objOfVtx X (BigonVtx.mk (.inr ⟨j, h⟩)) c :=
  congrArg (fun k : Fin (n + 1) => objOfVtx X (BigonVtx.mk (.inr k)) c)
    (Fin.ext (Nat.min_eq_left hj))

theorem srcVtxOf_zero {m n : ℕ} (c : X.obj (op (.cell m n))) :
    srcVtxOf X c 0 = objOfVtx X (BigonVtx.start m n) c :=
  srcVtxOf_of_le X c (Nat.zero_le m)

theorem srcVtxOf_last {m n : ℕ} (c : X.obj (op (.cell m n))) :
    srcVtxOf X c m = objOfVtx X (BigonVtx.finish m n) c :=
  srcVtxOf_of_le X c (Nat.le_refl m)

theorem tgtVtxOf_zero {m n : ℕ} (c : X.obj (op (.cell m n))) :
    tgtVtxOf X c 0 = objOfVtx X (BigonVtx.start m n) c := by
  rw [tgtVtxOf_of_le X c (Nat.zero_le n), BigonVtx.start_eq]

theorem tgtVtxOf_last {m n : ℕ} (c : X.obj (op (.cell m n))) :
    tgtVtxOf X c n = objOfVtx X (BigonVtx.finish m n) c := by
  rw [tgtVtxOf_of_le X c (Nat.le_refl n), BigonVtx.finish_eq]; rfl

/-- The `i`-th letter of a 2-cell's source string. -/
def srcHomOf {m n : ℕ} (c : X.obj (op (.cell m n))) (i : ℕ) (h : i < m) :
    srcVtxOf X c i ⟶ srcVtxOf X c (i + 1) :=
  ⟨edgOf X (.inl ⟨i, h⟩) c, by
      rw [srcVtxOf_of_le X c h.le]; exact endpt_edgOf X false (.inl ⟨i, h⟩) c, by
      rw [srcVtxOf_of_le X c h]; exact endpt_edgOf X true (.inl ⟨i, h⟩) c⟩

/-- The `j`-th letter of a 2-cell's target string. -/
def tgtHomOf {m n : ℕ} (c : X.obj (op (.cell m n))) (j : ℕ) (h : j < n) :
    tgtVtxOf X c j ⟶ tgtVtxOf X c (j + 1) :=
  ⟨edgOf X (.inr ⟨j, h⟩) c, by
      rw [tgtVtxOf_of_le X c h.le]; exact endpt_edgOf X false (.inr ⟨j, h⟩) c, by
      rw [tgtVtxOf_of_le X c h]; exact endpt_edgOf X true (.inr ⟨j, h⟩) c⟩

/-- The source word of a 2-cell of `X`. -/
def srcPathOf {m n : ℕ} (c : X.obj (op (.cell m n))) :
    Quiver.Path (srcVtxOf X c 0) (srcVtxOf X c m) :=
  Quiver.Path.ofCoords (srcVtxOf X c) m (srcHomOf X c)

/-- The target word of a 2-cell of `X`. -/
def tgtPathOf {m n : ℕ} (c : X.obj (op (.cell m n))) :
    Quiver.Path (tgtVtxOf X c 0) (tgtVtxOf X c n) :=
  Quiver.Path.ofCoords (tgtVtxOf X c) n (tgtHomOf X c)

/-- The 2-cells of the polygraph a presheaf carries. -/
structure RelOfPsh (a b : GenObj (genOfPsh X)) : Type u where
  /-- the source boundary length -/
  m : ℕ
  /-- the target boundary length -/
  n : ℕ
  /-- the 2-cell of `X` -/
  c : X.obj (op (.cell m n))
  /-- …whose boundary starts at `a` -/
  hx : objOfVtx X (BigonVtx.start m n) c = a
  /-- …and finishes at `b` -/
  hy : objOfVtx X (BigonVtx.finish m n) c = b

/-- **The polygraph a presheaf carries.** -/
def ofPsh : Polygraph.{u, u, u} where
  V := X.obj (op .pt)
  Gen := genOfPsh X
  Rel := RelOfPsh X
  src r := (srcPathOf X r.c).castPath ((srcVtxOf_zero X r.c).trans r.hx)
    ((srcVtxOf_last X r.c).trans r.hy)
  tgt r := (tgtPathOf X r.c).castPath ((tgtVtxOf_zero X r.c).trans r.hx)
    ((tgtVtxOf_last X r.c).trans r.hy)

@[simp] theorem length_src_ofPsh {a b : GenObj (genOfPsh X)} (r : RelOfPsh X a b) :
    ((ofPsh X).src r).length = r.m :=
  (Quiver.Path.length_castPath ..).trans (Quiver.Path.length_ofCoords ..)

@[simp] theorem length_tgt_ofPsh {a b : GenObj (genOfPsh X)} (r : RelOfPsh X a b) :
    ((ofPsh X).tgt r).length = r.n :=
  (Quiver.Path.length_castPath ..).trans (Quiver.Path.length_ofCoords ..)

/-- A 0-cell of `X`, read as a 0-cell. -/
def fromPt (a : X.obj (op .pt)) : GenObj (genOfPsh X) := ⟨a⟩

/-- A 1-cell of `X`, read as a 1-cell. -/
def fromEdge (t : X.obj (op .edge)) : Total (GenObj (genOfPsh X)) :=
  ⟨⟨endptOf X false t⟩, ⟨endptOf X true t⟩, ⟨t, rfl, rfl⟩⟩

/-- A 2-cell of `X`, read as a shaped cell. -/
def fromCell {m n : ℕ} (c : X.obj (op (.cell m n))) : ShapedCell (ofPsh X) m n where
  x := objOfVtx X (BigonVtx.start m n) c
  y := objOfVtx X (BigonVtx.finish m n) c
  cell := ⟨m, n, c, rfl, rfl⟩
  len_src := length_src_ofPsh X _
  len_tgt := length_tgt_ofPsh X _

/-- **The cells of `X`, read as cells of the polygraph it carries.** -/
def fromPsh : (Y : PolyShape) → X.obj (op Y) → cellsObj (ofPsh X) Y
  | .pt => fromPt X
  | .edge => fromEdge X
  | .cell _ _ => fromCell X

/-- The 1-cell underlying an arrow of the quiver a presheaf carries. -/
def totalVal (t : Total (GenObj (genOfPsh X))) : X.obj (op .edge) :=
  (t.hom : genOfPsh X t.left.as t.right.as).1

/-- **An arrow of the quiver a presheaf carries is its 1-cell** — the endpoints are read off it. -/
theorem total_ext_of_val {t u : Total (GenObj (genOfPsh X))} (h : totalVal X t = totalVal X u) :
    t = u := by
  obtain ⟨a, b, s, hs₁, hs₂⟩ := t
  obtain ⟨a', b', s', hs₁', hs₂'⟩ := u
  obtain rfl : s = s' := h
  obtain rfl : a = a' := GenObj.ext (hs₁.symm.trans hs₁')
  obtain rfl : b = b' := GenObj.ext (hs₂.symm.trans hs₂')
  rfl

theorem vtx_fromCell {m n : ℕ} (c : X.obj (op (.cell m n))) (v : BigonVtx m n) :
    (fromCell X c).vtx v = objOfVtx X v c := by
  induction v using BigonVtx.ind with
  | h w =>
      cases w with
      | inl i =>
          have h : (fromCell X c).vtx (BigonVtx.mk (.inl i))
              = ((Quiver.Path.ofCoords (srcVtxOf X c) m (srcHomOf X c)).castPath
                  (srcVtxOf_zero X c) (srcVtxOf_last X c)).vtx (i : ℕ) := rfl
          rw [h, Quiver.Path.vtx_castPath,
            Quiver.Path.vtx_ofCoords _ _ _ (Nat.lt_succ_iff.1 i.isLt)]
          exact srcVtxOf_of_le X c (Nat.lt_succ_iff.1 i.isLt)
      | inr j =>
          have h : (fromCell X c).vtx (BigonVtx.mk (.inr j))
              = ((Quiver.Path.ofCoords (tgtVtxOf X c) n (tgtHomOf X c)).castPath
                  (tgtVtxOf_zero X c) (tgtVtxOf_last X c)).vtx (j : ℕ) := rfl
          rw [h, Quiver.Path.vtx_castPath,
            Quiver.Path.vtx_ofCoords _ _ _ (Nat.lt_succ_iff.1 j.isLt)]
          exact tgtVtxOf_of_le X c (Nat.lt_succ_iff.1 j.isLt)

theorem edg_fromCell {m n : ℕ} (c : X.obj (op (.cell m n))) (e : BigonEdge m n) :
    (fromCell X c).edg e = fromEdge X (edgOf X e c) := by
  cases e with
  | inl i =>
      have h₁ : (fromCell X c).edg (.inl i)
          = ((Quiver.Path.ofCoords (srcVtxOf X c) m (srcHomOf X c)).castPath
              (srcVtxOf_zero X c) (srcVtxOf_last X c)).edgeAt (i : ℕ) (by simp) := rfl
      have h₂ : ((Quiver.Path.ofCoords (srcVtxOf X c) m (srcHomOf X c)).castPath
              (srcVtxOf_zero X c) (srcVtxOf_last X c)).edgeAt (i : ℕ) (by simp)
          = (Quiver.Path.ofCoords (srcVtxOf X c) m (srcHomOf X c)).edgeAt (i : ℕ) (by simp) :=
        Quiver.Path.edgeAt_castPath _ _ _ _ _ _
      have h₃ : (Quiver.Path.ofCoords (srcVtxOf X c) m (srcHomOf X c)).edgeAt (i : ℕ) (by simp)
          = ⟨srcVtxOf X c (i : ℕ), srcVtxOf X c ((i : ℕ) + 1), srcHomOf X c (i : ℕ) i.isLt⟩ :=
        Quiver.Path.edgeAt_ofCoords _ _ _ i.isLt _
      exact ((h₁.trans h₂).trans h₃).trans (total_ext_of_val X rfl)
  | inr j =>
      have h₁ : (fromCell X c).edg (.inr j)
          = ((Quiver.Path.ofCoords (tgtVtxOf X c) n (tgtHomOf X c)).castPath
              (tgtVtxOf_zero X c) (tgtVtxOf_last X c)).edgeAt (j : ℕ) (by simp) := rfl
      have h₂ : ((Quiver.Path.ofCoords (tgtVtxOf X c) n (tgtHomOf X c)).castPath
              (tgtVtxOf_zero X c) (tgtVtxOf_last X c)).edgeAt (j : ℕ) (by simp)
          = (Quiver.Path.ofCoords (tgtVtxOf X c) n (tgtHomOf X c)).edgeAt (j : ℕ) (by simp) :=
        Quiver.Path.edgeAt_castPath _ _ _ _ _ _
      have h₃ : (Quiver.Path.ofCoords (tgtVtxOf X c) n (tgtHomOf X c)).edgeAt (j : ℕ) (by simp)
          = ⟨tgtVtxOf X c (j : ℕ), tgtVtxOf X c ((j : ℕ) + 1), tgtHomOf X c (j : ℕ) j.isLt⟩ :=
        Quiver.Path.edgeAt_ofCoords _ _ _ j.isLt _
      exact ((h₁.trans h₂).trans h₃).trans (total_ext_of_val X rfl)

theorem fromPsh_naturality {Y Z : PolyShape} (u : Y ⟶ Z) (c : X.obj (op Z)) :
    fromPsh X Y (X.map (Quiver.Hom.op u) c) = cellsMap (ofPsh X) u (fromPsh X Z c) := by
  cases u with
  | id Y => exact congrArg (fromPsh X Y) (ConcreteCategory.congr_hom (X.map_id (op Y)) c)
  | end_ b => cases b <;> rfl
  | vtx v => exact (vtx_fromCell X c v).symm
  | edg e => exact (edg_fromCell X c e).symm

/-- The 2-cell of `X` a shaped cell of the polygraph it carries came from. -/
def toCell {m n : ℕ} (s : ShapedCell (ofPsh X) m n) : X.obj (op (.cell m n)) :=
  cast (by rw [(length_src_ofPsh X s.cell).symm.trans s.len_src,
    (length_tgt_ofPsh X s.cell).symm.trans s.len_tgt]) s.cell.c

theorem bijective_fromPsh (Y : PolyShape) : Function.Bijective (fromPsh X Y) := by
  cases Y with
  | pt => exact ⟨fun _ _ h => congrArg GenObj.as h, fun g => ⟨g.as, rfl⟩⟩
  | edge =>
      exact ⟨Function.LeftInverse.injective (g := totalVal X) fun _ => rfl,
        fun t => ⟨totalVal X t, total_ext_of_val X rfl⟩⟩
  | cell m n =>
      refine ⟨Function.LeftInverse.injective (g := toCell X) fun _ => rfl, ?_⟩
      rintro ⟨a, b, ⟨m', n', c, hx, hy⟩, hs, ht⟩
      obtain rfl : m' = m := (length_src_ofPsh X _).symm.trans hs
      obtain rfl : n' = n := (length_tgt_ofPsh X _).symm.trans ht
      subst hx; subst hy
      exact ⟨c, rfl⟩

/-- **Every presheaf on `PolyShape` is the cells of a polygraph.** -/
noncomputable def isoFromPsh : X ≅ cellsPsh (ofPsh X) :=
  NatIso.ofComponents (fun s => (Equiv.ofBijective _ (bijective_fromPsh X s.unop)).toIso)
    (fun f => by ext c; exact fromPsh_naturality X f.unop c)

end OfPsh

instance : polyToPsh.{u}.EssSurj where
  mem_essImage X := ⟨ofPsh X, ⟨(isoFromPsh X).symm⟩⟩

instance : polyToPsh.{u}.IsEquivalence where

/-! ## The theorem, and what it buys -/

/-- **2-polygraphs are a presheaf topos** — Schanuel's theorem, by Carboni–Johnstone's route. -/
noncomputable def polyEquivPresheaf : Polygraph.{u, u, u} ≌ (PolyShapeᵒᵖ ⥤ Type u) :=
  polyToPsh.asEquivalence

/-- Polygraphs have every colimit the coefficients have. -/
instance hasColimitsOfShape (J : Type*) [Category* J] [HasColimitsOfShape J (Type u)] :
    HasColimitsOfShape J Polygraph.{u, u, u} :=
  Adjunction.hasColimitsOfShape_of_equivalence polyToPsh

/-- Polygraphs have every limit the coefficients have. -/
instance hasLimitsOfShape (J : Type*) [Category* J] [HasLimitsOfShape J (Type u)] :
    HasLimitsOfShape J Polygraph.{u, u, u} :=
  Adjunction.hasLimitsOfShape_of_equivalence polyToPsh

/-- **All colimits**, on the universe diagonal — which is where a `Type u`-valued presheaf puts
them: 0-, 1- and 2-cells are seen in one universe. -/
instance hasColimitsOfSize : HasColimitsOfSize.{u, u} Polygraph.{u, u, u} where

/-- **All limits**, likewise. -/
instance hasLimitsOfSize : HasLimitsOfSize.{u, u} Polygraph.{u, u, u} where

/-- The `s`-cells of a polygraph. -/
def cellsAt (s : PolyShape) : Polygraph.{u, u, u} ⥤ Type u :=
  polyToPsh ⋙ (evaluation PolyShapeᵒᵖ (Type u)).obj (op s)

@[simp] theorem cellsAt_obj (s : PolyShape) (P : Polygraph.{u, u, u}) :
    (cellsAt s).obj P = cellsObj P s := rfl

/-- **A colimit of polygraphs is cellwise**: its 0-, 1- and 2-cells are the colimits of those. -/
noncomputable instance (s : PolyShape) : PreservesColimitsOfSize.{u, u} (cellsAt.{u} s) := by
  unfold cellsAt; infer_instance

/-- **A limit of polygraphs is cellwise.** -/
noncomputable instance (s : PolyShape) : PreservesLimitsOfSize.{u, u} (cellsAt.{u} s) := by
  unfold cellsAt; infer_instance

noncomputable example : Polygraph.{0, 0, 0} ≌ (PolyShapeᵒᵖ ⥤ Type) := polyEquivPresheaf

example : HasCoequalizers Polygraph.{u, u, u} := inferInstance
example : HasPushouts Polygraph.{u, u, u} := inferInstance
example : HasEqualizers Polygraph.{u, u, u} := inferInstance
example : HasCoproducts.{u} Polygraph.{u, u, u} := inferInstance
example : HasProducts.{u} Polygraph.{u, u, u} := inferInstance
example : HasColimits Polygraph.{u, u, u} := inferInstance
example : HasLimits Polygraph.{u, u, u} := inferInstance

end Polygraph

end CategoryTheory
