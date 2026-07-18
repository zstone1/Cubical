import CubeChains.Foundations.BoxMonoidal

/-!
# Foundations/GeoTensor — the computable geometric tensor

The geometric (parallel) product of precubical sets, built from the concrete closed form of the
Day coend rather than mathlib's noncomputable Day convolution.  Because the box tensor is
coordinate concatenation (`▫m ⊗ ▫n = ▫(m+n)`, X-coords then Y-coords), a cell of `▫(p+q)` splits
uniquely into its `Fin p`-block and `Fin q`-block, so the coend collapses to

    (X ⊗ Y)(▫n)  =  Σ (p q : ℕ) (_ : p + q = n),  X(▫p) × Y(▫q)

with restriction = split the cell into its two blocks and restrict each half.
-/

open CategoryTheory Opposite StdCube

namespace GeoTensor

/-- Cells of the geometric tensor in degree `n`: a `p`-cell of `X` and a `q`-cell of `Y`
with `p + q = n`. -/
structure tensorCells (X Y : PrecubicalSet) (n : ℕ) where
  /-- Dimension carried by the `X`-half. -/
  p : ℕ
  /-- Dimension carried by the `Y`-half. -/
  q : ℕ
  /-- The two halves fill the total dimension. -/
  hpq : p + q = n
  /-- The `X`-cell. -/
  x : X.obj (op ▫p)
  /-- The `Y`-cell. -/
  y : Y.obj (op ▫q)

/-- Structure equality for `tensorCells`, reduced to the dimensions and the two half-cells. -/
theorem tensorCells_ext {X Y : PrecubicalSet} {n : ℕ} {c d : tensorCells X Y n}
    (hp : c.p = d.p) (hq : c.q = d.q) (hx : HEq c.x d.x) (hy : HEq c.y d.y) : c = d := by
  cases c with
  | mk cp cq chpq cx cy =>
    cases d with
    | mk dp dq dhpq dx dy =>
      cases hp
      cases hq
      cases eq_of_heq hx
      cases eq_of_heq hy
      rfl

/-! ### Restriction of a presheaf cell by a sign vector -/

/-- Restrict `x : X(▫p)` along the sign vector `c : Cell p a`, i.e. by the classified map
`ofSign c : ▫a ⟶ ▫p`. -/
def restr (X : PrecubicalSet) {p a : ℕ} (x : X.obj (op ▫p)) (c : Cell p a) : X.obj (op ▫a) :=
  X.map (Box.ofSign c).op x

theorem restr_topCell (X : PrecubicalSet) {p : ℕ} (x : X.obj (op ▫p)) :
    restr X x (topCell p) = x := by
  have h : Box.ofSign (topCell p) = 𝟙 (▫p) := Box.hom_ext (by rw [Box.sign_ofSign, Box.sign_id])
  rw [restr, h, op_id, Functor.map_id_apply]

theorem restr_comp (X : PrecubicalSet) {p a a' : ℕ} (x : X.obj (op ▫p)) (c : Cell p a)
    (d : Cell a a') : restr X (restr X x c) d = restr X x (subst c d) := by
  have hs : Box.ofSign d ≫ Box.ofSign c = Box.ofSign (subst c d) :=
    Box.hom_ext (by rw [Box.sign_comp, Box.sign_ofSign, Box.sign_ofSign, Box.sign_ofSign])
  change X.map (Box.ofSign d).op (X.map (Box.ofSign c).op x) = X.map (Box.ofSign (subst c d)).op x
  rw [← Functor.map_comp_apply, ← op_comp, hs]

/-- `restr` is a congruence in its cell argument (across differing target dimension). -/
theorem restr_heq (X : PrecubicalSet) {p a a' : ℕ} (x : X.obj (op ▫p)) {c : Cell p a}
    {c' : Cell p a'} (ha : a = a') (h : HEq c c') : HEq (restr X x c) (restr X x c') := by
  cases ha
  cases eq_of_heq h
  rfl

/-- Restricting by an all-`none` sign vector is the identity (heterogeneously, as the
target dimension is a priori only propositionally the source dimension). -/
theorem restr_allNone (X : PrecubicalSet) {p a : ℕ} {c : Cell p a} (hc : AllNone c)
    (x : X.obj (op ▫p)) : HEq (restr X x c) x := by
  have ha : a = p := (allNone_dim hc).symm
  subst ha
  rw [eq_topCell c]
  exact heq_of_eq (restr_topCell X x)

/-! ### Cast of the ambient dimension, and the two coordinate blocks -/

/-- Reindex a cell along `p + q = N`. -/
def recast {p q k N : ℕ} (h : p + q = N) (s : Cell N k) : Cell (p + q) k :=
  ⟨s.val ∘ Fin.cast h, by subst h; exact s.prop⟩

@[simp] theorem recast_val {p q k N : ℕ} (h : p + q = N) (s : Cell N k) :
    (recast h s).val = s.val ∘ Fin.cast h := rfl

/-- A `recast` along any proof of a reflexive equation is the identity. -/
theorem recast_eq {p q k : ℕ} (h : p + q = p + q) (s : Cell (p + q) k) : recast h s = s := by
  apply Subtype.ext
  funext j
  rfl

/-- A `recast` is heterogeneously the original cell. -/
theorem recast_heq {p q k N : ℕ} (h : p + q = N) (s : Cell N k) : HEq (recast h s) s := by
  subst h
  exact heq_of_eq (recast_eq _ s)

theorem allNone_recast {p q k N : ℕ} (h : p + q = N) {s : Cell N k} (hs : AllNone s) :
    AllNone (recast h s) := fun _ => hs _

/-- The `Fin p`-block of a cell of `▫(p+q)`. -/
def splitLeft {p q k : ℕ} (s : Cell (p + q) k) :
    Cell p (noneSet (fun i => s.val (Fin.castAdd q i))).card :=
  ⟨fun i => s.val (Fin.castAdd q i), rfl⟩

/-- The `Fin q`-block of a cell of `▫(p+q)`. -/
def splitRight {p q k : ℕ} (s : Cell (p + q) k) :
    Cell q (noneSet (fun i => s.val (Fin.natAdd p i))).card :=
  ⟨fun i => s.val (Fin.natAdd p i), rfl⟩

@[simp] theorem splitLeft_val {p q k : ℕ} (s : Cell (p + q) k) :
    (splitLeft s).val = fun i => s.val (Fin.castAdd q i) := rfl

@[simp] theorem splitRight_val {p q k : ℕ} (s : Cell (p + q) k) :
    (splitRight s).val = fun i => s.val (Fin.natAdd p i) := rfl

/-- Reassembling the two blocks of a cell recovers it (as a `.val` equation). -/
theorem append_split {p q k : ℕ} (s : Cell (p + q) k) :
    Fin.append (fun i => s.val (Fin.castAdd q i)) (fun i => s.val (Fin.natAdd p i)) = s.val :=
  Fin.append_castAdd_natAdd

/-- The two block dimensions add up to the total. -/
theorem splitLeft_dim_add {p q k : ℕ} (s : Cell (p + q) k) :
    (noneSet (fun i => s.val (Fin.castAdd q i))).card
      + (noneSet (fun i => s.val (Fin.natAdd p i))).card = k := by
  rw [← card_noneSet_append, append_split]; exact s.prop

/-- Two cells with equal underlying vector are heterogeneously equal. -/
theorem cell_heq_of_val {N k k' : ℕ} {c : Cell N k} {d : Cell N k'} (hv : c.val = d.val) :
    HEq c d := by
  have hk : k = k' := by rw [← c.prop, ← d.prop, hv]
  cases hk
  exact heq_of_eq (Subtype.ext hv)

/-- `subst` is a congruence for heterogeneous equality of its two cell arguments. -/
theorem subst_heq {N n n' k k' : ℕ} (hn : n = n') (hk : k = k') {c : Cell N n} {c' : Cell N n'}
    {a : Cell n k} {a' : Cell n' k'} (hc : HEq c c') (ha : HEq a a') :
    HEq (subst c a) (subst c' a') := by
  cases hn
  cases hk
  cases eq_of_heq hc
  cases eq_of_heq ha
  rfl

/-! ### The restriction operation on tensor cells -/

/-- Restrict the product cell `(x, y)` along the sign vector `s : Cell (p+q) k`: split `s` into
its two coordinate blocks and restrict each half. -/
def restrictAux (X Y : PrecubicalSet) {p q k : ℕ} (s : Cell (p + q) k)
    (x : X.obj (op ▫p)) (y : Y.obj (op ▫q)) : tensorCells X Y k where
  p := (noneSet (fun i => s.val (Fin.castAdd q i))).card
  q := (noneSet (fun i => s.val (Fin.natAdd p i))).card
  hpq := by rw [← card_noneSet_append, append_split]; exact s.prop
  x := restr X x (splitLeft s)
  y := restr Y y (splitRight s)

/-- Restricting along a concatenated sign vector is restricting each half separately. -/
theorem restrictAux_appendCell (X Y : PrecubicalSet) {p q k₁ k₂ : ℕ} (c₁ : Cell p k₁)
    (c₂ : Cell q k₂) (x : X.obj (op ▫p)) (y : Y.obj (op ▫q)) :
    restrictAux X Y (appendCell c₁ c₂) x y = ⟨k₁, k₂, rfl, restr X x c₁, restr Y y c₂⟩ := by
  have hleft : (fun i => (appendCell c₁ c₂).val (Fin.castAdd q i)) = c₁.val := by
    funext i; rw [appendCell_val, Fin.append_left]
  have hright : (fun i => (appendCell c₁ c₂).val (Fin.natAdd p i)) = c₂.val := by
    funext i; rw [appendCell_val, Fin.append_right]
  refine tensorCells_ext ?_ ?_ ?_ ?_
  · change (noneSet (fun i => (appendCell c₁ c₂).val (Fin.castAdd q i))).card = k₁
    rw [hleft, c₁.prop]
  · change (noneSet (fun i => (appendCell c₁ c₂).val (Fin.natAdd p i))).card = k₂
    rw [hright, c₂.prop]
  · exact restr_heq X x (by rw [hleft, c₁.prop]) (cell_heq_of_val hleft)
  · exact restr_heq Y y (by rw [hright, c₂.prop]) (cell_heq_of_val hright)

/-- `restrictAux` is a congruence for heterogeneous equality of its sign vector. -/
theorem restrictAux_heq (X Y : PrecubicalSet) {p q k k' : ℕ} (hk : k = k') {s : Cell (p + q) k}
    {s' : Cell (p + q) k'} (hs : HEq s s') (x : X.obj (op ▫p)) (y : Y.obj (op ▫q)) :
    HEq (restrictAux X Y s x y) (restrictAux X Y s' x y) := by
  cases hk
  cases eq_of_heq hs
  rfl


/-- Restricting an all-`none` sign vector is the identity (up to the forced dimension equation). -/
theorem restrictAux_allNone (X Y : PrecubicalSet) {p q k : ℕ} {s : Cell (p + q) k}
    (hs : AllNone s) (x : X.obj (op ▫p)) (y : Y.obj (op ▫q)) :
    restrictAux X Y s x y = ⟨p, q, allNone_dim hs, x, y⟩ := by
  have hsl : AllNone (splitLeft s) := fun _ => hs _
  have hsr : AllNone (splitRight s) := fun _ => hs _
  exact tensorCells_ext (allNone_dim hsl).symm (allNone_dim hsr).symm
    (restr_allNone X hsl x) (restr_allNone Y hsr y)

/-- Functoriality of restriction: restricting first by `sf` and then by `sg` is restricting by
the composite sign vector `subst sf sg`.  The two coordinate blocks compose independently
(`subst_appendCell`). -/
theorem restrictAux_comp (X Y : PrecubicalSet) {p q N kf kg : ℕ} (h : p + q = N) (sf : Cell N kf)
    (sg : Cell kf kg) (x : X.obj (op ▫p)) (y : Y.obj (op ▫q)) :
    restrictAux X Y (recast (restrictAux X Y (recast h sf) x y).hpq sg)
        (restrictAux X Y (recast h sf) x y).x (restrictAux X Y (recast h sf) x y).y
      = restrictAux X Y (recast h (subst sf sg)) x y := by
  subst h
  simp only [recast_eq]
  change restrictAux X Y (recast (restrictAux X Y sf x y).hpq sg)
      (restr X x (splitLeft sf)) (restr Y y (splitRight sf))
    = restrictAux X Y (subst sf sg) x y
  set rc := recast (restrictAux X Y sf x y).hpq sg with hrc
  -- Both sides restrict along genuine concatenations of the two coordinate blocks.
  have hrec : HEq rc sg := by rw [hrc]; exact recast_heq (restrictAux X Y sf x y).hpq sg
  have hsL : HEq rc (appendCell (splitLeft rc) (splitRight rc)) :=
    cell_heq_of_val (by rw [appendCell_val]; exact (append_split rc).symm)
  have hsR : HEq (subst sf sg)
      (appendCell (subst (splitLeft sf) (splitLeft rc))
        (subst (splitRight sf) (splitRight rc))) := by
    have h1 : HEq (subst sf sg)
        (subst (appendCell (splitLeft sf) (splitRight sf))
          (appendCell (splitLeft rc) (splitRight rc))) :=
      subst_heq (splitLeft_dim_add sf).symm (splitLeft_dim_add rc).symm
        (cell_heq_of_val (by rw [appendCell_val]; exact (append_split sf).symm))
        (hrec.symm.trans hsL)
    rwa [subst_appendCell] at h1
  apply eq_of_heq
  refine HEq.trans
    (restrictAux_heq X Y (splitLeft_dim_add rc).symm hsL (restr X x (splitLeft sf))
      (restr Y y (splitRight sf))) ?_
  refine HEq.trans ?_ (HEq.symm
    (restrictAux_heq X Y (splitLeft_dim_add rc).symm hsR x y))
  rw [restrictAux_appendCell, restrictAux_appendCell, restr_comp, restr_comp]
  rfl

/-! ### The geometric tensor presheaf -/

/-- The geometric tensor object as a presheaf: restriction splits the cell into two blocks
and restricts each half. -/
def tensorObj (X Y : PrecubicalSet) : PrecubicalSet where
  obj B := tensorCells X Y B.unop.dim
  map {B _} f := TypeCat.ofHom
    (fun (c : tensorCells X Y B.unop.dim) =>
      restrictAux X Y (recast c.hpq (Box.sign f.unop)) c.x c.y)
  map_id := by
    intro B
    apply ConcreteCategory.hom_ext
    intro c
    change restrictAux X Y (recast c.hpq (Box.sign (𝟙 B).unop)) c.x c.y = c
    rw [unop_id, Box.sign_id,
      restrictAux_allNone X Y (allNone_recast c.hpq (allNone_topCell _)) c.x c.y]
  map_comp := by
    intro B B' B'' f g
    apply ConcreteCategory.hom_ext
    intro c
    change restrictAux X Y (recast c.hpq (Box.sign (f ≫ g).unop)) c.x c.y
      = restrictAux X Y (recast (restrictAux X Y (recast c.hpq (Box.sign f.unop)) c.x c.y).hpq
          (Box.sign g.unop))
          (restrictAux X Y (recast c.hpq (Box.sign f.unop)) c.x c.y).x
          (restrictAux X Y (recast c.hpq (Box.sign f.unop)) c.x c.y).y
    rw [unop_comp, Box.sign_comp]
    exact (restrictAux_comp X Y c.hpq (Box.sign f.unop) (Box.sign g.unop) c.x c.y).symm

/-! ### Convenience API -/

@[simp] theorem tensorObj_obj (X Y : PrecubicalSet) (B : Boxᵒᵖ) :
    (tensorObj X Y).obj B = tensorCells X Y B.unop.dim := rfl

@[simp] theorem tensorObj_map (X Y : PrecubicalSet) {B B' : Boxᵒᵖ} (f : B ⟶ B')
    (c : tensorCells X Y B.unop.dim) :
    (tensorObj X Y).map f c = restrictAux X Y (recast c.hpq (Box.sign f.unop)) c.x c.y := rfl

/-- The product cell of a `p`-cell of `X` and a `q`-cell of `Y`. -/
def pair (X Y : PrecubicalSet) {p q : ℕ} (x : X.obj (op ▫p)) (y : Y.obj (op ▫q)) :
    (tensorObj X Y).obj (op ▫(p + q)) :=
  ⟨p, q, rfl, x, y⟩

/-- Restriction of a product cell: split the sign vector into its two blocks and restrict each
half separately. -/
theorem map_pair (X Y : PrecubicalSet) {p q : ℕ} {B' : Boxᵒᵖ} (f : op ▫(p + q) ⟶ B')
    (x : X.obj (op ▫p)) (y : Y.obj (op ▫q)) :
    (tensorObj X Y).map f (pair X Y x y) = restrictAux X Y (Box.sign f.unop) x y := by
  change restrictAux X Y (recast rfl (Box.sign f.unop)) x y = _
  rw [recast_eq]

end GeoTensor
