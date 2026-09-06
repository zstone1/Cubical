import CubeChains.Testing.H.HTwo
import CubeChains.Machinery.Cube.SymRepresentable
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Testing/H/HBar — the natural maps between powers of `H`

`H = symFree ⋙ symRestrict` carries the monad structure of `symFreeAdj`.  Its multiplication is
`(τ, σ, y) ↦ (σ * τ, y)` (`Hmul_app`) — the shear coordinate of `Testing/H/HTwo` — and it is the
*only* natural transformation `H² ⟶ H` (`Hmul_unique`): the bar construction's degree `1` carries
a single face.  Degree `2` carries two, `μ_{HK}` and `H μ_K`, and they differ
(`HmulOuter_ne_HmulInner`).

The closing computation counts `Nat(H^a, H^b) = (2 (a + 1)) ^ (b - 1)` — the monad has more
natural operations than `η` and `μ` generate, the extra ones twisting by the longest element.

Not built by `lake build CubeChains`.
-/

open CategoryTheory Opposite StdCube

namespace CubeChains

/-! ## The counit, and the multiplication -/

/-- The counit is the descent of the identity — `symFree_hom_ext` plus the triangle law. -/
theorem symFreeAdj_counit_app (G : SymPrecubicalSet) :
    symFreeAdj.counit.app G = symDesc G (𝟙 (symRestrict.obj G)) :=
  symFree_hom_ext <|
    (symFreeAdj_unit_app (symRestrict.obj G) ▸ symFreeAdj.right_triangle_components G).trans
      (symUnit_symDesc G (𝟙 (symRestrict.obj G))).symm

/-- The multiplication of the monad `H`. -/
noncomputable def Hmul : H ⋙ H ⟶ H :=
  Functor.whiskerRight (Functor.whiskerLeft symFree symFreeAdj.counit) symRestrict

theorem Hmul_eq_monad_mul : Hmul = symFreeAdj.toMonad.μ := rfl

/-- `H` on maps leaves the order alone. -/
theorem H_map_app {K L : PrecubicalSet} (f : K ⟶ L) {m : ℕ}
    (σ : Equiv.Perm (Fin m)) (y : K.obj (op ▫m)) :
    (H.map f).app (op ▫m) ((σ, y) : (H.obj K).obj (op ▫m))
      = ((σ, f.app (op ▫m) y) : (H.obj L).obj (op ▫m)) := rfl

/-- **The multiplication composes the two orders**: the outer order `τ` is performed first. -/
theorem Hmul_app {K : PrecubicalSet} {m : ℕ} (τ σ : Equiv.Perm (Fin m)) (y : K.obj (op ▫m)) :
    (Hmul.app K).app (op ▫m) ((τ, σ, y) : ((H ⋙ H).obj K).obj (op ▫m))
      = ((σ * τ, y) : (H.obj K).obj (op ▫m)) := by
  have h : (Hmul.app K).app (op ▫m) ((τ, σ, y) : ((H ⋙ H).obj K).obj (op ▫m))
      = (symFree.obj K).map (symHom τ).op ((σ, y) : (symFree.obj K).obj (op ▪m)) := by
    change (symFreeAdj.counit.app (symFree.obj K)).app (op ▪m) _ = _
    rw [symFreeAdj_counit_app]
    rfl
  rw [h, symFree_obj_map_symHom]
  rfl

/-! ## Edges see every axis

An edge carries no order (`Perm (Fin 1)` is trivial), so sorting one through `ρ` *is*
post-composition with `symHom ρ`, and the axis it performs moves by `ρ`. -/

/-- The edge of `□ⁿ` freeing exactly the coordinate `i`. -/
def edgeCell (n : ℕ) (i : Fin n) : Cell n 1 :=
  ⟨Function.update (fun _ => some false) i none, by
    rw [noneSet_update_none]
    have h : noneSet (fun _ : Fin n => some false) = ∅ := by
      ext j; simp [mem_noneSet]
    rw [h]
    simp⟩

/-- …as a box map. -/
def edge (n : ℕ) (i : Fin n) : ▫1 ⟶ ▫n := Box.ofSign (edgeCell n i)

theorem noneSet_edgeCell (n : ℕ) (i : Fin n) : noneSet (edgeCell n i).val = {i} := by
  change noneSet (Function.update (fun _ : Fin n => some false) i none) = {i}
  rw [noneSet_update_none]
  have h : noneSet (fun _ : Fin n => some false) = ∅ := by
    ext j; simp [mem_noneSet]
  rw [h]
  simp

@[simp] theorem faceEmb_edge (n : ℕ) (i : Fin n) : faceEmb (edge n i) 0 = i := by
  have hmem : nones (edgeCell n i) 0 ∈ noneSet (edgeCell n i).val :=
    Finset.orderEmbOfFin_mem _ (edgeCell n i).prop 0
  rw [noneSet_edgeCell, Finset.mem_singleton] at hmem
  change nones (Box.sign (Box.ofSign (edgeCell n i))) 0 = i
  rw [Box.sign_ofSign]
  exact hmem

/-- **Sorting an edge through `ρ` is post-composition with `ρ`** — there is no order to sort. -/
theorem J_sortFace_edge {n : ℕ} (g : ▫1 ⟶ ▫n) (ρ : Equiv.Perm (Fin n)) :
    (J.map (SHom.sortFace (J.map g) ρ) : ▪1 ⟶ ▪n) = J.map g ≫ symHom ρ := by
  have h := SHom.symm_sortPerm_sortFace (J.map g) ρ
  rwa [sHomEquiv_symm_apply, Subsingleton.elim (SHom.sortPerm (J.map g) ρ) 1, symHom_one,
    Category.id_comp] at h

/-- …so the axis the edge performs moves by `ρ`. -/
theorem faceEmb_sortFace_edge {n : ℕ} (g : ▫1 ⟶ ▫n) (ρ : Equiv.Perm (Fin n)) :
    faceEmb (SHom.sortFace (J.map g) ρ) 0 = ρ (faceEmb g 0) := by
  have h := congrArg (fun u : ▪1 ⟶ ▪n => SHom.pos u 0) (J_sortFace_edge g ρ)
  simpa using h

/-! ## There is only one natural map `H² ⟶ H` -/

/-- The order a natural `H² ⟶ H` returns, read on the representable's top cell.  `nat_app` says
this is all of it. -/
noncomputable def natOrd (θ : H ⋙ H ⟶ H) (m : ℕ) (τ σ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin m) :=
  ((θ.app (yoneda.obj ▫m)).app (op ▫m)
    ((τ, σ, 𝟙 ▫m) : ((H ⋙ H).obj (yoneda.obj ▫m)).obj (op ▫m))).1

/-- **A natural `H² ⟶ H` cannot touch the cell**: naturality in `K` reduces it to the cube, whose
top cell is rigid, so only the order can move. -/
theorem nat_app (θ : H ⋙ H ⟶ H) {K : PrecubicalSet} {m : ℕ}
    (τ σ : Equiv.Perm (Fin m)) (y : K.obj (op ▫m)) :
    (θ.app K).app (op ▫m) ((τ, σ, y) : ((H ⋙ H).obj K).obj (op ▫m))
      = ((natOrd θ m τ σ, y) : (H.obj K).obj (op ▫m)) := by
  have hy : (yonedaEquiv.symm y).app (op ▫m) (𝟙 ▫m) = y :=
    (yonedaEquiv_apply _).symm.trans (yonedaEquiv.apply_symm_apply y)
  have hnat := comp_app_cell₂ (θ.naturality (yonedaEquiv.symm y)) m
    ((τ, σ, 𝟙 ▫m) : ((H ⋙ H).obj (yoneda.obj ▫m)).obj (op ▫m))
  have hL : ((H ⋙ H).map (yonedaEquiv.symm y)).app (op ▫m)
      ((τ, σ, 𝟙 ▫m) : ((H ⋙ H).obj (yoneda.obj ▫m)).obj (op ▫m))
      = ((τ, σ, y) : ((H ⋙ H).obj K).obj (op ▫m)) := by
    have h0 : ((H ⋙ H).map (yonedaEquiv.symm y)).app (op ▫m)
        ((τ, σ, 𝟙 ▫m) : ((H ⋙ H).obj (yoneda.obj ▫m)).obj (op ▫m))
        = ((τ, σ, (yonedaEquiv.symm y).app (op ▫m) (𝟙 ▫m)) :
            ((H ⋙ H).obj K).obj (op ▫m)) := rfl
    rw [h0, hy]
  have hR : (H.map (yonedaEquiv.symm y)).app (op ▫m)
      ((θ.app (yoneda.obj ▫m)).app (op ▫m)
        ((τ, σ, 𝟙 ▫m) : ((H ⋙ H).obj (yoneda.obj ▫m)).obj (op ▫m)))
      = ((natOrd θ m τ σ, y) : (H.obj K).obj (op ▫m)) := by
    have h0 : (H.map (yonedaEquiv.symm y)).app (op ▫m)
        ((θ.app (yoneda.obj ▫m)).app (op ▫m)
          ((τ, σ, 𝟙 ▫m) : ((H ⋙ H).obj (yoneda.obj ▫m)).obj (op ▫m)))
        = ((natOrd θ m τ σ, (yonedaEquiv.symm y).app (op ▫m)
            (((θ.app (yoneda.obj ▫m)).app (op ▫m)
              ((τ, σ, 𝟙 ▫m) : ((H ⋙ H).obj (yoneda.obj ▫m)).obj (op ▫m))).2)) :
            (H.obj K).obj (op ▫m)) := rfl
    rw [h0, Box.endo_eq_id (((θ.app (yoneda.obj ▫m)).app (op ▫m)
      ((τ, σ, 𝟙 ▫m) : ((H ⋙ H).obj (yoneda.obj ▫m)).obj (op ▫m))).2)]
    exact congrArg (fun t : K.obj (op ▫m) => ((natOrd θ m τ σ, t) : (H.obj K).obj (op ▫m))) hy
  exact ((congrArg ((θ.app K).app (op ▫m)) hL).symm.trans hnat).trans hR

/-- **The order is forced to be the product** — naturality along the edge freeing `i` reads the
composite `σ ∘ τ` off the axis `i`. -/
theorem natOrd_eq (θ : H ⋙ H ⟶ H) {n : ℕ} (τ σ : Equiv.Perm (Fin n)) :
    natOrd θ n τ σ = σ * τ := by
  refine Equiv.ext fun i => ?_
  set F := natOrd θ n τ σ
  set g : ▫1 ⟶ ▫n := edge n i with hg
  set g₁ : ▫1 ⟶ ▫n := SHom.sortFace (J.map g) τ with hg₁
  have hnat := NatTrans.naturality_apply (θ.app (yoneda.obj ▫n)) g.op
    ((τ, σ, 𝟙 ▫n) : ((H ⋙ H).obj (yoneda.obj ▫n)).obj (op ▫n))
  have hL : (((H ⋙ H).obj (yoneda.obj ▫n)).map g.op
      ((τ, σ, 𝟙 ▫n) : ((H ⋙ H).obj (yoneda.obj ▫n)).obj (op ▫n)))
      = ((SHom.sortPerm (J.map g) τ, SHom.sortPerm (J.map g₁) σ,
          SHom.sortFace (J.map g₁) σ) : ((H ⋙ H).obj (yoneda.obj ▫n)).obj (op ▫1)) := by
    have h0 : (((H ⋙ H).obj (yoneda.obj ▫n)).map g.op
        ((τ, σ, 𝟙 ▫n) : ((H ⋙ H).obj (yoneda.obj ▫n)).obj (op ▫n)))
        = ((SHom.sortPerm (J.map g) τ, SHom.sortPerm (J.map g₁) σ,
            SHom.sortFace (J.map g₁) σ ≫ 𝟙 ▫n) :
              ((H ⋙ H).obj (yoneda.obj ▫n)).obj (op ▫1)) := rfl
    rw [h0, Category.comp_id]
  have hR : (H.obj (yoneda.obj ▫n)).map g.op
      ((F, 𝟙 ▫n) : (H.obj (yoneda.obj ▫n)).obj (op ▫n))
      = ((SHom.sortPerm (J.map g) F, SHom.sortFace (J.map g) F) :
          (H.obj (yoneda.obj ▫n)).obj (op ▫1)) := by
    have h0 : (H.obj (yoneda.obj ▫n)).map g.op
        ((F, 𝟙 ▫n) : (H.obj (yoneda.obj ▫n)).obj (op ▫n))
        = ((SHom.sortPerm (J.map g) F, SHom.sortFace (J.map g) F ≫ 𝟙 ▫n) :
            (H.obj (yoneda.obj ▫n)).obj (op ▫1)) := rfl
    rw [h0, Category.comp_id]
  rw [hL, nat_app, nat_app, hR] at hnat
  have h2 : SHom.sortFace (J.map g₁) σ = SHom.sortFace (J.map g) F := congrArg Prod.snd hnat
  have e0 : faceEmb g 0 = i := by rw [hg]; exact faceEmb_edge n i
  have e1 : faceEmb g₁ 0 = τ i := by
    rw [hg₁]
    exact (faceEmb_sortFace_edge g τ).trans (congrArg (fun j : Fin n => τ j) e0)
  have h3 := congrArg (fun ψ : ▫1 ⟶ ▫n => faceEmb ψ 0) h2
  rw [Equiv.Perm.mul_apply]
  calc F i = F (faceEmb g 0) := by rw [e0]
    _ = faceEmb (SHom.sortFace (J.map g) F) 0 := (faceEmb_sortFace_edge g F).symm
    _ = faceEmb (SHom.sortFace (J.map g₁) σ) 0 := h3.symm
    _ = σ (faceEmb g₁ 0) := faceEmb_sortFace_edge g₁ σ
    _ = σ (τ i) := by rw [e1]

/-- **`Hmul` is the only natural transformation `H² ⟶ H`** — degree `1` of the bar construction
has a single face. -/
theorem Hmul_unique (θ : H ⋙ H ⟶ H) : θ = Hmul := by
  refine NatTrans.ext (funext fun K => ?_)
  refine NatTrans.ext_apply fun B p => ?_
  obtain ⟨τ, σ, y⟩ := p
  exact (nat_app θ (m := B.unop.dim) τ σ y).trans
    ((congrArg (fun ρ => ((ρ, y) : (H.obj K).obj B)) (natOrd_eq θ τ σ)).trans
      (Hmul_app τ σ y).symm)

instance : Subsingleton (H ⋙ H ⟶ H) :=
  ⟨fun θ θ' => (Hmul_unique θ).trans (Hmul_unique θ').symm⟩

theorem swap_ne_one : Equiv.swap (0 : Fin 2) 1 ≠ 1 := by
  intro hswap
  have h3 := congrArg (fun p : Equiv.Perm (Fin 2) => p 0) hswap
  simp at h3

/-- **Forgetting the outer order is not natural**: at `τ = (0 1)`, `σ = 1` every natural map
returns `(0 1)`, not `σ`. -/
theorem natOrd_forget_outer (θ : H ⋙ H ⟶ H) : natOrd θ 2 (Equiv.swap 0 1) 1 ≠ 1 := by
  rw [natOrd_eq, one_mul]
  exact swap_ne_one

/-- **…nor is forgetting the inner order**: at `τ = 1`, `σ = (0 1)` it returns `(0 1)`, not `τ`. -/
theorem natOrd_forget_inner (θ : H ⋙ H ⟶ H) : natOrd θ 2 1 (Equiv.swap 0 1) ≠ 1 := by
  rw [natOrd_eq, mul_one]
  exact swap_ne_one

/-! ## Degree `2`: the two faces are different

`μ_{HK}` multiplies the two *outer* orders and `H μ_K` the two *inner* ones; the monad law only
makes them agree after a further `μ`. -/

/-- `μ_{HK}` — the bar face that multiplies the outer pair. -/
noncomputable def HmulOuter : H ⋙ H ⋙ H ⟶ H ⋙ H := Functor.whiskerLeft H Hmul

/-- `H μ_K` — the bar face that multiplies the inner pair. -/
noncomputable def HmulInner : H ⋙ H ⋙ H ⟶ H ⋙ H := Functor.whiskerRight Hmul H

theorem HmulOuter_app {K : PrecubicalSet} {m : ℕ} (ρ τ σ : Equiv.Perm (Fin m))
    (y : K.obj (op ▫m)) :
    (HmulOuter.app K).app (op ▫m) ((ρ, τ, σ, y) : ((H ⋙ H ⋙ H).obj K).obj (op ▫m))
      = ((τ * ρ, σ, y) : ((H ⋙ H).obj K).obj (op ▫m)) :=
  Hmul_app (K := H.obj K) ρ τ ((σ, y) : (H.obj K).obj (op ▫m))

theorem HmulInner_app {K : PrecubicalSet} {m : ℕ} (ρ τ σ : Equiv.Perm (Fin m))
    (y : K.obj (op ▫m)) :
    (HmulInner.app K).app (op ▫m) ((ρ, τ, σ, y) : ((H ⋙ H ⋙ H).obj K).obj (op ▫m))
      = ((ρ, σ * τ, y) : ((H ⋙ H).obj K).obj (op ▫m)) := by
  have h0 : (HmulInner.app K).app (op ▫m) ((ρ, τ, σ, y) : ((H ⋙ H ⋙ H).obj K).obj (op ▫m))
      = ((ρ, (Hmul.app K).app (op ▫m) ((τ, σ, y) : ((H ⋙ H).obj K).obj (op ▫m))) :
          ((H ⋙ H).obj K).obj (op ▫m)) := rfl
  rw [h0, Hmul_app]
  rfl

/-- **The two degree-`2` faces differ** — already on the `2`-cube, at a transposition. -/
theorem HmulOuter_ne_HmulInner : HmulOuter ≠ HmulInner := by
  intro h
  have key : (HmulOuter.app (yoneda.obj ▫2)).app (op ▫2)
        (((1 : Equiv.Perm (Fin 2)), Equiv.swap (0 : Fin 2) (1 : Fin 2),
            (1 : Equiv.Perm (Fin 2)), 𝟙 ▫2) :
          ((H ⋙ H ⋙ H).obj (yoneda.obj ▫2)).obj (op ▫2))
      = (HmulInner.app (yoneda.obj ▫2)).app (op ▫2)
        (((1 : Equiv.Perm (Fin 2)), Equiv.swap (0 : Fin 2) (1 : Fin 2),
            (1 : Equiv.Perm (Fin 2)), 𝟙 ▫2) :
          ((H ⋙ H ⋙ H).obj (yoneda.obj ▫2)).obj (op ▫2)) := by
    rw [h]
  rw [HmulOuter_app, HmulInner_app] at key
  refine swap_ne_one ?_
  have h1 := congrArg Prod.fst key
  rwa [mul_one] at h1

/-! ## `Nat(H^a, H^b)`, on the validated model

`Testing/H/HTwo`'s `pattern`/`imageOf` **are** `SHom.sortPerm`/`sortFace` (`sortCheck`).  Three
reductions, then a finite search:

* the `K`-component of a natural `H^a ⟶ H^b` is untouched (`nat_app`'s argument, verbatim), so
  such a map is a tuple of functions of the orders alone;
* in the **partial-product** coordinates `Π_c = π_c ⋯ π_1` the `H^a`-restriction acts
  componentwise (`shearGaps`), i.e. `H^a 1 ≅ (H 1)^a`, and the components of the map are free
  exactly when its partial products `F₁, …, F_{b-1}` are maps `H^a 1 ⟶ H 1` — the last one is
  pinned to `Π_a` by the cell.  So `Nat(H^a, H^b) ≅ Hom(H^a 1, H 1)^{b-1}`;
* a permutation is its inversion set, and naturality along the `2`-element faces reads that set
  off a boolean table on the `a` inversion bits of a pair — so `Hom(H^a 1, H 1)` embeds in the
  `2 ^ 2 ^ a` tables, and `natTables` searches them. -/

/-- The partial products `Π₁, …, Π_a` of `(π₁, …, π_a)`, outermost first. -/
def partialProds (d : ℕ) (πs : List (List ℕ)) : List (List ℕ) :=
  (πs.scanl (fun acc p => compL p acc) (List.range d)).tail

/-- The `H^a`-restriction of `(π₁, …, π_a)` along the face freeing `T`: each order is sorted
through the face the outer ones have already twisted. -/
def haRestrict (πs : List (List ℕ)) (T : List ℕ) : List (List ℕ) × List ℕ :=
  πs.foldl (fun acc p => (acc.1 ++ [pattern p acc.2], imageOf p acc.2)) ([], T)

/-- Mismatches of `H^a 1 ≅ (H 1)^a`: the restriction is componentwise on partial products. -/
def shearGaps (a d : ℕ) : ℕ :=
  (cartesian (List.replicate a (permsOf d))).foldl (fun acc πs =>
    let P := partialProds d πs
    ((List.range d).sublists).foldl (fun acc T =>
      let r := haRestrict πs T
      if partialProds T.length r.1 == P.map (pattern · T)
          && r.2 == imageOf (P.getLastD []) T then acc else acc + 1) acc) 0

/-- All boolean tables of length `n`. -/
def boolTables : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolTables n).flatMap fun l => [false :: l, true :: l]

/-- The inversion indicator of the one-line word `w` at the pair `p < q`. -/
def invBit (w : List ℕ) (p q : ℕ) : Bool := decide (w.getD q 0 < w.getD p 0)

/-- The index of `(invBit Π₁ p q, …, invBit Π_a p q)`, `Π₁` most significant. -/
def bitIdx (Ps : List (List ℕ)) (p q : ℕ) : ℕ :=
  Ps.foldl (fun acc w => 2 * acc + (if invBit w p q then 1 else 0)) 0

/-- The one-line word whose inversion set the table `F` prescribes. -/
def fromBits (d : ℕ) (Ps : List (List ℕ)) (F : List Bool) : List ℕ :=
  (List.range d).map fun i =>
    ((List.range i).countP fun j => !F.getD (bitIdx Ps j i) false) +
      ((List.range d).countP fun j => decide (i < j) && F.getD (bitIdx Ps i j) false)

/-- Is `l` a one-line word of `S_d`? -/
def isWord (d : ℕ) (l : List ℕ) : Bool := l.length == d && (List.range d).all (l.contains ·)

/-- The tables whose prescribed inversion set is a permutation and is natural under every face of
`▫d`; `Ps` runs over all `a`-tuples of orders, which is what the shear makes the coordinates. -/
def filterAt (a d : ℕ) (ts : List (List Bool)) : List (List Bool) :=
  let subs := (List.range d).sublists
  let tuples := cartesian (List.replicate a (permsOf d))
  ts.filter fun F =>
    tuples.all fun Ps =>
      let v := fromBits d Ps F
      isWord d v && subs.all fun T => fromBits T.length (Ps.map (pattern · T)) F == pattern v T

/-- `Hom(H^a 1, H 1)`, as tables. -/
def natTables (a : ℕ) : List (List Bool) := filterAt a 3 (boolTables (2 ^ a))

/-- `w₀^ε · Π_c` as a table: the `c`-th inversion bit (`c = 0`: none), optionally negated. -/
def prefixTable (a c : ℕ) (neg : Bool) : List Bool :=
  (List.range (2 ^ a)).map fun idx =>
    xor neg (if c == 0 then false else (idx / 2 ^ (a - c)) % 2 == 1)

/-- The `2 (a + 1)` maps built from the unit, the partial products, and the longest element. -/
def expectedTables (a : ℕ) : List (List Bool) :=
  (List.range (a + 1)).flatMap fun c => [prefixTable a c false, prefixTable a c true]

/-! ### The verdict

The shear holds; the surviving tables are exactly `w₀^ε · Π_c`, so `Hom(H^a 1, H 1)` has
`2 (a + 1)` elements and `Nat(H^a, H^b)` has `(2 (a + 1)) ^ (b - 1)`.  Two of the eight at
`a = 3, b = 2` are the bar faces `μ_{HK}` (`c = 2`) and `H μ_K` (`c = 1`); `c = 0` and `c = 3` are
the two unit-padded copies of `μ ∘ μ`, and the `w₀` half is the run-reversal twist — an operation
the monad structure alone does not produce. -/

#eval (shearGaps 1 4, shearGaps 2 4, shearGaps 3 4)                -- (0, 0, 0)
#eval ((natTables 1).length, (natTables 2).length, (natTables 3).length)   -- (4, 6, 8)
#eval (setEq (natTables 1) (expectedTables 1), setEq (natTables 2) (expectedTables 2),
       setEq (natTables 3) (expectedTables 3))                     -- (true, true, true)
#eval ((filterAt 1 4 (natTables 1)).length, (filterAt 2 4 (natTables 2)).length,
       (filterAt 3 4 (natTables 3)).length)                        -- (4, 6, 8): `d = 3` is final
#eval (fromBits 4 [List.range 4] (prefixTable 1 0 true),
       fromBits 4 [[1, 0, 3, 2]] (prefixTable 1 1 true))
                                          -- ([3,2,1,0], [2,3,0,1]) — w₀, and w₀ · σ

end CubeChains

