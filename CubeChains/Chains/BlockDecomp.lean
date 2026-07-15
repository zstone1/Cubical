import CubeChains.Chains.Category
import CubeChains.Chains.WedgeMap
import CubeChains.Chains.CubeNonSelfLinked
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# Chains/BlockDecomp — block decomposition of a serial-wedge map

For a bi-pointed wedge map `φ : ⋁ad ⟶ ⋁cd`, each source bead `i` factors through a
unique target block `blockIdx φ i` via a `Box`-face `blockFace φ i`; `faceEmb` reads off that
face's free coordinates as an order embedding.  This is pure cube-chain data — shared by the
chamber presheaf (`Lines`), the event system, and the `Ch(K)`-skeletality proof.
-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChain

/-- The `Fin`-indexed sum of `g` over a list's entries equals the sum of the mapped list. -/
theorem sum_get_eq_sum_map {α : Type*} {M : Type*} [AddCommMonoid M] (l : List α) (g : α → M) :
    ∑ i : Fin l.length, g (l.get i) = (l.map g).sum := by
  rw [← List.sum_ofFn (f := fun i => g (l.get i)), List.ofFn_comp', List.ofFn_get]

/-! ### The free-coordinate embedding of a cube face

A `k`-face `incl : □ᵏ ⟶ □ᵐ` has `k` free (`none`/star) coordinates;
`faceEmb incl : Fin k ↪o Fin m` enumerates them.  Chambers pull back along it. -/

/-- The order embedding of the free coordinates of a cube face `incl : □ᵏ ⟶ □ᵐ`. -/
def faceEmb {k m : ℕ} (incl : ▫k ⟶ ▫m) : Fin k ↪o Fin m :=
  nones (ev incl)

/-- `nones` of the top cell is the identity embedding. -/
theorem nones_topCell (k : ℕ) (x : Fin k) : nones (topCell k) x = x := by
  have h : (id : Fin k → Fin k) = nones (topCell k) :=
    Finset.orderEmbOfFin_unique (topCell k).prop
      (fun y => by simp [mem_noneSet, topCell]) strictMono_id
  exact (congrFun h x).symm

/-- The free-coordinate embedding of the identity face is the identity. -/
theorem faceEmb_id (k : ℕ) (x : Fin k) : faceEmb (𝟙 ▫k) x = x := by
  have h1 : ev (𝟙 ▫k) = topCell k := by
    have e : (𝟙 ▫k : ▫k ⟶ ▫k) = canonicalMap (topCell k) :=
      (canonicalMap_topCell k).symm
    rw [e]; exact ev_canonicalMap _
  change nones (ev (𝟙 ▫k)) x = x
  rw [h1]; exact nones_topCell k x

/-- `ev` of a composite of cube faces is the iterated-face map of the two sign vectors. -/
theorem ev_comp_app {k e m : ℕ} (p : ▫k ⟶ ▫e) (q : ▫e ⟶ ▫m) :
    ev (p ≫ q) = act (K := stdPre m) (ev q) (ev p) :=
  (ev_comp p q).trans (app_unique q rfl (ev p))

/-- `faceEmb (p ≫ q) = faceEmb q ∘ faceEmb p`. -/
theorem faceEmb_comp {k e m : ℕ} (p : ▫k ⟶ ▫e) (q : ▫e ⟶ ▫m)
    (x : Fin k) : faceEmb (p ≫ q) x = faceEmb q (faceEmb p x) := by
  change nones (ev (p ≫ q)) x
    = nones (ev q) (nones (ev p) x)
  rw [ev_comp_app p q]
  exact CubeChain.nones_app (ev q) (ev p) x

/-- `faceEmb` of the `eqToHom` of a dimension equality is the `Fin` cast: an `eqToHom` between
boxes has no free coordinates to permute. -/
theorem faceEmb_eqToHom {k k' : ℕ} (h : k = k') (x : Fin k) :
    faceEmb (eqToHom (congrArg Box.ob h)) x = Fin.cast h x := by
  subst h
  simp only [Fin.cast_eq_self]
  exact faceEmb_id k x

/-- Value form of `faceEmb_eqToHom`, for a box equality rather than a dimension equality. -/
theorem faceEmb_eqToHom_val {k k' : ℕ} (h : ▫k = ▫k') (x : Fin k) :
    (faceEmb (eqToHom h) x).1 = x.1 := by
  obtain rfl : k = k' := congrArg Box.dim h
  rw [eqToHom_refl, faceEmb_id]

/-! ### Block data of a wedge map

`wedgeMap_block` factors a source bead's inclusion `ι_i ≫ φ` through a unique target
block (`blockIdx φ i`) via a `Box`-face (`blockFace φ i`). -/

/-- The **target block index** of source bead `i` under a wedge map `φ`: the unique
`cd`-block `r` such that `ι_i ≫ φ` factors through block `r`. -/
noncomputable def blockIdx {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    Fin cd.length :=
  (wedgeMap_block φ i).choose

/-- The **face inclusion** of source bead `i` under a wedge map `φ`: the `Box`
morphism `□^{ad.get i} ⟶ □^{cd.get (blockIdx φ i)}` witnessing that `ι_i ≫ φ` lands
in a face of the target block. -/
noncomputable def blockFace {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    ▫((ad.get i) : ℕ) ⟶ ▫((cd.get (blockIdx φ i)) : ℕ) :=
  (wedgeMap_block φ i).choose_spec.choose

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
      = yoneda.map (blockFace φ i) ≫ ιᵂ cd (blockIdx φ i) :=
  (wedgeMap_block φ i).choose_spec.choose_spec

/-! ### `blockIdx` computes (`@[csimp]`)

The block index of a positive cell is read off the `Glue` `Quot` directly (which summand,
recursively), so `blockIdx` `#eval`s without the `.choose`.  Kept as a spec + `@[csimp]`
because `blockFace`'s type depends on `blockIdx`, and downstream proofs use `blockFace_spec`. -/

-- The block a positive cell of `⋁dims` lies in, read off the `Glue` `Quot`.
unseal Glue.gluePsh Glue.inl Glue.inr in
def serialWedgeBlockOf : (dims : List ℕ+) → {m : ℕ} → 1 ≤ m → (⋁dims).cells m → Fin dims.length
  | [], _, hm, c => ((cube0_cells_isEmpty hm).false c).elim
  | _ :: rest, m, hm, c =>
      Quot.lift
        (fun x => match x with
          | Sum.inl _ => (0 : Fin (rest.length + 1))
          | Sum.inr b => (serialWedgeBlockOf rest hm b).succ)
        (by intro _ _ r; obtain ⟨s⟩ := r
            exact ((cube0_cells_isEmpty hm).false s).elim)
        c

theorem serialWedgeBlockOf_zero {n : ℕ+} {rest : List ℕ+} {m : ℕ} (hm : 1 ≤ m)
    (x : (□(n : ℕ)).cells m) :
    serialWedgeBlockOf (n :: rest) hm ((Glue.inl (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫ x)
      = 0 := by
  show serialWedgeBlockOf (n :: rest) hm ((Glue.inl _ _).app (op ▫m) x) = 0
  rw [Glue.inl_app]; rfl

theorem serialWedgeBlockOf_succ {n : ℕ+} {rest : List ℕ+} {m : ℕ} (hm : 1 ≤ m)
    (y : (⋁rest).cells m) :
    serialWedgeBlockOf (n :: rest) hm ((Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫ y)
      = (serialWedgeBlockOf rest hm y).succ := by
  show serialWedgeBlockOf (n :: rest) hm ((Glue.inr _ _).app (op ▫m) y) = _
  rw [Glue.inr_app]; rfl

/-- **`serialWedgeBlockOf` names a real block**: the cell factors through the block it reports. -/
theorem serialWedgeBlockOf_mem : ∀ (dims : List ℕ+) {m : ℕ} (hm : 1 ≤ m) (c : (⋁dims).cells m),
    ∃ x, (ιᵂ dims (serialWedgeBlockOf dims hm c))⟪m⟫ x = c
  | [], _, hm, c => ((cube0_cells_isEmpty hm).false c).elim
  | n :: rest, m, hm, c => by
      rcases wedge2_cell_cases (□(n : ℕ)) (⋁rest) m c with ⟨x, hx⟩ | ⟨y, hy⟩
      · rw [← hx, serialWedgeBlockOf_zero]
        exact ⟨x, by rw [serialWedge_ι_zero_app]⟩
      · rw [← hy, serialWedgeBlockOf_succ]
        obtain ⟨x', hx'⟩ := serialWedgeBlockOf_mem rest hm y
        exact ⟨x', by rw [serialWedge_ι_succ_app, hx']⟩

/-- Computable implementation of `blockIdx`; `#eval` uses it. -/
def blockIdxImpl {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) : Fin cd.length :=
  serialWedgeBlockOf cd (ad.get i).pos (yonedaEquiv (ιᵂ ad i ≫ φ))

@[csimp] theorem blockIdx_eq_impl : @blockIdx = @blockIdxImpl := by
  funext ad cd φ i
  refine serialWedge_block_unique cd (ad.get i).pos (blockIdx φ i) (blockIdxImpl φ i)
    (yonedaEquiv (ιᵂ ad i ≫ φ)) ?_ ?_
  · refine ⟨yonedaEquiv (yoneda.map (blockFace φ i)), ?_⟩
    rw [← yonedaEquiv_comp]
    exact congrArg yonedaEquiv (blockFace_spec φ i).symm
  · exact serialWedgeBlockOf_mem cd (ad.get i).pos _

/-- If `ι_i ≫ φ = g ≫ ι_r` for any face `g`, then `r = blockIdx φ i`. -/
theorem blockIdx_eq_of_factor {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length)
    (r : Fin cd.length) (g : ▫((ad.get i) : ℕ) ⟶ ▫((cd.get r) : ℕ))
    (h : ιᵂ ad i ≫ φ = yoneda.map g ≫ ιᵂ cd r) :
    r = blockIdx φ i := by
  refine serialWedge_block_unique cd (ad.get i).2 r (blockIdx φ i)
    (yonedaEquiv (ιᵂ ad i ≫ φ))
    ⟨yonedaEquiv (yoneda.map g),
      (yonedaEquiv_comp (yoneda.map g) (ιᵂ cd r)).symm.trans
        (congrArg yonedaEquiv h.symm)⟩
    ⟨yonedaEquiv (yoneda.map (blockFace φ i)),
      (yonedaEquiv_comp (yoneda.map (blockFace φ i))
        (ιᵂ cd (blockIdx φ i))).symm.trans
        (congrArg yonedaEquiv (blockFace_spec φ i).symm)⟩

/-- The two-step block factorization of `ι_i ≫ (φ ≫ ψ)` (`r := blockIdx φ i`, `r' := blockIdx ψ r`):

      □^{ad.get i}   --ι-->  □^∨(ad)
           |                    |
   blockFace φ i                φ
           v                    v
      □^{bd.get r}   --ι-->  □^∨(bd)
           |                    |
   blockFace ψ r                ψ
           v                    v
      □^{cd.get r'}  --ι-->  □^∨(cd)
-/
theorem blockFace_spec_comp {ad bd cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁bd).toPsh)
    (ψ : (⋁bd).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    ιᵂ ad i ≫ (φ ≫ ψ)
      = yoneda.map (blockFace φ i ≫ blockFace ψ (blockIdx φ i))
        ≫ ιᵂ cd (blockIdx ψ (blockIdx φ i)) :=
  calc ιᵂ ad i ≫ (φ ≫ ψ)
      = (ιᵂ ad i ≫ φ) ≫ ψ := (Category.assoc _ _ _).symm
    _ = (yoneda.map (blockFace φ i) ≫ ιᵂ bd (blockIdx φ i)) ≫ ψ :=
        congrArg (· ≫ ψ) (blockFace_spec φ i)
    _ = yoneda.map (blockFace φ i) ≫ (ιᵂ bd (blockIdx φ i) ≫ ψ) :=
        Category.assoc _ _ _
    _ = yoneda.map (blockFace φ i) ≫ (yoneda.map (blockFace ψ (blockIdx φ i))
          ≫ ιᵂ cd (blockIdx ψ (blockIdx φ i))) :=
        congrArg (yoneda.map (blockFace φ i) ≫ ·) (blockFace_spec ψ (blockIdx φ i))
    _ = (yoneda.map (blockFace φ i) ≫ yoneda.map (blockFace ψ (blockIdx φ i)))
          ≫ ιᵂ cd (blockIdx ψ (blockIdx φ i)) := (Category.assoc _ _ _).symm
    _ = yoneda.map (blockFace φ i ≫ blockFace ψ (blockIdx φ i))
          ≫ ιᵂ cd (blockIdx ψ (blockIdx φ i)) :=
        congrArg (· ≫ ιᵂ cd (blockIdx ψ (blockIdx φ i)))
          (yoneda.map_comp (blockFace φ i) (blockFace ψ (blockIdx φ i))).symm

/-- `blockIdx (φ ≫ ψ) i = blockIdx ψ (blockIdx φ i)`. -/
theorem blockIdx_comp {ad bd cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁bd).toPsh)
    (ψ : (⋁bd).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    blockIdx (φ ≫ ψ) i = blockIdx ψ (blockIdx φ i) :=
  (blockIdx_eq_of_factor (φ ≫ ψ) i (blockIdx ψ (blockIdx φ i))
    (blockFace φ i ≫ blockFace ψ (blockIdx φ i)) (blockFace_spec_comp φ ψ i)).symm

end CubeChain
