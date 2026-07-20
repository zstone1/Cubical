import CubeChains.Chains.Category
import CubeChains.Chains.WedgeMap
import CubeChains.Chains.CubeNonSelfLinked
import CubeChains.Chains.SegalAltitude
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

/-- The `Fin`-indexed sum over a list's entries is the sum of the mapped list. -/
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

`serialWedgeCell` reads a positive cell of `⋁dims` off the `Glue` `Quot`: the block it lies in,
and the face of that block's cube it is (`serialWedgeCell_spec`).  `blockIdx`/`blockFace` are its
two projections at the source-bead restriction `ι_i ≫ φ`, so a wedge map's block data is genuinely
computable (no `.choose`).  `blockFace`'s codomain matches `blockIdx φ i` with no cast: it *is* the
cube-face projection, whose type reduces to `▫(ad.get i) ⟶ ▫(cd.get (blockIdx φ i))`. -/

-- The block a positive cell of `⋁dims` lies in, together with the face of that block's cube it is,
-- read off the `Glue` `Quot`.
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
      rcases wedge2_cell_cases (□(n : ℕ)) (⋁rest) m c with ⟨x, hx⟩ | ⟨y, hy⟩
      · rw [← hx, serialWedgeCell_zero]
        exact serialWedge_ι_zero_app n rest x
      · rw [← hy, serialWedgeCell_succ,
          serialWedge_ι_succ_app n rest (serialWedgeCell rest hm y).1
            (serialWedgeCell rest hm y).2]
        exact congrArg
          ((Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫)
          (serialWedgeCell_spec rest hm y)

/-- The **target block index** of source bead `i` under a wedge map `φ`: the `cd`-block that the
restriction `ι_i ≫ φ` factors through. -/
def blockIdx {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    Fin cd.length :=
  (serialWedgeCell cd (ad.get i).pos (yonedaEquiv (ιᵂ ad i ≫ φ))).1

/-- The **face inclusion** of source bead `i` under a wedge map `φ`: the `Box`
morphism `□^{ad.get i} ⟶ □^{cd.get (blockIdx φ i)}` witnessing that `ι_i ≫ φ` lands
in a face of the target block. -/
def blockFace {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    ▫((ad.get i) : ℕ) ⟶ ▫((cd.get (blockIdx φ i)) : ℕ) :=
  (serialWedgeCell cd (ad.get i).pos (yonedaEquiv (ιᵂ ad i ≫ φ))).2

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
  exact (serialWedgeCell_spec cd (ad.get i).pos (yonedaEquiv (ιᵂ ad i ≫ φ))).symm

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

/-! ### Where a block sits: the prefix-sum sandwich

`blockIdx` is pinned numerically by dimension prefix sums.  Everything here runs on the serial
wedge's *own* tautological altitude (`serialWedge_admitsAltitude`), which always exists — no
hypothesis on any ambient `K`. -/

/-- The altitude of the `k`-th read-off cube of a wedge map `hom : ⋁ed ⟶ ⋁cd`
whose source-init lands on `cd`'s init: it is the dimension prefix-sum of the earlier
cubes.  A packaging of `isCubeChain_alt_get` through `wedgeToCubes_get`. -/
theorem serialWedge_bead_alt {ed cd : List ℕ+}
    (alt : ∀ n, (⋁cd).cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude (⋁cd).toPsh alt)
    (h0 : alt 0 (⋁cd).init = 0)
    (hom : (⋁ed).toPsh ⟶ (⋁cd).toPsh)
    (q : (⋁cd).cells 0)
    (hci : IsCubeChain (⋁cd).init (wedgeToCubes ⟨ed, hom⟩) q)
    (k : Fin ed.length) :
    alt (ed.get k : ℕ) (yonedaEquiv (ιᵂ ed k ≫ hom))
      = dimPrefixSum (wedgeToCubes ⟨ed, hom⟩) k.val := by
  have hlt : k.val < (wedgeToCubes ⟨ed, hom⟩).length := by
    rw [wedgeToCubes_length]; exact k.isLt
  have hcast : (⟨k.val, hlt⟩ : Fin (wedgeToCubes ⟨ed, hom⟩).length).cast
      (wedgeToCubes_length ed hom) = k := Fin.ext rfl
  have hget := wedgeToCubes_get ed hom ⟨k.val, hlt⟩
  have hg := isCubeChain_alt_get alt hax (wedgeToCubes ⟨ed, hom⟩)
    (⋁cd).init q hci k.val hlt
  rw [h0, zero_add] at hg
  rw [hget, hcast] at hg
  exact hg

/-- **Prefix-sum sandwich for `blockIdx`.**  For a wedge map `φ : ⋁ad ⟶ ⋁cd`
sending `ad`-init to `cd`-init, the block of source bead `i` (`blockIdx φ i`) is pinned
by the dimension prefix sums: its `cd`-prefix is `≤` bead `i`'s `ad`-prefix, which in
turn is `<` the next `cd`-prefix.  Uses **only** `serialWedge_admitsAltitude cd`. -/
theorem serialWedge_blockIdx_prefix_bound {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    (i : Fin ad.length) :
    dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) (blockIdx φ i).val
        ≤ dimPrefixSum (wedgeToCubes ⟨ad, φ⟩) i.val
      ∧ dimPrefixSum (wedgeToCubes ⟨ad, φ⟩) i.val
        < dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩)
            ((blockIdx φ i).val + 1) := by
  obtain ⟨alt, hax, h0⟩ := BPSet.serialWedge_admitsAltitude cd
  -- The taut (identity) chain of `⋁cd`.
  have hciT : IsCubeChain (⋁cd).init
      (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) (⋁cd).final := by
    have h := wedgeToCubes_isCubeChain (K := ⋁cd) cd
      (𝟙 (⋁cd).toPsh)
    simpa using h
  -- The pushed chain (`φ` read off) in `⋁cd`.
  have hciP : IsCubeChain (⋁cd).init (wedgeToCubes ⟨ad, φ⟩)
      (φ⟪0⟫ (⋁ad).final) := by
    have h := wedgeToCubes_isCubeChain (K := ⋁cd) ad φ
    rwa [hinit] at h
  -- Bead altitudes.
  have hP_i := serialWedge_bead_alt alt hax h0 φ _ hciP i
  have hT_j := serialWedge_bead_alt alt hax h0 (𝟙 (⋁cd).toPsh) _ hciT
    (blockIdx φ i)
  rw [Category.comp_id] at hT_j
  -- The pushed bead `i` is the `cd`-bead `blockIdx φ i` pulled back along `blockFace φ i`.
  have hce : yonedaEquiv (ιᵂ ad i ≫ φ)
      = (⋁cd).toPsh.map (blockFace φ i).op
          (yonedaEquiv (ιᵂ cd (blockIdx φ i))) :=
    (congrArg yonedaEquiv (blockFace_spec φ i)).trans
      (yonedaEquiv_naturality (ιᵂ cd (blockIdx φ i)) (blockFace φ i)).symm
  have hc := PrecubicalSet.alt_cubeMap alt hax
    (yonedaEquiv (ιᵂ cd (blockIdx φ i))) (blockFace φ i)
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply] at hc
  -- The key equation of prefix sums.
  have haltrel : dimPrefixSum (wedgeToCubes ⟨ad, φ⟩) i.val
      = dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) (blockIdx φ i).val
        + (trueCount (ev (blockFace φ i)) : ℤ) := by
    rw [← hP_i, ← hT_j, hce]; exact hc
  -- The `(blockIdx φ i)`-th successor of the taut prefix sum.
  have hjlt : (blockIdx φ i).val < (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩).length := by
    rw [wedgeToCubes_length]; exact (blockIdx φ i).isLt
  have hgetfst : ((wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩).get
      ⟨(blockIdx φ i).val, hjlt⟩).1 = cd.get (blockIdx φ i) := by
    rw [wedgeToCubes_get]; exact congrArg cd.get (Fin.ext rfl)
  have hsucc := dimPrefixSum_succ (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) hjlt
  rw [hgetfst] at hsucc
  -- trueCount bounds: `0 ≤ tc < cd.get (blockIdx φ i)`.
  have hle : (ad.get i : ℕ) ≤ (cd.get (blockIdx φ i) : ℕ) :=
    cells_card_le (ev (blockFace φ i))
  have htle : trueCount (ev (blockFace φ i))
      ≤ (cd.get (blockIdx φ i) : ℕ) - (ad.get i : ℕ) :=
    trueCount_le (ev (blockFace φ i))
  have hipos : 0 < (ad.get i : ℕ) := (ad.get i).2
  have htN : trueCount (ev (blockFace φ i)) < (cd.get (blockIdx φ i) : ℕ) := by
    omega
  have htlt : (trueCount (ev (blockFace φ i)) : ℤ)
      < ((cd.get (blockIdx φ i) : ℕ) : ℤ) := by exact_mod_cast htN
  have hnn : (0 : ℤ) ≤ (trueCount (ev (blockFace φ i)) : ℤ) :=
    Int.natCast_nonneg _
  refine ⟨by omega, ?_⟩
  rw [hsucc]
  omega

end CubeChain
