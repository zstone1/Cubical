import CubeChains.Events.EventLocalSystem
import CubeChains.Salvetti.SalBraidPartition
import Mathlib.Data.Fintype.Inv

/-!
# Events/EventMapBij — `eventMap` is bijective for every `K`

`eventMap f : EventObj a → EventObj b` (`EventNaming.lean`) reads only the block data of `fᵂ`, never
`K`, and is bijective for every bi-pointed `K` with no side conditions — the general-`K` upgrade of
the cube fact `cube_eventMap_bijective`.  Packaged as the event bijection `eventEquiv f`, a functor
`Ch K ⥤ Type` in all but name (`eventEquiv_id`, `eventEquiv_comp`).

The proof is injective-first, reduced to a within-cube fact: two events of `a` collide under
`eventMap f` iff they land in the same coarse bead `r = blockIdx φ i` and hit the same direction of
`□^{b.dims.get r}`.  The fine beads over a fixed coarse bead flip disjoint coordinate sets of that
cube (`blockFace_noneSet_disjoint`) — a coordinate, once flipped to `1`, never unflips — the same
monotonicity as `SalBraidPartition`'s `blockOf_disjoint`, carried to a wedge map's block faces via
the consecutive-junction identity (`blockFace_junction`).  Equal event counts along a refinement
(`card_eventObj_eq_of_hom`) then upgrade injective to bijective.
-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChain

/-! ## The consecutive-junction identity for block faces

For a wedge map `φ : ⋁ad ⟶ ⋁cd` sending init to init, the read-off cube chain
`wedgeToCubes ⟨ad, φ⟩` links consecutive beads at a common junction vertex.  Pushed through the
block factorisation `ι_j ≫ φ = yoneda (blockFace φ j) ≫ ι_{blockIdx φ j}`, this equates, for
consecutive source beads `j`, `j+1`, the target vertex of `blockFace φ j` with the source vertex
of `blockFace φ (j+1)` inside the wedge. -/

variable {ad cd : List ℕ+}

/-- The target vertex of pushed bead `j` (`vertex₁` of the `j`-th read-off cube) as the target-block
inclusion of `finalVertexMap ≫ blockFace φ j`. -/
theorem vertex₁_pushBead
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (j : Fin ad.length) :
    (⋁cd).toPsh.vertex₁ (yonedaEquiv (ιᵂ ad j ≫ φ))
      = (ιᵂ cd (blockIdx φ j))⟪0⟫
          (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j) := by
  have hce : yonedaEquiv (ιᵂ ad j ≫ φ)
      = (⋁cd).toPsh.map (blockFace φ j).op
          (yonedaEquiv (ιᵂ cd (blockIdx φ j))) :=
    (congrArg yonedaEquiv (blockFace_spec φ j)).trans
      (yonedaEquiv_naturality (ιᵂ cd (blockIdx φ j)) (blockFace φ j)).symm
  rw [hce]
  change (⋁cd).toPsh.map (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ)).op
        ((⋁cd).toPsh.map (blockFace φ j).op
          (yonedaEquiv (ιᵂ cd (blockIdx φ j))))
      = _
  rw [← Functor.map_comp_apply, ← op_comp]
  exact map_yonedaEquiv (ιᵂ cd (blockIdx φ j))
    (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)

/-- The source vertex of pushed bead `j` as the target-block inclusion of
`initVertexMap ≫ blockFace φ j`. -/
theorem vertex₀_pushBead
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (j : Fin ad.length) :
    (⋁cd).toPsh.vertex₀ (yonedaEquiv (ιᵂ ad j ≫ φ))
      = (ιᵂ cd (blockIdx φ j))⟪0⟫
          (PrecubicalSet.initVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j) := by
  have hce : yonedaEquiv (ιᵂ ad j ≫ φ)
      = (⋁cd).toPsh.map (blockFace φ j).op
          (yonedaEquiv (ιᵂ cd (blockIdx φ j))) :=
    (congrArg yonedaEquiv (blockFace_spec φ j)).trans
      (yonedaEquiv_naturality (ιᵂ cd (blockIdx φ j)) (blockFace φ j)).symm
  rw [hce]
  change (⋁cd).toPsh.map (PrecubicalSet.initVertexMap ((ad.get j) : ℕ)).op
        ((⋁cd).toPsh.map (blockFace φ j).op
          (yonedaEquiv (ιᵂ cd (blockIdx φ j))))
      = _
  rw [← Functor.map_comp_apply, ← op_comp]
  exact map_yonedaEquiv (ιᵂ cd (blockIdx φ j))
    (PrecubicalSet.initVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)

/-- The consecutive-junction identity: for consecutive source beads `j, j'` (`j'.val = j.val + 1`)
of a wedge map `φ` sending init to init, the target vertex of pushed bead `j` equals the source
vertex of pushed bead `j'`. -/
theorem blockFace_junction
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    {j j' : Fin ad.length} (hjj' : j'.val = j.val + 1) :
    (ιᵂ cd (blockIdx φ j))⟪0⟫
        (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)
      = (ιᵂ cd (blockIdx φ j'))⟪0⟫
          (PrecubicalSet.initVertexMap ((ad.get j') : ℕ) ≫ blockFace φ j') := by
  rw [← vertex₁_pushBead, ← vertex₀_pushBead]
  -- descend to the read-off cube chain and use its junction link
  set L := wedgeToCubes (K := ⋁cd) ⟨ad, φ⟩ with hLdef
  have hlen : L.length = ad.length := wedgeToCubes_length ad φ
  have hchain : IsCubeChain (⋁cd).init L
      (φ⟪0⟫ (⋁ad).final) := by
    have h := wedgeToCubes_isCubeChain (K := ⋁cd) ad φ
    rwa [hinit] at h
  set jc : Fin L.length := Fin.cast hlen.symm j with hjc
  set jc' : Fin L.length := Fin.cast hlen.symm j' with hjc'
  have hgetc : L.get jc
      = ⟨ad.get j, yonedaEquiv (ιᵂ ad j ≫ φ)⟩ := by
    rw [wedgeToCubes_get ad φ jc]
    have : jc.cast (wedgeToCubes_length ad φ) = j := Fin.ext rfl
    rw [this]
  have hgetc' : L.get jc'
      = ⟨ad.get j', yonedaEquiv (ιᵂ ad j' ≫ φ)⟩ := by
    rw [wedgeToCubes_get ad φ jc']
    have : jc'.cast (wedgeToCubes_length ad φ) = j' := Fin.ext rfl
    rw [this]
  have htgt := isCubeChain_vtx_tgt (⋁cd).init
    (φ⟪0⟫ (⋁ad).final) L hchain jc
  have hsrc := vtxCanon_castSucc L (φ⟪0⟫ (⋁ad).final) jc'
  have hsucc : (jc.succ : Fin (L.length + 1)) = jc'.castSucc := by
    apply Fin.ext
    rw [hjc, hjc']
    change j.val + 1 = j'.val
    omega
  rw [hgetc] at htgt
  rw [hgetc'] at hsrc
  rw [htgt, hsucc]
  exact hsrc

/-! ## Flip monotonicity along the fine beads over a coarse bead

Reading a coordinate `p` of the coarse bead `□^{cd.get r}` through the block faces gives a
transport-free `ℕ`-valued sign `bfSgnN`.  The junction identity says that, at a shared junction of
two consecutive fine beads, the free coordinates of the earlier bead have flipped to `1` while the
free coordinates of the later bead are still `0`.  Hence a coordinate, once `1`, stays `1` — so two
distinct fine beads over the same coarse bead cannot both flip the same coordinate. -/

/-- `ev` of the final-vertex inclusion is the all-`1` vertex. -/
theorem ev_finalVertexMap (n : ℕ) :
    ev (PrecubicalSet.finalVertexMap n) = constVertex n true :=
  ev_canonicalMap _

/-- `ev` of the initial-vertex inclusion is the all-`0` vertex. -/
theorem ev_initVertexMap (n : ℕ) :
    ev (PrecubicalSet.initVertexMap n) = constVertex n false :=
  ev_canonicalMap _

/-- The coordinate-`p` sign of the block face of bead `j`: `none` = free (flips here),
`some false` = still `0`, `some true` = already `1`; out-of-range `none`.  `ℕ`-valued to be
transport-free across the propositionally-equal block dimensions of distinct beads over one coarse
bead. -/
def bfSgnN
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (j : Fin ad.length) (p : ℕ) : Option Bool :=
  if h : p < (cd.get (blockIdx φ j) : ℕ) then (ev (blockFace φ j)).val ⟨p, h⟩ else none

/-- Transport of `ι`-composition across an equality of block indices (proved by `subst`). -/
theorem ι_app_blockcast {R R' : Fin cd.length} (hR : R = R')
    (u : ▫0 ⟶ ▫((cd.get R : ℕ))) :
    (ιᵂ cd R')⟪0⟫ (hR ▸ u)
      = (ιᵂ cd R)⟪0⟫ u := by
  subst hR; rfl

/-- Transport of an `ev`-value read across an equality of block indices (proved by `subst`). -/
theorem ev_val_blockcast {R R' : Fin cd.length} (hR : R = R')
    (u : ▫0 ⟶ ▫((cd.get R : ℕ))) (p : ℕ)
    (hp : p < (cd.get R : ℕ)) (hp' : p < (cd.get R' : ℕ)) :
    (ev (K := stdPre ((cd.get R' : ℕ))) (hR ▸ u)).val ⟨p, hp'⟩
      = (ev u).val ⟨p, hp⟩ := by
  subst hR; rfl

/-- The target-vertex reading of bead `j` at coordinate `p`, through the block face. -/
theorem bfSgnN_end
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (j : Fin ad.length) {p : ℕ} (hp : p < (cd.get (blockIdx φ j) : ℕ)) :
    (if bfSgnN φ j p = none then some true else bfSgnN φ j p)
      = (ev (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)).val
          ⟨p, hp⟩ := by
  rw [ev_comp_app, ev_finalVertexMap, CubeChains.app_constVertex_val]
  simp only [bfSgnN, dif_pos hp, mem_noneSet]

/-- The source-vertex reading of bead `j` at coordinate `p`, through the block face. -/
theorem bfSgnN_start
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (j : Fin ad.length) {p : ℕ} (hp : p < (cd.get (blockIdx φ j) : ℕ)) :
    (if bfSgnN φ j p = none then some false else bfSgnN φ j p)
      = (ev (PrecubicalSet.initVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)).val
          ⟨p, hp⟩ := by
  rw [ev_comp_app, ev_initVertexMap, CubeChains.app_constVertex_val]
  simp only [bfSgnN, dif_pos hp, mem_noneSet]

/-- The value-level junction identity: for consecutive fine beads `j, j'` over the same coarse
bead, the target reading of `j` equals the source reading of `j'` at every in-range coordinate. -/
theorem bfSgnN_junction
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    {j j' : Fin ad.length} (hjj' : j'.val = j.val + 1) (hb : blockIdx φ j = blockIdx φ j')
    {p : ℕ} (hp : p < (cd.get (blockIdx φ j) : ℕ)) :
    (if bfSgnN φ j p = none then some true else bfSgnN φ j p)
      = (if bfSgnN φ j' p = none then some false else bfSgnN φ j' p) := by
  have hp' : p < (cd.get (blockIdx φ j') : ℕ) := hb ▸ hp
  rw [bfSgnN_end φ j hp, bfSgnN_start φ j' hp']
  -- reduce to the box-map junction, stripping `ι` after aligning the block index by `hb`
  have hstrip : (hb ▸ (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)
        : ▫0 ⟶ ▫((cd.get (blockIdx φ j') : ℕ)))
      = PrecubicalSet.initVertexMap ((ad.get j') : ℕ) ≫ blockFace φ j' := by
    have hfab : (ιᵂ cd (blockIdx φ j'))⟪0⟫
          (hb ▸ (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j))
        = (ιᵂ cd (blockIdx φ j'))⟪0⟫
          (PrecubicalSet.initVertexMap ((ad.get j') : ℕ) ≫ blockFace φ j') := by
      rw [ι_app_blockcast hb]
      exact blockFace_junction φ hinit hjj'
    exact serialWedge_ι_app_injective cd (blockIdx φ j') hfab
  calc (ev (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)).val ⟨p, hp⟩
      = (ev (K := stdPre ((cd.get (blockIdx φ j') : ℕ)))
            (hb ▸ (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j))).val
          ⟨p, hp'⟩ := (ev_val_blockcast hb _ p hp hp').symm
    _ = (ev (PrecubicalSet.initVertexMap ((ad.get j') : ℕ) ≫ blockFace φ j')).val
          ⟨p, hp'⟩ :=
        congrArg (fun u : ▫0 ⟶ ▫((cd.get (blockIdx φ j') : ℕ)) =>
          (ev u).val ⟨p, hp'⟩) hstrip

/-! ### The monotone consequence and disjointness -/

/-- The flip step: along consecutive fine beads `j, j'` over the same coarse bead, a coordinate
not still `0` in bead `j` (`≠ some false`) is already `1` (`= some true`) in bead `j'`. -/
theorem bfSgnN_step
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    {j j' : Fin ad.length} (hjj' : j'.val = j.val + 1) (hb : blockIdx φ j = blockIdx φ j')
    {p : ℕ} (hp : p < (cd.get (blockIdx φ j) : ℕ)) (hj : bfSgnN φ j p ≠ some false) :
    bfSgnN φ j' p = some true := by
  have hjunc := bfSgnN_junction φ hinit hjj' hb hp
  -- LHS of the junction is `some true` because bead `j` is `none` or `some true`
  have hlhs : (if bfSgnN φ j p = none then some true else bfSgnN φ j p) = some true := by
    rcases hcase : bfSgnN φ j p with _ | b
    · simp
    · rcases b with _ | _
      · exact absurd hcase hj
      · simp
  rw [hlhs] at hjunc
  -- hence bead `j'` is `some true`
  rcases hcase' : bfSgnN φ j' p with _ | b
  · rw [hcase'] at hjunc; simp at hjunc
  · rcases b with _ | _
    · rw [hcase'] at hjunc; simp at hjunc
    · rfl

/-- The block index is constant on `[i, i']` when `blockIdx φ i = blockIdx φ i'` (monotone
squeeze). -/
theorem blockIdx_const_of_le
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    {i i' m : Fin ad.length} (hr : blockIdx φ i = blockIdx φ i') (him : i ≤ m) (hmi' : m ≤ i') :
    blockIdx φ m = blockIdx φ i := by
  have hmono := serialWedge_blockIdx_monotone φ hinit
  have h1 : blockIdx φ i ≤ blockIdx φ m := hmono him
  have h2 : blockIdx φ m ≤ blockIdx φ i := hr ▸ hmono hmi'
  exact le_antisymm h2 h1

/-- The flip step relativised to a fixed interval `[i, i']` (`'`): for consecutive beads `j, j'`
inside `[i, i']`, all over the same coarse bead, a coordinate not still `0` in `j` is already `1`
in `j'`. -/
theorem bfSgnN_step'
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    {i i' j j' : Fin ad.length} (hr : blockIdx φ i = blockIdx φ i')
    (hij : i ≤ j) (hjj' : j'.val = j.val + 1) (hj'i' : j' ≤ i')
    {p : ℕ} (hp : p < (cd.get (blockIdx φ i) : ℕ)) (hj : bfSgnN φ j p ≠ some false) :
    bfSgnN φ j' p = some true := by
  have hjj'le : j ≤ j' := Fin.le_def.mpr (by omega)
  have hji' : j ≤ i' := le_trans hjj'le hj'i'
  have hbj : blockIdx φ j = blockIdx φ i := blockIdx_const_of_le φ hinit hr hij hji'
  have hbj' : blockIdx φ j' = blockIdx φ i :=
    blockIdx_const_of_le φ hinit hr (le_trans hij hjj'le) hj'i'
  have hb : blockIdx φ j = blockIdx φ j' := by rw [hbj, hbj']
  have hpj : p < (cd.get (blockIdx φ j) : ℕ) := by rw [hbj]; exact hp
  exact bfSgnN_step φ hinit hjj' hb hpj hj

/-- Once flipped, stays flipped: if coordinate `p` is free in bead `i` (`bfSgnN = none`), it is
already `1` in every later bead `i'` over the same coarse bead. -/
theorem bfSgnN_flip
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    {i i' : Fin ad.length} (hii : i < i') (hr : blockIdx φ i = blockIdx φ i')
    {p : ℕ} (hp : p < (cd.get (blockIdx φ i) : ℕ)) (hpi : bfSgnN φ i p = none) :
    bfSgnN φ i' p = some true := by
  have hii' : i.val < i'.val := hii
  have key : ∀ n, i.val + 1 ≤ n → ∀ (hn' : n < ad.length), n ≤ i'.val →
      bfSgnN φ ⟨n, hn'⟩ p = some true := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro hn' hle
      exact bfSgnN_step' (j := i) φ hinit hr (le_refl i) rfl (Fin.le_def.mpr hle) hp
        (by rw [hpi]; simp)
    | succ m hm ih =>
      intro hn' hle
      have hmlt : m < ad.length := by omega
      have hmle : m ≤ i'.val := by omega
      have hprev : bfSgnN φ ⟨m, hmlt⟩ p = some true := ih hmlt hmle
      exact bfSgnN_step' (j := ⟨m, hmlt⟩) φ hinit hr
        (Fin.le_def.mpr (show i.val ≤ m from by omega)) rfl
        (Fin.le_def.mpr hle) hp (by rw [hprev]; simp)
  exact key i'.val (by omega) i'.isLt (le_refl _)

/-- Within-coarse-bead disjointness of the block-face free sets: two distinct fine beads over the
same coarse bead cannot both leave a coordinate free (once `i` flips `p`, `p` is `1` in `i'`). -/
theorem blockFace_noneSet_disjoint
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    {i i' : Fin ad.length} (hii : i < i') (hr : blockIdx φ i = blockIdx φ i')
    {p : ℕ} (hp : p < (cd.get (blockIdx φ i) : ℕ))
    (hpi : bfSgnN φ i p = none) (hpi' : bfSgnN φ i' p = none) : False := by
  have hflip : bfSgnN φ i' p = some true := bfSgnN_flip φ hinit hii hr hp hpi
  rw [hflip] at hpi'
  simp at hpi'

end CubeChain

namespace CubeChains

open CubeChain

variable {K : BPSet}

/-! ## `eventMap` is bijective

Injectivity is the within-coarse-bead disjointness (`blockFace_noneSet_disjoint`): colliding events
share a coarse bead and coordinate, but distinct fine beads there flip disjoint coordinate sets.
Equal event counts (`card_eventObj_eq_of_hom`) upgrade injective to bijective, hence surjective. -/

/-- `eventMap` is injective: a collision forces the same coarse bead and coordinate, but distinct
fine beads over that coarse bead flip disjoint coordinate sets (`blockFace_noneSet_disjoint`). -/
theorem eventMap_injective_hom {a b : Ch K} (f : a ⟶ b) :
    Function.Injective (eventMap f) := by
  rintro ⟨i, x⟩ ⟨i', x'⟩ he
  set φ := fᵂ with hφ
  have hinit : φ⟪0⟫ (⋁a.dims).init
      = (⋁b.dims).init := f.φ.app_init
  have hidx : blockIdx φ i = blockIdx φ i' := congrArg Sigma.fst he
  have hval : (faceEmb (blockFace φ i) x).val = (faceEmb (blockFace φ i') x').val :=
    congrArg (fun e : EventObj b => (e.2 : ℕ)) he
  -- a face-embedded coordinate is free in its bead
  have free : ∀ {j : ChainCat.Bead a} (y : Fin (ChainCat.beadDim a j)),
      bfSgnN φ j ((faceEmb (blockFace φ j) y).val) = none := by
    intro j y
    have hlt := (faceEmb (blockFace φ j) y).isLt
    have hmem : (ev (blockFace φ j)).val (faceEmb (blockFace φ j) y) = none :=
      mem_noneSet.mp
        (Finset.orderEmbOfFin_mem _ (ev (blockFace φ j)).prop y)
    simp only [bfSgnN]
    rw [dif_pos hlt,
      show (⟨(faceEmb (blockFace φ j) y).val, hlt⟩ : Fin _) = faceEmb (blockFace φ j) y from
        Fin.ext rfl]
    exact hmem
  rcases eq_or_ne i i' with hii | hii
  · subst hii
    have hx : x = x' := (faceEmb (blockFace φ i)).injective (Fin.ext hval)
    rw [hx]
  · rcases lt_or_gt_of_ne hii with hlt | hlt
    · exact (blockFace_noneSet_disjoint φ hinit hlt hidx
        (faceEmb (blockFace φ i) x).isLt (free x) (by rw [hval]; exact free x')).elim
    · exact (blockFace_noneSet_disjoint φ hinit hlt hidx.symm
        (faceEmb (blockFace φ i') x').isLt (free x') (by rw [← hval]; exact free x)).elim

/-- `eventMap` is bijective: injective plus equal source/target event counts along a refinement
(`card_eventObj_eq_of_hom`). -/
theorem eventMap_bijective {a b : Ch K} (f : a ⟶ b) :
    Function.Bijective (eventMap f) :=
  (Fintype.bijective_iff_injective_and_card (eventMap f)).mpr
    ⟨eventMap_injective_hom f, card_eventObj_eq_of_hom f⟩

/-- `eventMap` is surjective for every `K`: the discharge of the `Surjective (eventMap f)` input of
the cone-monotonicity results. -/
theorem eventMap_surjective {a b : Ch K} (f : a ⟶ b) :
    Function.Surjective (eventMap f) :=
  (eventMap_bijective f).surjective

/-! ## The event bijection -/

/-- The event bijection along a refinement.  The inverse is a computable `Fintype.bijInv` search
(coarse event ↦ the fine event it comes from), so `eventEquiv` `#eval`s both ways. -/
def eventEquiv {a b : Ch K} (f : a ⟶ b) : EventObj a ≃ EventObj b where
  toFun := eventMap f
  invFun := Fintype.bijInv (eventMap_bijective f)
  left_inv := Fintype.leftInverse_bijInv _
  right_inv := Fintype.rightInverse_bijInv _

theorem eventEquiv_id (a : Ch K) : eventEquiv (𝟙 a) = Equiv.refl (EventObj a) :=
  Equiv.ext eventMap_id

theorem eventEquiv_comp {a b c : Ch K} (f : a ⟶ b) (g : b ⟶ c) :
    eventEquiv (f ≫ g) = (eventEquiv f).trans (eventEquiv g) :=
  Equiv.ext fun e => eventMap_comp f g e

end CubeChains
