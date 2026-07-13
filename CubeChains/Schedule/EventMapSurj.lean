import CubeChains.Schedule.OccurrenceCone
import CubeChains.Schedule.EventLocalSystem
import CubeChains.Salvetti.SalBraidPartition

/-!
# Schedule/EventMapSurj — `eventMap` is bijective for every `K`

`eventMap f : EventObj a → EventObj b` (`Schedule/EventNaming.lean`) reads only the block data of
`f.φ.hom`, never `K`, and is bijective for every bi-pointed `K` with no side conditions — the
general-`K` upgrade of the cube fact `cube_eventMap_bijective`.

The proof is injective-first, reduced to a within-cube fact: two events of `a` collide under
`eventMap f` iff they land in the same coarse bead `r = blockIdx φ i` and hit the same direction of
`□^{b.dims.get r}`.  The fine beads over a fixed coarse bead flip disjoint coordinate sets of that
cube (`blockFace_noneSet_disjoint`) — a coordinate, once flipped to `1`, never unflips — the same
monotonicity as `SalBraidPartition`'s `blockOf_disjoint`, carried to a wedge map's block faces via
the consecutive-junction identity (`blockFace_junction`).  Equal event counts along a refinement
(`card_eventObj_eq_of_hom`) then upgrade injective to bijective, discharging the sole non-free input
`Surjective (eventMap f)` of the `OccurrenceCone`/`ChainCone` monotonicity corollaries.
-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChain

/-! ## The consecutive-junction identity for block faces

For a wedge map `φ : □^∨(ad) ⟶ □^∨(cd)` sending init to init, the read-off cube chain
`wedgeToCubes ⟨ad, φ⟩` links consecutive beads at a common junction vertex.  Pushed through the
block factorisation `ι_j ≫ φ = yoneda (blockFace φ j) ≫ ι_{blockIdx φ j}`, this equates, for
consecutive source beads `j`, `j+1`, the target vertex of `blockFace φ j` with the source vertex
of `blockFace φ (j+1)` inside the wedge. -/

variable {ad cd : List ℕ+}

/-- The target vertex of pushed bead `j` (`vertex₁` of the `j`-th read-off cube) as the target-block
inclusion of `finalVertexMap ≫ blockFace φ j`. -/
theorem vertex₁_pushBead
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh) (j : Fin ad.length) :
    (BPSet.serialWedge cd).toPsh.vertex₁ (yonedaEquiv (BPSet.serialWedge.ι ad j ≫ φ))
      = (BPSet.serialWedge.ι cd (blockIdx φ j)).app (op (Box.ob 0))
          (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j) := by
  have hce : yonedaEquiv (BPSet.serialWedge.ι ad j ≫ φ)
      = (BPSet.serialWedge cd).toPsh.map (blockFace φ j).op
          (yonedaEquiv (BPSet.serialWedge.ι cd (blockIdx φ j))) :=
    (congrArg yonedaEquiv (blockFace_spec φ j)).trans
      (yonedaEquiv_naturality (BPSet.serialWedge.ι cd (blockIdx φ j)) (blockFace φ j)).symm
  rw [hce]
  change (BPSet.serialWedge cd).toPsh.map (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ)).op
        ((BPSet.serialWedge cd).toPsh.map (blockFace φ j).op
          (yonedaEquiv (BPSet.serialWedge.ι cd (blockIdx φ j))))
      = _
  rw [← Functor.map_comp_apply, ← op_comp]
  exact map_yonedaEquiv (BPSet.serialWedge.ι cd (blockIdx φ j))
    (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)

/-- The source vertex of pushed bead `j` as the target-block inclusion of
`initVertexMap ≫ blockFace φ j`. -/
theorem vertex₀_pushBead
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh) (j : Fin ad.length) :
    (BPSet.serialWedge cd).toPsh.vertex₀ (yonedaEquiv (BPSet.serialWedge.ι ad j ≫ φ))
      = (BPSet.serialWedge.ι cd (blockIdx φ j)).app (op (Box.ob 0))
          (PrecubicalSet.initVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j) := by
  have hce : yonedaEquiv (BPSet.serialWedge.ι ad j ≫ φ)
      = (BPSet.serialWedge cd).toPsh.map (blockFace φ j).op
          (yonedaEquiv (BPSet.serialWedge.ι cd (blockIdx φ j))) :=
    (congrArg yonedaEquiv (blockFace_spec φ j)).trans
      (yonedaEquiv_naturality (BPSet.serialWedge.ι cd (blockIdx φ j)) (blockFace φ j)).symm
  rw [hce]
  change (BPSet.serialWedge cd).toPsh.map (PrecubicalSet.initVertexMap ((ad.get j) : ℕ)).op
        ((BPSet.serialWedge cd).toPsh.map (blockFace φ j).op
          (yonedaEquiv (BPSet.serialWedge.ι cd (blockIdx φ j))))
      = _
  rw [← Functor.map_comp_apply, ← op_comp]
  exact map_yonedaEquiv (BPSet.serialWedge.ι cd (blockIdx φ j))
    (PrecubicalSet.initVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)

/-- The consecutive-junction identity: for consecutive source beads `j, j'` (`j'.val = j.val + 1`)
of a wedge map `φ` sending init to init, the target vertex of pushed bead `j` equals the source
vertex of pushed bead `j'`. -/
theorem blockFace_junction
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (hinit : φ.app (op (Box.ob 0)) (BPSet.serialWedge ad).init = (BPSet.serialWedge cd).init)
    {j j' : Fin ad.length} (hjj' : j'.val = j.val + 1) :
    (BPSet.serialWedge.ι cd (blockIdx φ j)).app (op (Box.ob 0))
        (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)
      = (BPSet.serialWedge.ι cd (blockIdx φ j')).app (op (Box.ob 0))
          (PrecubicalSet.initVertexMap ((ad.get j') : ℕ) ≫ blockFace φ j') := by
  rw [← vertex₁_pushBead, ← vertex₀_pushBead]
  -- descend to the read-off cube chain and use its junction link
  set L := wedgeToCubes (K := BPSet.serialWedge cd) ⟨ad, φ⟩ with hLdef
  have hlen : L.length = ad.length := wedgeToCubes_length ad φ
  have hchain : IsCubeChain (BPSet.serialWedge cd).init L
      (φ.app (op (Box.ob 0)) (BPSet.serialWedge ad).final) := by
    have h := wedgeToCubes_isCubeChain (K := BPSet.serialWedge cd) ad φ
    rwa [hinit] at h
  set jc : Fin L.length := Fin.cast hlen.symm j with hjc
  set jc' : Fin L.length := Fin.cast hlen.symm j' with hjc'
  have hgetc : L.get jc
      = ⟨ad.get j, yonedaEquiv (BPSet.serialWedge.ι ad j ≫ φ)⟩ := by
    rw [wedgeToCubes_get ad φ jc]
    have : jc.cast (wedgeToCubes_length ad φ) = j := Fin.ext rfl
    rw [this]
  have hgetc' : L.get jc'
      = ⟨ad.get j', yonedaEquiv (BPSet.serialWedge.ι ad j' ≫ φ)⟩ := by
    rw [wedgeToCubes_get ad φ jc']
    have : jc'.cast (wedgeToCubes_length ad φ) = j' := Fin.ext rfl
    rw [this]
  have htgt := isCubeChain_vtx_tgt (BPSet.serialWedge cd).init
    (φ.app (op (Box.ob 0)) (BPSet.serialWedge ad).final) L hchain jc
  have hsrc := vtxCanon_castSucc L (φ.app (op (Box.ob 0)) (BPSet.serialWedge ad).final) jc'
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
    StdCube.ev (PrecubicalSet.finalVertexMap n) = StdCube.constVertex n true :=
  StdCube.ev_canonicalMap _

/-- `ev` of the initial-vertex inclusion is the all-`0` vertex. -/
theorem ev_initVertexMap (n : ℕ) :
    StdCube.ev (PrecubicalSet.initVertexMap n) = StdCube.constVertex n false :=
  StdCube.ev_canonicalMap _

/-- The coordinate-`p` sign of the block face of bead `j`: `none` = free (flips here),
`some false` = still `0`, `some true` = already `1`; out-of-range `none`.  `ℕ`-valued to be
transport-free across the propositionally-equal block dimensions of distinct beads over one coarse
bead. -/
noncomputable def bfSgnN
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (j : Fin ad.length) (p : ℕ) : Option Bool :=
  if h : p < (cd.get (blockIdx φ j) : ℕ) then (StdCube.ev (blockFace φ j)).val ⟨p, h⟩ else none

/-- Transport of `ι`-composition across an equality of block indices (proved by `subst`). -/
theorem ι_app_blockcast {R R' : Fin cd.length} (hR : R = R')
    (u : Box.ob 0 ⟶ Box.ob ((cd.get R : ℕ))) :
    (BPSet.serialWedge.ι cd R').app (op (Box.ob 0)) (hR ▸ u)
      = (BPSet.serialWedge.ι cd R).app (op (Box.ob 0)) u := by
  subst hR; rfl

/-- Transport of an `ev`-value read across an equality of block indices (proved by `subst`). -/
theorem ev_val_blockcast {R R' : Fin cd.length} (hR : R = R')
    (u : Box.ob 0 ⟶ Box.ob ((cd.get R : ℕ))) (p : ℕ)
    (hp : p < (cd.get R : ℕ)) (hp' : p < (cd.get R' : ℕ)) :
    (StdCube.ev (K := StdCube.stdPre ((cd.get R' : ℕ))) (hR ▸ u)).val ⟨p, hp'⟩
      = (StdCube.ev u).val ⟨p, hp⟩ := by
  subst hR; rfl

/-- The target-vertex reading of bead `j` at coordinate `p`, through the block face. -/
theorem bfSgnN_end
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (j : Fin ad.length) {p : ℕ} (hp : p < (cd.get (blockIdx φ j) : ℕ)) :
    (if bfSgnN φ j p = none then some true else bfSgnN φ j p)
      = (StdCube.ev (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)).val
          ⟨p, hp⟩ := by
  rw [ev_comp_app, ev_finalVertexMap, FinalBraid.app_constVertex_val]
  simp only [bfSgnN, dif_pos hp, StdCube.mem_noneSet]

/-- The source-vertex reading of bead `j` at coordinate `p`, through the block face. -/
theorem bfSgnN_start
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (j : Fin ad.length) {p : ℕ} (hp : p < (cd.get (blockIdx φ j) : ℕ)) :
    (if bfSgnN φ j p = none then some false else bfSgnN φ j p)
      = (StdCube.ev (PrecubicalSet.initVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)).val
          ⟨p, hp⟩ := by
  rw [ev_comp_app, ev_initVertexMap, FinalBraid.app_constVertex_val]
  simp only [bfSgnN, dif_pos hp, StdCube.mem_noneSet]

/-- The value-level junction identity: for consecutive fine beads `j, j'` over the same coarse
bead, the target reading of `j` equals the source reading of `j'` at every in-range coordinate. -/
theorem bfSgnN_junction
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (hinit : φ.app (op (Box.ob 0)) (BPSet.serialWedge ad).init = (BPSet.serialWedge cd).init)
    {j j' : Fin ad.length} (hjj' : j'.val = j.val + 1) (hb : blockIdx φ j = blockIdx φ j')
    {p : ℕ} (hp : p < (cd.get (blockIdx φ j) : ℕ)) :
    (if bfSgnN φ j p = none then some true else bfSgnN φ j p)
      = (if bfSgnN φ j' p = none then some false else bfSgnN φ j' p) := by
  have hp' : p < (cd.get (blockIdx φ j') : ℕ) := hb ▸ hp
  rw [bfSgnN_end φ j hp, bfSgnN_start φ j' hp']
  -- reduce to the box-map junction, stripping `ι` after aligning the block index by `hb`
  have hstrip : (hb ▸ (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)
        : Box.ob 0 ⟶ Box.ob ((cd.get (blockIdx φ j') : ℕ)))
      = PrecubicalSet.initVertexMap ((ad.get j') : ℕ) ≫ blockFace φ j' := by
    have hfab : (BPSet.serialWedge.ι cd (blockIdx φ j')).app (op (Box.ob 0))
          (hb ▸ (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j))
        = (BPSet.serialWedge.ι cd (blockIdx φ j')).app (op (Box.ob 0))
          (PrecubicalSet.initVertexMap ((ad.get j') : ℕ) ≫ blockFace φ j') := by
      rw [ι_app_blockcast hb]
      exact blockFace_junction φ hinit hjj'
    exact serialWedge_ι_app_injective cd (blockIdx φ j') hfab
  calc (StdCube.ev (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j)).val ⟨p, hp⟩
      = (StdCube.ev (K := StdCube.stdPre ((cd.get (blockIdx φ j') : ℕ)))
            (hb ▸ (PrecubicalSet.finalVertexMap ((ad.get j) : ℕ) ≫ blockFace φ j))).val
          ⟨p, hp'⟩ := (ev_val_blockcast hb _ p hp hp').symm
    _ = (StdCube.ev (PrecubicalSet.initVertexMap ((ad.get j') : ℕ) ≫ blockFace φ j')).val
          ⟨p, hp'⟩ :=
        congrArg (fun u : Box.ob 0 ⟶ Box.ob ((cd.get (blockIdx φ j') : ℕ)) =>
          (StdCube.ev u).val ⟨p, hp'⟩) hstrip

/-! ### The monotone consequence and disjointness -/

/-- The flip step: along consecutive fine beads `j, j'` over the same coarse bead, a coordinate
not still `0` in bead `j` (`≠ some false`) is already `1` (`= some true`) in bead `j'`. -/
theorem bfSgnN_step
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (hinit : φ.app (op (Box.ob 0)) (BPSet.serialWedge ad).init = (BPSet.serialWedge cd).init)
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
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (hinit : φ.app (op (Box.ob 0)) (BPSet.serialWedge ad).init = (BPSet.serialWedge cd).init)
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
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (hinit : φ.app (op (Box.ob 0)) (BPSet.serialWedge ad).init = (BPSet.serialWedge cd).init)
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
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (hinit : φ.app (op (Box.ob 0)) (BPSet.serialWedge ad).init = (BPSet.serialWedge cd).init)
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
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (hinit : φ.app (op (Box.ob 0)) (BPSet.serialWedge ad).init = (BPSet.serialWedge cd).init)
    {i i' : Fin ad.length} (hii : i < i') (hr : blockIdx φ i = blockIdx φ i')
    {p : ℕ} (hp : p < (cd.get (blockIdx φ i) : ℕ))
    (hpi : bfSgnN φ i p = none) (hpi' : bfSgnN φ i' p = none) : False := by
  have hflip : bfSgnN φ i' p = some true := bfSgnN_flip φ hinit hii hr hp hpi
  rw [hflip] at hpi'
  simp at hpi'

end CubeChain

namespace FinalBraid

open CubeChain HDA

variable {K : BPSet}

/-! ## `eventMap` is bijective, and the cone corollaries

Injectivity is the within-coarse-bead disjointness (`blockFace_noneSet_disjoint`): colliding events
share a coarse bead and coordinate, but distinct fine beads there flip disjoint coordinate sets.
Equal event counts (`card_eventObj_eq_of_hom`) upgrade injective to bijective, hence surjective. -/

/-- `eventMap` is injective: a collision forces the same coarse bead and coordinate, but distinct
fine beads over that coarse bead flip disjoint coordinate sets (`blockFace_noneSet_disjoint`). -/
theorem eventMap_injective_hom {a b : ChainCat.Obj K} (f : a ⟶ b) :
    Function.Injective (eventMap f) := by
  rintro ⟨i, x⟩ ⟨i', x'⟩ he
  set φ := f.φ.hom with hφ
  have hinit : φ.app (op (Box.ob 0)) (BPSet.serialWedge a.dims).init
      = (BPSet.serialWedge b.dims).init := f.φ.app_init
  have hidx : blockIdx φ i = blockIdx φ i' := congrArg Sigma.fst he
  have hval : (faceEmb (blockFace φ i) x).val = (faceEmb (blockFace φ i') x').val :=
    congrArg (fun e : EventObj b => (e.2 : ℕ)) he
  -- a face-embedded coordinate is free in its bead
  have free : ∀ {j : Fin a.dims.length} (y : Fin ((a.dims.get j : ℕ))),
      bfSgnN φ j ((faceEmb (blockFace φ j) y).val) = none := by
    intro j y
    have hlt := (faceEmb (blockFace φ j) y).isLt
    have hmem : (StdCube.ev (blockFace φ j)).val (faceEmb (blockFace φ j) y) = none :=
      StdCube.mem_noneSet.mp
        (Finset.orderEmbOfFin_mem _ (StdCube.ev (blockFace φ j)).prop y)
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
theorem eventMap_bijective {a b : ChainCat.Obj K} (f : a ⟶ b) :
    Function.Bijective (eventMap f) :=
  (Fintype.bijective_iff_injective_and_card (eventMap f)).mpr
    ⟨eventMap_injective_hom f, card_eventObj_eq_of_hom f⟩

/-- `eventMap` is surjective for every `K`: the discharge of `Surjective (eventMap f)` the cone
corollaries need. -/
theorem eventMap_surjective {a b : ChainCat.Obj K} (f : a ⟶ b) :
    Function.Surjective (eventMap f) :=
  (eventMap_bijective f).surjective

variable {A : Type}

/-- Occurrence-cone monotonicity for every `K`: `eventMap_surjective` discharges the sole input of
`hdaConeOcc_mem_of_pullback` (`'` = general-`K` form of `hdaConeOcc_mem_of_pullback_cube`). -/
theorem hdaConeOcc_mem_of_pullback' {a b : ChainCat.Obj K} (f : a ⟶ b) {s : EventObj b → ℝ}
    (hs : (fun e : EventObj a => s (eventMap f e)) ∈ hdaConeOcc a) :
    s ∈ hdaConeOcc b :=
  hdaConeOcc_mem_of_pullback f (eventMap_surjective f) hs

/-- Label-cone monotonicity `hdaCone ℓ a ⊆ hdaCone ℓ b` for every `K` (contrast `hdaCone_mono_run`,
which consumed `RunInjective`): `eventMap_surjective` feeds `hdaCone_mono_via_occ`. -/
theorem hdaCone_mono' (ℓ : EdgeLabelling K A) {a b : ChainCat.Obj K} (f : a ⟶ b) :
    hdaCone ℓ a ⊆ hdaCone ℓ b :=
  hdaCone_mono_via_occ ℓ f (eventMap_surjective f)

end FinalBraid
