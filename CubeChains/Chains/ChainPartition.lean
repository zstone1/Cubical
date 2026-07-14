import CubeChains.Salvetti.SalBraidChain
import CubeChains.Events.EventNaming

/-!
# Chains/ChainPartition — the chain of an ordered partition of a chain's events

An **ordered partition** of the events of a cube chain `a` is a surjection `β : EventObj a → Fin m`
that is strictly increasing across `a`'s beads.  Every such `β` is realised by a refinement of `a`:
block `j` is the braid-chain cell (`blockStar`) cut out of `a`'s bead `pbead j` by `β`, consecutive
blocks glue — inside a bead by the junction vertices, across beads by `serialWedge_junction` — and
the chain they form is `pchain β`, refining `a` by `prefine β`.  Its event map is `β` back again
(`beta_eventMap`), so an ordered partition and its refinement carry the same data.
-/

open CategoryTheory Opposite CubeChain StdCube BPSet

namespace CubeChain

/-- **The block data of a wedge map is read off any factorisation.**  Packaged as a `Σ`-equation:
the block index and the block face are determined together, so no transport is needed. -/
theorem blockData_eq_of_factor {ad cd : List ℕ+}
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh) (i : Fin ad.length)
    (r : Fin cd.length) (g : ▫((ad.get i : ℕ)) ⟶ ▫((cd.get r : ℕ)))
    (h : ιᵂ ad i ≫ φ = yoneda.map g ≫ ιᵂ cd r) :
    (⟨blockIdx φ i, blockFace φ i⟩ :
        Σ R : Fin cd.length, ▫((ad.get i : ℕ)) ⟶ ▫((cd.get R : ℕ)))
      = ⟨r, g⟩ := by
  have hr : r = blockIdx φ i := blockIdx_eq_of_factor φ i r g h
  subst hr
  have hsp := (blockFace_spec φ i).symm.trans h
  have hcell : (ιᵂ cd (blockIdx φ i))⟪((ad.get i : ℕ))⟫
        (blockFace φ i)
      = (ιᵂ cd (blockIdx φ i))⟪((ad.get i : ℕ))⟫ g := by
    have h1 := congrArg yonedaEquiv hsp
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map] at h1
  rw [serialWedge_ι_app_injective cd (blockIdx φ i) hcell]

end CubeChain

namespace CubeChains

variable {K : BPSet}

/-! ## The gluing data of a serial wedge

The taut chain of `⋁dims` (one bead per cube) supplies the three facts the tie-block construction
glues along: the first bead starts at `init`, the last ends at `final`, consecutive beads meet. -/

section Wedge

variable (dims : List ℕ+)

/-- Blocks of a serial wedge are read off its taut chain. -/
theorem tautCubes_isChain :
    IsCubeChain (BPSet.serialWedge dims).init
      (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩)
      (BPSet.serialWedge dims).final := by
  have h := wedgeToCubes_isCubeChain (K := BPSet.serialWedge dims) dims
    (𝟙 (BPSet.serialWedge dims).toPsh)
  simpa using h

theorem tautCubes_get (R : Fin dims.length)
    (k : Fin (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).length)
    (hk : k.val = R.val) :
    (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).get k
      = ⟨dims.get R, yonedaEquiv (ιᵂ dims R)⟩ := by
  rw [wedgeToCubes_get dims _ k]
  have hcast : k.cast (wedgeToCubes_length dims (𝟙 (BPSet.serialWedge dims).toPsh)) = R :=
    Fin.ext hk
  rw [hcast, Category.comp_id]

/-- The initial vertex of the wedge is the initial vertex of its first block. -/
theorem serialWedge_init_ι (R : Fin dims.length) (hR : R.val = 0) :
    (ιᵂ dims R)⟪0⟫
        (PrecubicalSet.initVertexMap ((dims.get R : ℕ)))
      = (BPSet.serialWedge dims).init := by
  have hlen : (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).length = dims.length :=
    wedgeToCubes_length dims _
  have hpos : 0 < (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).length := by
    rw [hlen]; omega
  have hzero := isCubeChain_vtx_zero (BPSet.serialWedge dims).init (BPSet.serialWedge dims).final
    _ (tautCubes_isChain dims)
  have hget := tautCubes_get dims R ⟨0, hpos⟩ hR.symm
  have hsrc := vtxCanon_castSucc (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩)
    (BPSet.serialWedge dims).final ⟨0, hpos⟩
  rw [hget] at hsrc
  rw [PrecubicalSet.vertex₀_yonedaEquiv] at hsrc
  have h0 : (⟨0, hpos⟩ : Fin _).castSucc = 0 := Fin.ext rfl
  rw [h0, hzero] at hsrc
  exact hsrc.symm

/-- The final vertex of the wedge is the final vertex of its last block. -/
theorem serialWedge_final_ι (R : Fin dims.length) (hR : R.val + 1 = dims.length) :
    (ιᵂ dims R)⟪0⟫
        (PrecubicalSet.finalVertexMap ((dims.get R : ℕ)))
      = (BPSet.serialWedge dims).final := by
  have hlen : (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).length = dims.length :=
    wedgeToCubes_length dims _
  have hRlt : R.val < (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).length := by
    rw [hlen]; exact R.isLt
  have htgt := isCubeChain_vtx_tgt (BPSet.serialWedge dims).init (BPSet.serialWedge dims).final
    _ (tautCubes_isChain dims) ⟨R.val, hRlt⟩
  rw [tautCubes_get dims R ⟨R.val, hRlt⟩ rfl, PrecubicalSet.vertex₁_yonedaEquiv] at htgt
  have hsucc : (⟨R.val, hRlt⟩ : Fin _).succ
      = Fin.last (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).length :=
    Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
  rw [hsucc, vtxCanon_last] at htgt
  exact htgt

/-- Consecutive blocks of a serial wedge meet: the final vertex of block `R` is the initial vertex
of block `R + 1`. -/
theorem serialWedge_junction {R R' : Fin dims.length} (h : R'.val = R.val + 1) :
    (ιᵂ dims R)⟪0⟫
        (PrecubicalSet.finalVertexMap ((dims.get R : ℕ)))
      = (ιᵂ dims R')⟪0⟫
          (PrecubicalSet.initVertexMap ((dims.get R' : ℕ))) := by
  have hlen : (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).length = dims.length :=
    wedgeToCubes_length dims _
  have hRlt : R.val < (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).length := by
    rw [hlen]; exact R.isLt
  have hR'lt : R'.val < (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).length := by
    rw [hlen]; exact R'.isLt
  have htgt := isCubeChain_vtx_tgt (BPSet.serialWedge dims).init (BPSet.serialWedge dims).final
    _ (tautCubes_isChain dims) ⟨R.val, hRlt⟩
  have hsrc := vtxCanon_castSucc (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩)
    (BPSet.serialWedge dims).final ⟨R'.val, hR'lt⟩
  rw [tautCubes_get dims R ⟨R.val, hRlt⟩ rfl, PrecubicalSet.vertex₁_yonedaEquiv] at htgt
  rw [tautCubes_get dims R' ⟨R'.val, hR'lt⟩ rfl, PrecubicalSet.vertex₀_yonedaEquiv] at hsrc
  have hsucc : (⟨R.val, hRlt⟩ : Fin _).succ = (⟨R'.val, hR'lt⟩ : Fin _).castSucc :=
    Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
  rw [hsucc] at htgt
  exact htgt.trans hsrc

/-- Naturality of a block inclusion at the source vertex. -/
theorem ι_app_vertex₀ (R : Fin dims.length) {k : ℕ}
    (x : (BPSet.cube ((dims.get R : ℕ))).cells k) :
    (BPSet.serialWedge dims).toPsh.vertex₀
        ((ιᵂ dims R)⟪k⟫ x)
      = (ιᵂ dims R)⟪0⟫
          ((BPSet.cube ((dims.get R : ℕ))).toPsh.vertex₀ x) :=
  (PrecubicalSet.map_vertex₀ (ιᵂ dims R) x).symm

/-- Naturality of a block inclusion at the target vertex. -/
theorem ι_app_vertex₁ (R : Fin dims.length) {k : ℕ}
    (x : (BPSet.cube ((dims.get R : ℕ))).cells k) :
    (BPSet.serialWedge dims).toPsh.vertex₁
        ((ιᵂ dims R)⟪k⟫ x)
      = (ιᵂ dims R)⟪0⟫
          ((BPSet.cube ((dims.get R : ℕ))).toPsh.vertex₁ x) :=
  (PrecubicalSet.map_vertex₁ (ιᵂ dims R) x).symm

/-- The Yoneda classifier of a cell of a block. -/
theorem yonedaEquiv_symm_ι_app (R : Fin dims.length) {k : ℕ}
    (g : ▫k ⟶ ▫((dims.get R : ℕ))) :
    yonedaEquiv.symm ((ιᵂ dims R)⟪k⟫ g)
      = yoneda.map g ≫ ιᵂ dims R := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rfl

end Wedge

/-! ## The chain of an ordered partition

An **ordered partition** of `a`'s events — a surjection `β : EventObj a → Fin m`, strictly
increasing across `a`'s beads — is the tie pattern of a timing in `a`'s cone.  It is realised by a
refinement of `a`: block `j` is the braid-chain cell (`blockStar`, `Salvetti/SalBraidChain`) cut out
of `a`'s bead `pbead j` by `β`.  Consecutive blocks glue — inside a bead by the junction vertices,
across beads by `serialWedge_junction`. -/

/-- **Reading an event off a block cell.**  If the `j`-th block cell of a refinement is the star
vector `w` of bead `R`, then the events of bead `j` are the free coordinates of `w`, inside bead `R`
of `a`.  The `Σ`-form of the hypothesis carries the (propositional) equality of the two bead
dimensions, so `d` can be substituted away and no transport survives. -/
theorem eventMap_of_cellSigma {K : BPSet} {a c : Ch K} (f : c ⟶ a)
    (j : ChainCat.Bead c) (δ : Fin ((ChainCat.beadDim c j)))
    (R : ChainCat.Bead a) {d : ℕ+} (w : Cell ((ChainCat.beadDim a R)) ((d : ℕ)))
    (hSig : (⟨c.dims.get j, yonedaEquiv (ιᵂ c.dims j ≫ fᵂ)⟩
          : Σ n : ℕ+, (BPSet.serialWedge a.dims).cells (n : ℕ))
        = ⟨d, (ιᵂ a.dims R)⟪((d : ℕ))⟫
              (canonicalMap w)⟩) :
    ∃ p ∈ noneSet w.val, eventMap f ⟨j, δ⟩ = ⟨R, p⟩ := by
  have hd : (c.dims.get j : ℕ+) = d := congrArg Sigma.fst hSig
  subst hd
  have hcell : yonedaEquiv (ιᵂ c.dims j ≫ fᵂ)
      = (ιᵂ a.dims R)⟪((ChainCat.beadDim c j))⟫
          (canonicalMap w) := by
    have h := (Sigma.mk.inj hSig).2
    exact eq_of_heq h
  set g : ▫((ChainCat.beadDim c j)) ⟶ ▫((ChainCat.beadDim a R)) :=
    canonicalMap w with hg
  have hfac : ιᵂ c.dims j ≫ fᵂ
      = yoneda.map g ≫ ιᵂ a.dims R := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact hcell
  have hbd := blockData_eq_of_factor fᵂ j R g hfac
  have hev : ev g = w := by
    rw [hg]
    exact ev_canonicalMap (K := stdPre ((ChainCat.beadDim a R))) w
  have hfe : faceEmb g δ = nones w δ := by rw [faceEmb, hev]
  refine ⟨nones w δ, Finset.orderEmbOfFin_mem _ w.prop δ, ?_⟩
  rw [← hfe]
  exact congrArg (fun cc : Σ i : ChainCat.Bead a,
      ▫((ChainCat.beadDim c j)) ⟶ ▫((ChainCat.beadDim a i)) =>
        (⟨cc.1, faceEmb cc.2 δ⟩ : EventObj a)) hbd

/-- The junction before a bead not yet started is that bead's initial vertex (the `top`-dual of
`juncVertex_top`). -/
theorem juncVertex_bot {n k : ℕ} (γ : Fin n → Fin k) {M : ℕ} (h : ∀ p, ¬ (γ p : ℕ) < M) :
    juncVertex γ M = (BPSet.cube n).init :=
  congrArg canonicalMap
    (show juncStar γ M = constVertex n false by
      apply Subtype.ext; funext p; simp [juncStar, constVertex, h p])

section Partition

variable {K : BPSet} {a : Ch K} {m : ℕ} (β : EventObj a → Fin m)

/-- `β` read on the coordinates of one bead of `a`. -/
def bslice (R : ChainCat.Bead a) : Fin ((ChainCat.beadDim a R)) → Fin m := fun p => β ⟨R, p⟩

variable (hβ : Function.Surjective β)

/-- The bead of `a` that block `j` lives in. -/
noncomputable def pbead (j : Fin m) : ChainCat.Bead a := (Function.surjInv hβ j).1

theorem psz_pos (j : Fin m) :
    0 < (Finset.univ.filter (fun p => bslice β (pbead β hβ j) p = j)).card :=
  Finset.card_pos.mpr ⟨(Function.surjInv hβ j).2,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Function.surjInv_eq hβ j⟩⟩

/-- The size of block `j`. -/
noncomputable def psz (j : Fin m) : ℕ+ :=
  ⟨(Finset.univ.filter (fun p => bslice β (pbead β hβ j) p = j)).card, psz_pos β hβ j⟩

/-- Block `j` as a cell of `⋁a.dims`: the braid-chain cell of bead `pbead j` cut out by `β`. -/
noncomputable def pcell (j : Fin m) :
    (BPSet.serialWedge a.dims).cells ((psz β hβ j : ℕ)) :=
  (ιᵂ a.dims (pbead β hβ j))⟪((psz β hβ j : ℕ))⟫
    (blockCell (bslice β (pbead β hβ j)) j)

theorem vertex₀_pcell (j : Fin m) :
    (BPSet.serialWedge a.dims).toPsh.vertex₀ (pcell β hβ j)
      = (ιᵂ a.dims (pbead β hβ j))⟪0⟫
          (juncVertex (bslice β (pbead β hβ j)) (j : ℕ)) := by
  rw [pcell, ι_app_vertex₀]
  exact congrArg (fun x => (ιᵂ a.dims (pbead β hβ j))⟪0⟫ x)
    (vertex₀_blockCell (bslice β (pbead β hβ j)) j)

theorem vertex₁_pcell (j : Fin m) :
    (BPSet.serialWedge a.dims).toPsh.vertex₁ (pcell β hβ j)
      = (ιᵂ a.dims (pbead β hβ j))⟪0⟫
          (juncVertex (bslice β (pbead β hβ j)) ((j : ℕ) + 1)) := by
  rw [pcell, ι_app_vertex₁]
  exact congrArg (fun x => (ιᵂ a.dims (pbead β hβ j))⟪0⟫ x)
    (vertex₁_blockCell (bslice β (pbead β hβ j)) j)

/-- The tie-block cube list: one cell per block, in time order. -/
noncomputable def pcubes :
    List (Σ n : ℕ+, (BPSet.serialWedge a.dims).cells (n : ℕ)) :=
  List.ofFn (fun j : Fin m => ⟨psz β hβ j, pcell β hβ j⟩)

theorem pcubes_length : (pcubes β hβ).length = m := List.length_ofFn

theorem pcubes_get (k : Fin (pcubes β hβ).length) :
    (pcubes β hβ).get k
      = ⟨psz β hβ (Fin.cast (pcubes_length β hβ) k),
          pcell β hβ (Fin.cast (pcubes_length β hβ) k)⟩ :=
  List.get_ofFn _ k

variable (hmo : ∀ e e' : EventObj a, (e.1 : ℕ) < (e'.1 : ℕ) → β e < β e')

include hmo

/-- Every event of block `j` lies in bead `pbead j` (a block cannot straddle two beads). -/
theorem pbead_eq (e : EventObj a) : pbead β hβ (β e) = e.1 := by
  have hx : β (Function.surjInv hβ (β e)) = β e := Function.surjInv_eq hβ (β e)
  rcases lt_trichotomy ((Function.surjInv hβ (β e)).1 : ℕ) (e.1 : ℕ) with h | h | h
  · exact absurd (hmo _ e h) (by rw [hx]; exact lt_irrefl _)
  · exact Fin.ext h
  · exact absurd (hmo e _ h) (by rw [hx]; exact lt_irrefl _)

theorem pbead_mono {j j' : Fin m} (h : j ≤ j') :
    ((pbead β hβ j : ChainCat.Bead a) : ℕ) ≤ ((pbead β hβ j' : ChainCat.Bead a) : ℕ) := by
  by_contra hc
  rw [not_le] at hc
  have h1 : β (Function.surjInv hβ j') < β (Function.surjInv hβ j) := hmo _ _ hc
  rw [Function.surjInv_eq hβ j', Function.surjInv_eq hβ j] at h1
  exact absurd h1 (not_lt.mpr h)

theorem pbead_surjective : Function.Surjective (pbead β hβ) := fun i =>
  ⟨β ⟨i, ⟨0, (a.dims.get i).2⟩⟩, pbead_eq β hβ hmo _⟩

/-- The bead of a coordinate of bead `R` is `R` itself. -/
theorem pbead_bslice (R : ChainCat.Bead a) (p : Fin ((ChainCat.beadDim a R))) :
    pbead β hβ (bslice β R p) = R :=
  pbead_eq β hβ hmo ⟨R, p⟩

/-- Blocks do not skip a bead of `a`: every bead is used. -/
theorem pbead_succ {j j' : Fin m} (hjj' : (j' : ℕ) = (j : ℕ) + 1)
    (hlt : ((pbead β hβ j : ChainCat.Bead a) : ℕ) < ((pbead β hβ j' : ChainCat.Bead a) : ℕ)) :
    ((pbead β hβ j' : ChainCat.Bead a) : ℕ)
      = ((pbead β hβ j : ChainCat.Bead a) : ℕ) + 1 := by
  by_contra hne
  have hgt : ((pbead β hβ j : ChainCat.Bead a) : ℕ) + 1
      < ((pbead β hβ j' : ChainCat.Bead a) : ℕ) := by omega
  have hlen : ((pbead β hβ j : ChainCat.Bead a) : ℕ) + 1 < a.dims.length := by
    have := (pbead β hβ j').isLt; omega
  obtain ⟨j'', hj''⟩ := pbead_surjective β hβ hmo
    ⟨((pbead β hβ j : ChainCat.Bead a) : ℕ) + 1, hlen⟩
  have hv : ((pbead β hβ j'' : ChainCat.Bead a) : ℕ)
      = ((pbead β hβ j : ChainCat.Bead a) : ℕ) + 1 := by rw [hj'']
  have h1 : (j : ℕ) < (j'' : ℕ) := by
    by_contra hc
    have := pbead_mono β hβ hmo (Fin.le_def.mpr (not_lt.mp hc))
    omega
  have h2 : (j'' : ℕ) < (j' : ℕ) := by
    by_contra hc
    have := pbead_mono β hβ hmo (Fin.le_def.mpr (not_lt.mp hc))
    omega
  omega

/-- Every coordinate of `a`'s bead `pbead j` is timed by block `j` at the latest, when block `j+1`
has moved on to a later bead. -/
theorem bslice_le_of_bead_lt {j j' : Fin m} (hjj' : (j' : ℕ) = (j : ℕ) + 1)
    (hlt : ((pbead β hβ j : ChainCat.Bead a) : ℕ) < ((pbead β hβ j' : ChainCat.Bead a) : ℕ))
    (p : Fin ((ChainCat.beadDim a (pbead β hβ j)))) :
    ((bslice β (pbead β hβ j) p : Fin m) : ℕ) < (j : ℕ) + 1 := by
  by_contra hc
  rw [not_lt] at hc
  have hle : j' ≤ bslice β (pbead β hβ j) p := by rw [Fin.le_def, hjj']; exact hc
  have h1 := pbead_mono β hβ hmo hle
  rw [pbead_bslice β hβ hmo] at h1
  omega

/-- No coordinate of `a`'s bead `pbead j'` is timed before block `j'`, when block `j'` opens that
bead. -/
theorem bslice_ge_of_bead_lt {j j' : Fin m}
    (hlt : ((pbead β hβ j : ChainCat.Bead a) : ℕ) < ((pbead β hβ j' : ChainCat.Bead a) : ℕ))
    (p : Fin ((ChainCat.beadDim a (pbead β hβ j')))) :
    ¬ ((bslice β (pbead β hβ j') p : Fin m) : ℕ) < (j : ℕ) + 1 := by
  intro hc
  have hle : bslice β (pbead β hβ j') p ≤ j := by rw [Fin.le_def]; omega
  have h1 := pbead_mono β hβ hmo hle
  rw [pbead_bslice β hβ hmo] at h1
  omega

omit hmo in
/-- Transport of a junction vertex across an equality of beads. -/
theorem ι_juncVertex_congr {R R' : ChainCat.Bead a} (h : R = R') (M : ℕ) :
    (ιᵂ a.dims R)⟪0⟫ (juncVertex (bslice β R) M)
      = (ιᵂ a.dims R')⟪0⟫ (juncVertex (bslice β R') M) := by
  subst h; rfl

/-- **Consecutive blocks meet.**  Inside one bead of `a` both vertices are the same junction; across
beads, block `j` finishes its bead and block `j'` opens the next. -/
theorem pcell_junction {j j' : Fin m} (hjj' : (j' : ℕ) = (j : ℕ) + 1) :
    (BPSet.serialWedge a.dims).toPsh.vertex₁ (pcell β hβ j)
      = (BPSet.serialWedge a.dims).toPsh.vertex₀ (pcell β hβ j') := by
  rw [vertex₁_pcell, vertex₀_pcell]
  rcases Nat.lt_or_ge ((pbead β hβ j : ChainCat.Bead a) : ℕ)
    ((pbead β hβ j' : ChainCat.Bead a) : ℕ) with hlt | hge
  · rw [juncVertex_top _ (bslice_le_of_bead_lt β hβ hmo hjj' hlt), hjj',
      juncVertex_bot _ (bslice_ge_of_bead_lt β hβ hmo hlt)]
    exact serialWedge_junction a.dims (pbead_succ β hβ hmo hjj' hlt)
  · have hjlt : j ≤ j' := by rw [Fin.le_def]; omega
    have heq : pbead β hβ j = pbead β hβ j' :=
      Fin.ext (le_antisymm (pbead_mono β hβ hmo hjlt) hge)
    rw [hjj']
    exact ι_juncVertex_congr β heq ((j : ℕ) + 1)

/-- The first block starts at the wedge's initial vertex. -/
theorem pcell_init (hm : 0 < m) :
    (BPSet.serialWedge a.dims).toPsh.vertex₀ (pcell β hβ ⟨0, hm⟩)
      = (BPSet.serialWedge a.dims).init := by
  have hlen : 0 < a.dims.length :=
    lt_of_le_of_lt (Nat.zero_le _) (Function.surjInv hβ (⟨0, hm⟩ : Fin m)).1.isLt
  have hR0 : ((pbead β hβ ⟨0, hm⟩ : ChainCat.Bead a) : ℕ) = 0 := by
    obtain ⟨j0, hj0⟩ := pbead_surjective β hβ hmo ⟨0, hlen⟩
    have hle := pbead_mono β hβ hmo (Fin.le_def.mpr (Nat.zero_le (j0 : ℕ)) : (⟨0, hm⟩ : Fin m) ≤ j0)
    rw [hj0] at hle
    have h0 : ((⟨0, hlen⟩ : ChainCat.Bead a) : ℕ) = 0 := rfl
    omega
  rw [vertex₀_pcell, juncVertex_zero]
  exact serialWedge_init_ι a.dims (pbead β hβ ⟨0, hm⟩) hR0

/-- The last block ends at the wedge's final vertex. -/
theorem pcell_final (l : Fin m) (hl : (l : ℕ) + 1 = m) :
    (BPSet.serialWedge a.dims).toPsh.vertex₁ (pcell β hβ l)
      = (BPSet.serialWedge a.dims).final := by
  have hlen : 0 < a.dims.length :=
    lt_of_le_of_lt (Nat.zero_le _) (Function.surjInv hβ l).1.isLt
  have hRl : ((pbead β hβ l : ChainCat.Bead a) : ℕ) + 1 = a.dims.length := by
    have hh : a.dims.length - 1 < a.dims.length := by omega
    obtain ⟨j0, hj0⟩ := pbead_surjective β hβ hmo ⟨a.dims.length - 1, hh⟩
    have hj0l : (j0 : ℕ) ≤ (l : ℕ) := by have := j0.isLt; omega
    have hle := pbead_mono β hβ hmo (Fin.le_def.mpr hj0l)
    rw [hj0] at hle
    have hval : ((⟨a.dims.length - 1, hh⟩ : ChainCat.Bead a) : ℕ) = a.dims.length - 1 := rfl
    have hlt := (pbead β hβ l).isLt
    omega
  rw [vertex₁_pcell, juncVertex_top _ (fun p => by rw [hl]; exact (bslice β _ p).isLt)]
  exact serialWedge_final_ι a.dims (pbead β hβ l) hRl

omit hmo in
theorem vertex₀_pcubes_get (k : Fin (pcubes β hβ).length) :
    (BPSet.serialWedge a.dims).toPsh.vertex₀ ((pcubes β hβ).get k).2
      = (BPSet.serialWedge a.dims).toPsh.vertex₀
          (pcell β hβ (Fin.cast (pcubes_length β hβ) k)) :=
  congrArg (fun c : Σ n : ℕ+, (BPSet.serialWedge a.dims).cells (n : ℕ) =>
    (BPSet.serialWedge a.dims).toPsh.vertex₀ c.2) (pcubes_get β hβ k)

omit hmo in
theorem vertex₁_pcubes_get (k : Fin (pcubes β hβ).length) :
    (BPSet.serialWedge a.dims).toPsh.vertex₁ ((pcubes β hβ).get k).2
      = (BPSet.serialWedge a.dims).toPsh.vertex₁
          (pcell β hβ (Fin.cast (pcubes_length β hβ) k)) :=
  congrArg (fun c : Σ n : ℕ+, (BPSet.serialWedge a.dims).cells (n : ℕ) =>
    (BPSet.serialWedge a.dims).toPsh.vertex₁ c.2) (pcubes_get β hβ k)

/-- **The tie-block cells form a cube chain of `⋁a.dims`.** -/
theorem pcubes_isChain :
    IsCubeChain (BPSet.serialWedge a.dims).init (pcubes β hβ)
      (BPSet.serialWedge a.dims).final := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- no blocks: `a` has no events, hence no beads, and the wedge is a point
    have hlen0 : a.dims.length = 0 := by
      by_contra hc
      have hpos : 0 < a.dims.length := Nat.pos_of_ne_zero hc
      exact (β ⟨⟨0, hpos⟩, ⟨0, (a.dims.get ⟨0, hpos⟩).2⟩⟩).elim0
    have hnil : a.dims = [] := List.eq_nil_of_length_eq_zero hlen0
    have hp0 : pcubes β hβ = [] := by rw [pcubes]; exact List.ofFn_zero
    rw [hp0, hnil]
    exact Subsingleton.elim ((BPSet.cube 0).init) ((BPSet.cube 0).final)
  have hlen : (pcubes β hβ).length = m := pcubes_length β hβ
  have hpos : 0 < (pcubes β hβ).length := by rw [hlen]; exact hm
  have hchain := isCubeChain_aux (K := BPSet.serialWedge a.dims) (pcubes β hβ)
    (Fin.snoc (fun i => (BPSet.serialWedge a.dims).toPsh.vertex₀ ((pcubes β hβ).get i).2)
      (BPSet.serialWedge a.dims).final)
    (fun i => by rw [Fin.snoc_castSucc])
    (fun i => by
      by_cases hi : (i : ℕ) + 1 < (pcubes β hβ).length
      · have hsucc : (i.succ : Fin ((pcubes β hβ).length + 1))
            = (⟨(i : ℕ) + 1, hi⟩ : Fin (pcubes β hβ).length).castSucc := Fin.ext rfl
        rw [hsucc, Fin.snoc_castSucc, vertex₁_pcubes_get, vertex₀_pcubes_get]
        exact pcell_junction (β := β) (hβ := hβ) (hmo := hmo) (hjj' := rfl)
      · have hilast : (i : ℕ) + 1 = (pcubes β hβ).length := by have := i.isLt; omega
        have hsucc : (i.succ : Fin ((pcubes β hβ).length + 1))
            = Fin.last (pcubes β hβ).length := Fin.ext hilast
        rw [hsucc, Fin.snoc_last, vertex₁_pcubes_get]
        exact pcell_final (β := β) (hβ := hβ) (hmo := hmo) (l := Fin.cast hlen i)
          (hl := by
            have hv : ((Fin.cast hlen i : Fin m) : ℕ) = (i : ℕ) := rfl
            omega))
  have hzero : (Fin.snoc (α := fun _ : Fin ((pcubes β hβ).length + 1) =>
          (BPSet.serialWedge a.dims).cells 0)
        (fun i => (BPSet.serialWedge a.dims).toPsh.vertex₀ ((pcubes β hβ).get i).2)
        (BPSet.serialWedge a.dims).final) 0 = (BPSet.serialWedge a.dims).init := by
    have h0 : (0 : Fin ((pcubes β hβ).length + 1))
        = (⟨0, hpos⟩ : Fin (pcubes β hβ).length).castSucc := Fin.ext rfl
    rw [h0, Fin.snoc_castSucc, vertex₀_pcubes_get]
    have hcast : (Fin.cast hlen ⟨0, hpos⟩ : Fin m) = ⟨0, hm⟩ := Fin.ext rfl
    rw [hcast]
    exact pcell_init (β := β) (hβ := hβ) (hmo := hmo) (hm := hm)
  rw [hzero, Fin.snoc_last] at hchain
  exact hchain

/-! ### The refinement and its bead map -/

/-- The wedge map of the tie-block chain: `⋁(block sizes) ⟶ ⋁a.dims`. -/
noncomputable def pmap :
    BPSet.serialWedge ((pcubes β hβ).map (·.1)) ⟶ BPSet.serialWedge a.dims :=
  wedgeDescHom (pcubes β hβ)
    (wedgeDesc (BPSet.serialWedge a.dims).init (BPSet.serialWedge a.dims).final
      (pcubes β hβ) (pcubes_isChain β hβ hmo))

/-- The tie-block chain of `K` refining `a`. -/
noncomputable def pchain : Ch K := ⟨(pcubes β hβ).map (·.1), pmap β hβ hmo ≫ a.map⟩

/-- The refinement of `a` realising the partition. -/
noncomputable def prefine : pchain β hβ hmo ⟶ a := ⟨pmap β hβ hmo, rfl⟩

theorem pchain_dims_length : (pchain β hβ hmo).dims.length = m := by
  have h : (pchain β hβ hmo).dims = (pcubes β hβ).map (·.1) := rfl
  rw [h, List.length_map, pcubes_length]

/-- **The refinement realises the partition**: the bead of the refined chain timing an event of `a`
is that event's `β`-block. -/
theorem beta_eventMap (x : EventObj (pchain β hβ hmo)) :
    ((β (eventMap (prefine β hβ hmo) x) : Fin m) : ℕ)
      = ((x.1 : Fin (pchain β hβ hmo).dims.length) : ℕ) := by
  obtain ⟨j, δ⟩ := x
  have hlm : (pchain β hβ hmo).dims.length = (pcubes β hβ).length := List.length_map _
  have hlen2 : (wedgeToCubes ⟨(pchain β hβ hmo).dims,
      (pmap β hβ hmo).hom⟩).length = (pchain β hβ hmo).dims.length :=
    wedgeToCubes_length _ _
  have hjlt : (j : ℕ) < (wedgeToCubes ⟨(pchain β hβ hmo).dims,
      (pmap β hβ hmo).hom⟩).length := by rw [hlen2]; exact j.isLt
  have hWT : wedgeToCubes ⟨(pchain β hβ hmo).dims, (pmap β hβ hmo).hom⟩ = pcubes β hβ :=
    wedgeToCubes_wedgeDesc _ _ _ _
  -- the cell of block `j`, read off the descent map and off the construction
  have hcast : (Fin.cast hlen2 ⟨(j : ℕ), hjlt⟩) = j := Fin.ext rfl
  have h1 : (wedgeToCubes ⟨(pchain β hβ hmo).dims, (pmap β hβ hmo).hom⟩).get ⟨(j : ℕ), hjlt⟩
      = ⟨(pchain β hβ hmo).dims.get j,
          yonedaEquiv (ιᵂ (pchain β hβ hmo).dims j
            ≫ (pmap β hβ hmo).hom)⟩ := by
    rw [wedgeToCubes_get, hcast]
  have h2 : (wedgeToCubes ⟨(pchain β hβ hmo).dims, (pmap β hβ hmo).hom⟩).get ⟨(j : ℕ), hjlt⟩
      = (pcubes β hβ).get (Fin.cast hlm j) := by
    rw [List.get_of_eq hWT]
    congr 1
  have h3 := pcubes_get β hβ (Fin.cast hlm j)
  have hSig := h1.symm.trans (h2.trans h3)
  obtain ⟨p, hp, hev⟩ := eventMap_of_cellSigma (prefine β hβ hmo) j δ
    (pbead β hβ (Fin.cast (pcubes_length β hβ) (Fin.cast hlm j)))
    (d := psz β hβ (Fin.cast (pcubes_length β hβ) (Fin.cast hlm j)))
    (blockStar (bslice β (pbead β hβ (Fin.cast (pcubes_length β hβ) (Fin.cast hlm j))))
      (Fin.cast (pcubes_length β hβ) (Fin.cast hlm j))) hSig
  have hbp : bslice β (pbead β hβ (Fin.cast (pcubes_length β hβ) (Fin.cast hlm j))) p
      = Fin.cast (pcubes_length β hβ) (Fin.cast hlm j) :=
    (mem_noneSet_blockStar _ _ p).mp hp
  rw [hev]
  exact congrArg (fun i : Fin m => (i : ℕ)) hbp

end Partition

end CubeChains
