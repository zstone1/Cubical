import CubeChains.Braid.ElementaryBraiding
import CubeChains.Braid.Surjectivity
import CubeChains.Chains.Correspondence

/-!
# Salvetti/ConcConnectivity — connectivity of the concurrency groupoid

`ConcCat K = (Lines K).Elements`.  A `Ch K` morphism *is* a coarsening (`⟨φ, φ ≫ b.map = a.map⟩`,
fine → coarse), so `cubeChain` (the single `n`-bead, coarsest) is **terminal** and every chain
coarsens to it.  Connectivity of the `n`-event component of `ConcGrpd (□n)` then reduces to:

* within-chain: two executions on one chain join (`sameChain_connected`);
* the coarsening `a ⟶ cubeChain` (`toCubeChain`), whose descent is the append-point iso
  `⋁[n] = wedge2 (□n) (□0) ≅ □n` (`cubeChain_map_isIso`).
-/

open CategoryTheory CubeChain StdCube Opposite

namespace CubeChains

variable {K : BPSet}

/-! ## Within-chain connectivity -/

/-- Every execution is joined, in `ConcGrpd K`, to its sequentialization (a run). -/
theorem nonempty_hom_seqExec (x : ConcCat K) :
    Nonempty ((FreeGroupoid.mk x : ConcGrpd K) ⟶ FreeGroupoid.mk (seqExec x)) :=
  ⟨(runIso x).inv⟩

/-- `seqMor` lands in the run of the chosen line, as a free-groupoid iso. -/
noncomputable def seqMorIso (x : ConcCat K) (M : LinesObj x.chain) :
    (FreeGroupoid.mk x : ConcGrpd K)
      ≅ FreeGroupoid.mk (runExec (seqChain M) (seqChain_isRun M)) :=
  asIso (FreeGroupoid.homMk (seqMor x M))

/-- **Same-chain connectivity.**  Two executions on the same chain are joined in `ConcGrpd K`. -/
theorem sameChain_connected (a : Ch K) (L L' : LinesObj a) :
    Nonempty ((FreeGroupoid.mk (⟨Opposite.op a, L⟩ : ConcCat K) : ConcGrpd K)
      ⟶ FreeGroupoid.mk ⟨Opposite.op a, L'⟩) :=
  ⟨(seqMorIso (⟨Opposite.op a, L⟩ : ConcCat K) L').hom
    ≫ (seqMorIso (⟨Opposite.op a, L'⟩ : ConcCat K) L').inv⟩

/-! ## The append-point iso and the coarsening `a ⟶ cubeChain` -/

/-- **Appending the point `□0` is an iso** (right-hand mirror of `Segal.wedge2_cube0_inr_isIso`):
the left inclusion `X ⟶ wedge2 X (□0)` is invertible because the opposite leg `(□0).initVertex` is. -/
instance wedge2_cube0_inl_isIso (X : BPSet) :
    IsIso (Glue.inl X.finalVertex (□0).initVertex) :=
  (Glue.isPushout _ _).isIso_inl_of_isIso

/-- A bi-pointed morphism whose underlying presheaf map is an iso is an iso. -/
noncomputable def bpsetHomInv {K L : BPSet} (f : K ⟶ L)
    [IsIso (f : BPSet.Hom K L).hom] : L ⟶ K where
  hom := inv (f : BPSet.Hom K L).hom
  app_init := by
    have h := congrArg (fun g : K.toPsh ⟶ K.toPsh => g.app _ K.init) (IsIso.hom_inv_id f.hom)
    simp only [NatTrans.comp_app, types_comp_apply, NatTrans.id_app, types_id_apply] at h
    rw [← f.app_init]; exact h
  app_final := by
    have h := congrArg (fun g : K.toPsh ⟶ K.toPsh => g.app _ K.final) (IsIso.hom_inv_id f.hom)
    simp only [NatTrans.comp_app, types_comp_apply, NatTrans.id_app, types_id_apply] at h
    rw [← f.app_final]; exact h

theorem bpsetHomInv_hom_inv_id {K L : BPSet} (f : K ⟶ L) [IsIso (f : BPSet.Hom K L).hom] :
    f ≫ bpsetHomInv f = 𝟙 K :=
  BPSet.hom_ext (by simp [bpsetHomInv, IsIso.hom_inv_id])

instance bpset_isIso_of_hom {K L : BPSet} (f : K ⟶ L) [IsIso (f : BPSet.Hom K L).hom] :
    IsIso f :=
  ⟨bpsetHomInv f, bpsetHomInv_hom_inv_id f, BPSet.hom_ext (by simp [bpsetHomInv, IsIso.inv_hom_id])⟩

/-- The Yoneda classifier of a top cell is an iso: `k = n` forces the top cell (`eq_topCell`),
whose canonical map is the identity (`canonicalMap_topCell`). -/
theorem yonedaSymm_cell_isIso {n d : ℕ} (a : Cell n d) (hd : d = n) :
    IsIso ((yonedaEquiv (X := ▫d) (F := (□n).toPsh)).symm (canonicalMap a)) := by
  subst d
  change IsIso ((yonedaEquiv (X := ▫n) (F := yoneda.obj ▫n)).symm (canonicalMap a))
  rw [eq_topCell a, canonicalMap_topCell]
  have hsymm : (yonedaEquiv (X := ▫n) (F := yoneda.obj ▫n)).symm (𝟙 (stdPre n))
      = 𝟙 (yoneda.obj ▫n) := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, ← CategoryTheory.Functor.map_id yoneda]
    exact (yonedaEquiv_yoneda_map (𝟙 ▫n)).symm
  rw [hsymm]
  infer_instance

/-- **The coarsest chain's descent is an iso.**  The single `n`-bead chain descends by the
append-point iso `⋁[n] = wedge2 (□n) (□0) ≅ □n`: the head block is `Glue.inl` (invertible,
`wedge2_cube0_inl_isIso`) and its Yoneda classifier is the top cell (invertible,
`yonedaSymm_cell_isIso`). -/
theorem cubeChain_map_isIso {n : ℕ} (hn : 0 < n) : IsIso (cubeChain hn).map := by
  have hβ := collapseβ_surjective hn
  haveI hhom : IsIso ((cubeChain hn).map : BPSet.Hom _ _).hom := by
    have hcard : (Finset.univ.filter (fun p => collapseβ n p = (0 : Fin 1))).card = n := by
      rw [Finset.filter_true_of_mem (fun p _ => Subsingleton.elim _ _), Finset.card_univ,
        Fintype.card_fin]
    haveI hh0 : IsIso (yonedaEquiv.symm ((bead (collapseβ n) hβ 0).2)) :=
      yonedaSymm_cell_isIso (blockStar (collapseβ n) 0) hcard
    haveI hf : IsIso (Glue.inl (□((bead (collapseβ n) hβ 0).1 : ℕ)).finalVertex (□0).initVertex) :=
      wedge2_cube0_inl_isIso _
    have hcomp : Glue.inl (□((bead (collapseβ n) hβ 0).1 : ℕ)).finalVertex (□0).initVertex
          ≫ ((cubeChain hn).map : BPSet.Hom _ _).hom
        = yonedaEquiv.symm ((bead (collapseβ n) hβ 0).2) :=
      CubeChain.inl_comp_wedgeDesc (□n).init (□n).final (bead (collapseβ n) hβ 0).1
        (bead (collapseβ n) hβ 0).2 [] (chainOf (collapseβ n) hβ).isChain
    haveI : IsIso (Glue.inl (□((bead (collapseβ n) hβ 0).1 : ℕ)).finalVertex (□0).initVertex
        ≫ ((cubeChain hn).map : BPSet.Hom _ _).hom) := by rw [hcomp]; exact hh0
    exact IsIso.of_isIso_comp_left
      (Glue.inl (□((bead (collapseβ n) hβ 0).1 : ℕ)).finalVertex (□0).initVertex) _
  exact bpset_isIso_of_hom (cubeChain hn).map

/-- The unique coarsening of a chain onto the terminal single-`n`-bead chain, `φ = map ≫ inv`. -/
noncomputable def toCubeChain {n : ℕ} (hn : 0 < n) (a : Ch (□n)) : a ⟶ cubeChain hn :=
  haveI := cubeChain_map_isIso hn
  ⟨a.map ≫ inv (cubeChain hn).map, by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩

/-- The fixed hub execution: the coarsest chain with the natural per-bead order. -/
noncomputable def cubeHub {n : ℕ} (hn : 0 < n) (L : LinesObj (cubeChain hn)) : ConcCat (□n) :=
  ⟨op (cubeChain hn), L⟩

/-- The coarsening execution morphism `cubeHub ⟶ seqExec w`: the chamber condition is free
because `seqExec w` is a run (`linesObj_subsingleton`). -/
noncomputable def cubeHubMor {n : ℕ} (hn : 0 < n) (w : ConcCat (□n)) (L : LinesObj (cubeChain hn)) :
    cubeHub hn L ⟶ seqExec w :=
  ⟨(toCubeChain hn (seqExec w).chain).op,
   @Subsingleton.elim _ (linesObj_subsingleton (seq_isRun w)) _ _⟩

/-- **`n`-event connectivity of `ConcGrpd (□n)`.**  Every execution coarsens onto the terminal
single-`n`-bead chain, so all are joined through the fixed hub. -/
theorem concGrpd_nEvents_connected {n : ℕ} (hn : 0 < n) (y z : ConcCat (□n))
    (hy : nEvents y = n) (hz : nEvents z = n) :
    Nonempty ((FreeGroupoid.mk y : ConcGrpd (□n)) ⟶ FreeGroupoid.mk z) := by
  let L₀ : LinesObj (cubeChain hn) := fun i => natChamber (ChainCat.beadDim (cubeChain hn) i)
  have hub : ∀ w : ConcCat (□n),
      (FreeGroupoid.mk (cubeHub hn L₀) : ConcGrpd (□n)) ≅ FreeGroupoid.mk w := fun w =>
    asIso (FreeGroupoid.homMk (cubeHubMor hn w L₀)) ≪≫ runIso w
  exact ⟨((hub y).symm ≪≫ hub z).hom⟩

end CubeChains
