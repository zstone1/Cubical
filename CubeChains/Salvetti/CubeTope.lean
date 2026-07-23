import CubeChains.Salvetti.TopeSal

/-!
# Salvetti/CubeTope — the tope of an execution of the cube

An execution `x : Ch⋆ (□n)` orders the `n` coordinates: `coordOf x` says which coordinate an event
flips, `rankEquiv x` says when it fires, and their composite is the **tope** `tope x : Perm (Fin n)`
— the chamber of the braid arrangement `x` sits in, read as "coordinate ↦ rank".

The one fact everything downstream uses is that the crossing permutation of a refinement is the
*change of tope*:

    permOf f = tope y ∘ (tope x)⁻¹                (`permOf_tope`)

so `ConcPos` on the cube is graded by a coboundary — which is exactly why its loops are **pure**.
Naturality of `coordOf` (a refinement does not move an event to a different coordinate) is the
whole proof; it is `coordFlip`'s coend functoriality.
-/

open CategoryTheory Opposite BPSet ChainCat CubeChain Equiv

namespace CubeChains

variable {n : ℕ}

/-! ## The event count -/

/-- An execution of `□ⁿ` has exactly `n` events. -/
theorem Nev_cube (x : Ch⋆ (□n)) : Nev x = n := wedgeDimSum_eq x.chain.map

/-! ## The coordinate of an event -/

/-- **Which coordinate of `□ⁿ` an event flips** — the chain's coordinate bijection. -/
noncomputable def coordOf (x : Ch⋆ (□n)) : beadEvent x.chain.dims ≃ Fin n := coordFlip x.chain.map

/-- The bead of an event is the bead of its coordinate. -/
theorem coordOf_symm_fst (x : Ch⋆ (□n)) (q : Fin n) :
    ((coordOf x).symm q).1 = beadOf x.chain q := rfl

/-- **A refinement does not move an event off its coordinate.**  This is `coordFlip`'s
functoriality read on the refinement triangle `wedgeOf f ≫ x.map = y.map`. -/
theorem coordOf_eventEquiv {x y : Ch⋆ (□n)} (f : x ⟶ y) (e : beadEvent y.chain.dims) :
    coordOf x (eventEquiv f e) = coordOf y e := by
  rw [coordOf, eventEquiv_apply, ← coordFlip_comp, wedgeOf_w]
  rfl

/-! ## The tope -/

/-- The run order of an execution, as a bijection "coordinate ↦ rank". -/
noncomputable def topeOrd (x : Ch⋆ (□n)) : Fin n ≃ Fin (Nev x) :=
  (coordOf x).symm.trans (rankEquiv x)

/-- **The tope of an execution**: the linear order its run puts on the coordinates. -/
noncomputable def tope (x : Ch⋆ (□n)) : Perm (Fin n) := (topeOrd x).trans (finCongr (Nev_cube x))

/-- The tope, read as a rank — the form the bead computations meet. -/
theorem tope_val (x : Ch⋆ (□n)) (q : Fin n) :
    (tope x q : ℕ) = (rankEquiv x ((coordOf x).symm q) : ℕ) := by
  rw [tope, Equiv.trans_apply, finCongr_apply, Fin.coe_cast]
  rfl

/-- A refinement carries `x`'s order to `y`'s: the two orders differ by the event relabelling. -/
theorem topeOrd_rawPerm {x y : Ch⋆ (□n)} (f : x ⟶ y) (q : Fin n) :
    rawPerm f (topeOrd x q) = topeOrd y q := by
  have hev : (eventEquiv f).symm ((coordOf x).symm q) = (coordOf y).symm q := by
    rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq, coordOf_eventEquiv f, Equiv.apply_symm_apply]
  rw [topeOrd, topeOrd, Equiv.trans_apply, Equiv.trans_apply, rawPerm_rankEquiv, hev]

/-- **The crossing permutation of a refinement is its change of tope.** -/
theorem permOf_tope {x y : Ch⋆ (□n)} (f : x ⟶ y) :
    permCast (Nev_cube x) (permOf f) = tope y * (tope x)⁻¹ := by
  refine Equiv.ext fun q => Fin.ext ?_
  set u := (tope x)⁻¹ q with hu
  have hq : tope x u = q := Equiv.apply_symm_apply _ _
  have hcast : (finCongr (Nev_cube x)).symm q = topeOrd x u := by
    apply Fin.ext
    rw [finCongr_symm, finCongr_apply, Fin.coe_cast, ← hq, tope, Equiv.trans_apply,
      finCongr_apply, Fin.coe_cast]
  rw [permCast, Equiv.permCongr_apply, hcast, Equiv.Perm.mul_apply, ← hu, finCongr_apply,
    Fin.coe_cast, permOf, Equiv.trans_apply, finCongr_symm, finCongr_apply, Fin.coe_cast,
    topeOrd_rawPerm f, tope, Equiv.trans_apply, finCongr_apply, Fin.coe_cast]

/-- Lengths are read off the tope change. -/
theorem permLen_tope {x y : Ch⋆ (□n)} (f : x ⟶ y) :
    permLen (tope y * (tope x)⁻¹) = permLen (permOf f) := by
  rw [← permOf_tope f, permLen_permCast]

/-! ## All-edges executions

An all-edges chain carries a *unique* run — its braid face is already a tope, and there is nothing
above a tope.  So its fibre of `Lines` is a subsingleton, which is what makes every refinement into
it exist with no condition to check, and its tope is just the chain's own bead order. -/

/-- **Nothing sits above a tope**: the runs of an all-edges chain are all equal. -/
theorem salObj_subsingleton {c : Ch (□n)} (hc : IsRun (□n) c) : Subsingleton (SalObj c) := by
  have htope : (braidCOM n).IsTope (chFace c).1 := isTope_chFace_run ⟨c, hc⟩
  exact ⟨fun s t =>
    Subtype.ext ((htope.2 s.1 s.2.1.1 s.2.2).trans (htope.2 t.1 t.2.1.1 t.2.2).symm)⟩

/-- **An all-edges chain has a unique run** — the fibre of `Lines` over it is a point. -/
theorem lines_subsingleton {c : Ch (□n)} (hc : IsRun (□n) c) :
    Subsingleton ((⋁c.dims).toPsh ⟶ runPresheaf) :=
  haveI := salObj_subsingleton hc
  haveI := (phiEquiv c).subsingleton
  (runPshEquiv c.dims).subsingleton

/-- **A refinement of executions exists as soon as the chains are ordered**, provided the target is
all edges: there is then no run condition left to check. -/
def homOfIsRun {x z : Ch⋆ (□n)} (hz : IsRun (□n) z.chain)
    (h : (chFace x.chain).1 ⊑ (chFace z.chain).1) : x ⟶ z :=
  ⟨(reflectHom h).op, @Subsingleton.elim _ (lines_subsingleton hz) _ _⟩

/-- Within an all-edges execution every event has rank its own bead. -/
theorem rankEquiv_val_of_isRun (x : Ch⋆ (□n)) (hx : IsRun (□n) x.chain)
    (i : Fin x.chain.dims.length) (k : Fin (x.chain.dims.get i : ℕ)) :
    (rankEquiv x ⟨i, k⟩ : ℕ) = (i : ℕ) := by
  have hone : ∀ j : Fin x.chain.dims.length, (x.chain.dims.get j : ℕ) = 1 := fun j =>
    congrArg PNat.val (hx _ (List.get_mem _ _))
  have hlocal : (beadOf (runProj x.run i).chain k : ℕ) = 0 := by
    have hlen := runProj_dims_length x i
    have h1 := hone i
    have := (beadOf (runProj x.run i).chain k).isLt
    omega
  rw [rankEquiv_val, hlocal, Nat.add_zero]
  calc ∑ j : Fin (i : ℕ), (x.chain.dims.get (Fin.castLE i.2.le j) : ℕ)
      = ∑ _j : Fin (i : ℕ), 1 := Finset.sum_congr rfl fun j _ => hone _
    _ = (i : ℕ) := by simp

/-- Within a one-bead execution the rank is the bead's own local run. -/
theorem rankEquiv_val_of_single {x : Ch⋆ (□n)} {i : Fin x.chain.dims.length} (hi : (i : ℕ) = 0)
    (k : Fin (x.chain.dims.get i : ℕ)) :
    (rankEquiv x ⟨i, k⟩ : ℕ) = (beadOf (runProj x.run i).chain k : ℕ) := by
  rw [rankEquiv_val, Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega), Nat.zero_add]

/-- **The tope of an all-edges execution is its chain's bead order.** -/
theorem tope_of_isRun (x : Ch⋆ (□n)) (hx : IsRun (□n) x.chain) (q : Fin n) :
    (tope x q : ℕ) = (beadOf x.chain q : ℕ) := by
  rw [tope_val, ← Sigma.eta ((coordOf x).symm q), rankEquiv_val_of_isRun x hx, coordOf_symm_fst]

/-! ## Executions with a prescribed tope

`ofBlockMap` builds the chain of `□ⁿ` realising an ordered partition; a *bijection* `Fin n ≃ Fin n`
gives the all-edges chain firing coordinate `q` at time `β q`, and the constant map to `Fin 1` gives
the coarsest chain, the single `n`-cube. -/

/-- The chain of `□ⁿ` realising the ordered partition `β`. -/
noncomputable def blockChain {L : ℕ} (β : Fin n → Fin L) (hβ : Function.Surjective β) : Ch (□n) :=
  (chEquivCubeChain (□n)).symm (ofBlockMap β hβ)

@[simp] theorem beadOf_blockChain {L : ℕ} (β : Fin n → Fin L) (hβ : Function.Surjective β)
    (q : Fin n) : (beadOf (blockChain β hβ) q : ℕ) = (β q : ℕ) :=
  beadOf_ofBlockMap β hβ q

@[simp] theorem blockChain_dims_length {L : ℕ} (β : Fin n → Fin L) (hβ : Function.Surjective β) :
    (blockChain β hβ).dims.length = L := by
  rw [blockChain, chEquivCubeChain_symm_dims]
  change ((blockCubes β hβ).map (·.1)).length = L
  rw [List.length_map, length_blockCubes]

/-- **The all-edges chain firing coordinate `q` at time `β q`.** -/
noncomputable def edgeChain (β : Perm (Fin n)) : Ch (□n) := blockChain β β.surjective

theorem edgeChain_isRun (β : Perm (Fin n)) : IsRun (□n) (edgeChain β) := by
  refine all_one_of_dimSum_eq_length ?_
  rw [wedgeDimSum_eq (edgeChain β).map, edgeChain, blockChain_dims_length]

/-- The all-edges chain of `□ⁿ`, as a run. -/
noncomputable def edgeRun (β : Perm (Fin n)) : Run (□n) := ⟨edgeChain β, edgeChain_isRun β⟩

@[simp] theorem edgeRun_chain (β : Perm (Fin n)) : (edgeRun β).chain = edgeChain β := rfl

/-- The execution of an all-edges chain — its run is forced, so there is nothing to choose. -/
noncomputable def edgeExec {c : Ch (□n)} (hc : IsRun (□n) c) : Ch⋆ (□n) :=
  ⟨op c, pshOfRun _ ⟨⟨c.dims, 𝟙 _⟩, hc⟩⟩

@[simp] theorem edgeExec_chain {c : Ch (□n)} (hc : IsRun (□n) c) : (edgeExec hc).chain = c := rfl

/-- The **finest execution** with tope `β`. -/
noncomputable def fineExec (β : Perm (Fin n)) : Ch⋆ (□n) := edgeExec (edgeChain_isRun β)

theorem fineExec_chain (β : Perm (Fin n)) : (fineExec β).chain = edgeChain β := rfl

/-- **Every permutation is the tope of an execution** — of the all-edges chain realising it. -/
@[simp] theorem tope_fineExec (β : Perm (Fin n)) : tope (fineExec β) = β :=
  Equiv.ext fun q => Fin.ext <| by
    rw [tope_of_isRun _ (edgeChain_isRun β), fineExec_chain, edgeChain, beadOf_blockChain]

/-! ## The coarsest execution

The single `n`-cube fires all `n` events at once, so its braid face is the zero covector and *every*
tope sits above it: it refines to every all-edges chain.  Its descent is the right unitor, whose one
bead is the whole cube — so that bead labels the coordinates by themselves, and prescribing a tope
is just running the bead in that order. -/

/-- The **coarsest chain** of `□ⁿ`: the single `n`-cube. -/
def coarseChain (hn : 0 < n) : Ch (□n) := ⟨[⟨n, hn⟩], (wedge2RightUnit (□n)).hom⟩

/-- Its one bead. -/
def coarseBead (hn : 0 < n) : Fin (coarseChain hn).dims.length := ⟨0, Nat.zero_lt_one⟩

/-- **The coarsest chain ties every pair**: its braid face is the zero covector, which is below
every tope — this is why it refines to every execution. -/
theorem chFace_coarseChain (hn : 0 < n) : (chFace (coarseChain hn)).1 = 0 := by
  have hbead : ∀ q, ((beadOf (coarseChain hn) q : ℕ) : ℤ) = 0 := fun q => by
    have := (beadOf (coarseChain hn) q).isLt
    have h1 : (coarseChain hn).dims.length = 1 := rfl
    omega
  change braidSign (fun q => ((beadOf (coarseChain hn) q : ℕ) : ℤ)) = 0
  rw [funext hbead]
  exact braidSign_const_zero 0

/-- **The single bead is the whole cube**: its face is the identity (`wedge2Desc_inl` on the right
unitor), so it labels the coordinates by themselves. -/
theorem coordFlip_coarseChain (hn : 0 < n) (k : Fin n) :
    coordFlip (coarseChain hn).map ⟨coarseBead hn, k⟩ = k := by
  have hincl : ιᵂ (coarseChain hn).dims (coarseBead hn) ≫ (coarseChain hn).map.hom
      = 𝟙 (□n).toPsh := wedge2Desc_inl _ _ _
  have hbead : beadFace (coarseChain hn).map.hom (coarseBead hn) = 𝟙 (▫n) :=
    congrArg yonedaEquiv hincl
  rw [coordFlip_eq, hbead]
  exact faceEmb_id n k

/-- The run of the coarsest chain firing the coordinates in the order `τ` names. -/
noncomputable def coarseRun (hn : 0 < n) (τ : Perm (Fin n)) : Run (⋁(coarseChain hn).dims) :=
  (runConcat (□n) (⋁([] : List ℕ+))).obj (edgeRun τ, (runUnit : Run (⋁([] : List ℕ+))))

/-- The **coarsest execution** with tope `τ`. -/
noncomputable def coarseExec (hn : 0 < n) (τ : Perm (Fin n)) : Ch⋆ (□n) :=
  ⟨op (coarseChain hn), pshOfRun _ (coarseRun hn τ)⟩

theorem coarseExec_chain (hn : 0 < n) (τ : Perm (Fin n)) :
    (coarseExec hn τ).chain = coarseChain hn := rfl

theorem coarseExec_run (hn : 0 < n) (τ : Perm (Fin n)) :
    (coarseExec hn τ).run = coarseRun hn τ :=
  runOfPsh_pshOfRun _ _

/-- The single bead's local run is the one prescribed — `pshOfRun_inl` reads it back off the
left-hand summand of `⋁[n] = □ⁿ ∨ □⁰`. -/
theorem runProj_coarseExec (hn : 0 < n) (τ : Perm (Fin n)) :
    runProj (coarseExec hn τ).run (coarseBead hn) = edgeRun τ := by
  have hinl : ιᵂ (coarseExec hn τ).chain.dims (coarseBead hn)
        ≫ pshOfRun (coarseExec hn τ).chain.dims (coarseRun hn τ)
      = yonedaEquiv.symm (runSplit (consAltitude ⟨n, hn⟩ []) (coarseRun hn τ)).1 :=
    pshOfRun_inl ⟨n, hn⟩ [] (coarseRun hn τ)
  rw [runProj, coarseExec_run]
  -- `rw [hinl]` fails: the two `≫` carry different spellings of the wedge object
  refine (congrArg yonedaEquiv hinl).trans ?_
  rw [Equiv.apply_symm_apply, coarseRun]
  exact congrArg Prod.fst (runSplit_runConcat _ (edgeRun τ) runUnit)

/-- **Every permutation is the tope of a coarsest execution.** -/
@[simp] theorem tope_coarseExec (hn : 0 < n) (τ : Perm (Fin n)) : tope (coarseExec hn τ) = τ := by
  refine Equiv.ext fun q => Fin.ext ?_
  have hev : (coordOf (coarseExec hn τ)).symm q = ⟨coarseBead hn, q⟩ :=
    ((coordOf (coarseExec hn τ)).symm_apply_eq).mpr (coordFlip_coarseChain hn q).symm
  rw [tope_val, hev, rankEquiv_val_of_single rfl, runProj_coarseExec]
  exact beadOf_blockChain (⇑τ) τ.surjective q

end CubeChains
