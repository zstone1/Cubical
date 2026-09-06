import CubeChains.Machinery.Cube.SymRepresentable
import CubeChains.Concurrency.Complexification.ChStarSym
import CubeChains.Concurrency.Salvetti.SalExec
import CubeChains.Machinery.Arrangement.SalSymmetry
import CubeChains.Machinery.Arrangement.SalElements
import Mathlib.Tactic.FinCases

/-!
# Concurrency/Complexification/SymReorient — the reorientation action, and the product model's
obstruction

`Ch (Hbp K) ≌ Ch (K.prod runBp)` sees no difference between the two models; their symmetry groups
do.  `Sₙ` acts on `Hbp □ⁿ` by bi-pointed automorphisms (`reorientBp`, faithful), and across
`hbpBraidSalEquiv : Ch (Hbp □ⁿ) ≌ (Sal (braidCOM n))ᵒᵖ` that action *is* the arrangement's
reorientation: a decorated chain's Salvetti face is the braid face of the chain it decorates, its
tope the braid face of the chain its run performs, and `σ` relabels the direction of every step.
Whereas `□ⁿ` is rigid, so every endomorphism of `□ⁿ × run` over the base lies over the *identity*
and leaves underlying chains alone — while `reorient σ` moves every chamber.
-/

open CategoryTheory Opposite BPSet StdCube SignType CubeChain

namespace CubeChains

/-! ## `Sₙ` acts on the decorated cube -/

variable (n : ℕ)

theorem reorientH_init (σ : Equiv.Perm (Fin n)) :
    (reorientH n σ).hom⟪0⟫ (Hbp.obj (□n)).init = (Hbp.obj (□n)).init :=
  (congrArg (fun w => sHomEquiv (w ≫ symHom σ)) (sHomEquiv_symm_one (□n).init)).trans
    ((congrArg sHomEquiv (J_map_const_comp_symHom _ (sign_endVertexMap false n) σ)).trans
      (sHomEquiv_J_map _))

theorem reorientH_final (σ : Equiv.Perm (Fin n)) :
    (reorientH n σ).hom⟪0⟫ (Hbp.obj (□n)).final = (Hbp.obj (□n)).final :=
  (congrArg (fun w => sHomEquiv (w ≫ symHom σ)) (sHomEquiv_symm_one (□n).final)).trans
    ((congrArg sHomEquiv (J_map_const_comp_symHom _ (sign_endVertexMap true n) σ)).trans
      (sHomEquiv_J_map _))

/-- The reorientation as a bi-pointed endomorphism; a symmetry fixes the extremal vertices. -/
def reorientEnd : Equiv.Perm (Fin n) →* End (Hbp.obj (□n)) where
  toFun σ := ⟨(reorientH n σ).hom, reorientH_init n σ, reorientH_final n σ⟩
  map_one' := hom_ext (congrArg Iso.hom (map_one (reorientH n)))
  map_mul' σ τ := hom_ext (congrArg Iso.hom (map_mul (reorientH n) σ τ))

/-- **`Sₙ` acts on `Hbp □ⁿ` by bi-pointed automorphisms.** -/
def reorientBp : Equiv.Perm (Fin n) →* Aut (Hbp.obj (□n)) :=
  (Aut.unitsEndEquivAut _).toMonoidHom.comp (reorientEnd n).toHomUnits

theorem reorientBp_injective : Function.Injective (reorientBp n) := fun _ _ h =>
  reorientH_injective n (Iso.ext
    (congrArg (fun a : Aut (Hbp.obj (□n)) => a.hom.hom) h))

/-- …hence on the chain category of the decorated cube. -/
def reorientCh : Equiv.Perm (Fin n) →* Aut (chFunctor.obj (Hbp.obj (□n))) :=
  (Aut.liftToCh (Hbp.obj (□n))).comp (reorientBp n)

/-! ## `□ⁿ` is rigid -/

/-- **The cube has no endomorphism but the identity**: `Box` is rigid and `□ⁿ` is representable. -/
theorem cube_endo_eq_id {n : ℕ} (f : □n ⟶ □n) : f = 𝟙 (□n) :=
  hom_ext (yonedaEquiv.injective (Box.endo_eq_id (yonedaEquiv f.hom)))

instance : Subsingleton (□n ⟶ □n) :=
  ⟨fun f g => (cube_endo_eq_id f).trans (cube_endo_eq_id g).symm⟩

/-- **`Aut □ⁿ` is trivial** — no symmetry group acts on the cube itself. -/
instance : Subsingleton (Aut (□n)) := ⟨fun f g => Iso.ext (Subsingleton.elim f.hom g.hom)⟩

/-! ## The product model carries no reorientation

```
   □ⁿ × run ───── Θ ─────▶ □ⁿ × run
        │                      │
   prodFst                 prodFst
        ▼          c           ▼
       □ⁿ ──────────────────▶ □ⁿ        c = 𝟙 by rigidity
```
-/

/-- **An endomorphism of `□ⁿ × run` over the base lies over the identity.** -/
theorem prodFst_comm_of_over {Θ : (□n).prod runBp ⟶ (□n).prod runBp} {c : □n ⟶ □n}
    (h : Θ ≫ prodFst (□n) runBp = prodFst (□n) runBp ≫ c) :
    Θ ≫ prodFst (□n) runBp = prodFst (□n) runBp := by
  rw [h, cube_endo_eq_id c, Category.comp_id]

/-- …so it leaves every underlying chain of `□ⁿ` alone. -/
theorem pushforward_prodFst_of_over {Θ : (□n).prod runBp ⟶ (□n).prod runBp} {c : □n ⟶ □n}
    (h : Θ ≫ prodFst (□n) runBp = prodFst (□n) runBp ≫ c) :
    ChainCat.pushforward Θ ⋙ ChainCat.pushforward (prodFst (□n) runBp)
      = ChainCat.pushforward (prodFst (□n) runBp) := by
  rw [← ChainCat.pushforward_comp, prodFst_comm_of_over n h]

/-! ## Reorientation does move faces -/

/-- Reorienting a tope multiplies its run word on the left. -/
theorem reorient_wordTope {n : ℕ} (σ w : Equiv.Perm (Fin n)) :
    reorient σ (wordTope w) = wordTope (σ * w) := by
  rw [wordTope_eq_braidSign, wordTope_eq_braidSign, reorient_braidSign]
  exact congrArg braidSign (funext fun i => congrArg (fun k : Fin n => ((k : ℕ) : ℤ)) (by rfl))

/-- **Reorientation moves every chamber** — a tope is a run word, and `σ` multiplies it. -/
theorem reorient_tope_ne {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1) (T : Tope n) :
    reorient σ T.1 ≠ T.1 := by
  rw [← wordTope_symm T, reorient_wordTope]
  exact fun h => hσ (by simpa using wordTope_injective h)

/-- The `n = 2` witness: the transposition flips the wall `x₀ < x₁`. -/
theorem reorient_swap_braidSign_ne :
    reorient (Equiv.swap (0 : Fin 2) 1) (braidSign ![0, 1]) ≠ braidSign ![(0 : ℤ), 1] :=
  fun h => absurd (congrFun h ⟨(0, 1), by decide⟩) (by decide)

/-! ## The steps of a decorated chain

A decorated chain performs its `n` directions one at a time: bead `i`'s `j`-th step performs
`beadDir α i j`, and both halves of the Salvetti cell — the chain and the run — read off it. -/

/-- The axis of `□ⁿ` bead `i` of a decorated chain performs at its `j`-th step. -/
def beadDir {n : ℕ} {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n)) (i : Fin d.length)
    (j : Fin (d.get i : ℕ)) : Fin n := cellDir (bead d α i) j

/-- **Reorientation relabels every step by `σ`.** -/
theorem beadDir_reorient {n : ℕ} {d : List ℕ+} (σ : Equiv.Perm (Fin n))
    (α : ⋁d ⟶ Hbp.obj (□n)) (i : Fin d.length) (j : Fin (d.get i : ℕ)) :
    beadDir (α ≫ (reorientBp n σ).hom) i j = σ (beadDir α i j) := by
  rw [beadDir, beadDir, bead_comp]
  exact cellDir_reorientH n σ (bead d α i) j

/-- The underlying chain flips `beadDir α i j` at bead `i`'s axis `(bead d α i).1 j`. -/
theorem coordFlip_chainOf {n : ℕ} {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n)) (i : Fin d.length)
    (j : Fin (d.get i : ℕ)) :
    coordFlip (chainOf (□n) α) ⟨i, (bead d α i).1 j⟩ = beadDir α i j := by
  rw [coordFlip_eq, beadDir, cellDir_eq]
  exact congrArg (fun c : (□n).cells (d.get i : ℕ) => faceEmb c ((bead d α i).1 j))
    (bead_chainOf (□n) α i)

/-- The run a decorated chain carries, as an all-edges refinement of `⋁d`. -/
def chainRun {n : ℕ} {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n)) : Run (⋁d) :=
  runOfPsh d (runOf (□n) α).hom

/-- Bead `i`'s local run is bead `i`'s order, inverted — the `symCell` convention. -/
theorem runProj_chainRun {n : ℕ} {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n)) (i : Fin d.length) :
    runProj (chainRun α) i = runOfPerm ((bead d α i).1)⁻¹ := by
  rw [chainRun, runProj, pshOfRun_runOfPsh]
  exact bead_runOf (□n) α i

theorem flatten_runProj_chainRun {n : ℕ} {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n))
    (i : Fin d.length) : flatten (runProj (chainRun α) i).chain = ((bead d α i).1)⁻¹ := by
  rw [runProj_chainRun]
  exact flatten_runOfPerm _

/-- **The chain the run performs**: an all-edges chain of `□ⁿ`, one step per direction. -/
def runLine {n : ℕ} {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n)) : Ch (□n) :=
  ⟨(chainRun α).dims, (chainRun α).map ≫ chainOf (□n) α⟩

/-- Step `beadStart d i + j` of the run performs `beadDir α i j` — the Segal decomposition
(`coordFlip_run_concat`) with the local run order cancelled against the decoration. -/
theorem coordFlip_runLine {n : ℕ} {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n))
    (e : beadEvent (chainRun α).dims) (i : Fin d.length) (j : Fin (d.get i : ℕ))
    (h : (pos e : ℕ) = beadStart d i + (j : ℕ)) :
    coordFlip (runLine α).map e = beadDir α i j := by
  change coordFlip ((chainRun α).map ≫ chainOf (□n) α) e = beadDir α i j
  rw [coordFlip_run_concat (chainRun α) (chainOf (□n) α) e i j h, flatten_runProj_chainRun,
    show beadFace (chainOf (□n) α).hom i = (bead d α i).2 from bead_chainOf (□n) α i, beadDir,
    cellDir_eq]
  congr 1

/-! ## Reorientation moves the chain and the run

Both halves of the Salvetti cell are `chFace` of a chain of `□ⁿ` — the decorated chain's own, and
the one its run performs — and reorientation relabels the directions of both by `σ`. -/

/-- A witness for `q`'s bead: any event flipping `q` names it. -/
theorem beadOf_eq_of_coordFlip {n : ℕ} {C : Ch (□n)} {p : beadEvent C.dims} {q : Fin n}
    (h : coordFlip C.map p = q) : beadOf C q = p.1 := by
  rw [beadOf_eq, ← h, Equiv.symm_apply_apply]

/-- **Reorientation carries direction `q` of the underlying chain to `σ q`.** -/
theorem beadOf_chainOf_reorient {n : ℕ} {d : List ℕ+} (σ : Equiv.Perm (Fin n))
    (α : ⋁d ⟶ Hbp.obj (□n)) (q : Fin n) :
    beadOf ⟨d, chainOf (□n) (α ≫ (reorientBp n σ).hom)⟩ (σ q) = beadOf ⟨d, chainOf (□n) α⟩ q := by
  obtain ⟨⟨i, k⟩, hik⟩ : ∃ p : beadEvent d, coordFlip (chainOf (□n) α) p = q :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  have hdir : beadDir α i (((bead d α i).1).symm k) = q := by
    rw [← coordFlip_chainOf α i (((bead d α i).1).symm k), Equiv.apply_symm_apply]
    exact hik
  refine Eq.trans (beadOf_eq_of_coordFlip (C := (⟨d, chainOf (□n) (α ≫ (reorientBp n σ).hom)⟩ :
      Ch (□n))) (p := ⟨i, (bead d (α ≫ (reorientBp n σ).hom) i).1 (((bead d α i).1).symm k)⟩)
    ?_) ?_
  · rw [coordFlip_chainOf, beadDir_reorient, hdir]
  · exact (beadOf_eq_of_coordFlip (C := (⟨d, chainOf (□n) α⟩ : Ch (□n))) (p := ⟨i, k⟩) hik).symm

/-- **Reorientation carries the direction performed at each step to its `σ`-image**, leaving the
step order alone. -/
theorem beadOf_runLine_reorient {n : ℕ} {d : List ℕ+} (σ : Equiv.Perm (Fin n))
    (α : ⋁d ⟶ Hbp.obj (□n)) (q : Fin n) :
    (beadOf (runLine (α ≫ (reorientBp n σ).hom)) (σ q) : ℕ) = (beadOf (runLine α) q : ℕ) := by
  have hd : dimSum d = n := wedgeDimSum_eq (chainOf (□n) α)
  have hr : dimSum (chainRun α).dims = n :=
    wedgeDimSum_eq ((chainRun α).map ≫ chainOf (□n) α)
  have hr' : dimSum (chainRun (α ≫ (reorientBp n σ).hom)).dims = n :=
    wedgeDimSum_eq ((chainRun (α ≫ (reorientBp n σ).hom)).map
      ≫ chainOf (□n) (α ≫ (reorientBp n σ).hom))
  obtain ⟨e, he⟩ : ∃ e : beadEvent (chainRun α).dims, coordFlip (runLine α).map e = q :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  set f : beadEvent d := strandTransfer hr hd e with hf
  have hposf : (pos f : ℕ) = (pos e : ℕ) := pos_strandTransfer hr hd e
  set e' : beadEvent (chainRun (α ≫ (reorientBp n σ).hom)).dims := strandTransfer hd hr' f with hfe'
  have hpose' : (pos e' : ℕ) = (pos f : ℕ) := pos_strandTransfer hd hr' f
  have hdir : beadDir α f.1 f.2 = q :=
    (coordFlip_runLine α e f.1 f.2 (hposf.symm.trans (pos_val f))).symm.trans he
  have hdir' : coordFlip (runLine (α ≫ (reorientBp n σ).hom)).map e' = σ q := by
    rw [coordFlip_runLine (α ≫ (reorientBp n σ).hom) e' f.1 f.2 (hpose'.trans (pos_val f)),
      beadDir_reorient, hdir]
  rw [beadOf_eq_of_coordFlip (C := runLine (α ≫ (reorientBp n σ).hom)) (p := e') hdir',
    beadOf_eq_of_coordFlip (C := runLine α) (p := e) he,
    ← pos_ones (chainRun (α ≫ (reorientBp n σ).hom)).ones e', ← pos_ones (chainRun α).ones e,
    hpose', hposf]

/-- **A chain whose beads are permuted has its braid face reoriented** — `chFace` sees `beadOf`
and nothing else, so this is the only content of both reorientation statements below. -/
theorem chFace_reorient_of_beadOf {n : ℕ} {C C' : Ch (□n)} (σ : Equiv.Perm (Fin n))
    (h : ∀ q : Fin n, (beadOf C' (σ q) : ℕ) = (beadOf C q : ℕ)) :
    (chFace C').1 = reorient σ (chFace C).1 := by
  rw [chFace_val, chFace_val, reorient_braidSign]
  exact congrArg braidSign (funext fun q => congrArg (fun m : ℕ => (m : ℤ))
    ((congrArg (fun p : Fin n => (beadOf C' p : ℕ)) (Equiv.apply_symm_apply σ q)).symm.trans
      (h (σ⁻¹ q))))

/-- **The braid face of the underlying chain is reoriented.** -/
theorem chFace_chainOf_reorient {n : ℕ} {d : List ℕ+} (σ : Equiv.Perm (Fin n))
    (α : ⋁d ⟶ Hbp.obj (□n)) :
    (chFace ⟨d, chainOf (□n) (α ≫ (reorientBp n σ).hom)⟩).1
      = reorient σ (chFace ⟨d, chainOf (□n) α⟩).1 :=
  chFace_reorient_of_beadOf σ fun q => congrArg Fin.val (beadOf_chainOf_reorient σ α q)

/-- **The braid face of the run's chain — the Salvetti tope — is reoriented.** -/
theorem chFace_runLine_reorient {n : ℕ} {d : List ℕ+} (σ : Equiv.Perm (Fin n))
    (α : ⋁d ⟶ Hbp.obj (□n)) :
    (chFace (runLine (α ≫ (reorientBp n σ).hom))).1 = reorient σ (chFace (runLine α)).1 :=
  chFace_reorient_of_beadOf σ (beadOf_runLine_reorient σ α)

/-! ## Equivariance of the comparison -/

/-- **The decorated chains of the cube are the Salvetti poset of the braid arrangement.** -/
def hbpBraidSalEquiv (n : ℕ) : Ch (Hbp.obj (□n)) ≌ (Sal (braidCOM n))ᵒᵖ :=
  hbpSalEquiv chFaceCatEquiv linesTopeIso

/-- The Salvetti face of a decorated chain is the braid face of the chain it decorates. -/
@[simp] theorem face_hbpBraidSalEquiv {n : ℕ} (a : Ch (Hbp.obj (□n))) :
    ((hbpBraidSalEquiv n).functor.obj a).unop.face = (chFace ⟨a.dims, chainOf (□n) a.map⟩).1 := rfl

/-- …and its Salvetti tope is the braid face of the chain its run performs. -/
@[simp] theorem tope_hbpBraidSalEquiv {n : ℕ} (a : Ch (Hbp.obj (□n))) :
    ((hbpBraidSalEquiv n).functor.obj a).unop.tope = (chFace (runLine a.map)).1 :=
  congrArg (fun C : Ch (□n) => (chFace C).1)
    (ChStar.runChain_eq_wordChain (unop ((chSymChStarEquiv (□n)).functor.obj a))).symm

/-- **The comparison is `Sₙ`-equivariant**, cell by cell. -/
theorem hbpBraidSalEquiv_reorient {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Ch (Hbp.obj (□n))) :
    (hbpBraidSalEquiv n).functor.obj ((reorientCh n σ).hom.toFunctor.obj a)
      = op (σ • ((hbpBraidSalEquiv n).functor.obj a).unop) := by
  refine unop_injective (Subtype.ext (Prod.ext ?_ ?_))
  · change ((hbpBraidSalEquiv n).functor.obj ((reorientCh n σ).hom.toFunctor.obj a)).unop.face
        = (σ • ((hbpBraidSalEquiv n).functor.obj a).unop).face
    rw [face_hbpBraidSalEquiv, smul_face, face_hbpBraidSalEquiv]
    exact chFace_chainOf_reorient σ a.map
  · change ((hbpBraidSalEquiv n).functor.obj ((reorientCh n σ).hom.toFunctor.obj a)).unop.tope
        = (σ • ((hbpBraidSalEquiv n).functor.obj a).unop).tope
    rw [tope_hbpBraidSalEquiv, smul_tope, tope_hbpBraidSalEquiv]
    exact chFace_runLine_reorient σ a.map

/-- **`reorientCh n σ` *is* `salReorientFunctor σ` across the comparison** — an equality of
functors: `Sal` is a poset, so the arrow half is automatic. -/
theorem reorientCh_comp_hbpBraidSalEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (reorientCh n σ).hom.toFunctor ⋙ (hbpBraidSalEquiv n).functor
      = (hbpBraidSalEquiv n).functor ⋙ (salReorientFunctor σ).op :=
  CategoryTheory.Functor.ext (hbpBraidSalEquiv_reorient σ) fun _ _ _ => Subsingleton.elim _ _

/-- **The transported action is nowhere trivial** — every chamber's cell moves. -/
theorem smul_topeCell_ne {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1) (T : Tope n) :
    σ • topeCell T ≠ topeCell T := fun h =>
  reorient_tope_ne hσ T (congrArg COM.SalCell.face h)

/-! ## The obstruction -/

/-- `Sal` is a poset, so the comparison's counit is an equality of cells. -/
theorem hbpBraidSalEquiv_functor_inverse {n : ℕ} (Y : (Sal (braidCOM n))ᵒᵖ) :
    (hbpBraidSalEquiv n).functor.obj ((hbpBraidSalEquiv n).inverse.obj Y) = Y :=
  unop_injective (le_antisymm (leOfHom ((hbpBraidSalEquiv n).counitIso.inv.app Y).unop)
    (leOfHom ((hbpBraidSalEquiv n).counitIso.hom.app Y).unop))

/-- **The reorientation is realized on `H(□ⁿ)` and on nothing over `□ⁿ`.**  `Box` is rigid, so
`□ⁿ` has no symmetries and `□ⁿ × run` inherits that rigidity over the base; `H(□ⁿ)` supplies them,
and across the comparison they are the arrangement's reorientations. -/
theorem not_reorientCh_of_over_base {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1)
    {Θ : (□n).prod runBp ⟶ (□n).prod runBp} {c : □n ⟶ □n}
    (hover : Θ ≫ prodFst (□n) runBp = prodFst (□n) runBp ≫ c) :
    (chSymEquiv (□n)).functor ⋙ ChainCat.pushforward Θ
      ≠ (reorientCh n σ).hom.toFunctor ⋙ (chSymEquiv (□n)).functor := by
  intro heq
  set a : Ch (Hbp.obj (□n)) :=
    (hbpBraidSalEquiv n).inverse.obj (op (topeCell (wordTopeEquiv (1 : Equiv.Perm (Fin n)))))
    with ha
  have hface : (chFace ⟨a.dims, chainOf (□n) a.map⟩).1
      = (wordTopeEquiv (1 : Equiv.Perm (Fin n))).1 := by
    rw [← face_hbpBraidSalEquiv a, ha, hbpBraidSalEquiv_functor_inverse]
    rfl
  have hL : (ChainCat.pushforward (prodFst (□n) runBp)).obj
      ((ChainCat.pushforward Θ).obj ((chSymEquiv (□n)).functor.obj a))
      = (⟨a.dims, chainOf (□n) a.map⟩ : Ch (□n)) :=
    congrArg (fun F : Ch ((□n).prod runBp) ⥤ Ch (□n) =>
      F.obj ((chSymEquiv (□n)).functor.obj a)) (pushforward_prodFst_of_over n hover)
  have hR : (ChainCat.pushforward (prodFst (□n) runBp)).obj
      ((ChainCat.pushforward Θ).obj ((chSymEquiv (□n)).functor.obj a))
      = (⟨a.dims, chainOf (□n) (a.map ≫ (reorientBp n σ).hom)⟩ : Ch (□n)) :=
    congrArg (fun F : Ch (Hbp.obj (□n)) ⥤ Ch ((□n).prod runBp) =>
      (ChainCat.pushforward (prodFst (□n) runBp)).obj (F.obj a)) heq
  have h2 := (congrArg (fun C : Ch (□n) => (chFace C).1) (hL.symm.trans hR)).trans
    (chFace_chainOf_reorient σ a.map)
  rw [hface] at h2
  exact reorient_tope_ne hσ (wordTopeEquiv 1) h2.symm

/-! ## `n = 2`, computably

The chamber of the identity run word is the wall `reorient_swap_braidSign_ne` names, and the
transposition moves it — as a tope, and as a Salvetti cell. -/

example : wordTope (1 : Equiv.Perm (Fin 2)) = braidSign ![(0 : ℤ), 1] :=
  (wordTope_eq_braidSign 1).trans (congrArg braidSign (funext fun q => by fin_cases q <;> rfl))

example : reorient (Equiv.swap (0 : Fin 2) 1) (wordTope (1 : Equiv.Perm (Fin 2)))
    ≠ wordTope 1 := reorient_tope_ne (by decide) (wordTopeEquiv 1)

example : (Equiv.swap (0 : Fin 2) 1) • topeCell (wordTopeEquiv (1 : Equiv.Perm (Fin 2)))
    ≠ topeCell (wordTopeEquiv 1) := smul_topeCell_ne (by decide) _

end CubeChains

