import CubeChains.Salvetti.CubeTope
import CubeChains.Braid.Kernel

/-!
# Salvetti/ConcPure — the loops of executions of the cube are the pure braids

On `□ⁿ` the crossing permutation of a refinement is a *coboundary* (`permOf_tope`), so the braid
functor factors through the ungraded

    cubeConcPos n : Ch⋆ (□n) ⥤ SingleObj (Braid n),   f ↦ ofPerm (tope y · (tope x)⁻¹)

whose free-groupoid lift assigns a braid `concBraid g` to every loop of executions.  Two halves:

* **purity** — a coboundary trivialises `cubeConcPos ⋙ permHom`, so the lift of that composite is
  isomorphic to the constant functor and every loop has trivial permutation (`concBraid_loop_perm`);
* **fullness** — the coarsest chain refines to *every* all-edges chain, so the four-step zigzag
  `coarse(1) → fine(1) ← coarse(C⁻¹) → fine(A) ← coarse(1)` realises the conjugated cocycle
  `(σ_A)⁻¹ σ_{A·C} (σ_C)⁻¹`, and those generate `ker (Braid n ↠ Sₙ)` (`pureBraid_le`).

`Salvetti/ConcCube` grades this back up to `Conc (□n)` itself.
-/

open CategoryTheory Opposite BPSet ChainCat CubeChain Equiv FreeGroupoid

namespace CubeChains

variable {n : ℕ}

/-! ## The ungraded braid functor of the cube -/

/-- **The braid of a refinement is the simple braid of its change of tope.**  Length-additivity is
`permOf_noDoubleCross`, transported along `permOf_tope`. -/
noncomputable def cubeConcPos (n : ℕ) : Ch⋆ (□n) ⥤ SingleObj (Braid n) where
  obj _ := SingleObj.star (Braid n)
  map {x y} _ := ofPerm (tope y * (tope x)⁻¹)
  map_id x := by rw [SingleObj.id_as_one, mul_inv_cancel, ofPerm_one]
  map_comp {x y z} f g := by
    have hmul : (tope z * (tope y)⁻¹) * (tope y * (tope x)⁻¹) = tope z * (tope x)⁻¹ := by group
    have hlen : permLen ((tope z * (tope y)⁻¹) * (tope y * (tope x)⁻¹))
        = permLen (tope z * (tope y)⁻¹) + permLen (tope y * (tope x)⁻¹) := by
      rw [hmul, permLen_tope (f ≫ g), permLen_tope f, permLen_tope g, permOf_noDoubleCross f g,
        Nat.add_comm]
    rw [SingleObj.comp_as_mul, ofPerm_mul hlen, hmul]

/-- **The concurrency braid functor of the cube**, ungraded. -/
noncomputable def cubeConc (n : ℕ) : FreeGroupoid (Ch⋆ (□n)) ⥤ SingleObj (Braid n) :=
  FreeGroupoid.lift (cubeConcPos n)

/-- The braid a zigzag of refinements realises. -/
noncomputable def concBraid {x y : Ch⋆ (□n)} (g : mk x ⟶ mk y) : Braid n := (cubeConc n).map g

@[simp] theorem concBraid_homMk {x y : Ch⋆ (□n)} (f : x ⟶ y) :
    concBraid (homMk f) = ofPerm (tope y * (tope x)⁻¹) :=
  FreeGroupoid.lift_map_homMk _ f

theorem concBraid_id (x : Ch⋆ (□n)) : concBraid (𝟙 (mk x)) = 1 := by
  rw [concBraid, (cubeConc n).map_id, SingleObj.id_as_one]

theorem concBraid_comp {x y z : Ch⋆ (□n)} (g : mk x ⟶ mk y) (h : mk y ⟶ mk z) :
    concBraid (g ≫ h) = concBraid h * concBraid g := by
  rw [concBraid, (cubeConc n).map_comp, SingleObj.comp_as_mul]
  rfl

theorem concBraid_inv {x y : Ch⋆ (□n)} (g : mk x ⟶ mk y) :
    concBraid (Groupoid.inv g) = (concBraid g)⁻¹ := by
  rw [concBraid, Groupoid.inv_eq_inv, (cubeConc n).map_inv, SingleObj.inv_as_inv]
  rfl

/-! ## Purity: the permutation of a loop is trivial

`cubeConcPos ⋙ permHom` sends `f` to the coboundary `tope y · (tope x)⁻¹`, so it is naturally
isomorphic to the constant functor at `1`; lifting, every loop maps to `1`.  No induction over
free-groupoid words. -/

/-- The permutation a refinement performs. -/
noncomputable def cubePerm (n : ℕ) : Ch⋆ (□n) ⥤ SingleObj (Perm (Fin n)) :=
  cubeConcPos n ⋙ SingleObj.mapHom _ _ (permHom n)

theorem cubePerm_map {x y : Ch⋆ (□n)} (f : x ⟶ y) :
    (cubePerm n).map f = tope y * (tope x)⁻¹ :=
  permHom_ofPerm _

/-- **The tope trivialises the permutation functor** — its components are the topes themselves. -/
noncomputable def cubePermIso (n : ℕ) :
    cubePerm n ≅ (Functor.const (Ch⋆ (□n))).obj (SingleObj.star (Perm (Fin n))) :=
  NatIso.ofComponents
    (fun x =>
      { hom := ((tope x)⁻¹ : Perm (Fin n))
        inv := (tope x : Perm (Fin n))
        hom_inv_id := mul_inv_cancel (tope x)
        inv_hom_id := inv_mul_cancel (tope x) })
    (fun {x y} f => by
      change (tope y)⁻¹ * (cubePerm n).map f = 1 * (tope x)⁻¹
      rw [cubePerm_map, one_mul]
      group)

/-- **Loops are pure**: the permutation of a loop of executions is trivial. -/
theorem concBraid_loop_perm {x : Ch⋆ (□n)} (g : mk x ⟶ mk x) : permHom n (concBraid g) = 1 := by
  set Φ := cubeConc n ⋙ SingleObj.mapHom _ _ (permHom n) with hΦ
  have hspec : FreeGroupoid.of (Ch⋆ (□n)) ⋙ Φ = cubePerm n := by
    rw [hΦ, ← Functor.assoc, cubeConc, FreeGroupoid.lift_spec]
    rfl
  have hconst : FreeGroupoid.of (Ch⋆ (□n))
      ⋙ (Functor.const (FreeGroupoid (Ch⋆ (□n)))).obj (SingleObj.star (Perm (Fin n)))
      = (Functor.const (Ch⋆ (□n))).obj (SingleObj.star (Perm (Fin n))) := rfl
  set β := FreeGroupoid.liftNatIso Φ
    ((Functor.const (FreeGroupoid (Ch⋆ (□n)))).obj (SingleObj.star (Perm (Fin n))))
    (eqToIso hspec ≪≫ cubePermIso n ≪≫ eqToIso hconst.symm) with hβ
  set a : Perm (Fin n) := β.hom.app (mk x) with ha
  have h1 : a * permHom n (concBraid g) = a * 1 := by
    rw [mul_one, ha]
    exact (β.hom.naturality g).trans (Category.comp_id _)
  exact mul_left_cancel h1

/-! ## The loops of executions, and the braids they realise -/

/-- The braids realised by the loops of executions at `x`. -/
noncomputable def concImage (x : Ch⋆ (□n)) : Subgroup (Braid n) where
  carrier := {b | ∃ g : mk x ⟶ mk x, concBraid g = b}
  one_mem' := ⟨𝟙 _, concBraid_id x⟩
  mul_mem' := by
    rintro _ _ ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨h ≫ g, concBraid_comp h g⟩
  inv_mem' := by
    rintro _ ⟨g, rfl⟩
    exact ⟨Groupoid.inv g, concBraid_inv g⟩

theorem mem_concImage {x : Ch⋆ (□n)} {b : Braid n} :
    b ∈ concImage x ↔ ∃ g : mk x ⟶ mk x, concBraid g = b := Iff.rfl

/-- Every braid realised by a loop is pure. -/
theorem concImage_le_pureBraid (x : Ch⋆ (□n)) : concImage x ≤ PureBraid n := by
  rintro _ ⟨g, rfl⟩
  exact concBraid_loop_perm g

/-- The coarsest chain sits below every all-edges chain, so it refines to every fine execution. -/
noncomputable def coarseToFine (hn : 0 < n) (τ β : Perm (Fin n)) :
    coarseExec hn τ ⟶ fineExec β :=
  homOfIsRun (edgeChain_isRun β) (by
    rw [coarseExec_chain, chFace_coarseChain]
    exact fun e => Or.inl rfl)

/-- **The four-step zigzag.**  `coarse(1) → fine(1) ← coarse(C⁻¹) → fine(A) ← coarse(1)` reads off
the conjugated cocycle — which is exactly the algebra `pureBraid_le` asks for. -/
theorem cocycle'_mem_concImage (hn : 0 < n) (A C : Perm (Fin n)) :
    (ofPerm A)⁻¹ * ofPerm (A * C) * (ofPerm C)⁻¹ ∈ concImage (coarseExec hn 1) := by
  refine ⟨homMk (coarseToFine hn 1 1) ≫ Groupoid.inv (homMk (coarseToFine hn C⁻¹ 1))
      ≫ homMk (coarseToFine hn C⁻¹ A) ≫ Groupoid.inv (homMk (coarseToFine hn 1 A)), ?_⟩
  rw [concBraid_comp, concBraid_comp, concBraid_comp, concBraid_inv, concBraid_inv,
    concBraid_homMk, concBraid_homMk, concBraid_homMk, concBraid_homMk]
  simp

/-! ## Fullness -/

/-- Transport along a zigzag: the image subgroups are conjugate, and `PureBraid` is normal. -/
theorem pureBraid_le_of_path {x y : Ch⋆ (□n)} (p : mk x ⟶ mk y)
    (h : PureBraid n ≤ concImage x) : PureBraid n ≤ concImage y := by
  intro b hb
  have hconj : (concBraid p)⁻¹ * b * concBraid p ∈ PureBraid n := by
    rw [MonoidHom.mem_ker] at hb ⊢
    rw [map_mul, map_mul, map_inv, hb, mul_one, inv_mul_cancel]
  obtain ⟨g, hg⟩ := h hconj
  refine ⟨Groupoid.inv p ≫ g ≫ p, ?_⟩
  rw [concBraid_comp, concBraid_comp, concBraid_inv, hg]
  group

/-- Every execution refines to an all-edges one: its own run, pushed forward along its chain. -/
noncomputable def toEdgeExec (x : Ch⋆ (□n)) : Ch⋆ (□n) :=
  edgeExec (c := pushC x.chain x.run) x.run.ones

/-- Both `x` and the coarsest execution refine to `toEdgeExec x`, so every execution is connected
to the coarsest one. -/
noncomputable def pathToCoarse (hn : 0 < n) (x : Ch⋆ (□n)) : mk x ⟶ mk (coarseExec hn 1) :=
  homMk (homOfIsRun (z := toEdgeExec x) x.run.ones (chFace_faceLE (pushHom x.chain x.run)))
    ≫ Groupoid.inv (homMk (homOfIsRun (z := toEdgeExec x) x.run.ones (by
        rw [coarseExec_chain, chFace_coarseChain]
        exact fun e => Or.inl rfl)))

/-- **Fullness onto the pure braids**, ungraded: at *any* execution, every pure braid is realised
by a loop. -/
theorem pureBraid_le_concImage (x : Ch⋆ (□n)) : PureBraid n ≤ concImage x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine pureBraid_le _ fun A C => ?_
    rw [Subsingleton.elim A 1, Subsingleton.elim C 1, one_mul, ofPerm_one, inv_one, mul_one,
      mul_one]
    exact one_mem _
  · exact pureBraid_le_of_path (Groupoid.inv (pathToCoarse hn x))
      (pureBraid_le _ fun A C => cocycle'_mem_concImage hn A C)

/-- **The loops of executions of `□ⁿ` are exactly the pure braids.** -/
theorem concImage_eq_pureBraid (x : Ch⋆ (□n)) : concImage x = PureBraid n :=
  le_antisymm (concImage_le_pureBraid x) (pureBraid_le_concImage x)

end CubeChains
