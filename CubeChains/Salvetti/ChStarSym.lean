import CubeChains.Foundations.SymPresheaf
import CubeChains.Salvetti.ChStarProduct
import CubeChains.Salvetti.RunPerm
import CubeChains.Salvetti.SymRun

/-!
# Salvetti/ChStarSym — the symmetric round trip is the run product

`Ch (Hbp K) ≌ Ch (K.prod runBp)` for every `K`.  There is no map `Hbp K ⟶ K`; the
correspondence is a *twist*, and it exists because a symmetry fixes the extremal vertices of a
cube, so a bead-wise symmetry glues across a wedge.
-/

open CategoryTheory Opposite BPSet CubeChain ChainCat StdCube

namespace CubeChains

/-! ## A symmetry fixes a constant vertex

`J v ≫ symHom σ = J v` for a constant-sign `v : ▫0 ⟶ ▫n`: permuting the coordinates of a vertex
whose coordinates are all `ε` changes nothing. -/

/-- A symmetry fixes a constant-sign box map. -/
theorem J_map_const_comp_symHom {n : ℕ} {ε : Bool} (v : ▫0 ⟶ ▫n)
    (hv : Box.sign v = constVertex n ε) (σ : Equiv.Perm (Fin n)) :
    J.map v ≫ symHom σ = J.map v :=
  SHom.ext <| funext fun j => by
    change SHom.coord (J.map v) (σ.symm j) = SHom.coord (J.map v) j
    rw [J_map_coord, J_map_coord, hv, (cellCoord_eq_inl_iff _ _ ε).2 rfl,
      (cellCoord_eq_inl_iff _ _ ε).2 rfl]

/-- Sorting a constant-sign box map through a symmetry does nothing. -/
theorem sortPerm_sortFace_const {n : ℕ} {ε : Bool} (v : ▫0 ⟶ ▫n)
    (hv : Box.sign v = constVertex n ε) (σ : Equiv.Perm (Fin n)) :
    (SHom.sortPerm (J.map v) σ, SHom.sortFace (J.map v) σ) = (1, v) :=
  SHom.sortPerm_sortFace_eq (by
    rw [sHomEquiv_symm_one]; exact (J_map_const_comp_symHom v hv σ).symm)

theorem sign_initVertexMap (n : ℕ) :
    Box.sign (PrecubicalSet.initVertexMap n) = constVertex n false := ev_canonicalMap _

theorem sign_finalVertexMap (n : ℕ) :
    Box.sign (PrecubicalSet.finalVertexMap n) = constVertex n true := ev_canonicalMap _

/-! ## `Hbp` — the round trip on bi-pointed sets -/

/-- `Hbp K` — `H K` based at `K`'s own endpoints in the identity order. -/
def Hbp : BPSet ⥤ BPSet where
  obj K :=
    { toPsh := H.obj K.toPsh
      init := (1, K.init)
      final := (1, K.final) }
  map f :=
    { hom := H.map f.hom
      app_init := Prod.ext rfl f.app_init
      app_final := Prod.ext rfl f.app_final }
  map_id K := hom_ext (H.map_id K.toPsh)
  map_comp f g := hom_ext (H.map_comp f.hom g.hom)

@[simp] theorem Hbp_obj_toPsh (K : BPSet) : (Hbp.obj K).toPsh = H.obj K.toPsh := rfl

@[simp] theorem Hbp_map_hom {K L : BPSet} (f : K ⟶ L) : (Hbp.map f).hom = H.map f.hom := rfl

@[simp] theorem Hbp_map_app {K L : BPSet} (f : K ⟶ L) {n : ℕ}
    (p : Equiv.Perm (Fin n) × K.cells n) :
    (Hbp.map f).hom⟪n⟫ p = (p.1, f.hom⟪n⟫ p.2) := rfl

/-- **An `Hbp`-cell's extremal vertices forget the order** — a symmetry fixes them. -/
theorem Hbp_vertex₀ {K : BPSet} {n : ℕ} (p : Equiv.Perm (Fin n) × K.cells n) :
    (Hbp.obj K).toPsh.vertex₀ p = ((1 : Equiv.Perm (Fin 0)), K.toPsh.vertex₀ p.2) := by
  have h := sortPerm_sortFace_const (PrecubicalSet.initVertexMap n) (sign_initVertexMap n) p.1
  change (H.obj K.toPsh).map (PrecubicalSet.initVertexMap n).op p = _
  rw [Prod.mk.injEq] at h
  rw [H_obj_map, h.1, h.2]
  rfl

theorem Hbp_vertex₁ {K : BPSet} {n : ℕ} (p : Equiv.Perm (Fin n) × K.cells n) :
    (Hbp.obj K).toPsh.vertex₁ p = ((1 : Equiv.Perm (Fin 0)), K.toPsh.vertex₁ p.2) := by
  have h := sortPerm_sortFace_const (PrecubicalSet.finalVertexMap n) (sign_finalVertexMap n) p.1
  change (H.obj K.toPsh).map (PrecubicalSet.finalVertexMap n).op p = _
  rw [Prod.mk.injEq] at h
  rw [H_obj_map, h.1, h.2]
  rfl

/-! ## A decorated cube is a cube with a run

The order is read **backwards**: a run restricts along the *twisted* face, and inverting is what
turns that into `sortPerm`'s own cocycle. -/

variable (K : BPSet)

/-- An `Hbp`-cell is a `K`-cell together with a run of its axes. -/
def symCell (n : ℕ) : (Hbp.obj K).cells n → (K.prod runBp).cells n :=
  fun p => (p.2, (runPermEquiv n).symm p.1⁻¹)

/-- …and back. -/
def unsymCell (n : ℕ) : (K.prod runBp).cells n → (Hbp.obj K).cells n :=
  fun q => ((runPermEquiv n q.2)⁻¹, q.1)

@[simp] theorem unsymCell_symCell (n : ℕ) (p : (Hbp.obj K).cells n) :
    unsymCell K n (symCell K n p) = p := by
  refine Prod.ext ?_ rfl
  change ((runPermEquiv n) ((runPermEquiv n).symm p.1⁻¹))⁻¹ = p.1
  rw [Equiv.apply_symm_apply, inv_inv]

@[simp] theorem symCell_unsymCell (n : ℕ) (q : (K.prod runBp).cells n) :
    symCell K n (unsymCell K n q) = q := by
  refine Prod.ext rfl ?_
  change (runPermEquiv n).symm ((runPermEquiv n q.2)⁻¹)⁻¹ = q.2
  rw [inv_inv, Equiv.symm_apply_apply]

theorem symCell_injective (n : ℕ) : Function.Injective (symCell K n) :=
  Function.LeftInverse.injective (unsymCell_symCell K n)

theorem symCell_vertex₀ (n : ℕ) (p : (Hbp.obj K).cells n) :
    symCell K 0 ((Hbp.obj K).toPsh.vertex₀ p)
      = (K.prod runBp).toPsh.vertex₀ (symCell K n p) := by
  rw [symCell, Hbp_vertex₀]
  exact Prod.ext rfl (run_cube0_eq _ _)

theorem symCell_vertex₁ (n : ℕ) (p : (Hbp.obj K).cells n) :
    symCell K 0 ((Hbp.obj K).toPsh.vertex₁ p)
      = (K.prod runBp).toPsh.vertex₁ (symCell K n p) := by
  rw [symCell, Hbp_vertex₁]
  exact Prod.ext rfl (run_cube0_eq _ _)

@[simp] theorem symCell_init : symCell K 0 (Hbp.obj K).init = (K.prod runBp).init :=
  Prod.ext rfl (run_cube0_eq _ _)

@[simp] theorem symCell_final : symCell K 0 (Hbp.obj K).final = (K.prod runBp).final :=
  Prod.ext rfl (run_cube0_eq _ _)

/-- A decorated cube, read as a cube with a run. -/
def symCube (c : Σ n : ℕ+, (Hbp.obj K).cells (n : ℕ)) : Σ n : ℕ+, (K.prod runBp).cells (n : ℕ) :=
  ⟨c.1, symCell K _ c.2⟩

/-- …and back. -/
def unsymCube (c : Σ n : ℕ+, (K.prod runBp).cells (n : ℕ)) :
    Σ n : ℕ+, (Hbp.obj K).cells (n : ℕ) :=
  ⟨c.1, unsymCell K _ c.2⟩

@[simp] theorem unsymCube_symCube (c : Σ n : ℕ+, (Hbp.obj K).cells (n : ℕ)) :
    unsymCube K (symCube K c) = c :=
  congrArg (Sigma.mk c.1) (unsymCell_symCell K _ c.2)

@[simp] theorem symCube_unsymCube (c : Σ n : ℕ+, (K.prod runBp).cells (n : ℕ)) :
    symCube K (unsymCube K c) = c :=
  congrArg (Sigma.mk c.1) (symCell_unsymCell K _ c.2)

@[simp] theorem map_unsymCube_symCube (l : List (Σ n : ℕ+, (Hbp.obj K).cells (n : ℕ))) :
    (l.map (symCube K)).map (unsymCube K) = l := by
  rw [List.map_map]
  exact (List.map_congr_left fun c _ => unsymCube_symCube K c).trans (List.map_id l)

@[simp] theorem map_symCube_unsymCube (l : List (Σ n : ℕ+, (K.prod runBp).cells (n : ℕ))) :
    (l.map (unsymCube K)).map (symCube K) = l := by
  rw [List.map_map]
  exact (List.map_congr_left fun c _ => symCube_unsymCube K c).trans (List.map_id l)

/-- **Chains transfer**: a cube list of `Hbp K` is a chain exactly when its run-reading is. -/
theorem isCubeChain_symCube (l : List (Σ n : ℕ+, (Hbp.obj K).cells (n : ℕ))) :
    IsCubeChain (Hbp.obj K).init l (Hbp.obj K).final
      ↔ IsCubeChain (K.prod runBp).init (l.map (symCube K)) (K.prod runBp).final := by
  constructor
  · intro h
    have := isCubeChain_push (u := symCell K) (symCell_vertex₀ K) (symCell_vertex₁ K) l h
    rwa [symCell_init, symCell_final] at this
  · intro h
    refine isCubeChain_of_push (u := symCell K) (symCell_vertex₀ K) (symCell_vertex₁ K)
      (symCell_injective K 0) l _ _ ?_
    rwa [symCell_init, symCell_final]

/-- **A chain in `Hbp K` is a chain in `K` with a run.** -/
def chainSymEquiv : CubeChain (Hbp.obj K) ≃ CubeChain (K.prod runBp) where
  toFun C := ⟨C.cubes.map (symCube K), (isCubeChain_symCube K C.cubes).1 C.2⟩
  invFun D := ⟨D.cubes.map (unsymCube K), (isCubeChain_symCube K _).2 (by
    rw [map_symCube_unsymCube]; exact D.2)⟩
  left_inv C := Subtype.ext (map_unsymCube_symCube K C.cubes)
  right_inv D := Subtype.ext (map_symCube_unsymCube K D.cubes)

@[simp] theorem chainSymEquiv_dims (C : CubeChain (Hbp.obj K)) :
    (chainSymEquiv K C).dims = C.dims := by
  change (C.cubes.map (symCube K)).map (·.1) = C.cubes.map (·.1)
  rw [List.map_map]; rfl

@[simp] theorem chainSymEquiv_symm_dims (D : CubeChain (K.prod runBp)) :
    ((chainSymEquiv K).symm D).dims = D.dims := by
  change (D.cubes.map (unsymCube K)).map (·.1) = D.cubes.map (·.1)
  rw [List.map_map]; rfl

/-! ## Cube lists and classifying maps

A bi-pointed map `⋁d ⟶ K` *is* a cube chain with dimension sequence `d`: `wedgeChain` reads the
cubes off, `ofCubes` glues them back, and `wedgeMap_ext` says the cubes determine the map. -/

/-- The chain a bi-pointed wedge map classifies, indexed by the dimension sequence. -/
def wedgeChain {K : BPSet} (d : List ℕ+) (α : ⋁d ⟶ K) : CubeChain K := chCubes K ⟨d, α⟩

@[simp] theorem wedgeChain_cubes {K : BPSet} (d : List ℕ+) (α : ⋁d ⟶ K) :
    (wedgeChain d α).cubes = wedgeToCubes ⟨d, α.hom⟩ := rfl

@[simp] theorem wedgeChain_dims {K : BPSet} (d : List ℕ+) (α : ⋁d ⟶ K) :
    (wedgeChain d α).dims = d := chCubes_dims ⟨d, α⟩

/-- **A bi-pointed wedge map is its cube list.** -/
theorem wedgeMap_ext {K : BPSet} {d : List ℕ+} {α β : ⋁d ⟶ K}
    (h : wedgeChain d α = wedgeChain d β) : α = β :=
  hom_ext (wedgeToCubes_inj d α.hom β.hom (congrArg Subtype.val h)
    (α.app_init.trans β.app_init.symm))

/-- …and every chain with the right dimensions is one. -/
def ofCubes {K : BPSet} {d : List ℕ+} (C : CubeChain K) (h : C.dims = d) : ⋁d ⟶ K :=
  ⋁≡ h.symm ≫ wedgeDescHom C.cubes C.2

@[simp] theorem wedgeChain_ofCubes {K : BPSet} {d : List ℕ+} (C : CubeChain K) (h : C.dims = d) :
    wedgeChain d (ofCubes C h) = C :=
  Subtype.ext (by
    subst h
    simp only [ofCubes, eqToHom_refl, Category.id_comp]
    exact wedgeToCubes_wedgeDescHom C.cubes C.2)

/-! ## The order/run correspondence on classifying maps -/

/-- **A chain in `Hbp K` is a chain in `K` with a run**, read on classifying maps. -/
def desym {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) : ⋁d ⟶ K.prod runBp :=
  ofCubes (chainSymEquiv K (wedgeChain d α)) (by rw [chainSymEquiv_dims, wedgeChain_dims])

/-- …and back. -/
def resym {d : List ℕ+} (β : ⋁d ⟶ K.prod runBp) : ⋁d ⟶ Hbp.obj K :=
  ofCubes ((chainSymEquiv K).symm (wedgeChain d β))
    (by rw [chainSymEquiv_symm_dims, wedgeChain_dims])

@[simp] theorem wedgeChain_desym {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) :
    wedgeChain d (desym K α) = chainSymEquiv K (wedgeChain d α) := wedgeChain_ofCubes _ _

@[simp] theorem wedgeChain_resym {d : List ℕ+} (β : ⋁d ⟶ K.prod runBp) :
    wedgeChain d (resym K β) = (chainSymEquiv K).symm (wedgeChain d β) := wedgeChain_ofCubes _ _

@[simp] theorem resym_desym {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) : resym K (desym K α) = α :=
  wedgeMap_ext (by rw [wedgeChain_resym, wedgeChain_desym, Equiv.symm_apply_apply])

@[simp] theorem desym_resym {d : List ℕ+} (β : ⋁d ⟶ K.prod runBp) : desym K (resym K β) = β :=
  wedgeMap_ext (by rw [wedgeChain_desym, wedgeChain_resym, Equiv.apply_symm_apply])

/-- **A chain in `Hbp K` is a chain in `K` with a run**, as a bijection of classifying maps. -/
def symMapEquiv (d : List ℕ+) : (⋁d ⟶ Hbp.obj K) ≃ (⋁d ⟶ K.prod runBp) where
  toFun := desym K
  invFun := resym K
  left_inv := resym_desym K
  right_inv := desym_resym K

/-! ## Beads

A bi-pointed wedge map is its list of beads, and post-composition acts bead-wise: all the
computations below are one bead at a time. -/

/-- Bead `i` of a bi-pointed wedge map. -/
def bead {K : BPSet} (d : List ℕ+) (α : ⋁d ⟶ K) (i : Fin d.length) : K.cells (d.get i : ℕ) :=
  yonedaEquiv (ιᵂ d i ≫ α.hom)

theorem wedgeChain_eq_ofFn {K : BPSet} (d : List ℕ+) (α : ⋁d ⟶ K) :
    (wedgeChain d α).cubes = List.ofFn (fun i => ⟨d.get i, bead d α i⟩) :=
  wedgeToCubes_eq_ofFn d α.hom

/-- Read a bead off a known cube list. -/
theorem bead_eq_of_cubes {K : BPSet} {d : List ℕ+} {α : ⋁d ⟶ K}
    {f : ∀ i : Fin d.length, K.cells (d.get i : ℕ)}
    (h : (wedgeChain d α).cubes = List.ofFn (fun i => ⟨d.get i, f i⟩)) (i : Fin d.length) :
    bead d α i = f i := by
  rw [wedgeChain_eq_ofFn] at h
  simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using congrFun (List.ofFn_inj.mp h) i

/-- **A bi-pointed wedge map is its beads.** -/
theorem wedgeMap_ext_bead {K : BPSet} {d : List ℕ+} {α β : ⋁d ⟶ K}
    (h : ∀ i, bead d α i = bead d β i) : α = β :=
  wedgeMap_ext (Subtype.ext (by
    change (wedgeChain d α).cubes = (wedgeChain d β).cubes
    rw [wedgeChain_eq_ofFn, wedgeChain_eq_ofFn]
    exact congrArg List.ofFn (funext fun i => congrArg (Sigma.mk _) (h i))))

@[simp] theorem bead_comp {K L : BPSet} {d : List ℕ+} (α : ⋁d ⟶ K) (g : K ⟶ L)
    (i : Fin d.length) :
    bead d (α ≫ g) i = g.hom⟪(d.get i : ℕ)⟫ (bead d α i) := by
  rw [bead, bead, comp_hom, ← Category.assoc, yonedaEquiv_comp]

theorem bead_id_comp {K : BPSet} {d : List ℕ+} (g : ⋁d ⟶ K) (i : Fin d.length) :
    g.hom⟪(d.get i : ℕ)⟫ (bead d (𝟙 (⋁d)) i) = bead d g i := by
  rw [← bead_comp, Category.id_comp]

theorem bead_prodLift {X Y : BPSet} {d : List ℕ+} (f : ⋁d ⟶ X) (g : ⋁d ⟶ Y)
    (i : Fin d.length) : bead d (prodLift f g) i = (bead d f i, bead d g i) := rfl

theorem bead_desym {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) (i : Fin d.length) :
    bead d (desym K α) i = symCell K _ (bead d α i) :=
  bead_eq_of_cubes (by
    rw [wedgeChain_desym]
    change ((wedgeChain d α).cubes.map (symCube K)) = _
    rw [wedgeChain_eq_ofFn, List.map_ofFn]
    rfl) i

theorem bead_resym {d : List ℕ+} (β : ⋁d ⟶ K.prod runBp) (i : Fin d.length) :
    bead d (resym K β) i = unsymCell K _ (bead d β i) :=
  bead_eq_of_cubes (by
    rw [wedgeChain_resym]
    change ((wedgeChain d β).cubes.map (unsymCube K)) = _
    rw [wedgeChain_eq_ofFn, List.map_ofFn]
    rfl) i

/-! ## The bead-wise symmetry, and the factorization it generates -/

/-- **The bead-wise symmetry of `⋁d`** — the tautological chain with its beads re-ordered by `ρ`.
It exists because a symmetry fixes the extremal vertices, so the orders glue at the junctions. -/
def symOf {d : List ℕ+} (ρ : ⋁d ⟶ runBp) : ⋁d ⟶ Hbp.obj (⋁d) :=
  resym (⋁d) (prodLift (𝟙 (⋁d)) ρ)

/-- The underlying chain of a decorated chain. -/
def und {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) : ⋁d ⟶ K := desym K α ≫ prodFst K runBp

/-- The run of a decorated chain. -/
def runOf {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) : ⋁d ⟶ runBp := desym K α ≫ prodSnd K runBp

@[simp] theorem bead_und {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) (i : Fin d.length) :
    bead d (und K α) i = (bead d α i).2 := by
  rw [und, bead_comp, bead_desym]; rfl

@[simp] theorem bead_runOf {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) (i : Fin d.length) :
    bead d (runOf K α) i = (runPermEquiv (d.get i : ℕ)).symm (bead d α i).1⁻¹ := by
  rw [runOf, bead_comp, bead_desym]; rfl

/-- The tautological cube of bead `i` — bead `i` of the identity. -/
def taut (d : List ℕ+) (i : Fin d.length) : (⋁d).cells (d.get i : ℕ) := yonedaEquiv (ιᵂ d i)

@[simp] theorem bead_id (d : List ℕ+) (i : Fin d.length) : bead d (𝟙 (⋁d)) i = taut d i := by
  rw [bead, id_hom, Category.comp_id, taut]

@[simp] theorem bead_symOf_fst {d : List ℕ+} (ρ : ⋁d ⟶ runBp) (i : Fin d.length) :
    (bead d (symOf ρ) i).1 = (runPermEquiv (d.get i : ℕ) (bead (K := runBp) d ρ i))⁻¹ := by
  rw [symOf, bead_resym]; rfl

@[simp] theorem bead_symOf_snd {d : List ℕ+} (ρ : ⋁d ⟶ runBp) (i : Fin d.length) :
    (bead d (symOf ρ) i).2 = taut d i := by
  have h : (bead d (symOf ρ) i).2 = bead d (𝟙 (⋁d)) i := by rw [symOf, bead_resym]; rfl
  rw [h, bead_id]

@[simp] theorem bead_Hbp_map_fst {L : BPSet} {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) (c : K ⟶ L)
    (i : Fin d.length) : (bead d (α ≫ Hbp.map c) i).1 = (bead d α i).1 := by
  rw [bead_comp]; rfl

@[simp] theorem bead_Hbp_map_snd {L : BPSet} {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) (c : K ⟶ L)
    (i : Fin d.length) :
    (bead d (α ≫ Hbp.map c) i).2 = c.hom⟪(d.get i : ℕ)⟫ (bead d α i).2 := by
  rw [bead_comp]; rfl

/-- **The factorization is unique**: the chain of `symOf ρ ≫ Hbp c` is `c`… -/
@[simp] theorem und_symOf_comp {d : List ℕ+} (ρ : ⋁d ⟶ runBp) (c : ⋁d ⟶ K) :
    und K (symOf ρ ≫ Hbp.map c) = c :=
  wedgeMap_ext_bead fun i => by
    rw [bead_und, bead_Hbp_map_snd, bead_symOf_snd, ← bead_id]
    exact bead_id_comp c i

/-- …and its run is `ρ`. -/
@[simp] theorem runOf_symOf_comp {d : List ℕ+} (ρ : ⋁d ⟶ runBp) (c : ⋁d ⟶ K) :
    runOf K (symOf ρ ≫ Hbp.map c) = ρ :=
  wedgeMap_ext_bead fun i => by
    rw [bead_runOf, bead_Hbp_map_fst, bead_symOf_fst, inv_inv, Equiv.symm_apply_apply]

/-- **Every decorated chain is a bead-wise symmetry followed by a chain.** -/
theorem symOf_und {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) :
    symOf (runOf K α) ≫ Hbp.map (und K α) = α :=
  wedgeMap_ext_bead fun i => Prod.ext
    (by rw [bead_Hbp_map_fst, bead_symOf_fst, bead_runOf, Equiv.apply_symm_apply, inv_inv])
    (by rw [bead_Hbp_map_snd, bead_symOf_snd, ← bead_id, bead_id_comp, bead_und])

/-! ## The twist

Composing a wedge map with a bead-wise symmetry and factoring again *twists* the map.  Its
functoriality is associativity of `≫` plus uniqueness of the factorization — nothing else. -/

/-- **The twist of a wedge map by a run**: the chain underlying `φ ≫ symOf ρ`. -/
def twist {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) : ⋁a ⟶ ⋁b :=
  und (⋁b) (φ ≫ symOf ρ)

/-- …and the run the twist leaves on the source. -/
def twistRun {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) : ⋁a ⟶ runBp :=
  runOf (⋁b) (φ ≫ symOf ρ)

theorem twist_spec {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) :
    φ ≫ symOf ρ = symOf (twistRun ρ φ) ≫ Hbp.map (twist ρ φ) :=
  (symOf_und (⋁b) (φ ≫ symOf ρ)).symm

@[simp] theorem twist_id {b : List ℕ+} (ρ : ⋁b ⟶ runBp) : twist ρ (𝟙 (⋁b)) = 𝟙 (⋁b) := by
  rw [twist, Category.id_comp, ← Category.comp_id (symOf ρ), ← Hbp.map_id, und_symOf_comp]

@[simp] theorem twistRun_id {b : List ℕ+} (ρ : ⋁b ⟶ runBp) : twistRun ρ (𝟙 (⋁b)) = ρ := by
  rw [twistRun, Category.id_comp, ← Category.comp_id (symOf ρ), ← Hbp.map_id, runOf_symOf_comp]

/-- Twisting twice is twisting once — associativity in `Hbp`, read through uniqueness. -/
theorem twist_spec_comp {a b c : List ℕ+} (υ : ⋁c ⟶ runBp) (φ : ⋁a ⟶ ⋁b) (ψ : ⋁b ⟶ ⋁c) :
    (φ ≫ ψ) ≫ symOf υ
      = symOf (twistRun (twistRun υ ψ) φ)
        ≫ Hbp.map (twist (twistRun υ ψ) φ ≫ twist υ ψ) := by
  rw [Category.assoc, twist_spec υ ψ, ← Category.assoc, twist_spec (twistRun υ ψ) φ,
    Hbp.map_comp, Category.assoc]

theorem twist_comp {a b c : List ℕ+} (υ : ⋁c ⟶ runBp) (φ : ⋁a ⟶ ⋁b) (ψ : ⋁b ⟶ ⋁c) :
    twist υ (φ ≫ ψ) = twist (twistRun υ ψ) φ ≫ twist υ ψ := by
  rw [twist, twist_spec_comp, und_symOf_comp]

theorem twistRun_comp {a b c : List ℕ+} (υ : ⋁c ⟶ runBp) (φ : ⋁a ⟶ ⋁b) (ψ : ⋁b ⟶ ⋁c) :
    twistRun υ (φ ≫ ψ) = twistRun (twistRun υ ψ) φ := by
  rw [twistRun, twist_spec_comp, runOf_symOf_comp]

/-! ## The twisted map carries the run

`twistRun ρ φ` is the restriction of `ρ` along the *twisted* map, not along `φ`.  This is the one
statement that looks at blocks, and the only use of `sortPerm_sortFace_inv`. -/

/-- A wedge map's bead `i` is a face of the target bead it lands in. -/
theorem bead_factor {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (i : Fin a.length) :
    bead a φ i = (⋁b).toPsh.map (blockFace φ.hom i).op (taut b (blockIdx φ.hom i)) :=
  (congrArg yonedaEquiv (blockFace_spec φ.hom i)).trans
    (yonedaEquiv_naturality (ιᵂ b (blockIdx φ.hom i)) (blockFace φ.hom i)).symm

theorem hom_taut {d : List ℕ+} (g : ⋁d ⟶ K) (i : Fin d.length) :
    g.hom⟪(d.get i : ℕ)⟫ (taut d i) = bead d g i := by rw [← bead_id, bead_id_comp]

/-- Bead-wise, post-composition happens in the target bead. -/
theorem bead_comp_block {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (α : ⋁b ⟶ K) (i : Fin a.length) :
    bead a (φ ≫ α) i
      = K.toPsh.map (blockFace φ.hom i).op (bead b α (blockIdx φ.hom i)) := by
  rw [bead_comp, bead_factor, ← hom_taut K α]
  exact NatTrans.naturality_apply α.hom (blockFace φ.hom i).op (taut b (blockIdx φ.hom i))

theorem Hbp_obj_map_fst {X : BPSet} {k m : ℕ} (g : ▫k ⟶ ▫m)
    (p : Equiv.Perm (Fin m) × X.cells m) :
    ((Hbp.obj X).toPsh.map g.op p).1 = SHom.sortPerm (J.map g) p.1 := rfl

theorem Hbp_obj_map_snd {X : BPSet} {k m : ℕ} (g : ▫k ⟶ ▫m)
    (p : Equiv.Perm (Fin m) × X.cells m) :
    ((Hbp.obj X).toPsh.map g.op p).2 = X.toPsh.map (SHom.sortFace (J.map g) p.1).op p.2 := rfl

/-- `runPermEquiv_map` spelled at `runBp` (`rw` will not unfold `runBp.toPsh` to `runPresheaf`). -/
theorem runPermEquiv_map_bp {k m : ℕ} (g : ▫k ⟶ ▫m) (r : runBp.cells m) :
    runPermEquiv k (runBp.toPsh.map g.op r) = SHom.sortPerm (J.map g) (runPermEquiv m r) :=
  runPermEquiv_map g r

/-- `sortPerm_sortFace_inv` in the form the run comparison needs. -/
theorem sortPerm_sortFace_inv' {m n : ℕ} (ψ : ▫m ⟶ ▫n) (τ : Equiv.Perm (Fin n)) :
    SHom.sortPerm (J.map (SHom.sortFace (J.map ψ) τ⁻¹)) τ = (SHom.sortPerm (J.map ψ) τ⁻¹)⁻¹ := by
  simpa using SHom.sortPerm_sortFace_perm ψ τ⁻¹

/-- The order `ρ` gives the target bead that source bead `i` lands in. -/
abbrev blockPerm {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) (i : Fin a.length) :
    Equiv.Perm (Fin (b.get (blockIdx φ.hom i) : ℕ)) :=
  runPermEquiv (b.get (blockIdx φ.hom i) : ℕ) (bead b ρ (blockIdx φ.hom i))

/-- **The bead-wise twist formula**, from any factorization of the source bead through a target
bead — so it applies to a twist as readily as to the map it came from. -/
theorem bead_twist_of {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) (i : Fin a.length)
    (j : Fin b.length) (f : ▫(a.get i : ℕ) ⟶ ▫(b.get j : ℕ))
    (h : bead a φ i = (⋁b).toPsh.map f.op (taut b j)) :
    bead a (twist ρ φ) i
      = (⋁b).toPsh.map (SHom.sortFace (J.map f)
          (runPermEquiv (b.get j : ℕ) (bead b ρ j))⁻¹).op (taut b j) := by
  have hb : bead a (φ ≫ symOf ρ) i
      = (Hbp.obj (⋁b)).toPsh.map f.op (bead b (symOf ρ) j) := by
    rw [bead_comp, h, ← hom_taut (Hbp.obj (⋁b)) (symOf ρ)]
    exact NatTrans.naturality_apply (symOf ρ).hom f.op (taut b j)
  rw [twist, bead_und, hb, Hbp_obj_map_snd, bead_symOf_fst, bead_symOf_snd]

theorem bead_twist {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) (i : Fin a.length) :
    bead a (twist ρ φ) i
      = (⋁b).toPsh.map (SHom.sortFace (J.map (blockFace φ.hom i))
          (blockPerm ρ φ i)⁻¹).op (taut b (blockIdx φ.hom i)) :=
  bead_twist_of ρ φ i _ _ (bead_factor φ i)

theorem bead_twistRun {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) (i : Fin a.length) :
    bead a (twistRun ρ φ) i
      = (runPermEquiv (a.get i : ℕ)).symm
          (SHom.sortPerm (J.map (blockFace φ.hom i)) (blockPerm ρ φ i)⁻¹)⁻¹ := by
  rw [twistRun, bead_runOf, bead_comp_block, Hbp_obj_map_fst, bead_symOf_fst]

/-- **The twist carries the run**: the source run is `ρ` restricted along the twisted map. -/
theorem twistRun_eq {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) :
    twistRun ρ φ = twist ρ φ ≫ ρ :=
  wedgeMap_ext_bead fun i => by
    rw [bead_comp, bead_twist, bead_twistRun,
      NatTrans.naturality_apply ρ.hom _ (taut b (blockIdx φ.hom i)), hom_taut]
    refine (runPermEquiv (a.get i : ℕ)).injective ?_
    rw [Equiv.apply_symm_apply, runPermEquiv_map_bp, sortPerm_sortFace_inv']

/-! ## Inverting a run, and the twist as a bijection -/

/-- A run of a point is no data, so any cube list of runs is a chain. -/
theorem isCubeChain_runBp :
    ∀ (l : List (Σ n : ℕ+, runBp.cells (n : ℕ))) (u v : runBp.cells 0), IsCubeChain u l v
  | [], u, v => run_cube0_eq u v
  | ⟨_, _⟩ :: tl, _, v => ⟨run_cube0_eq _ _, isCubeChain_runBp tl _ v⟩

/-- Invert every bead's order. -/
def starCube (c : Σ n : ℕ+, runBp.cells (n : ℕ)) : Σ n : ℕ+, runBp.cells (n : ℕ) :=
  ⟨c.1, (runPermEquiv (c.1 : ℕ)).symm (runPermEquiv (c.1 : ℕ) c.2)⁻¹⟩

/-- **The bead-wise inverse of a run** — each bead's order read backwards.  Bead-local, hence not
natural in the wedge; it is what un-twists. -/
def starRun {d : List ℕ+} (ρ : ⋁d ⟶ runBp) : ⋁d ⟶ runBp :=
  ofCubes ⟨(wedgeChain d ρ).cubes.map starCube, isCubeChain_runBp _ _ _⟩
    (by
      change ((wedgeChain d ρ).cubes.map starCube).map (·.1) = d
      rw [List.map_map]
      exact wedgeChain_dims d ρ)

@[simp] theorem wedgeChain_starRun {d : List ℕ+} (ρ : ⋁d ⟶ runBp) :
    (wedgeChain d (starRun ρ)).cubes = (wedgeChain d ρ).cubes.map starCube :=
  congrArg Subtype.val (wedgeChain_ofCubes _ _)

@[simp] theorem bead_starRun {d : List ℕ+} (ρ : ⋁d ⟶ runBp) (i : Fin d.length) :
    bead d (starRun ρ) i
      = (runPermEquiv (d.get i : ℕ)).symm (runPermEquiv (d.get i : ℕ) (bead d ρ i))⁻¹ := by
  refine bead_eq_of_cubes (α := starRun ρ)
    (f := fun i => (runPermEquiv (d.get i : ℕ)).symm (runPermEquiv (d.get i : ℕ) (bead d ρ i))⁻¹)
    ?_ i
  rw [wedgeChain_starRun, wedgeChain_eq_ofFn, List.map_ofFn]
  rfl

@[simp] theorem starRun_starRun {d : List ℕ+} (ρ : ⋁d ⟶ runBp) : starRun (starRun ρ) = ρ :=
  wedgeMap_ext_bead fun i => by
    rw [bead_starRun, bead_starRun, Equiv.apply_symm_apply, inv_inv, Equiv.symm_apply_apply]

/-- `sortFace_sortFace_inv` in the form the un-twist needs. -/
theorem sortFace_sortFace_inv' {m n : ℕ} (ψ : ▫m ⟶ ▫n) (τ : Equiv.Perm (Fin n)) :
    SHom.sortFace (J.map (SHom.sortFace (J.map ψ) τ⁻¹)) τ = ψ := by
  simpa using SHom.sortFace_sortFace_inv ψ τ⁻¹

/-- **Twisting by the inverse run un-twists.** -/
theorem twist_starRun_twist {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) :
    twist (starRun ρ) (twist ρ φ) = φ :=
  wedgeMap_ext_bead fun i => by
    rw [bead_twist_of (starRun ρ) (twist ρ φ) i (blockIdx φ.hom i) _ (bead_twist ρ φ i),
      bead_starRun, Equiv.apply_symm_apply, inv_inv, sortFace_sortFace_inv']
    exact (bead_factor φ i).symm

theorem twist_twist_starRun {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (ψ : ⋁a ⟶ ⋁b) :
    twist ρ (twist (starRun ρ) ψ) = ψ := by
  have h := twist_starRun_twist (starRun ρ) ψ
  rwa [starRun_starRun] at h

/-- **Twisting by a run is a bijection on wedge maps.** -/
def twistEquiv {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) : (⋁a ⟶ ⋁b) ≃ (⋁a ⟶ ⋁b) where
  toFun := twist ρ
  invFun := twist (starRun ρ)
  left_inv := twist_starRun_twist ρ
  right_inv := twist_twist_starRun ρ

/-- Restriction of the inverse run is the inverse of the twisted restriction. -/
theorem twistRun_starRun {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (ψ : ⋁a ⟶ ⋁b) :
    twistRun (starRun ρ) ψ = starRun (ψ ≫ ρ) :=
  wedgeMap_ext_bead fun i => by
    rw [bead_twistRun, bead_starRun, bead_comp_block, runPermEquiv_map_bp]
    simp only [blockPerm, bead_starRun, Equiv.apply_symm_apply, inv_inv]

/-! ## `Ch (Hbp K) ≌ Ch (K.prod runBp)` -/

theorem und_comp {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (β : ⋁b ⟶ Hbp.obj K) :
    und K (φ ≫ β) = twist (runOf K β) φ ≫ und K β := by
  conv_lhs => rw [← symOf_und K β]
  rw [← Category.assoc, twist_spec, Category.assoc, ← Hbp.map_comp, und_symOf_comp]

theorem runOf_comp {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (β : ⋁b ⟶ Hbp.obj K) :
    runOf K (φ ≫ β) = twist (runOf K β) φ ≫ runOf K β := by
  conv_lhs => rw [← symOf_und K β]
  rw [← Category.assoc, twist_spec, Category.assoc, ← Hbp.map_comp, runOf_symOf_comp, twistRun_eq]

theorem desym_comp {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (β : ⋁b ⟶ Hbp.obj K) :
    desym K (φ ≫ β) = twist (runOf K β) φ ≫ desym K β :=
  prod_hom_ext (by rw [Category.assoc]; exact und_comp K φ β)
    (by rw [Category.assoc]; exact runOf_comp K φ β)

theorem desym_inj {d : List ℕ+} {u v : ⋁d ⟶ Hbp.obj K} (h : desym K u = desym K v) : u = v := by
  rw [← resym_desym K u, ← resym_desym K v, h]

/-- Chains with the same dimensions and the same classifying map are isomorphic by the identity. -/
def chainIdIso {X : BPSet} {d : List ℕ+} {u v : ⋁d ⟶ X} (h : u = v) :
    (⟨d, u⟩ : Ch X) ≅ ⟨d, v⟩ where
  hom := ⟨𝟙 (⋁d), by rw [Category.id_comp, h]⟩
  inv := ⟨𝟙 (⋁d), by rw [Category.id_comp, h]⟩
  hom_inv_id := ChainCat.hom_ext' (Category.comp_id _)
  inv_hom_id := ChainCat.hom_ext' (Category.comp_id _)

/-- **A decorated chain is a chain with a run**; a morphism twists by the target's run. -/
def symToProd : Ch (Hbp.obj K) ⥤ Ch (K.prod runBp) where
  obj a := ⟨a.dims, desym K a.map⟩
  map {a b} φ := ⟨twist (runOf K b.map) φ.φ, by rw [← desym_comp, φ.w]⟩
  map_id a := ChainCat.hom_ext' (twist_id _)
  map_comp {a b c} f g := ChainCat.hom_ext' (by
    change twist (runOf K c.map) (f.φ ≫ g.φ)
      = twist (runOf K b.map) f.φ ≫ twist (runOf K c.map) g.φ
    rw [twist_comp, twistRun_eq, ← runOf_comp, g.w])

/-- …and back, twisting by the inverse run. -/
def prodToSym : Ch (K.prod runBp) ⥤ Ch (Hbp.obj K) where
  obj x := ⟨x.dims, resym K x.map⟩
  map {x y} ψ := ⟨twist (starRun (runOf K (resym K y.map))) ψ.φ, by
    refine desym_inj K ?_
    rw [desym_comp, twist_twist_starRun, desym_resym, desym_resym]
    exact ψ.w⟩
  map_id x := ChainCat.hom_ext' (twist_id _)
  map_comp {x y z} f g := ChainCat.hom_ext' (by
    have hz : runOf K (resym K z.map) = z.map ≫ prodSnd K runBp := by rw [runOf, desym_resym]
    have hy : runOf K (resym K y.map) = y.map ≫ prodSnd K runBp := by rw [runOf, desym_resym]
    change twist (starRun (runOf K (resym K z.map))) (f.φ ≫ g.φ)
      = twist (starRun (runOf K (resym K y.map))) f.φ
        ≫ twist (starRun (runOf K (resym K z.map))) g.φ
    rw [twist_comp, twistRun_starRun, hz, hy, ← Category.assoc, g.w])

/-- **The symmetric round trip is the run product**: `Ch (Hbp K) ≌ Ch (K ⨯ runBp)`, for every
`K`. -/
def chSymEquiv : Ch (Hbp.obj K) ≌ Ch (K.prod runBp) where
  functor := symToProd K
  inverse := prodToSym K
  unitIso := NatIso.ofComponents (fun a => (chainIdIso (resym_desym K a.map)).symm)
    (fun {a b} φ => ChainCat.hom_ext' (by
      change ChainCat.Hom.φ φ ≫ 𝟙 (⋁b.dims)
        = 𝟙 (⋁a.dims) ≫ twist (starRun (runOf K (resym K (desym K b.map))))
            (twist (runOf K b.map) (ChainCat.Hom.φ φ))
      rw [Category.comp_id, Category.id_comp, resym_desym, twist_starRun_twist]))
  counitIso := NatIso.ofComponents (fun x => chainIdIso (desym_resym K x.map))
    (fun {x y} ψ => ChainCat.hom_ext' (by
      change twist (runOf K (resym K y.map))
            (twist (starRun (runOf K (resym K y.map))) (ChainCat.Hom.φ ψ)) ≫ 𝟙 (⋁y.dims)
        = 𝟙 (⋁x.dims) ≫ ChainCat.Hom.φ ψ
      rw [Category.comp_id, Category.id_comp, twist_twist_starRun]))
  functor_unitIso_comp a := ChainCat.hom_ext' (by
    change twist (runOf K (resym K (desym K a.map))) (𝟙 (⋁a.dims)) ≫ 𝟙 (⋁a.dims) = 𝟙 (⋁a.dims)
    rw [twist_id, Category.comp_id])

/-- **A decorated chain is a complexified chain, read backwards**: `Ch (Hbp K) ≌ (Ch⋆ K)ᵒᵖ`. -/
def chSymChStarEquiv : Ch (Hbp.obj K) ≌ (Ch⋆ K)ᵒᵖ :=
  (chSymEquiv K).trans (chStarProdEquiv K).leftOp.symm

end CubeChains
