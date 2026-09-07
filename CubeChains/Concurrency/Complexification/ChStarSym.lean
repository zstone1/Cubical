import CubeChains.Machinery.Cube.SymPresheaf
import CubeChains.Concurrency.Executions.ChStarProduct
import CubeChains.Concurrency.Executions.RunPerm
import CubeChains.Concurrency.Complexification.SymRun

/-!
# Concurrency/Complexification/ChStarSym — the symmetric round trip is the run product

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

theorem sign_endVertexMap (ε : Bool) (n : ℕ) :
    Box.sign (PrecubicalSet.endVertexMap ε n) = constVertex n ε := ev_canonicalMap _

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

/-- **An `H`-cell's constant-sign faces forget the order** — a symmetry fixes them. -/
theorem H_obj_map_const {K : PrecubicalSet} {n : ℕ} {ε : Bool} (v : ▫0 ⟶ ▫n)
    (hv : Box.sign v = constVertex n ε) (p : Equiv.Perm (Fin n) × K.obj (op ▫n)) :
    (H.obj K).map v.op p = ((1 : Equiv.Perm (Fin 0)), K.map v.op p.2) := by
  have h := sortPerm_sortFace_const v hv p.1
  rw [Prod.mk.injEq] at h
  rw [H_obj_map, h.1, h.2]

theorem Hbp_vertexEnd (ε : Bool) {K : BPSet} {n : ℕ} (p : Equiv.Perm (Fin n) × K.cells n) :
    (Hbp.obj K).toPsh.vertexEnd ε p
      = ((1 : Equiv.Perm (Fin 0)), K.toPsh.vertexEnd ε p.2) :=
  H_obj_map_const _ (sign_endVertexMap ε n) p

/-! ## A decorated cube is a cube with a run

The order is read **backwards**: a run restricts along the *twisted* face, and inverting is what
turns that into `sortPerm`'s own cocycle. -/

variable (K : BPSet)

/-- **An `Hbp`-cell is a `K`-cell with a run of its axes** — the order read backwards. -/
def symCell (n : ℕ) : (Hbp.obj K).cells n ≃ (K.prod runBp).cells n :=
  (Equiv.prodComm _ _).trans
    (Equiv.prodCongr (Equiv.refl _) ((Equiv.inv _).trans (runPermEquiv n).symm))

theorem symCell_vertexEnd (ε : Bool) (n : ℕ) (p : (Hbp.obj K).cells n) :
    symCell K 0 ((Hbp.obj K).toPsh.vertexEnd ε p)
      = (K.prod runBp).toPsh.vertexEnd ε (symCell K n p) :=
  Prod.ext (congrArg Prod.snd (Hbp_vertexEnd ε p)) (run_cube0_eq _ _)

@[simp] theorem symCell_init : symCell K 0 (Hbp.obj K).init = (K.prod runBp).init :=
  Prod.ext rfl (run_cube0_eq _ _)

@[simp] theorem symCell_final : symCell K 0 (Hbp.obj K).final = (K.prod runBp).final :=
  Prod.ext rfl (run_cube0_eq _ _)

/-- A decorated cube, read as a cube with a run. -/
def symCube : (Σ n : ℕ+, (Hbp.obj K).cells (n : ℕ))
    ≃ Σ n : ℕ+, (K.prod runBp).cells (n : ℕ) :=
  Equiv.sigmaCongrRight fun n => symCell K (n : ℕ)

/-- …and cube-list-wise. -/
def symCubes : List (Σ n : ℕ+, (Hbp.obj K).cells (n : ℕ))
    ≃ List (Σ n : ℕ+, (K.prod runBp).cells (n : ℕ)) where
  toFun := List.map (symCube K)
  invFun := List.map (symCube K).symm
  left_inv l := by rw [List.map_map, Equiv.symm_comp_self, List.map_id]
  right_inv l := by rw [List.map_map, Equiv.self_comp_symm, List.map_id]

/-- **Chains transfer**: a cube list of `Hbp K` is a chain exactly when its run-reading is. -/
theorem isCubeChain_symCube (l : List (Σ n : ℕ+, (Hbp.obj K).cells (n : ℕ))) :
    IsCubeChain (Hbp.obj K).init l (Hbp.obj K).final
      ↔ IsCubeChain (K.prod runBp).init (symCubes K l) (K.prod runBp).final := by
  constructor
  · intro h
    simpa only [symCell_init, symCell_final] using
      isCubeChain_push (u := fun n => ⇑(symCell K n)) (symCell_vertexEnd K) l h
  · intro h
    refine isCubeChain_of_push (u := fun n => ⇑(symCell K n)) (symCell_vertexEnd K)
      (symCell K 0).injective l _ _ ?_
    simpa only [symCell_init, symCell_final] using h

/-- **A chain in `Hbp K` is a chain in `K` with a run.** -/
def chainSymEquiv : CubeChain (Hbp.obj K) ≃ CubeChain (K.prod runBp) :=
  (symCubes K).subtypeEquiv (isCubeChain_symCube K)

@[simp] theorem chainSymEquiv_dims (C : CubeChain (Hbp.obj K)) :
    (chainSymEquiv K C).dims = C.dims := by
  change (C.cubes.map (symCube K)).map (·.1) = C.cubes.map (·.1)
  rw [List.map_map]; rfl

@[simp] theorem chainSymEquiv_symm_dims (D : CubeChain (K.prod runBp)) :
    ((chainSymEquiv K).symm D).dims = D.dims := by
  change (D.cubes.map (symCube K).symm).map (·.1) = D.cubes.map (·.1)
  rw [List.map_map]; rfl

/-! ## Cube lists and classifying maps

A bi-pointed map `⋁d ⟶ K` *is* a cube chain with dimension sequence `d`: `wedgeChain` reads the
cubes off, `ofCubes` glues them back, and `wedgeMap_ext` says the cubes determine the map. -/

/-- The chain a bi-pointed wedge map classifies, indexed by the dimension sequence. -/
def wedgeChain {K : BPSet} (d : List ℕ+) (α : ⋁d ⟶ K) : CubeChain K := chCubes K ⟨d, α⟩

@[simp] theorem wedgeChain_dims {K : BPSet} (d : List ℕ+) (α : ⋁d ⟶ K) :
    (wedgeChain d α).dims = d := chCubes_dims ⟨d, α⟩

/-- **A bi-pointed wedge map is its cube list.** -/
theorem wedgeMap_ext {K : BPSet} {d : List ℕ+} {α β : ⋁d ⟶ K}
    (h : wedgeChain d α = wedgeChain d β) : α = β := by
  injection (chCubes K).injective h

/-- …and every chain with the right dimensions is one. -/
def ofCubes {K : BPSet} {d : List ℕ+} (C : CubeChain K) (h : C.dims = d) : ⋁d ⟶ K :=
  ⋁≡ h.symm ≫ ((chCubes K).symm C).map

@[simp] theorem wedgeChain_ofCubes {K : BPSet} {d : List ℕ+} (C : CubeChain K) (h : C.dims = d) :
    wedgeChain d (ofCubes C h) = C := by
  subst h
  simpa only [ofCubes, eqToHom_refl, Category.id_comp] using (chCubes K).apply_symm_apply C

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

/-! ## Beads

A bi-pointed wedge map is its list of beads, and post-composition acts bead-wise: all the
computations below are one bead at a time. -/

/-- Bead `i` of a bi-pointed wedge map — `beadCell` of the underlying presheaf map. -/
def bead {K : BPSet} (d : List ℕ+) (α : ⋁d ⟶ K) (i : Fin d.length) : K.cells (d.get i : ℕ) :=
  beadCell α.hom i

theorem wedgeChain_eq_ofFn {K : BPSet} (d : List ℕ+) (α : ⋁d ⟶ K) :
    (wedgeChain d α).cubes = List.ofFn (fun i => ⟨d.get i, bead d α i⟩) :=
  Beads.toList_eq_ofFn (beadCell α.hom)

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
  bpset_hom_ext_of_beadCell (funext h)

@[simp] theorem bead_comp {K L : BPSet} {d : List ℕ+} (α : ⋁d ⟶ K) (g : K ⟶ L)
    (i : Fin d.length) :
    bead d (α ≫ g) i = g.hom⟪(d.get i : ℕ)⟫ (bead d α i) :=
  beadCell_comp α.hom g.hom i

theorem bead_desym {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) (i : Fin d.length) :
    bead d (desym K α) i = symCell K _ (bead d α i) :=
  bead_eq_of_cubes (by
    rw [wedgeChain_desym]
    change ((wedgeChain d α).cubes.map (symCube K)) = _
    rw [wedgeChain_eq_ofFn, List.map_ofFn]
    rfl) i

theorem bead_resym {d : List ℕ+} (β : ⋁d ⟶ K.prod runBp) (i : Fin d.length) :
    bead d (resym K β) i = (symCell K _).symm (bead d β i) :=
  bead_eq_of_cubes (by
    rw [wedgeChain_resym]
    change ((wedgeChain d β).cubes.map (symCube K).symm) = _
    rw [wedgeChain_eq_ofFn, List.map_ofFn]
    rfl) i

/-! ## The bead-wise symmetry, and the factorization it generates -/

/-- **The bead-wise symmetry of `⋁d`** — the tautological chain with its beads re-ordered by `ρ`.
It exists because a symmetry fixes the extremal vertices, so the orders glue at the junctions. -/
def symOf {d : List ℕ+} (ρ : ⋁d ⟶ runBp) : ⋁d ⟶ Hbp.obj (⋁d) :=
  resym (⋁d) (prodLift (𝟙 (⋁d)) ρ)

/-- The underlying chain of a decorated chain. -/
def chainOf {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) : ⋁d ⟶ K := desym K α ≫ prodFst K runBp

/-- The run of a decorated chain. -/
def runOf {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) : ⋁d ⟶ runBp := desym K α ≫ prodSnd K runBp

@[simp] theorem bead_chainOf {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) (i : Fin d.length) :
    bead d (chainOf K α) i = (bead d α i).2 := by
  rw [chainOf, bead_comp, bead_desym]; rfl

@[simp] theorem bead_runOf {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) (i : Fin d.length) :
    bead d (runOf K α) i = (runPermEquiv (d.get i : ℕ)).symm (bead d α i).1⁻¹ := by
  rw [runOf, bead_comp, bead_desym]; rfl

@[simp] theorem bead_id (d : List ℕ+) (i : Fin d.length) : bead d (𝟙 (⋁d)) i = tautBead d i :=
  beadCell_id d i

theorem hom_tautBead {d : List ℕ+} (g : ⋁d ⟶ K) (i : Fin d.length) :
    g.hom⟪(d.get i : ℕ)⟫ (tautBead d i) = bead d g i :=
  (beadCell_eq_tautBead g.hom i).symm

@[simp] theorem bead_symOf_fst {d : List ℕ+} (ρ : ⋁d ⟶ runBp) (i : Fin d.length) :
    (bead d (symOf ρ) i).1 = (runPermEquiv (d.get i : ℕ) (bead (K := runBp) d ρ i))⁻¹ := by
  rw [symOf, bead_resym]; rfl

@[simp] theorem bead_symOf_snd {d : List ℕ+} (ρ : ⋁d ⟶ runBp) (i : Fin d.length) :
    (bead d (symOf ρ) i).2 = tautBead d i := by
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
    chainOf K (symOf ρ ≫ Hbp.map c) = c :=
  wedgeMap_ext_bead fun i => by
    rw [bead_chainOf, bead_Hbp_map_snd, bead_symOf_snd]
    exact hom_tautBead K c i

/-- …and its run is `ρ`. -/
@[simp] theorem runOf_symOf_comp {d : List ℕ+} (ρ : ⋁d ⟶ runBp) (c : ⋁d ⟶ K) :
    runOf K (symOf ρ ≫ Hbp.map c) = ρ :=
  wedgeMap_ext_bead fun i => by
    rw [bead_runOf, bead_Hbp_map_fst, bead_symOf_fst, inv_inv, Equiv.symm_apply_apply]

/-- **Every decorated chain is a bead-wise symmetry followed by a chain.** -/
theorem symOf_chainOf {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj K) :
    symOf (runOf K α) ≫ Hbp.map (chainOf K α) = α :=
  wedgeMap_ext_bead fun i => Prod.ext
    (by rw [bead_Hbp_map_fst, bead_symOf_fst, bead_runOf, Equiv.apply_symm_apply, inv_inv])
    (by rw [bead_Hbp_map_snd, bead_symOf_snd, hom_tautBead, bead_chainOf])

/-! ## The twist

Composing a wedge map with a bead-wise symmetry and factoring again *twists* the map.  Its
functoriality is associativity of `≫` plus uniqueness of the factorization — nothing else. -/

/-- **The twist of a wedge map by a run**: the chain underlying `φ ≫ symOf ρ`. -/
def twist {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) : ⋁a ⟶ ⋁b :=
  chainOf (⋁b) (φ ≫ symOf ρ)

/-- …and the run the twist leaves on the source. -/
def twistRun {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) : ⋁a ⟶ runBp :=
  runOf (⋁b) (φ ≫ symOf ρ)

theorem twist_spec {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) :
    φ ≫ symOf ρ = symOf (twistRun ρ φ) ≫ Hbp.map (twist ρ φ) :=
  (symOf_chainOf (⋁b) (φ ≫ symOf ρ)).symm

@[simp] theorem twist_id {b : List ℕ+} (ρ : ⋁b ⟶ runBp) : twist ρ (𝟙 (⋁b)) = 𝟙 (⋁b) := by
  rw [twist, Category.id_comp, ← Category.comp_id (symOf ρ), ← Hbp.map_id, und_symOf_comp]

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

/-! ## The twisted map carries the run

`twistRun ρ φ` is the restriction of `ρ` along the *twisted* map, not along `φ`.  This is the one
statement that looks at blocks, and the only use of `sortPerm_sortFace_inv`. -/

/-- A wedge map's bead reads off *any* factorization of it through a target bead. -/
theorem bead_of_factor {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (i : Fin a.length) (j : Fin b.length)
    (f : ▫((a.get i : ℕ)) ⟶ ▫((b.get j : ℕ)))
    (hfac : ιᵂ a i ≫ φ.hom = yoneda.map f ≫ ιᵂ b j) :
    bead a φ i = (⋁b).toPsh.map f.op (tautBead b j) :=
  (congrArg yonedaEquiv hfac).trans (yonedaEquiv_naturality (ιᵂ b j) f).symm

/-- **Bead-wise, post-composition happens in the target bead** — at any such factorization. -/
theorem bead_comp_of_factor {X : BPSet} {a b : List ℕ+} {φ : ⋁a ⟶ ⋁b} {i : Fin a.length}
    {j : Fin b.length} {f : ▫((a.get i : ℕ)) ⟶ ▫((b.get j : ℕ))}
    (h : bead a φ i = (⋁b).toPsh.map f.op (tautBead b j)) (α : ⋁b ⟶ X) :
    bead a (φ ≫ α) i = X.toPsh.map f.op (bead b α j) := by
  rw [bead_comp, h, ← hom_tautBead X α]
  exact NatTrans.naturality_apply α.hom f.op (tautBead b j)

/-- A wedge map's bead `i` is a face of the target bead it lands in. -/
theorem bead_factor {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (i : Fin a.length) :
    bead a φ i = (⋁b).toPsh.map (blockFace φ.hom i).op (tautBead b (blockIdx φ.hom i)) :=
  bead_of_factor φ i _ _ (blockFace_spec φ.hom i)

/-- Bead-wise, post-composition happens in the target bead. -/
theorem bead_comp_block {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (α : ⋁b ⟶ K) (i : Fin a.length) :
    bead a (φ ≫ α) i
      = K.toPsh.map (blockFace φ.hom i).op (bead b α (blockIdx φ.hom i)) :=
  bead_comp_of_factor (bead_factor φ i) α

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

/-- The order `ρ` gives the target bead that source bead `i` lands in. -/
abbrev blockPerm {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) (i : Fin a.length) :
    Equiv.Perm (Fin (b.get (blockIdx φ.hom i) : ℕ)) :=
  runPermEquiv (b.get (blockIdx φ.hom i) : ℕ) (bead b ρ (blockIdx φ.hom i))

/-- **The bead-wise twist formula**, from any factorization of the source bead through a target
bead — so it applies to a twist as readily as to the map it came from. -/
theorem bead_twist_of {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) (i : Fin a.length)
    (j : Fin b.length) (f : ▫(a.get i : ℕ) ⟶ ▫(b.get j : ℕ))
    (h : bead a φ i = (⋁b).toPsh.map f.op (tautBead b j)) :
    bead a (twist ρ φ) i
      = (⋁b).toPsh.map (SHom.sortFace (J.map f)
          (runPermEquiv (b.get j : ℕ) (bead b ρ j))⁻¹).op (tautBead b j) := by
  rw [twist, bead_chainOf, bead_comp_of_factor h (symOf ρ), Hbp_obj_map_snd, bead_symOf_fst,
    bead_symOf_snd]

theorem bead_twist {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) (i : Fin a.length) :
    bead a (twist ρ φ) i
      = (⋁b).toPsh.map (SHom.sortFace (J.map (blockFace φ.hom i))
          (blockPerm ρ φ i)⁻¹).op (tautBead b (blockIdx φ.hom i)) :=
  bead_twist_of ρ φ i _ _ (bead_factor φ i)

/-- **Plain restriction sorts the bead's order** along the factoring face. -/
theorem runPermEquiv_bead_comp {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b)
    (i : Fin a.length) (j : Fin b.length) (f : ▫((a.get i : ℕ)) ⟶ ▫((b.get j : ℕ)))
    (h : bead a φ i = (⋁b).toPsh.map f.op (tautBead b j)) :
    runPermEquiv (a.get i : ℕ) (bead a (φ ≫ ρ) i)
      = SHom.sortPerm (J.map f) (runPermEquiv (b.get j : ℕ) (bead b ρ j)) := by
  rw [bead_comp_of_factor h ρ, runPermEquiv_map_bp]

/-- **The twisted restriction sorts the bead's *inverse* order, then inverts.**  Sorting does not
commute with inverting, and that is the whole obstruction. -/
theorem runPermEquiv_bead_twistRun {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b)
    (i : Fin a.length) (j : Fin b.length) (f : ▫((a.get i : ℕ)) ⟶ ▫((b.get j : ℕ)))
    (h : bead a φ i = (⋁b).toPsh.map f.op (tautBead b j)) :
    runPermEquiv (a.get i : ℕ) (bead a (twistRun ρ φ) i)
      = (SHom.sortPerm (J.map f) (runPermEquiv (b.get j : ℕ) (bead b ρ j))⁻¹)⁻¹ := by
  rw [twistRun, bead_runOf, bead_comp_of_factor h (symOf ρ), Hbp_obj_map_fst, bead_symOf_fst,
    Equiv.apply_symm_apply]

theorem bead_twistRun {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) (i : Fin a.length) :
    bead a (twistRun ρ φ) i
      = (runPermEquiv (a.get i : ℕ)).symm
          (SHom.sortPerm (J.map (blockFace φ.hom i)) (blockPerm ρ φ i)⁻¹)⁻¹ :=
  (Equiv.eq_symm_apply _).mpr (runPermEquiv_bead_twistRun ρ φ i _ _ (bead_factor φ i))

/-- **The twist carries the run**: the source run is `ρ` restricted along the twisted map. -/
theorem twistRun_eq {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) :
    twistRun ρ φ = twist ρ φ ≫ ρ :=
  wedgeMap_ext_bead fun i => by
    rw [bead_comp, bead_twist, bead_twistRun,
      NatTrans.naturality_apply ρ.hom _ (tautBead b (blockIdx φ.hom i)), hom_tautBead]
    refine (runPermEquiv (a.get i : ℕ)).injective ?_
    rw [Equiv.apply_symm_apply, runPermEquiv_map_bp, SHom.sortPerm_sortFace_perm]

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

/-- **Twisting by the inverse run un-twists.** -/
theorem twist_starRun_twist {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (φ : ⋁a ⟶ ⋁b) :
    twist (starRun ρ) (twist ρ φ) = φ :=
  wedgeMap_ext_bead fun i => by
    rw [bead_twist_of (starRun ρ) (twist ρ φ) i (blockIdx φ.hom i) _ (bead_twist ρ φ i),
      bead_starRun, Equiv.apply_symm_apply, inv_inv, SHom.sortFace_sortFace_inv]
    exact (bead_factor φ i).symm

theorem twist_twist_starRun {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (ψ : ⋁a ⟶ ⋁b) :
    twist ρ (twist (starRun ρ) ψ) = ψ := by
  have h := twist_starRun_twist (starRun ρ) ψ
  rwa [starRun_starRun] at h

/-- Restriction of the inverse run is the inverse of the twisted restriction. -/
theorem twistRun_starRun {a b : List ℕ+} (ρ : ⋁b ⟶ runBp) (ψ : ⋁a ⟶ ⋁b) :
    twistRun (starRun ρ) ψ = starRun (ψ ≫ ρ) :=
  wedgeMap_ext_bead fun i => by
    rw [bead_twistRun, bead_starRun, bead_comp_block, runPermEquiv_map_bp]
    simp only [blockPerm, bead_starRun, Equiv.apply_symm_apply, inv_inv]

/-! ## `Ch (Hbp K) ≌ Ch (K.prod runBp)` -/

theorem und_comp {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (β : ⋁b ⟶ Hbp.obj K) :
    chainOf K (φ ≫ β) = twist (runOf K β) φ ≫ chainOf K β := by
  conv_lhs => rw [← symOf_chainOf K β]
  rw [← Category.assoc, twist_spec, Category.assoc, ← Hbp.map_comp, und_symOf_comp]

theorem runOf_comp {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (β : ⋁b ⟶ Hbp.obj K) :
    runOf K (φ ≫ β) = twist (runOf K β) φ ≫ runOf K β := by
  conv_lhs => rw [← symOf_chainOf K β]
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
