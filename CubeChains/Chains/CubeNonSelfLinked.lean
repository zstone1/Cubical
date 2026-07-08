import CubeChains.Foundations.Wedge
import CubeChains.Foundations.Altitude

/-!
# Chains/CubeNonSelfLinked — standard cubes are non-self-linked

The standard cube `□ᵐ = BPSet.cube m` is **non-self-linked** (`cube_nonSelfLinked`): for every
cell `c`, the topos-level cube map `((cube m).cubeMap c).app` is injective. A *foundational* fact
about cubes, independent of the chain machinery, so it lives in `Chains/` over only `Foundations`.

Also provides the concrete↔topos bridge `toStar` (= `StdCube.ev`) and the value law `app_val`
for the iterated-face map `StdCube.app`.

**Layer:** Chains (foundational).  **Imports:** `Foundations.Wedge`, `Foundations.Altitude`.
-/

open CategoryTheory Opposite

namespace CubeChain

open BPSet PrecubicalSet StdCube

/-! ## Part 0. The `StdCube.app` value law

Pure facts about the concrete iterated-face map `StdCube.app`: how it acts on `noneSet`
(the star/free positions) and its value at a target coordinate. -/

/-- The star positions of `app w v` are the `w`-images of those of `v` (given the `noneSet`
law): `nones (app w v) = nones v ≫ nones w`. -/
theorem nones_app_of_noneSet {N K1 J : ℕ} (w : StdCube.cells N K1) (v : StdCube.cells K1 J)
    (hns : StdCube.noneSet (StdCube.app (K := StdCube.stdPre N) w v).val
      = (StdCube.noneSet v.val).map (StdCube.nones w).toEmbedding) (p : Fin J) :
    StdCube.nones (StdCube.app (K := StdCube.stdPre N) w v) p
      = StdCube.nones w (StdCube.nones v p) := by
  have key : StdCube.nones (StdCube.app (K := StdCube.stdPre N) w v)
      = (StdCube.nones v).trans (StdCube.nones w) := by
    refine (Finset.orderEmbOfFin_unique'
      (StdCube.app (K := StdCube.stdPre N) w v).prop (fun y => ?_)).symm
    rw [hns]
    have hy : ((StdCube.nones v).trans (StdCube.nones w)) y
        = (StdCube.nones w).toEmbedding (StdCube.nones v y) := rfl
    rw [hy]
    exact Finset.mem_map_of_mem _ (Finset.orderEmbOfFin_mem _ v.prop y)
  rw [key]; rfl

/-- The star set of `app w v` is the `w`-image of the star set of `v`. -/
theorem noneSet_app {N K1 : ℕ} (w : StdCube.cells N K1) :
    ∀ {J : ℕ} (v : StdCube.cells K1 J),
      StdCube.noneSet (StdCube.app (K := StdCube.stdPre N) w v).val
        = (StdCube.noneSet v.val).map (StdCube.nones w).toEmbedding := by
  intro J v
  induction hd : K1 - J using Nat.strong_induction_on generalizing J v with
  | _ d ih =>
    rcases Nat.lt_or_ge J K1 with hlt | hge
    · rw [StdCube.app_unfold (K := StdCube.stdPre N) w v hlt]
      change StdCube.noneSet (StdCube.face (StdCube.minFixedVal v hlt) (StdCube.minFixedIdx v hlt)
          (StdCube.app (K := StdCube.stdPre N) w (StdCube.freeMin v hlt))).val
        = (StdCube.noneSet v.val).map (StdCube.nones w).toEmbedding
      rw [StdCube.face_val, StdCube.noneSet_update]
      have ihv' := ih (K1 - (J + 1)) (by omega) (StdCube.freeMin v hlt) rfl
      rw [ihv', nones_app_of_noneSet w (StdCube.freeMin v hlt) ihv' (StdCube.minFixedIdx v hlt)]
      have hv : StdCube.noneSet v.val
          = (StdCube.noneSet (StdCube.freeMin v hlt).val).erase
              (StdCube.nones (StdCube.freeMin v hlt) (StdCube.minFixedIdx v hlt)) := by
        rw [StdCube.noneSet_freeMin, StdCube.nones_minFixedIdx,
          Finset.erase_insert (StdCube.minFixed_notMem v hlt)]
      rw [hv, Finset.map_erase, RelEmbedding.coe_toEmbedding]
    · have hJK : J = K1 := le_antisymm (StdCube.cells_card_le v) hge
      subst hJK
      rw [StdCube.eq_topCell v, StdCube.app_topCell]
      have hu : StdCube.noneSet (StdCube.topCell J).val = Finset.univ := by
        ext j; simp [StdCube.mem_noneSet, StdCube.topCell]
      rw [hu]
      exact (Finset.map_orderEmbOfFin_univ (StdCube.noneSet w.val) w.prop).symm

/-- The `p`-th star position of `app w v` is `w`'s image of the `p`-th star position of
`v` (`nones (app w v) p = nones w (nones v p)`). -/
theorem nones_app {N K1 J : ℕ} (w : StdCube.cells N K1) (v : StdCube.cells K1 J) (p : Fin J) :
    StdCube.nones (StdCube.app (K := StdCube.stdPre N) w v) p
      = StdCube.nones w (StdCube.nones v p) :=
  nones_app_of_noneSet w v (noneSet_app w v) p

/-- **Value of the iterated-face map `app w v`.**  At a target coordinate `c`: a fixed
coordinate of `w` keeps `w`'s value; the `i`-th free coordinate of `w` takes `v`'s value
at source coordinate `i`. -/
theorem app_val {N K1 : ℕ} (w : StdCube.cells N K1) {J : ℕ} (v : StdCube.cells K1 J)
    (c : Fin N) :
    (StdCube.app (K := StdCube.stdPre N) w v).val c
      = if h : c ∈ StdCube.noneSet w.val then v.val (StdCube.nonesIdx w c h) else w.val c := by
  induction hd : K1 - J using Nat.strong_induction_on generalizing J v with
  | _ d ih =>
    rcases Nat.lt_or_ge J K1 with hlt | hge
    · rw [StdCube.app_unfold (K := StdCube.stdPre N) w v hlt]
      change (StdCube.face (StdCube.minFixedVal v hlt) (StdCube.minFixedIdx v hlt)
          (StdCube.app (K := StdCube.stdPre N) w (StdCube.freeMin v hlt))).val c = _
      rw [StdCube.face_val]
      have ihv := ih (K1 - (J + 1)) (by omega) (StdCube.freeMin v hlt) rfl
      have hnones : StdCube.nones
            (StdCube.app (K := StdCube.stdPre N) w (StdCube.freeMin v hlt))
            (StdCube.minFixedIdx v hlt)
          = StdCube.nones w (StdCube.minFixed v hlt) := by
        rw [nones_app, StdCube.nones_minFixedIdx]
      rw [hnones]
      by_cases hc : c ∈ StdCube.noneSet w.val
      · rw [dif_pos hc]
        by_cases hce : c = StdCube.nones w (StdCube.minFixed v hlt)
        · subst hce
          rw [Function.update_self]
          have hni : StdCube.nonesIdx w (StdCube.nones w (StdCube.minFixed v hlt)) hc
              = StdCube.minFixed v hlt :=
            (StdCube.nones w).injective (StdCube.nones_nonesIdx w _ hc)
          rw [hni, StdCube.minFixed_val_eq]
        · have hne : StdCube.nonesIdx w c hc ≠ StdCube.minFixed v hlt := by
            intro heq
            have hnn := StdCube.nones_nonesIdx w c hc
            rw [heq] at hnn
            exact hce hnn.symm
          rw [Function.update_of_ne hce, ihv, dif_pos hc, StdCube.freeMin_val,
            Function.update_of_ne hne]
      · rw [dif_neg hc]
        have hcne : c ≠ StdCube.nones w (StdCube.minFixed v hlt) := fun heq =>
          hc (by rw [heq]; exact Finset.orderEmbOfFin_mem _ w.prop _)
        rw [Function.update_of_ne hcne, ihv, dif_neg hc]
    · have hJK : J = K1 := le_antisymm (StdCube.cells_card_le v) hge
      subst hJK
      rw [StdCube.eq_topCell v, StdCube.app_topCell]
      by_cases hc : c ∈ StdCube.noneSet w.val
      · rw [dif_pos hc, StdCube.mem_noneSet.mp hc]
        rfl
      · rw [dif_neg hc]

/-! ## Part 1. The concrete↔topos bridge `toStar` -/

/-- Read a cube cell (= box morphism) as a concrete `StdCube.cells` (= `StdCube.ev`). -/
noncomputable def toStar {m k : ℕ} (f : (cube m).toPsh.cells k) : StdCube.cells m k :=
  StdCube.ev f

theorem toStar_eq {m k : ℕ} (f : (cube m).toPsh.cells k) : toStar f = StdCube.ev f := rfl

/-- A `□`-cell is determined by its sign vector (`toStar` is injective). -/
theorem toStar_injective {m k : ℕ} :
    Function.Injective (toStar : (cube m).toPsh.cells k → StdCube.cells m k) := by
  intro x y h
  rw [toStar_eq, toStar_eq] at h
  have hx := (StdCube.cubeRepr (StdCube.stdPre m) k).left_inv x
  have hy := (StdCube.cubeRepr (StdCube.stdPre m) k).left_inv y
  simp only [StdCube.cubeRepr] at hx hy
  rw [← hx, ← hy, h]

theorem toStar_canonicalMap {N k : ℕ} (x : StdCube.cells N k) :
    toStar (StdCube.canonicalMap x : (cube N).toPsh.cells k) = x := by
  rw [toStar_eq]; exact StdCube.ev_canonicalMap (K := StdCube.stdPre N) x

/-! ## Part 2. Standard cubes are non-self-linked

`NonSelfLinked (cube m)` asks that the topos-level cube map `((cube m).cubeMap c).app` is
injective for every cell `c`. -/

/-- **Injectivity of the iterated-face map.**  For a fixed sign vector `w`, the map
`v ↦ StdCube.app w v` is injective. -/
theorem stdApp_injective {m n : ℕ} (w : StdCube.cells m n) {k : ℕ} :
    Function.Injective
      (StdCube.app (K := StdCube.stdPre m) w : StdCube.cells n k → StdCube.cells m k) := by
  intro v1 v2 h
  apply Subtype.ext
  funext j
  have hc : StdCube.nones w j ∈ StdCube.noneSet w.val :=
    Finset.orderEmbOfFin_mem _ w.prop j
  have hidx : StdCube.nonesIdx w (StdCube.nones w j) hc = j :=
    (StdCube.nones w).injective (StdCube.nones_nonesIdx w _ hc)
  have e1 := app_val w v1 (StdCube.nones w j)
  have e2 := app_val w v2 (StdCube.nones w j)
  rw [dif_pos hc, hidx] at e1 e2
  have hval : (StdCube.app (K := StdCube.stdPre m) w v1).val (StdCube.nones w j)
      = (StdCube.app (K := StdCube.stdPre m) w v2).val (StdCube.nones w j) := by rw [h]
  rw [e1, e2] at hval
  exact hval

/-- **The `toStar`-bridge for the cube map:**
`toStar (((cube m).cubeMap c).app g) = StdCube.app (toStar c) (toStar g)` — `toStar`
intertwines the topos cube map with `StdCube.app`. -/
theorem toStar_cubeMap_app {m n k : ℕ} (c : (cube m).toPsh.cells n)
    (g : (cube n).toPsh.cells k) :
    toStar (((cube m).toPsh.cubeMap c).app (op (Box.ob k)) g)
      = StdCube.app (K := StdCube.stdPre m) (toStar c) (toStar g) := by
  simp only [toStar_eq]
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply]
  change StdCube.ev ((g : Box.ob k ⟶ Box.ob n) ≫ c) = _
  rw [StdCube.ev_comp]
  exact StdCube.app_unique (K := StdCube.stdPre m) c rfl (StdCube.ev g)

/-- **Standard cubes are non-self-linked.**  For every cube cell `c`, the cube map
`((cube m).cubeMap c).app` is injective. -/
theorem cube_nonSelfLinked (m : ℕ) : (BPSet.cube m).NonSelfLinked := by
  intro n c k g1 g2 h
  apply toStar_injective
  apply stdApp_injective (toStar c)
  rw [← toStar_cubeMap_app c g1, ← toStar_cubeMap_app c g2, h]

end CubeChain
