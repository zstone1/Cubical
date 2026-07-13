import CubeChains.Foundations.Wedge
import CubeChains.Foundations.Altitude

/-!
# Chains/CubeNonSelfLinked — standard cubes are non-self-linked

The standard cube `□ᵐ = □m` is **non-self-linked** (`cube_nonSelfLinked`): for every
cell `c`, the topos-level cube map `((□m).cubeMap c).app` is injective. A *foundational* fact
about cubes, independent of the chain machinery, so it lives in `Chains/` over only `Foundations`.

Also provides the concrete↔topos bridge `toStar` (= `ev`) and the value law `app_val`
for the iterated-face map `act`.

**Layer:** Chains (foundational).  **Imports:** `Foundations.Wedge`, `Foundations.Altitude`.
-/

open CategoryTheory Opposite

namespace CubeChain

open BPSet PrecubicalSet StdCube

/-! ## Part 0. The `act` value law

Pure facts about the concrete iterated-face map `act`: how it acts on `noneSet`
(the star/free positions) and its value at a target coordinate. -/

/-- The star positions of `app w v` are the `w`-images of those of `v` (given the `noneSet`
law): `nones (app w v) = nones v ≫ nones w`. -/
theorem nones_app_of_noneSet {N K1 J : ℕ} (w : Cell N K1) (v : Cell K1 J)
    (hns : noneSet (act (K := stdPre N) w v).val
      = (noneSet v.val).map (nones w).toEmbedding) (p : Fin J) :
    nones (act (K := stdPre N) w v) p
      = nones w (nones v p) := by
  have key : nones (act (K := stdPre N) w v)
      = (nones v).trans (nones w) := by
    refine (Finset.orderEmbOfFin_unique'
      (act (K := stdPre N) w v).prop (fun y => ?_)).symm
    rw [hns]
    have hy : ((nones v).trans (nones w)) y
        = (nones w).toEmbedding (nones v y) := rfl
    rw [hy]
    exact Finset.mem_map_of_mem _ (Finset.orderEmbOfFin_mem _ v.prop y)
  rw [key]; rfl

/-- The star set of `app w v` is the `w`-image of the star set of `v`. -/
theorem noneSet_app {N K1 : ℕ} (w : Cell N K1) :
    ∀ {J : ℕ} (v : Cell K1 J),
      noneSet (act (K := stdPre N) w v).val
        = (noneSet v.val).map (nones w).toEmbedding := by
  intro J v
  induction hd : K1 - J using Nat.strong_induction_on generalizing J v with
  | _ d ih =>
    rcases Nat.lt_or_ge J K1 with hlt | hge
    · rw [app_unfold (K := stdPre N) w v hlt]
      change noneSet (faceCell (minFixedVal v hlt) (minFixedIdx v hlt)
          (act (K := stdPre N) w (freeMin v hlt))).val
        = (noneSet v.val).map (nones w).toEmbedding
      rw [face_val, noneSet_update]
      have ihv' := ih (K1 - (J + 1)) (by omega) (freeMin v hlt) rfl
      rw [ihv', nones_app_of_noneSet w (freeMin v hlt) ihv' (minFixedIdx v hlt)]
      have hv : noneSet v.val
          = (noneSet (freeMin v hlt).val).erase
              (nones (freeMin v hlt) (minFixedIdx v hlt)) := by
        rw [noneSet_freeMin, nones_minFixedIdx,
          Finset.erase_insert (minFixed_notMem v hlt)]
      rw [hv, Finset.map_erase, RelEmbedding.coe_toEmbedding]
    · have hJK : J = K1 := le_antisymm (cells_card_le v) hge
      subst hJK
      rw [eq_topCell v, app_topCell]
      have hu : noneSet (topCell J).val = Finset.univ := by
        ext j; simp [mem_noneSet, topCell]
      rw [hu]
      exact (Finset.map_orderEmbOfFin_univ (noneSet w.val) w.prop).symm

/-- The `p`-th star position of `app w v` is `w`'s image of the `p`-th star position of
`v` (`nones (app w v) p = nones w (nones v p)`). -/
theorem nones_app {N K1 J : ℕ} (w : Cell N K1) (v : Cell K1 J) (p : Fin J) :
    nones (act (K := stdPre N) w v) p
      = nones w (nones v p) :=
  nones_app_of_noneSet w v (noneSet_app w v) p

/-- **Value of the iterated-face map `app w v`.**  At a target coordinate `c`: a fixed
coordinate of `w` keeps `w`'s value; the `i`-th free coordinate of `w` takes `v`'s value
at source coordinate `i`. -/
theorem app_val {N K1 : ℕ} (w : Cell N K1) {J : ℕ} (v : Cell K1 J)
    (c : Fin N) :
    (act (K := stdPre N) w v).val c
      = if h : c ∈ noneSet w.val then v.val (nonesIdx w c h) else w.val c := by
  induction hd : K1 - J using Nat.strong_induction_on generalizing J v with
  | _ d ih =>
    rcases Nat.lt_or_ge J K1 with hlt | hge
    · rw [app_unfold (K := stdPre N) w v hlt]
      change (faceCell (minFixedVal v hlt) (minFixedIdx v hlt)
          (act (K := stdPre N) w (freeMin v hlt))).val c = _
      rw [face_val]
      have ihv := ih (K1 - (J + 1)) (by omega) (freeMin v hlt) rfl
      have hnones : nones
            (act (K := stdPre N) w (freeMin v hlt))
            (minFixedIdx v hlt)
          = nones w (minFixed v hlt) := by
        rw [nones_app, nones_minFixedIdx]
      rw [hnones]
      by_cases hc : c ∈ noneSet w.val
      · rw [dif_pos hc]
        by_cases hce : c = nones w (minFixed v hlt)
        · subst hce
          rw [Function.update_self]
          have hni : nonesIdx w (nones w (minFixed v hlt)) hc
              = minFixed v hlt :=
            (nones w).injective (nones_nonesIdx w _ hc)
          rw [hni, minFixed_val_eq]
        · have hne : nonesIdx w c hc ≠ minFixed v hlt := by
            intro heq
            have hnn := nones_nonesIdx w c hc
            rw [heq] at hnn
            exact hce hnn.symm
          rw [Function.update_of_ne hce, ihv, dif_pos hc, freeMin_val,
            Function.update_of_ne hne]
      · rw [dif_neg hc]
        have hcne : c ≠ nones w (minFixed v hlt) := fun heq =>
          hc (by rw [heq]; exact Finset.orderEmbOfFin_mem _ w.prop _)
        rw [Function.update_of_ne hcne, ihv, dif_neg hc]
    · have hJK : J = K1 := le_antisymm (cells_card_le v) hge
      subst hJK
      rw [eq_topCell v, app_topCell]
      by_cases hc : c ∈ noneSet w.val
      · rw [dif_pos hc, mem_noneSet.mp hc]
        rfl
      · rw [dif_neg hc]

/-! ## Part 1. The concrete↔topos bridge `toStar` -/

/-- Read a cube cell (= box morphism) as a concrete `Cell` (= `ev`). -/
noncomputable def toStar {m k : ℕ} (f : (□m).cells k) : Cell m k :=
  ev f

theorem toStar_eq {m k : ℕ} (f : (□m).cells k) : toStar f = ev f := rfl

/-- A `□`-cell is determined by its sign vector (`toStar` is injective). -/
theorem toStar_injective {m k : ℕ} :
    Function.Injective (toStar : (□m).cells k → Cell m k) := by
  intro x y h
  rw [toStar_eq, toStar_eq] at h
  have hx := (cubeRepr (stdPre m) k).left_inv x
  have hy := (cubeRepr (stdPre m) k).left_inv y
  simp only [cubeRepr] at hx hy
  rw [← hx, ← hy, h]

theorem toStar_canonicalMap {N k : ℕ} (x : Cell N k) :
    toStar (canonicalMap x : (□N).cells k) = x := by
  rw [toStar_eq]; exact ev_canonicalMap (K := stdPre N) x

/-! ## Part 2. Standard cubes are non-self-linked

`NonSelfLinked (□m)` asks that the topos-level cube map `((□m).cubeMap c).app` is
injective for every cell `c`. -/

/-- **Injectivity of the iterated-face map.**  For a fixed sign vector `w`, the map
`v ↦ act w v` is injective. -/
theorem stdApp_injective {m n : ℕ} (w : Cell m n) {k : ℕ} :
    Function.Injective
      (act (K := stdPre m) w : Cell n k → Cell m k) := by
  intro v1 v2 h
  apply Subtype.ext
  funext j
  have hc : nones w j ∈ noneSet w.val :=
    Finset.orderEmbOfFin_mem _ w.prop j
  have hidx : nonesIdx w (nones w j) hc = j :=
    (nones w).injective (nones_nonesIdx w _ hc)
  have e1 := app_val w v1 (nones w j)
  have e2 := app_val w v2 (nones w j)
  rw [dif_pos hc, hidx] at e1 e2
  have hval : (act (K := stdPre m) w v1).val (nones w j)
      = (act (K := stdPre m) w v2).val (nones w j) := by rw [h]
  rw [e1, e2] at hval
  exact hval

/-- **The `toStar`-bridge for the cube map:**
`toStar (((□m).cubeMap c).app g) = act (toStar c) (toStar g)` — `toStar`
intertwines the topos cube map with `act`. -/
theorem toStar_cubeMap_app {m n k : ℕ} (c : (□m).cells n)
    (g : (□n).cells k) :
    toStar (((□m).toPsh.cubeMap c)⟪k⟫ g)
      = act (K := stdPre m) (toStar c) (toStar g) := by
  simp only [toStar_eq]
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply]
  change ev ((g : ▫k ⟶ ▫n) ≫ c) = _
  rw [ev_comp]
  exact app_unique (K := stdPre m) c rfl (ev g)

/-- **Standard cubes are non-self-linked.**  For every cube cell `c`, the cube map
`((□m).cubeMap c).app` is injective. -/
theorem cube_nonSelfLinked (m : ℕ) : (□m).NonSelfLinked := by
  intro n c k g1 g2 h
  apply toStar_injective
  apply stdApp_injective (toStar c)
  rw [← toStar_cubeMap_app c g1, ← toStar_cubeMap_app c g2, h]

end CubeChain
