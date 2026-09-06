import CubeChains.Machinery.Cube.BoxMonoidal
import CubeChains.Precubical.Wedge.Wedge
import CubeChains.Precubical.Basic.Altitude

/-!
# Precubical/Chains/CubeNonSelfLinked — standard cubes are non-self-linked

The standard cube `□ᵐ = □m` is **non-self-linked** (`cube_nonSelfLinked`): for every
cell `c`, the topos-level cube map `((□m).cubeMap c).app` is injective.

Also provides the concrete↔topos bridge `toStar` (= `ev`) and the value law `app_val`
for the iterated-face map `act`.
-/

open CategoryTheory Opposite

namespace CubeChain

open BPSet PrecubicalSet StdCube

/-! ## Part 0. The `act` value law

`Machinery/Cube/BoxMonoidal` proves these for `subst`; `act_eq_subst` identifies the two, so here
they are only respelled for the `act` (iterated-face) side, where the callers live. -/

/-- The star set of `act w v` is the `w`-image of the star set of `v`. -/
theorem noneSet_app {N K1 J : ℕ} (w : Cell N K1) (v : Cell K1 J) :
    noneSet (act (K := stdPre N) w v).val
      = (noneSet v.val).map (nones w).toEmbedding := by
  rw [act_eq_subst, subst_val]; exact noneSet_substFun w v

/-- The `p`-th star position of `act w v` is `w`'s image of the `p`-th star position of `v`. -/
theorem nones_app {N K1 J : ℕ} (w : Cell N K1) (v : Cell K1 J) (p : Fin J) :
    nones (act (K := stdPre N) w v) p = nones w (nones v p) := by
  rw [act_eq_subst]; exact nones_subst w v p

/-- **Value of the iterated-face map `act w v`.**  At a target coordinate `c`: a fixed
coordinate of `w` keeps `w`'s value; the `i`-th free coordinate of `w` takes `v`'s value
at source coordinate `i`. -/
theorem app_val {N K1 : ℕ} (w : Cell N K1) {J : ℕ} (v : Cell K1 J) (c : Fin N) :
    (act (K := stdPre N) w v).val c
      = if h : c ∈ noneSet w.val then v.val (nonesIdx w c h) else w.val c := by
  rw [act_eq_subst, subst_val, substFun]
  by_cases h : c ∈ noneSet w.val
  · rw [dif_pos h, dif_pos (mem_noneSet.mp h)]
  · rw [dif_neg h, dif_neg (fun hc => h (mem_noneSet.mpr hc))]

/-! ## Part 1. The concrete↔topos bridge `toStar` -/

/-- Read a cube cell (= box morphism) as a concrete `Cell` (= `ev`). -/
def toStar {m k : ℕ} (f : (□m).cells k) : Cell m k :=
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
