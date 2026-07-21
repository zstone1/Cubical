import CubeChains.Chains.BlockDecomp
import CubeChains.Chains.CubeNonSelfLinked
import CubeChains.Chains.Refine
import CubeChains.Foundations.BoxMonoidal

/-!
# Salvetti/CubeVtx — a cube face extends vertices; the primitive under the flip combinatorics

A cube face `g : ▫n ⟶ ▫m` extends an `n`-cube vertex to an `m`-cube vertex: the free
coordinates (`faceEmb g`) carry the given vertex, the rest take `g`'s fixed values.  It is
monotone **for free** (extend-by-constants) and functorial — a `cubeVtx : Box ⥤ Type` copresheaf
of vertices, with per-cell orientation `cubeVtxOfCell_bot_le_top`.  The functoriality is
`act`-associativity (`cubeVtxOfCell_act`), read off `ev_comp_app`.
-/

open CategoryTheory CubeChain StdCube

namespace CubeChains

variable {n m e : ℕ}

/-- **Vertex extension of a cell.**  A cell `c : Cell m n` (`n` free coordinates of `□m`)
extends an `n`-vertex to an `m`-vertex: free coordinates carry the vertex, fixed ones take
`c`'s value.  Monotone by construction. -/
def cubeVtxOfCell (c : Cell m n) : (Fin n → Bool) →o (Fin m → Bool) where
  toFun v q := if h : q ∈ noneSet c.val then v (nonesIdx c q h) else (c.val q).getD false
  monotone' v w hvw q := by
    by_cases h : q ∈ noneSet c.val
    · simp only [dif_pos h]; exact hvw _
    · simp only [dif_neg h]; exact le_refl _

theorem cubeVtxOfCell_apply (c : Cell m n) (v : Fin n → Bool) (q : Fin m) :
    cubeVtxOfCell c v q =
      if h : q ∈ noneSet c.val then v (nonesIdx c q h) else (c.val q).getD false := rfl

/-- **The vertex extension of a cube face** `g : ▫n ⟶ ▫m`, through its sign vector. -/
def cubeVtx (g : ▫n ⟶ ▫m) : (Fin n → Bool) →o (Fin m → Bool) :=
  cubeVtxOfCell (toStar (g : (□m).cells n))

theorem cubeVtx_eq (g : ▫n ⟶ ▫m) :
    cubeVtx g = cubeVtxOfCell (toStar (g : (□m).cells n)) := rfl

/-! ### Functoriality -/

/-- The top cell extends vertices by the identity. -/
@[simp] theorem cubeVtxOfCell_topCell : cubeVtxOfCell (topCell n) = OrderHom.id := by
  ext v q
  rw [cubeVtxOfCell_apply]
  have hq : q ∈ noneSet (topCell n).val := by simp [noneSet, topCell]
  rw [dif_pos hq]
  have hidx : nonesIdx (topCell n) q hq = q :=
    (nones_topCell n _).symm.trans (nones_nonesIdx (topCell n) q hq)
  rw [hidx]; rfl

/-- `ev`/`toStar` of the identity face is the top cell. -/
theorem toStar_id : toStar ((𝟙 ▫n : ▫n ⟶ ▫n) : (□n).cells n) = topCell n := by
  have e : (𝟙 ▫n : ▫n ⟶ ▫n) = canonicalMap (topCell n) := (canonicalMap_topCell n).symm
  change ev _ = _
  rw [e]; exact ev_canonicalMap _

@[simp] theorem cubeVtx_id : cubeVtx (𝟙 ▫n) = OrderHom.id := by
  rw [cubeVtx_eq, toStar_id, cubeVtxOfCell_topCell]

/-- **`act`-associativity of vertex extension** — the heart of functoriality.  Extending
along `act w v` (peel `w` then `v`) is extending along `v` then `w`. -/
theorem cubeVtxOfCell_act (w : Cell m e) (v : Cell e n) :
    cubeVtxOfCell (act (K := stdPre m) w v) = (cubeVtxOfCell w).comp (cubeVtxOfCell v) := by
  ext a q
  rw [OrderHom.comp_coe, Function.comp_apply, cubeVtxOfCell_apply, cubeVtxOfCell_apply]
  by_cases hqw : q ∈ noneSet w.val
  · by_cases hpv : nonesIdx w q hqw ∈ noneSet v.val
    · -- both free: `q` is free in `act w v`, indices compose
      have hq : q ∈ noneSet (act (K := stdPre m) w v).val := by
        rw [noneSet_app, Finset.mem_map]
        exact ⟨nonesIdx w q hqw, hpv, nones_nonesIdx w q hqw⟩
      rw [dif_pos hq, dif_pos hqw, cubeVtxOfCell_apply, dif_pos hpv]
      have hidx : nonesIdx (act (K := stdPre m) w v) q hq = nonesIdx v (nonesIdx w q hqw) hpv := by
        apply (nones (act (K := stdPre m) w v)).injective
        rw [nones_nonesIdx, nones_app, nones_nonesIdx, nones_nonesIdx]
      rw [hidx]
    · -- free in `w`, fixed in `v`: `q` fixed in `act w v`
      have hq : q ∉ noneSet (act (K := stdPre m) w v).val := by
        rw [noneSet_app, Finset.mem_map]
        rintro ⟨p, hp, hpq⟩
        have hpeq : p = nonesIdx w q hqw := by
          apply (nones w).injective; rw [nones_nonesIdx]; exact hpq
        exact hpv (hpeq ▸ hp)
      rw [dif_neg hq, dif_pos hqw, cubeVtxOfCell_apply, dif_neg hpv, app_val, dif_pos hqw]
  · -- fixed in `w`: `q` fixed in `act w v`, value from `w`
    have hq : q ∉ noneSet (act (K := stdPre m) w v).val := by
      rw [noneSet_app, Finset.mem_map]
      rintro ⟨p, hp, hpq⟩
      apply hqw; rw [← hpq]; exact nones_mem w p
    rw [dif_neg hq, dif_neg hqw, app_val, dif_neg hqw]

@[simp] theorem cubeVtx_comp (g : ▫n ⟶ ▫e) (h : ▫e ⟶ ▫m) :
    cubeVtx (g ≫ h) = (cubeVtx h).comp (cubeVtx g) := by
  rw [cubeVtx_eq, cubeVtx_eq, cubeVtx_eq]
  have hact : toStar ((g ≫ h : ▫n ⟶ ▫m) : (□m).cells n)
      = act (K := stdPre m) (toStar (h : (□m).cells e)) (toStar (g : (□e).cells n)) := by
    change ev _ = act (ev h) (ev g); exact ev_comp_app g h
  rw [hact, cubeVtxOfCell_act]

/-- **`cubeVtx` as a functor** `Box ⥤ Type`: `▫n ↦ (Fin n → Bool)` (its vertices), a cube face
acting by vertex extension.  Covariant, so it is the copresheaf of vertices. -/
def cubeVtxFunctor : Box ⥤ Type where
  obj b := Fin b.dim → Bool
  map g := ↾fun v => cubeVtx g v
  map_id b := by
    apply ConcreteCategory.hom_ext
    intro v
    rw [TypeCat.ofHom_apply, types_id_apply]
    change cubeVtx (𝟙 ▫b.dim) v = v
    rw [cubeVtx_id]; rfl
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro v
    rw [TypeCat.ofHom_apply, types_comp_apply, TypeCat.ofHom_apply, TypeCat.ofHom_apply]
    change cubeVtx (g ≫ h) v = cubeVtx h (cubeVtx g v)
    rw [cubeVtx_comp]; rfl

/-! ### Boundary vertices and orientation

A cell's two extremal vertices are `cubeVtx` at the constant `⊥`/`⊤` inputs, so `init ≤ final`
(the orientation `Fval_mono` proved by hand) is just `cubeVtx` monotone on `⊥ ≤ ⊤`. -/

/-- `cubeVtx` at a constant input is the boundary vertex `act w (constVertex ε)` — its free
coordinates set to `ε`, its fixed ones kept. -/
theorem cubeVtxOfCell_const (w : Cell m e) (ε : Bool) (q : Fin m) :
    cubeVtxOfCell w (fun _ => ε) q
      = ((act (K := stdPre m) w (constVertex e ε)).val q).getD false := by
  rw [cubeVtxOfCell_apply, app_val]
  by_cases h : q ∈ noneSet w.val
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h]

/-- **The single-cube orientation, for free.**  A cell's `⊥`-vertex sits below its `⊤`-vertex,
because `cubeVtx` is monotone — this is the per-bead content `Fval_mono` proved by hand. -/
theorem cubeVtxOfCell_bot_le_top (w : Cell m e) :
    cubeVtxOfCell w (fun _ => false) ≤ cubeVtxOfCell w (fun _ => true) :=
  (cubeVtxOfCell w).monotone' (fun _ => Bool.false_le _)

/-! ### Lift to wedges

`cubeVtx` is a cube→cube gadget; `wedgeHomFwd` lifts it bead-by-bead to a wedge map.  Bead `i` of
`χ : ⋁a ⟶ □m` contributes the vertex extension of its face into `□m`. -/

/-- The per-bead vertex extensions of a wedge map. -/
def wedgeVtx {a : List ℕ+} (χ : (⋁a).toPsh ⟶ (□m).toPsh) (i : Fin a.length) :
    (Fin ((a.get i : ℕ)) → Bool) →o (Fin m → Bool) :=
  cubeVtx (yonedaEquiv (ιᵂ a i ≫ χ))

end CubeChains
