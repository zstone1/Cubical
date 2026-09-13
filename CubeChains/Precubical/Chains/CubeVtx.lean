import CubeChains.Concurrency.Grading.BlockDecomp
import CubeChains.Precubical.Chains.Refine

/-!
# Precubical/Chains/CubeVtx — a cube face extends vertices

A cube face `g : ▫n ⟶ ▫m` extends an `n`-cube vertex to an `m`-cube vertex: the free
coordinates (`faceEmb g`) carry the given vertex, the rest take `g`'s fixed values.  Since a
vertex *is* a `0`-cell (`vtxEquiv`), that extension is substitution read through `vtxEquiv`, so
it is monotone for free (extend-by-constants) and functorial by `subst_assoc`.
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

/-- **Vertex extension *is* substitution**, read through the identification of a vertex with a
`0`-cell.  Every structural property of `cubeVtxOfCell` comes from this. -/
theorem cubeVtxOfCell_eq_subst (c : Cell m n) (v : Fin n → Bool) :
    cubeVtxOfCell c v = vtxEquiv m (subst c ((vtxEquiv n).symm v)) := by
  funext q
  rw [cubeVtxOfCell_apply]
  change _ = ((subst c ((vtxEquiv n).symm v)).val q).getD false
  by_cases h : q ∈ noneSet c.val
  · rw [dif_pos h, subst_val, substFun_of_none c _ (mem_noneSet.mp h)]; rfl
  · rw [dif_neg h, subst_val, substFun_of_some c _ (fun hc => h (mem_noneSet.mpr hc))]

/-- **The vertex extension of a cube face** `g : ▫n ⟶ ▫m`, through its sign vector. -/
def cubeVtx (g : ▫n ⟶ ▫m) : (Fin n → Bool) →o (Fin m → Bool) :=
  cubeVtxOfCell (Box.sign g)

theorem cubeVtx_eq (g : ▫n ⟶ ▫m) : cubeVtx g = cubeVtxOfCell (Box.sign g) := rfl

/-- The `⊥`-vertex vector reads a cell coordinatewise: free coords `false`, fixed coords their
value. -/
theorem cubeVtxOfCell_bot (b : Cell m n) (q : Fin m) :
    cubeVtxOfCell b (fun _ => false) q = (b.val q).getD false := by
  rw [cubeVtxOfCell_apply]
  by_cases h : q ∈ noneSet b.val
  · rw [dif_pos h, mem_noneSet.mp h]; rfl
  · rw [dif_neg h]

/-- `cubeVtxOfCell_bot` in `Box`-hom spelling: a face's `⊥`-vertex is its own sign vector. -/
theorem cubeVtx_bot_getD (g : ▫n ⟶ ▫m) (q : Fin m) :
    cubeVtx g (fun _ => false) q = ((Box.sign g).val q).getD false :=
  cubeVtxOfCell_bot (Box.sign g) q

/-! ### Functoriality — the unit and associativity of `subst` -/

/-- The top cell extends vertices by the identity. -/
@[simp] theorem cubeVtxOfCell_topCell : cubeVtxOfCell (topCell n) = OrderHom.id := by
  ext v
  rw [cubeVtxOfCell_eq_subst, topCell_subst, Equiv.apply_symm_apply]; rfl

@[simp] theorem cubeVtx_id : cubeVtx (𝟙 ▫n) = OrderHom.id :=
  cubeVtxOfCell_topCell

/-- **Substitution-associativity of vertex extension** — the heart of functoriality. -/
theorem cubeVtxOfCell_subst (w : Cell m e) (v : Cell e n) :
    cubeVtxOfCell (subst w v) = (cubeVtxOfCell w).comp (cubeVtxOfCell v) := by
  ext a
  rw [OrderHom.comp_coe, Function.comp_apply, cubeVtxOfCell_eq_subst, cubeVtxOfCell_eq_subst,
    cubeVtxOfCell_eq_subst, Equiv.symm_apply_apply, subst_assoc]

@[simp] theorem cubeVtx_comp (g : ▫n ⟶ ▫e) (h : ▫e ⟶ ▫m) :
    cubeVtx (g ≫ h) = (cubeVtx h).comp (cubeVtx g) :=
  (congrArg (fun c : Cell m n => cubeVtxOfCell c) (Box.sign_comp g h)).trans
    (cubeVtxOfCell_subst (Box.sign h) (Box.sign g))

/-- **Reading law** — the natural bridge between the coordinate functor (`faceEmb`) and the vertex
functor (`cubeVtx`): a pushed-forward vertex, read at a flip-target `faceEmb g i`, returns the
source value `v i`.  At a free coordinate the fixed values never intervene, so it holds for *every*
input `v`, not just `⊥`/`⊤` — this is what carries the boundary condition through the induction. -/
@[simp] theorem cubeVtx_faceEmb (g : ▫n ⟶ ▫m) (v : Fin n → Bool) (i : Fin n) :
    cubeVtx g v (faceEmb g i) = v i := by
  rw [cubeVtx_eq]
  have hface : (faceEmb g i : Fin m) = nones (Box.sign g) i := rfl
  rw [hface, cubeVtxOfCell_apply, dif_pos (nones_mem (Box.sign g) i), nonesIdx_nones]

/-! ### Boundary vertices and orientation

A cell's two extremal vertices are `cubeVtx` at the constant `⊥`/`⊤` inputs, so its orientation
`init ≤ final` is just `cubeVtx` monotone on `⊥ ≤ ⊤`. -/

/-- **The single-cube orientation, for free** — a cell's `⊥`-vertex sits below its `⊤`-vertex,
because `cubeVtx` is monotone. -/
theorem cubeVtxOfCell_bot_le_top (w : Cell m e) :
    cubeVtxOfCell w (fun _ => false) ≤ cubeVtxOfCell w (fun _ => true) :=
  (cubeVtxOfCell w).monotone' (fun _ => Bool.false_le _)

end CubeChains
