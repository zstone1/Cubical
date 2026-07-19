import CubeChains.Chains.SegalSplit

/-!
# Chains/WedgeSplit — the computable inverse of `chConcat`

A choice-free splitting of `X ∨ Y` data, the raw material for a *computable* `chSegal`.

* `Glue.cellSide` — the computable X/Y discriminator on a glued cell, at a level whose apex is
  empty (`Quot.lift` on the trivial relation); `wedge2CellSide` wraps it at bead levels.
* `splitObj` — the object-level inverse of `chConcat`, with both round-trips on the nose.
* `appendProjL` — the positive-dimensional left projection through `wedgeInclL`, with its
  correctness (`appendProjL_spec`, `appendProjL_wedgeInclL`).
* `isCubeChain_of_map_injective` — a precubical mono reflects `IsCubeChain`; this is what lets the
  morphism split rebuild vertices via `wedgeDesc` from bead data alone (no level-`0` projection).
-/

open CategoryTheory Opposite BPSet CubeChain

namespace Glue
variable {S A B : PrecubicalSet} (f : S ⟶ A) (g : S ⟶ B)

-- The computable X/Y discriminator on a glued cell at an empty-apex level: the pushout relation
-- has no generators there, so `Quot.lift id` recovers the `Sum`.
unseal gluePsh inl inr in
def cellSide (o : Boxᵒᵖ) (he : IsEmpty (S.obj o)) (z : (gluePsh f g).obj o) :
    A.obj o ⊕ B.obj o :=
  Quot.lift id (by rintro a b ⟨s⟩; exact (he.false s).elim) z

unseal gluePsh inl in
theorem cellSide_inl (o : Boxᵒᵖ) (he : IsEmpty (S.obj o)) (x : A.obj o) :
    cellSide f g o he ((inl f g).app o x) = Sum.inl x := rfl

unseal gluePsh inr in
theorem cellSide_inr (o : Boxᵒᵖ) (he : IsEmpty (S.obj o)) (y : B.obj o) :
    cellSide f g o he ((inr f g).app o y) = Sum.inr y := rfl

-- Re-including the discriminated cell recovers it: `cellSide` is a section of the sum inclusion.
unseal gluePsh inl inr in
theorem cellSide_elim (o : Boxᵒᵖ) (he : IsEmpty (S.obj o)) (z : (gluePsh f g).obj o) :
    Sum.elim (fun x => (inl f g).app o x) (fun y => (inr f g).app o y)
      (cellSide f g o he z) = z := by
  induction z using Quot.ind with
  | _ s => cases s <;> rfl

end Glue

namespace ChainCat

/-- The X/Y discriminator at a bead level of `X ∨ Y` (`□⁰` has no positive cells, so the apex is
empty). -/
def wedge2CellSide (X Y : BPSet) {m : ℕ} (hm : 1 ≤ m) (c : (wedge2 X Y).cells m) :
    X.cells m ⊕ Y.cells m :=
  Glue.cellSide X.finalVertex Y.initVertex (op ▫m) (CubeChain.cube0_cells_isEmpty hm) c

theorem wedge2CellSide_inl (X Y : BPSet) {m : ℕ} (hm : 1 ≤ m) (x : X.cells m) :
    wedge2CellSide X Y hm ((wedgeInl X Y)⟪m⟫ x) = Sum.inl x :=
  Glue.cellSide_inl X.finalVertex Y.initVertex (op ▫m) (CubeChain.cube0_cells_isEmpty hm) x

theorem wedge2CellSide_inr (X Y : BPSet) {m : ℕ} (hm : 1 ≤ m) (y : Y.cells m) :
    wedge2CellSide X Y hm ((wedgeInr X Y)⟪m⟫ y) = Sum.inr y :=
  Glue.cellSide_inr X.finalVertex Y.initVertex (op ▫m) (CubeChain.cube0_cells_isEmpty hm) y

variable {X Y : BPSet}

/-- The X-cubes of a cube list in `X ∨ Y`, read off computably by `cellSide`. -/
def xCubes (cs : List (Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ))) :
    List (Σ n : ℕ+, X.cells (n : ℕ)) :=
  cs.filterMap fun c =>
    match wedge2CellSide X Y c.1.pos c.2 with
    | Sum.inl x => some ⟨c.1, x⟩
    | Sum.inr _ => none

def yCubes (cs : List (Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ))) :
    List (Σ n : ℕ+, Y.cells (n : ℕ)) :=
  cs.filterMap fun c =>
    match wedge2CellSide X Y c.1.pos c.2 with
    | Sum.inl _ => none
    | Sum.inr y => some ⟨c.1, y⟩

@[simp] theorem xCubes_nil : xCubes ([] : List (Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ))) = [] := rfl

theorem xCubes_append (l₁ l₂ : List (Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ))) :
    xCubes (l₁ ++ l₂) = xCubes l₁ ++ xCubes l₂ := List.filterMap_append

/-- `xCubes` recovers the X-cubes from a pushed X-list. -/
theorem xCubes_map_inlPush (xc : List (Σ n : ℕ+, X.cells (n : ℕ))) :
    xCubes (xc.map (inlPush X Y)) = xc := by
  induction xc with
  | nil => rfl
  | cons c rest ih =>
    rw [List.map_cons, xCubes, List.filterMap_cons]
    have h : wedge2CellSide X Y (inlPush X Y c).1.pos (inlPush X Y c).2 = Sum.inl c.2 :=
      wedge2CellSide_inl X Y c.1.pos c.2
    simp only [inlPush] at h ⊢
    rw [h]
    simpa [xCubes] using ih

/-- `xCubes` drops all Y-cubes. -/
theorem xCubes_map_inrPush (yc : List (Σ n : ℕ+, Y.cells (n : ℕ))) :
    xCubes (yc.map (inrPush X Y)) = [] := by
  induction yc with
  | nil => rfl
  | cons c rest ih =>
    rw [List.map_cons, xCubes, List.filterMap_cons]
    have h : wedge2CellSide X Y (inrPush X Y c).1.pos (inrPush X Y c).2 = Sum.inr c.2 :=
      wedge2CellSide_inr X Y c.1.pos c.2
    simp only [inrPush] at h ⊢
    rw [h]
    simpa [xCubes] using ih

@[simp] theorem yCubes_nil : yCubes ([] : List (Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ))) = [] := rfl

theorem yCubes_append (l₁ l₂ : List (Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ))) :
    yCubes (l₁ ++ l₂) = yCubes l₁ ++ yCubes l₂ := List.filterMap_append

theorem yCubes_map_inrPush (yc : List (Σ n : ℕ+, Y.cells (n : ℕ))) :
    yCubes (yc.map (inrPush X Y)) = yc := by
  induction yc with
  | nil => rfl
  | cons c rest ih =>
    rw [List.map_cons, yCubes, List.filterMap_cons]
    have h : wedge2CellSide X Y (inrPush X Y c).1.pos (inrPush X Y c).2 = Sum.inr c.2 :=
      wedge2CellSide_inr X Y c.1.pos c.2
    simp only [inrPush] at h ⊢
    rw [h]
    simpa [yCubes] using ih

theorem yCubes_map_inlPush (xc : List (Σ n : ℕ+, X.cells (n : ℕ))) :
    yCubes (xc.map (inlPush X Y)) = [] := by
  induction xc with
  | nil => rfl
  | cons c rest ih =>
    rw [List.map_cons, yCubes, List.filterMap_cons]
    have h : wedge2CellSide X Y (inlPush X Y c).1.pos (inlPush X Y c).2 = Sum.inl c.2 :=
      wedge2CellSide_inl X Y c.1.pos c.2
    simp only [inlPush] at h ⊢
    rw [h]
    simpa [yCubes] using ih

/-- The read-off cube list of `c : Ch (X ∨ Y)` is a chain from init to final. -/
theorem obj_hch (c : Ch (wedge2 X Y)) :
    IsCubeChain (wedge2 X Y).init (wedgeToCubes ⟨c.dims, c.map.hom⟩) (wedge2 X Y).final := by
  have h0 := wedgeToCubes_isCubeChain c.dims c.map.hom
  rwa [c.map.app_init, c.map.app_final] at h0

theorem xCubes_isChain (h : (wedge2 X Y).AdmitsAltitude)
    (cs : List (Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ)))
    (hch : IsCubeChain (wedge2 X Y).init cs (wedge2 X Y).final) :
    IsCubeChain X.init (xCubes cs) X.final := by
  obtain ⟨xc, yc, hchx, hchy, hsplit⟩ := chain_split X Y h cs hch
  have hx : xCubes cs = xc := by
    rw [hsplit, xCubes_append, xCubes_map_inlPush, xCubes_map_inrPush, List.append_nil]
  rw [hx]; exact hchx

theorem yCubes_isChain (h : (wedge2 X Y).AdmitsAltitude)
    (cs : List (Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ)))
    (hch : IsCubeChain (wedge2 X Y).init cs (wedge2 X Y).final) :
    IsCubeChain Y.init (yCubes cs) Y.final := by
  obtain ⟨xc, yc, hchx, hchy, hsplit⟩ := chain_split X Y h cs hch
  have hy : yCubes cs = yc := by
    rw [hsplit, yCubes_append, yCubes_map_inlPush, yCubes_map_inrPush, List.nil_append]
  rw [hy]; exact hchy

/-- **The computable object split.**  Reads off the cube list, splits it by `cellSide`, and glues
each half back into a chain-object via `wedgeDescHom`. -/
def splitObj (h : (wedge2 X Y).AdmitsAltitude) (c : Ch (wedge2 X Y)) : Ch X × Ch Y :=
  (⟨(xCubes (wedgeToCubes ⟨c.dims, c.map.hom⟩)).map (·.1),
      wedgeDescHom (xCubes (wedgeToCubes ⟨c.dims, c.map.hom⟩))
        (xCubes_isChain h _ (obj_hch c))⟩,
   ⟨(yCubes (wedgeToCubes ⟨c.dims, c.map.hom⟩)).map (·.1),
      wedgeDescHom (yCubes (wedgeToCubes ⟨c.dims, c.map.hom⟩))
        (yCubes_isChain h _ (obj_hch c))⟩)

theorem split_reassemble (h : (wedge2 X Y).AdmitsAltitude)
    (cs : List (Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ)))
    (hch : IsCubeChain (wedge2 X Y).init cs (wedge2 X Y).final) :
    (xCubes cs).map (inlPush X Y) ++ (yCubes cs).map (inrPush X Y) = cs := by
  obtain ⟨xc, yc, hchx, hchy, hsplit⟩ := chain_split X Y h cs hch
  have hx : xCubes cs = xc := by
    rw [hsplit, xCubes_append, xCubes_map_inlPush, xCubes_map_inrPush, List.append_nil]
  have hy : yCubes cs = yc := by
    rw [hsplit, yCubes_append, yCubes_map_inlPush, yCubes_map_inrPush, List.nil_append]
  rw [hx, hy, ← hsplit]

theorem wedgeToCubes_splitObj_fst (h : (wedge2 X Y).AdmitsAltitude) (c : Ch (wedge2 X Y)) :
    wedgeToCubes ⟨(splitObj h c).1.dims, (splitObj h c).1.map.hom⟩
      = xCubes (wedgeToCubes ⟨c.dims, c.map.hom⟩) :=
  wedgeToCubes_wedgeDesc X.init X.final _ (xCubes_isChain h _ (obj_hch c))

theorem wedgeToCubes_splitObj_snd (h : (wedge2 X Y).AdmitsAltitude) (c : Ch (wedge2 X Y)) :
    wedgeToCubes ⟨(splitObj h c).2.dims, (splitObj h c).2.map.hom⟩
      = yCubes (wedgeToCubes ⟨c.dims, c.map.hom⟩) :=
  wedgeToCubes_wedgeDesc Y.init Y.final _ (yCubes_isChain h _ (obj_hch c))

/-- Forward round-trip: gluing the split back gives the original chain (on the nose). -/
theorem chConcat_obj_splitObj (h : (wedge2 X Y).AdmitsAltitude) (c : Ch (wedge2 X Y)) :
    (chConcat X Y).obj (splitObj h c) = c := by
  apply Obj.eq_of_wedgeToCubes
  change wedgeToCubes ⟨(splitObj h c).1.dims ++ (splitObj h c).2.dims,
      (concatChainMap X Y (splitObj h c).1 (splitObj h c).2).hom⟩
    = wedgeToCubes ⟨c.dims, c.map.hom⟩
  rw [wedgeToCubes_concatChainMap X Y (splitObj h c).1 (splitObj h c).2,
      wedgeToCubes_splitObj_fst h c, wedgeToCubes_splitObj_snd h c]
  exact split_reassemble h _ (obj_hch c)

/-- Backward round-trip: splitting a concatenation recovers the two halves (on the nose). -/
theorem splitObj_chConcat_obj (h : (wedge2 X Y).AdmitsAltitude) (a : Ch X) (b : Ch Y) :
    splitObj h ((chConcat X Y).obj (a, b)) = (a, b) := by
  refine Prod.ext ?_ ?_
  · apply Obj.eq_of_wedgeToCubes
    rw [wedgeToCubes_splitObj_fst h ((chConcat X Y).obj (a, b))]
    change xCubes (wedgeToCubes ⟨a.dims ++ b.dims, (concatChainMap X Y a b).hom⟩)
      = wedgeToCubes ⟨a.dims, a.map.hom⟩
    rw [wedgeToCubes_concatChainMap X Y a b, xCubes_append, xCubes_map_inlPush,
        xCubes_map_inrPush, List.append_nil]
  · apply Obj.eq_of_wedgeToCubes
    rw [wedgeToCubes_splitObj_snd h ((chConcat X Y).obj (a, b))]
    change yCubes (wedgeToCubes ⟨a.dims ++ b.dims, (concatChainMap X Y a b).hom⟩)
      = wedgeToCubes ⟨b.dims, b.map.hom⟩
    rw [wedgeToCubes_concatChainMap X Y a b, yCubes_append, yCubes_map_inlPush,
        yCubes_map_inrPush, List.nil_append]

/-- **Positive-dimensional left projection.**  A bead cell of `⋁(da ++ db)` in the `da`-block is
recovered as a cell of `⋁da` (recursion via `serialWedge_cons` + `cellSide`); `db`-block cells give
`none`.  Only used at bead levels `m ≥ 1`, so the empty `⋁[]` base is just `none`. -/
def appendProjL : (da db : List ℕ+) → (m : ℕ) → 1 ≤ m →
    (⋁(da ++ db)).cells m → Option ((⋁da).cells m)
  | [], _, _, _, _ => none
  | n :: da', db, m, hm, z =>
      match wedge2CellSide (□(n : ℕ)) (⋁(da' ++ db)) hm z with
      | Sum.inl x => some ((wedgeInl (□(n : ℕ)) (⋁da'))⟪m⟫ x)
      | Sum.inr w => (appendProjL da' db m hm w).map
          (fun r => (wedgeInr (□(n : ℕ)) (⋁da'))⟪m⟫ r)

theorem wedge2CellSide_elim (X Y : BPSet) {m : ℕ} (hm : 1 ≤ m) (z : (wedge2 X Y).cells m) :
    Sum.elim (fun x => (wedgeInl X Y)⟪m⟫ x)
        (fun y => (wedgeInr X Y)⟪m⟫ y) (wedge2CellSide X Y hm z) = z :=
  Glue.cellSide_elim X.finalVertex Y.initVertex (op ▫m) (CubeChain.cube0_cells_isEmpty hm) z

theorem wedgeInclL_inl_comp (n : ℕ+) (da' db : List ℕ+) :
    wedgeInl (□(n : ℕ)) (⋁da') ≫ wedgeInclL (n :: da') db
      = wedgeInl (□(n : ℕ)) (⋁(da' ++ db)) :=
  wedgeInclL_cons_inl n da' db

theorem wedgeInclL_inr_comp (n : ℕ+) (da' db : List ℕ+) :
    wedgeInr (□(n : ℕ)) (⋁da') ≫ wedgeInclL (n :: da') db
      = wedgeInclL da' db ≫ wedgeInr (□(n : ℕ)) (⋁(da' ++ db)) :=
  wedgeInclL_cons_inr n da' db

/-- `appendProjL` recovers the `wedgeInclL`-preimage: if it returns `some r`, then `r` includes
back to `z`. -/
theorem appendProjL_spec : ∀ (da db : List ℕ+) (m : ℕ) (hm : 1 ≤ m)
    (z : (⋁(da ++ db)).cells m) (r : (⋁da).cells m),
    appendProjL da db m hm z = some r → (wedgeInclL da db)⟪m⟫ r = z
  | [], db, m, hm, z, r, h => by simp only [appendProjL, reduceCtorEq] at h
  | n :: da', db, m, hm, z, r, h => by
      have hz := wedge2CellSide_elim (□(n : ℕ)) (⋁(da' ++ db)) hm z
      rw [appendProjL] at h
      split at h
      · rename_i x hcs
        rw [hcs, Sum.elim_inl] at hz
        obtain rfl : r = (wedgeInl (□(n : ℕ)) (⋁da'))⟪m⟫ x :=
          (Option.some_inj.mp h).symm
        rw [← hz]
        exact congrArg (fun f : (□(n : ℕ)).toPsh ⟶ (⋁(n :: da' ++ db)).toPsh => f⟪m⟫ x)
          (wedgeInclL_inl_comp n da' db)
      · rename_i w hcs
        rw [hcs, Sum.elim_inr] at hz
        rcases hmap : appendProjL da' db m hm w with _ | r'
        · rw [hmap] at h; simp only [Option.map_none, reduceCtorEq] at h
        · rw [hmap] at h
          simp only [Option.map_some, Option.some_inj] at h
          subst h
          have ih := appendProjL_spec da' db m hm w r' hmap
          rw [← hz, ← ih]
          exact congrArg (fun f : (⋁da').toPsh ⟶ (⋁(n :: da' ++ db)).toPsh => f⟪m⟫ r')
            (wedgeInclL_inr_comp n da' db)

/-- `appendProjL` recovers `r` from its inclusion: the round-trip on the image. -/
theorem appendProjL_wedgeInclL : ∀ (da db : List ℕ+) (m : ℕ) (hm : 1 ≤ m) (r : (⋁da).cells m),
    appendProjL da db m hm ((wedgeInclL da db)⟪m⟫ r) = some r
  | [], db, m, hm, r => (CubeChain.cube0_cells_isEmpty hm).elim r
  | n :: da', db, m, hm, r => by
      have hr := wedge2CellSide_elim (□(n : ℕ)) (⋁da') hm r
      cases hcs : wedge2CellSide (□(n : ℕ)) (⋁da') hm r with
      | inl x =>
        rw [hcs, Sum.elim_inl] at hr
        have key : (wedgeInclL (n :: da') db)⟪m⟫ r
            = (wedgeInl (□(n : ℕ)) (⋁(da' ++ db)))⟪m⟫ x := by
          rw [← hr]
          exact congrArg (fun f : (□(n : ℕ)).toPsh ⟶ (⋁(n :: da' ++ db)).toPsh => f⟪m⟫ x)
            (wedgeInclL_inl_comp n da' db)
        rw [appendProjL, key]
        simp only [wedge2CellSide_inl]
        rw [hr]
      | inr w =>
        rw [hcs, Sum.elim_inr] at hr
        have key : (wedgeInclL (n :: da') db)⟪m⟫ r
            = (wedgeInr (□(n : ℕ)) (⋁(da' ++ db)))⟪m⟫
                ((wedgeInclL da' db)⟪m⟫ w) :=
          hr ▸ congrArg (fun f : (⋁da').toPsh ⟶ (⋁(n :: da' ++ db)).toPsh => f⟪m⟫ w)
            (wedgeInclL_inr_comp n da' db)
        rw [appendProjL, key]
        simp only [wedge2CellSide_inr, appendProjL_wedgeInclL da' db m hm w, Option.map_some]
        rw [hr]

/-- **A precubical mono reflects `IsCubeChain`.**  If the `m`-images of `cubes` form a chain,
so do `cubes` — because `m` preserves `vertex₀`/`vertex₁` and is injective on `0`-cells. -/
theorem isCubeChain_of_map_injective {L W : PrecubicalSet} (m : L ⟶ W)
    (hm : ∀ k, Function.Injective (m.app k)) :
    ∀ (cubes : List (Σ n : ℕ+, L.cells (n : ℕ))) (u v : L.cells 0),
    IsCubeChain (m⟪0⟫ u)
        (cubes.map fun c => (⟨c.1, m⟪(c.1 : ℕ)⟫ c.2⟩ : Σ n : ℕ+, W.cells (n : ℕ))) (m⟪0⟫ v) →
    IsCubeChain u cubes v
  | [], u, v, h => hm _ h
  | ⟨n, c⟩ :: rest, u, v, h => by
      rw [List.map_cons] at h
      obtain ⟨h1, h2⟩ := h
      refine ⟨hm _ ((PrecubicalSet.map_vertex₀ m c).trans h1), ?_⟩
      refine isCubeChain_of_map_injective m hm rest (L.vertex₁ c) v ?_
      rw [PrecubicalSet.map_vertex₁]; exact h2

end ChainCat
