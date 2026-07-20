import CubeChains.Chains.SegalSplit

/-!
# Chains/WedgeSplit — the computable inverse of `chConcat`

A choice-free splitting of `X ∨ Y` data, the raw material for a *computable* `chSegal`.

* `Glue.cellSide` — the computable X/Y discriminator on a glued cell, at a level whose apex is
  empty (`Quot.lift` on the trivial relation); `wedge2CellSide` wraps it at bead levels.
* `splitObj` — the object-level inverse of `chConcat`, with both round-trips on the nose.
* `appendCellSide` — the `da`/`db` block discriminator on `⋁(da ++ db)`, obtained by transporting
  along `serialWedgeAppend` into `⋁da ∨ ⋁db` and reusing the wedge's own case split;
  `appendProjL`/`appendProjR` are its two halves, each with a `_spec` and a round-trip lemma.
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

theorem wedge2CellSide_elim (X Y : BPSet) {m : ℕ} (hm : 1 ≤ m) (z : (wedge2 X Y).cells m) :
    Sum.elim (fun x => (wedgeInl X Y)⟪m⟫ x)
        (fun y => (wedgeInr X Y)⟪m⟫ y) (wedge2CellSide X Y hm z) = z :=
  Glue.cellSide_elim X.finalVertex Y.initVertex (op ▫m) (CubeChain.cube0_cells_isEmpty hm) z

/-! ### The block discriminator of an appended serial wedge

`⋁(da ++ db)` is `⋁da ∨ ⋁db` transported along `serialWedgeAppend`, so a cell of it splits by
transporting back and applying the wedge's own pushout case split — no recursion on `da`. -/

theorem serialWedgeAppend_inv_hom_app (da db : List ℕ+) (m : ℕ) (z : (⋁(da ++ db)).cells m) :
    (serialWedgeAppendHom da db).hom⟪m⟫ ((serialWedgeAppend da db).inv.hom⟪m⟫ z) = z := by
  simpa using comp_app_cell (appendInv_comp_appendHom da db) m z

theorem serialWedgeAppend_hom_inv_app (da db : List ℕ+) (m : ℕ)
    (w : (wedge2 (⋁da) (⋁db)).cells m) :
    (serialWedgeAppend da db).inv.hom⟪m⟫ ((serialWedgeAppendHom da db).hom⟪m⟫ w) = w := by
  simpa using comp_app_cell (appendHom_comp_appendInv da db) m w

/-- The half-inclusions, cell-wise, as the wedge leaf followed by the append iso. -/
theorem wedgeInclL_app (da db : List ℕ+) (m : ℕ) (r : (⋁da).cells m) :
    (wedgeInclL da db)⟪m⟫ r
      = (serialWedgeAppendHom da db).hom⟪m⟫ ((wedgeInl (⋁da) (⋁db))⟪m⟫ r) :=
  (comp_app_cell (inl_comp_appendHom da db) m r).symm

theorem wedgeInclR_app (da db : List ℕ+) (m : ℕ) (r : (⋁db).cells m) :
    (wedgeInclR da db)⟪m⟫ r
      = (serialWedgeAppendHom da db).hom⟪m⟫ ((wedgeInr (⋁da) (⋁db))⟪m⟫ r) :=
  (comp_app_cell (inr_comp_appendHom da db) m r).symm

/-- **The block discriminator.**  Which half of `⋁(da ++ db)` a bead cell lies in, read off by
transporting along `serialWedgeAppend` into `⋁da ∨ ⋁db`. -/
def appendCellSide (da db : List ℕ+) {m : ℕ} (hm : 1 ≤ m) (z : (⋁(da ++ db)).cells m) :
    (⋁da).cells m ⊕ (⋁db).cells m :=
  wedge2CellSide (⋁da) (⋁db) hm ((serialWedgeAppend da db).inv.hom⟪m⟫ z)

/-- Unfolding lemma: `rw` keyed-matches at `.instances` transparency and will not unfold the
plain `def` on its own. -/
theorem appendCellSide_def (da db : List ℕ+) {m : ℕ} (hm : 1 ≤ m) (z : (⋁(da ++ db)).cells m) :
    appendCellSide da db hm z
      = wedge2CellSide (⋁da) (⋁db) hm ((serialWedgeAppend da db).inv.hom⟪m⟫ z) := rfl

theorem appendCellSide_wedgeInclL (da db : List ℕ+) {m : ℕ} (hm : 1 ≤ m) (r : (⋁da).cells m) :
    appendCellSide da db hm ((wedgeInclL da db)⟪m⟫ r) = Sum.inl r := by
  rw [appendCellSide_def, wedgeInclL_app, serialWedgeAppend_hom_inv_app, wedge2CellSide_inl]

theorem appendCellSide_wedgeInclR (da db : List ℕ+) {m : ℕ} (hm : 1 ≤ m) (r : (⋁db).cells m) :
    appendCellSide da db hm ((wedgeInclR da db)⟪m⟫ r) = Sum.inr r := by
  rw [appendCellSide_def, wedgeInclR_app, serialWedgeAppend_hom_inv_app, wedge2CellSide_inr]

/-- Re-including a discriminated cell recovers it. -/
theorem appendCellSide_elim (da db : List ℕ+) {m : ℕ} (hm : 1 ≤ m) (z : (⋁(da ++ db)).cells m) :
    Sum.elim (fun r => (wedgeInclL da db)⟪m⟫ r) (fun r => (wedgeInclR da db)⟪m⟫ r)
      (appendCellSide da db hm z) = z := by
  have key : ∀ s : (⋁da).cells m ⊕ (⋁db).cells m,
      Sum.elim (fun r => (wedgeInclL da db)⟪m⟫ r) (fun r => (wedgeInclR da db)⟪m⟫ r) s
        = (serialWedgeAppendHom da db).hom⟪m⟫
            (Sum.elim (fun x => (wedgeInl (⋁da) (⋁db))⟪m⟫ x)
              (fun y => (wedgeInr (⋁da) (⋁db))⟪m⟫ y) s) := by
    rintro (x | y)
    · exact wedgeInclL_app da db m x
    · exact wedgeInclR_app da db m y
  rw [appendCellSide_def, key, wedge2CellSide_elim, serialWedgeAppend_inv_hom_app]

/-- **Positive-dimensional left projection.**  A bead cell of `⋁(da ++ db)` in the `da`-block is
recovered as a cell of `⋁da`; `db`-block cells give `none`. -/
def appendProjL (da db : List ℕ+) (m : ℕ) (hm : 1 ≤ m) (z : (⋁(da ++ db)).cells m) :
    Option ((⋁da).cells m) :=
  match appendCellSide da db hm z with
  | Sum.inl r => some r
  | Sum.inr _ => none

/-- `appendProjL` recovers the `wedgeInclL`-preimage: if it returns `some r`, then `r` includes
back to `z`. -/
theorem appendProjL_spec (da db : List ℕ+) (m : ℕ) (hm : 1 ≤ m)
    (z : (⋁(da ++ db)).cells m) (r : (⋁da).cells m) (h : appendProjL da db m hm z = some r) :
    (wedgeInclL da db)⟪m⟫ r = z := by
  have he := appendCellSide_elim da db hm z
  rw [appendProjL] at h
  split at h
  · rename_i x hcs
    rw [hcs, Sum.elim_inl] at he
    rw [← Option.some_inj.mp h]; exact he
  · exact absurd h (by simp)

/-- `appendProjL` recovers `r` from its inclusion: the round-trip on the image. -/
theorem appendProjL_wedgeInclL (da db : List ℕ+) (m : ℕ) (hm : 1 ≤ m) (r : (⋁da).cells m) :
    appendProjL da db m hm ((wedgeInclL da db)⟪m⟫ r) = some r := by
  rw [appendProjL, appendCellSide_wedgeInclL]

/-- **Positive-dimensional right projection**, the `db`-block half of `appendCellSide`. -/
def appendProjR (da db : List ℕ+) (m : ℕ) (hm : 1 ≤ m) (z : (⋁(da ++ db)).cells m) :
    Option ((⋁db).cells m) :=
  match appendCellSide da db hm z with
  | Sum.inl _ => none
  | Sum.inr r => some r

theorem appendProjR_spec (da db : List ℕ+) (m : ℕ) (hm : 1 ≤ m)
    (z : (⋁(da ++ db)).cells m) (r : (⋁db).cells m) (h : appendProjR da db m hm z = some r) :
    (wedgeInclR da db)⟪m⟫ r = z := by
  have he := appendCellSide_elim da db hm z
  rw [appendProjR] at h
  split at h
  · exact absurd h (by simp)
  · rename_i y hcs
    rw [hcs, Sum.elim_inr] at he
    rw [← Option.some_inj.mp h]; exact he

theorem appendProjR_wedgeInclR (da db : List ℕ+) (m : ℕ) (hm : 1 ≤ m) (r : (⋁db).cells m) :
    appendProjR da db m hm ((wedgeInclR da db)⟪m⟫ r) = some r := by
  rw [appendProjR, appendCellSide_wedgeInclR]

end ChainCat
