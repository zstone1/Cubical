import CubeChains.Foundations.Representable
import Mathlib.Algebra.BigOperators.Fin

/-!
# Foundations/Shift

The box `shift` endofunctor (`⟨n⟩ ↦ ⟨n+1⟩`, appending a free dimension), the end
cofaces `coface ε : 𝟭 ⟶ shift`, the path object (cocylinder)
`PathOb : PrecubicalSet ⥤ PrecubicalSet` and the endpoints `endpoint ε : PathOb ⟶ 𝟭`
— the geometric `⊗□¹ ⊣ PathOb` infrastructure for the cylinder program.

`shift.map` is built via the cube Yoneda lemma + `snocFree`; the combinatorial
crux is `app_snocFree`.

This is the foundational module for the cylinder ⇒ pointed-functor program.  It
provides:

* `Box.shift : Box ⥤ Box`, `⟨n⟩ ↦ ⟨n + 1⟩`, which on a precubical map of cubes
  *appends a free dimension* (the new last coordinate is free and preserved);
* the two end-cofaces `Box.coface ε : 𝟭 Box ⟶ shift`, appending a fixed last
  coordinate `some ε`;
* the path object (cocylinder) `PathOb : PrecubicalSet ⥤ PrecubicalSet`,
  precomposition by `shift.op`, with `(PathOb K)_n = K_{n+1}`;
* the endpoint evaluations `endpoint ε : PathOb ⟶ 𝟭` induced by `coface ε`.

The combinatorial crux is `shift.map`.  We avoid the dependent-grading bookkeeping
of a raw cell formula by going through the **concrete cube Yoneda lemma**
(`Representable.lean`): a precubical map `□^m ⟶ □^n` is the same as an `m`-cell of
`□^n` (its value `ev f` on the top cell), and `□^m ⟶ K` is rebuilt from an
`m`-cell by `canonicalMap`.  We append a free last coordinate to the *cell*
(`snocFree`) and set `shift.map f := canonicalMap (snocFree (ev f))`.
Functoriality and `coface`-naturality then reduce to the single combinatorial
lemma `app_snocFree`: the iterated-face map `act` commutes with `snocFree`.
-/

open CategoryTheory Opposite

namespace StdCube

variable {N : ℕ}

/-! ### `noneSet` cardinality under `Fin.snoc` -/

/-- The `none`-count is the number of `none` coordinates, written as a sum. -/
theorem card_noneSet_eq_sum (w : Fin N → Option Bool) :
    (noneSet w).card = ∑ j, if w j = none then 1 else 0 := by
  rw [noneSet, Finset.card_filter]

/-- Appending a coordinate `e` adds one `none` iff `e = none`. -/
theorem card_noneSet_snoc {n : ℕ} (v : Fin n → Option Bool) (e : Option Bool) :
    (noneSet (Fin.snoc v e)).card = (noneSet v).card + (if e = none then 1 else 0) := by
  rw [card_noneSet_eq_sum (Fin.snoc v e), Fin.sum_univ_castSucc, card_noneSet_eq_sum v]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-! ### Appending a coordinate to a cell -/

/-- Append a free (`none`) last coordinate to a `k`-cell, giving a `(k+1)`-cell. -/
def snocFree {k : ℕ} (a : Cell N k) : Cell (N + 1) (k + 1) :=
  ⟨Fin.snoc a.val none, by rw [card_noneSet_snoc, a.prop]; simp⟩

@[simp] theorem snocFree_val {k : ℕ} (a : Cell N k) :
    (snocFree a).val = Fin.snoc a.val none := rfl

/-- Append a fixed (`some ε`) last coordinate to a `k`-cell, preserving the grade. -/
def snocFix (ε : Bool) {k : ℕ} (a : Cell N k) : Cell (N + 1) k :=
  ⟨Fin.snoc a.val (some ε), by rw [card_noneSet_snoc, a.prop]; simp⟩

@[simp] theorem snocFix_val (ε : Bool) {k : ℕ} (a : Cell N k) :
    (snocFix ε a).val = Fin.snoc a.val (some ε) := rfl

/-- The `none`-positions of `snocFree a`: the prefix ones via `castSucc`, plus the
new last coordinate.  Identified via `orderEmbOfFin_unique`. -/
theorem nones_snocFree {k : ℕ} (a : Cell N k) :
    (nones (snocFree a) : Fin (k + 1) → Fin (N + 1))
      = Fin.lastCases (Fin.last N) (fun x => Fin.castSucc (nones a x)) := by
  refine (Finset.orderEmbOfFin_unique (snocFree a).prop ?_ ?_).symm
  · intro y
    rw [mem_noneSet]
    rcases Fin.eq_castSucc_or_eq_last y with ⟨x, rfl⟩ | rfl
    · simp only [snocFree_val, Fin.lastCases_castSucc, Fin.snoc_castSucc]
      rw [← mem_noneSet]; exact Finset.orderEmbOfFin_mem _ a.prop x
    · simp only [snocFree_val, Fin.lastCases_last, Fin.snoc_last]
  · intro p q hpq
    rcases Fin.eq_castSucc_or_eq_last q with ⟨q', rfl⟩ | rfl
    · obtain ⟨p', rfl⟩ :=
        Fin.eq_castSucc_of_ne_last (ne_of_lt (lt_trans hpq (Fin.castSucc_lt_last q')))
      simp only [Fin.lastCases_castSucc]
      exact Fin.castSucc_lt_castSucc_iff.mpr
        ((nones a).strictMono (Fin.castSucc_lt_castSucc_iff.mp hpq))
    · obtain ⟨p', rfl⟩ := Fin.eq_castSucc_of_ne_last (ne_of_lt hpq)
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
      exact Fin.castSucc_lt_last _

theorem nones_snocFree_castSucc {k : ℕ} (a : Cell N k) (x : Fin k) :
    nones (snocFree a) (Fin.castSucc x) = Fin.castSucc (nones a x) := by
  have h := congrFun (nones_snocFree a) (Fin.castSucc x)
  simpa using h

theorem nones_snocFree_last {k : ℕ} (a : Cell N k) :
    nones (snocFree a) (Fin.last k) = Fin.last N := by
  have h := congrFun (nones_snocFree a) (Fin.last k)
  simpa using h

/-- The `none`-positions of `snocFix ε a` are exactly the prefix ones via `castSucc`. -/
theorem nones_snocFix (ε : Bool) {k : ℕ} (a : Cell N k) (x : Fin k) :
    nones (snocFix ε a) x = Fin.castSucc (nones a x) := by
  have key : (nones (snocFix ε a) : Fin k → Fin (N + 1)) = fun y => Fin.castSucc (nones a y) := by
    refine (Finset.orderEmbOfFin_unique (snocFix ε a).prop (fun y => ?_)
      (fun p q hpq => Fin.castSucc_lt_castSucc_iff.mpr ((nones a).strictMono hpq))).symm
    rw [mem_noneSet, snocFix_val, Fin.snoc_castSucc, ← mem_noneSet]
    exact Finset.orderEmbOfFin_mem _ a.prop y
  exact congrFun key x

/-- The top cell shifts to the top cell. -/
theorem snocFree_topCell (N : ℕ) : snocFree (topCell N) = topCell (N + 1) := by
  apply Subtype.ext
  rw [snocFree_val]
  funext q
  refine Fin.lastCases ?_ ?_ q
  · rw [Fin.snoc_last]; rfl
  · intro q'; rw [Fin.snoc_castSucc]; rfl

/-- Facing a prefix coordinate commutes with `snocFree`. -/
theorem face_snocFree_castSucc {k : ℕ} (X : Cell N (k + 1)) (ε : Bool) (i : Fin (k + 1)) :
    faceCell ε (Fin.castSucc i) (snocFree X) = snocFree (faceCell ε i X) := by
  apply Subtype.ext
  simp only [face_val, snocFree_val, nones_snocFree_castSucc, Fin.snoc_update]

/-- `snocFix ε a` is the `ε`-face of `snocFree a` at the appended (last) coordinate. -/
theorem snocFix_eq_face (ε : Bool) {k : ℕ} (a : Cell N k) :
    snocFix ε a = faceCell ε (Fin.last k) (snocFree a) := by
  apply Subtype.ext
  simp only [snocFix_val, face_val, snocFree_val, nones_snocFree_last, Fin.update_snoc_last]

/-- Faces commute with `snocFix` (the appended fixed coordinate is never the face
coordinate). -/
theorem face_snocFix (ε ε' : Bool) {k : ℕ} (i : Fin (k + 1)) (a : Cell N (k + 1)) :
    snocFix ε (faceCell ε' i a) = faceCell ε' i (snocFix ε a) := by
  apply Subtype.ext
  simp only [snocFix_val, face_val, nones_snocFix, Fin.snoc_update]

/-! ### `act` as a self-map of cubes

`act` has an implicit target `{K : PrecubicalConstructions}` inferred from
its first argument's type `K.cells n`.  When the target is itself a standard cube
this inference fails on a bare `Cell`, so we pin it with `sapp`. -/

/-- `act` specialized so its target is a standard cube (`K = stdPre P`).  A thin
wrapper that lets bare `Cell` arguments elaborate. -/
def sapp {P : ℕ} (c : Cell P N) {k : ℕ} (a : Cell N k) : Cell P k :=
  act (K := stdPre P) c a

theorem sapp_topCell {P : ℕ} (c : Cell P N) : sapp c (topCell N) = c :=
  app_topCell (K := stdPre P) c

theorem sapp_face {P k : ℕ} (c : Cell P N) (a : Cell N (k + 1)) (ε : Bool) (i : Fin (k + 1)) :
    sapp c (faceCell ε i a) = faceCell ε i (sapp c a) :=
  app_face (K := stdPre P) c a ε i

theorem sapp_unfold {P k : ℕ} (c : Cell P N) (a : Cell N k) (h : k < N) :
    sapp c a = faceCell (minFixedVal a h) (minFixedIdx a h) (sapp c (freeMin a h)) :=
  app_unfold (K := stdPre P) c a h

/-- The canonical-map value of the identity is the identity on cells. -/
theorem sapp_topCell_id {k : ℕ} (a : Cell N k) : sapp (topCell N) a = a :=
  (app_unique (𝟙 (stdPre N)) rfl a).symm

/-- `sapp` composes: peeling along `c₁` then `c₂` equals peeling along `sapp c₂ c₁`. -/
theorem sapp_comp {M P : ℕ} (c₂ : Cell P M) (c₁ : Cell M N) {k : ℕ} (a : Cell N k) :
    sapp c₂ (sapp c₁ a) = sapp (sapp c₂ c₁) a := by
  have hg : PrecubicalConstructions.Hom.app
      (canonicalMap (K := stdPre M) c₁ ≫ canonicalMap (K := stdPre P) c₂)
      N (topCell N) = sapp c₂ c₁ := by
    rw [PrecubicalConstructions.comp_app, canonicalMap_app, canonicalMap_app]
    exact congrArg (sapp c₂) (app_topCell (K := stdPre M) c₁)
  have h := app_unique (canonicalMap (K := stdPre M) c₁ ≫ canonicalMap (K := stdPre P) c₂) hg a
  rw [PrecubicalConstructions.comp_app, canonicalMap_app, canonicalMap_app] at h
  exact h

/-! ### `act` commutes with `snocFree`

The single combinatorial crux: the iterated-face map `act` (the underlying map of
`canonicalMap`) commutes with appending a free dimension.  Proved by peeling the
smallest fixed coordinate (`face_freeMin`) and inducting, using naturality of
`act` (`sapp_face`) and `face_snocFree_castSucc`. -/

theorem app_snocFree {P : ℕ} (c : Cell P N) {k : ℕ} (a : Cell N k) :
    sapp (snocFree c) (snocFree a) = snocFree (sapp c a) := by
  induction hd : N - k using Nat.strong_induction_on generalizing k a with
  | _ d ih =>
    rcases Nat.lt_or_ge k N with hlt | hge
    · -- non-top: `a = face _ _ (freeMin a)`, push `snocFree` through the face
      have hstep : sapp (snocFree c) (snocFree (freeMin a hlt))
          = snocFree (sapp c (freeMin a hlt)) := ih (N - (k + 1)) (by omega) (freeMin a hlt) rfl
      calc sapp (snocFree c) (snocFree a)
          = sapp (snocFree c)
              (snocFree (faceCell (minFixedVal a hlt) (minFixedIdx a hlt) (freeMin a hlt))) := by
            rw [face_freeMin]
        _ = sapp (snocFree c) (faceCell (minFixedVal a hlt) (Fin.castSucc (minFixedIdx a hlt))
              (snocFree (freeMin a hlt))) := by rw [face_snocFree_castSucc]
        _ = faceCell (minFixedVal a hlt) (Fin.castSucc (minFixedIdx a hlt))
              (sapp (snocFree c) (snocFree (freeMin a hlt))) := sapp_face _ _ _ _
        _ = faceCell (minFixedVal a hlt) (Fin.castSucc (minFixedIdx a hlt))
              (snocFree (sapp c (freeMin a hlt))) := by rw [hstep]
        _ = snocFree (faceCell (minFixedVal a hlt) (minFixedIdx a hlt)
              (sapp c (freeMin a hlt))) := by
            rw [face_snocFree_castSucc]
        _ = snocFree (sapp c a) := by rw [← sapp_unfold c a hlt]
    · -- top cell: `k = N`, both sides are `snocFree c`
      have hkn : k = N := le_antisymm (cells_card_le a) hge
      subst hkn
      rw [eq_topCell a, snocFree_topCell, sapp_topCell, sapp_topCell]

/-- `app (snocFree c)` carries `snocFix` to `snocFix` (the coface compatibility). -/
theorem app_snocFree_snocFix {P : ℕ} (c : Cell P N) (ε : Bool) {k : ℕ} (a : Cell N k) :
    sapp (snocFree c) (snocFix ε a) = snocFix ε (sapp c a) := by
  rw [snocFix_eq_face, sapp_face, app_snocFree, ← snocFix_eq_face]

end StdCube

/-! ## The shift functor on `Box` -/

namespace Box

open StdCube

/-- Append a free dimension: `shift ⟨n⟩ = ⟨n+1⟩`; on a precubical map it tensors
with the identity on the interval (the new last coordinate is free and preserved). -/
def shift : Box ⥤ Box where
  obj b := ▫(b.dim + 1)
  map {a b} f := canonicalMap (K := stdPre (b.dim + 1)) (snocFree (ev f))
  map_id b := by
    change canonicalMap (K := stdPre (b.dim + 1)) (snocFree (ev (𝟙 b))) = 𝟙 (stdPre (b.dim + 1))
    rw [show ev (𝟙 b) = topCell b.dim from rfl, snocFree_topCell, canonicalMap_topCell]
  map_comp {a b c} f g := by
    have hev : ev (f ≫ g) = sapp (ev g) (ev f) := app_unique g rfl (ev f)
    apply PrecubicalConstructions.hom_ext
    intro k x
    change sapp (snocFree (ev (f ≫ g))) x
      = sapp (snocFree (ev g)) (sapp (snocFree (ev f)) x)
    rw [sapp_comp, app_snocFree, ← hev]

@[simp] theorem shift_obj (n : ℕ) : shift.obj ▫n = ▫(n + 1) := rfl

@[simp] theorem shift_map_app {a b : Box} (f : a ⟶ b) {k : ℕ}
    (x : Cell (a.dim + 1) k) :
    PrecubicalConstructions.Hom.app (shift.map f) k x = sapp (snocFree (ev f)) x := rfl

/-- The component of the `ε`-end coface `⟨n⟩ ⟶ ⟨n+1⟩`: append the fixed last
coordinate `some ε`. -/
def cofaceComp (ε : Bool) (N : ℕ) : stdPre N ⟶ stdPre (N + 1) where
  app _k a := snocFix ε a
  app_face ε' i a := face_snocFix ε ε' i a

/-- The two end-cofaces `⟨n⟩ ⟶ ⟨n+1⟩` (the `ε`-end of the appended direction),
natural in `n`. -/
def coface (ε : Bool) : 𝟭 Box ⟶ shift where
  app b := cofaceComp ε b.dim
  naturality {a b} f := by
    apply PrecubicalConstructions.hom_ext
    intro k x
    change snocFix ε (PrecubicalConstructions.Hom.app f k x)
      = sapp (snocFree (ev f)) (snocFix ε x)
    rw [app_snocFree_snocFix]
    congr 1
    exact app_unique f rfl x

end Box

/-! ## The path object and endpoint evaluations -/

/-- The path object (cocylinder): `(PathOb K)_n = K_{n+1}`. -/
def PathOb : PrecubicalSet ⥤ PrecubicalSet :=
  (Functor.whiskeringLeft _ _ _).obj Box.shift.op

@[simp] theorem PathOb_obj (K : PrecubicalSet) (n : ℕ) :
    (PathOb.obj K).obj (Opposite.op ▫n) = K.obj (Opposite.op ▫(n + 1)) := rfl

/-- Endpoint evaluations `PathOb ⟹ 𝟭`, from `coface`. -/
def endpoint (ε : Bool) : PathOb ⟶ 𝟭 PrecubicalSet :=
  (Functor.whiskeringLeft _ _ _).map (NatTrans.op (Box.coface ε))

theorem endpoint_naturality (ε : Bool) {K L : PrecubicalSet} (f : K ⟶ L) :
    PathOb.map f ≫ (endpoint ε).app L = (endpoint ε).app K ≫ f :=
  NatTrans.naturality (endpoint ε) f
