import CubeChains.Cobordisms.DCob
import CubeChains.Cobordisms.Union

/-!
# Cobordisms/NonTriviality — the merge is non-invertible (M6)

`dCob` is **not a groupoid**: there is a non-invertible cobordism, the **merge**
`{a,b} ⇒ {∗}` collapsing two source vertices into one.  We obstruct invertibility
with a `π₀` (connected-components) invariant.

The milestone has three parts:

* **M6(a)** — there is *no closed cobordism out of `∅`*: re-exported here as
  `no_closed_cobordism_from_empty` (the `∅`-bottom result, proved in `Flags.lean`).
* **M6(b)** — the **merge** `mergeCob : (pt ⨿ pt) ⇒c pt` is a *valid* directed
  cobordism (Tier 1) yet is **not invertible** (Tier 3), because its source leg is
  not injective on `π₀` (Tier 2): the two source vertices `a`, `b` become
  reachability-connected in the middle (both columns rise to a common merge vertex
  `∗`), whereas the cylinder identity keeps them apart.  The invariant
  `srcLegπ₀Injective` holds for `idCob` (`idCob_src_π₀_injective`), **fails** for
  `mergeCob` (`mergeCob_inl_π₀_not_injective`), and is **destroyed by composition**
  (`mergeComp_not_srcLegπ₀Injective`).  Two grades of non-invertibility follow:
  - `merge_no_iso_inverse` — **unconditional**: no inverse `V` admits a *boundary-
    fixing iso* of `mergeCob.comp V` with `idCob S` (uses only the proved
    iso-invariance `srcLegπ₀Injective_cobIso_iff`).
  - `merge_not_invertible` — **unconditional**: `mergeCob` is not a `dCob`-equivalence
    (`IsEquivalenceCob`).  The required rel-∂ invariance of `srcLegπ₀Injective`
    (`srcLegπ₀Injective_rel`) is fully discharged here: the iso half is proved
    (`srcLegπ₀Injective_cobIso_iff`) and the *unit-move* half — a `π₀`-van-Kampen
    statement, prepending/appending a cylinder is a `π₀`-equivalence of middles — is
    routed through the `Research/Conjectures.lean` lemmas `dcob_unitL_srcInj_iff` /
    `dcob_unitR_srcInj_iff`.  No local hypothesis is needed.
* **M6(c)** — the cylinder `idCob` *is* the `dCob` identity (M5) and is distinct
  from the merge (different source/sink shape, and a different value of the
  `srcLegπ₀Injective` invariant).

## The merge construction (collar-compatible)

The naive mapping cylinder `pushout (cylEnd true S) (fold ≫ cylEnd false T)` is
**not** a valid cobordism: `fold` is non-mono, so the `Cyl S` injection is non-mono
and there is no *source collar* `Cyl S ↪ mid` (the two column tops would collapse).

The fix keeps every gluing leg **mono** and pushes the merge *strictly above* the
source-collar tops.  Let `G := pushout (cylEnd true pt) (cylEnd true pt)` be the
**Λ-junction** — two `pt`-edges glued at their *tops* into one apex vertex `∗`,
with the two *bottom* vertices `p`, `q` distinct.  The collapse map
`g : S = pt ⨿ pt ⟶ G` (`a ↦ p`, `b ↦ q`) is then **mono** (`p ≠ q`).  The merge
middle is

```
mergeMid := pushout (cylEnd true S) g
```

so the source collar is the (mono, by adhesivity) pushout injection
`p₁ : Cyl S ↪ mergeMid` — `top(a) ≠ top(b)` survive, glued onto `p ≠ q`, and the
merge `p → ∗ ← q` lives one level up inside `G`.  This is exactly the `Cospan.comp`
shape `cylCospan S` ∘ `(Cospan.of g (cylEnd true pt ≫ Gb))`, so the barrier lemmas
of `Composition.lean` discharge the sieve/cosieve fields.

**Layer:** Cobordisms.  **Imports:** `Cobordisms.DCob` (the cobordism category +
`cobordismRel`), `Cobordisms.Union` (the coproduct cell machinery for `pt ⨿ pt`).
-/

set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open Precubical.Cobordism

namespace PrecubicalSet

universe u

/-! ### M6(a) — no closed cobordism out of `∅` (re-export)

The `∅`-bottom theorem is proved in `Flags.lean`; we re-export it here as the M6(a)
component of the non-triviality milestone. -/

/-- **M6(a).**  There is no `Closed` cobordism out of the empty precubical set `∅`
once `C.mid` has a minimal vertex — the `∅`-bottom result (proved in `Flags.lean`).
Conceptually: `Closed` forces every minimal vertex into the source image, but the
source image of a cospan out of `∅` is empty. -/
theorem no_closed_cobordism_from_empty {X : PrecubicalSet} (C : Cospan emptyPsh X)
    (hC : C.Closed) (hmin : ∃ v : C.mid.cells 0, IsMinimalVertex C.mid v) : False :=
  C.no_closed_cobordism_from_empty hC hmin

/-! ### The one-vertex precubical set `pt` and the source `S = pt ⨿ pt` -/

/-- The **one-vertex** precubical set `□⁰`: a single `0`-cell and nothing higher,
the representable on `Box.ob 0`. -/
noncomputable def pt : PrecubicalSet := yoneda.obj (Box.ob 0)

/-- The two source vertices `a := coprod.inl`, `b := coprod.inr` of `S := pt ⨿ pt`. -/
noncomputable abbrev srcA : pt ⟶ pt ⨿ pt := coprod.inl
/-- The right source vertex. -/
noncomputable abbrev srcB : pt ⟶ pt ⨿ pt := coprod.inr

open Cylinder

/-- `pt` has **no cells above dimension `0`**: a cell of `pt.cells (n+1)` is a `Box`
map `Box.ob (n+1) ⟶ Box.ob 0`, i.e. a concrete map `stdPre (n+1) ⟶ stdPre 0`; its
value on the top cell lands in `StdCube.cells 0 (n+1)`, which is empty
(`cells_card_le`: `n+1 ≤ 0` is false). -/
instance pt_cells_succ_isEmpty (n : ℕ) : IsEmpty (pt.cells (n + 1)) := by
  constructor
  intro c
  -- `c : Box.ob (n+1) ⟶ Box.ob 0`, i.e. `stdPre (n+1) ⟶ stdPre 0`.
  have hcell : StdCube.cells 0 (n + 1) := StdCube.ev c
  exact absurd (StdCube.cells_card_le hcell) (by omega)

/-! ### The Λ-junction `G` and the collapse map `g : S ⟶ G`

`G` glues two `pt`-edges (`Cyl pt`) at their *tops* (`cylEnd true pt`) into one apex
vertex `∗`.  Its two injections `Ga`, `Gb` are mono (adhesive pushout of monos), and
their *bottom* vertices `p := Ga (bot ∗pt)`, `q := Gb (bot ∗pt)` are distinct (van
Kampen: a collision would factor through the glued top, contradicting bot ≠ top).
The collapse map `g` is the copairing of the two bottom-vertex inclusions; it is mono
because `p ≠ q`. -/

/-- The **Λ-junction** `G`: two `pt`-edges glued at their tops. -/
noncomputable def junc : PrecubicalSet := pushout (cylEnd true pt) (cylEnd true pt)

/-- The left edge `Cyl pt ↪ G`. -/
noncomputable abbrev juncA : Cyl.obj pt ⟶ junc := pushout.inl (cylEnd true pt) (cylEnd true pt)
/-- The right edge `Cyl pt ↪ G`. -/
noncomputable abbrev juncB : Cyl.obj pt ⟶ junc := pushout.inr (cylEnd true pt) (cylEnd true pt)

instance : Mono juncA :=
  Adhesive.mono_of_isPushout_of_mono_right (IsPushout.of_hasPushout _ _)

instance : Mono juncB :=
  Adhesive.mono_of_isPushout_of_mono_left (IsPushout.of_hasPushout _ _)

/-- The defining gluing square of `G`, evaluated at level `n` in `Type`, is a
pullback (van Kampen: pushout of the mono `cylEnd true pt`). -/
theorem junc_isPullback_app (n : ℕ) :
    IsPullback ((cylEnd true pt).app (op (Box.ob n))) ((cylEnd true pt).app (op (Box.ob n)))
      (juncA.app (op (Box.ob n))) (juncB.app (op (Box.ob n))) := by
  have hpush : IsPushout ((cylEnd true pt).app (op (Box.ob n)))
      ((cylEnd true pt).app (op (Box.ob n)))
      (juncA.app (op (Box.ob n))) (juncB.app (op (Box.ob n))) :=
    (IsPushout.of_hasPushout (cylEnd true pt) (cylEnd true pt)).map
      (F := (evaluation Boxᵒᵖ Type).obj (op (Box.ob n)))
  refine Types.isPullback_of_isPushout hpush ?_
  rw [← mono_iff_injective]
  exact (NatTrans.mono_iff_mono_app (cylEnd true pt)).1 inferInstance (op (Box.ob n))

/-- The two bottom vertices of `G` are distinct: `Ga (bot) ≠ Gb (bot)`.  A collision
factors through the glued top (van Kampen), but `cylEnd false pt` lands in `bot` and
`cylEnd true pt` in `top`, contradicting `cylEnd_disjoint`. -/
theorem junc_bot_ne (x y : pt.cells 0) :
    juncA.app (op (Box.ob 0)) ((cylEnd false pt).app (op (Box.ob 0)) x)
      ≠ juncB.app (op (Box.ob 0)) ((cylEnd false pt).app (op (Box.ob 0)) y) := by
  intro hcollide
  obtain ⟨w, hw₁, _hw₂⟩ :=
    Types.exists_of_isPullback (junc_isPullback_app 0)
      ((cylEnd false pt).app (op (Box.ob 0)) x)
      ((cylEnd false pt).app (op (Box.ob 0)) y) hcollide
  -- `hw₁ : cylEnd true pt w = cylEnd false pt x`, contradicting disjoint ends.
  exact cylEnd_disjoint pt x w hw₁.symm

/-- The **collapse map** `g : S = pt ⨿ pt ⟶ G`: the copairing of the two
bottom-vertex inclusions `pt → G`.  Sends `a ↦ p`, `b ↦ q`. -/
noncomputable def collapse : (pt ⨿ pt) ⟶ junc :=
  coprod.desc (cylEnd false pt ≫ juncA) (cylEnd false pt ≫ juncB)

@[simp] theorem collapse_inl :
    coprod.inl ≫ collapse = cylEnd false pt ≫ juncA :=
  coprod.inl_desc _ _

@[simp] theorem collapse_inr :
    coprod.inr ≫ collapse = cylEnd false pt ≫ juncB :=
  coprod.inr_desc _ _

/-- The action of `collapse` on the left summand. -/
theorem collapse_app_coprodInl {n : ℕ} (x : pt.cells n) :
    collapse.app (op (Box.ob n)) (FunctorToTypes.coprodInl x)
      = juncA.app (op (Box.ob n)) ((cylEnd false pt).app (op (Box.ob n)) x) := by
  rw [coprodInl_eq_inl_app]
  have h := NatTrans.congr_app collapse_inl (op (Box.ob n))
  apply_fun (fun φ => φ x) at h
  simp only [NatTrans.comp_app, types_comp_apply] at h
  exact h

/-- The action of `collapse` on the right summand. -/
theorem collapse_app_coprodInr {n : ℕ} (y : pt.cells n) :
    collapse.app (op (Box.ob n)) (FunctorToTypes.coprodInr y)
      = juncB.app (op (Box.ob n)) ((cylEnd false pt).app (op (Box.ob n)) y) := by
  rw [coprodInr_eq_inr_app]
  have h := NatTrans.congr_app collapse_inr (op (Box.ob n))
  apply_fun (fun φ => φ y) at h
  simp only [NatTrans.comp_app, types_comp_apply] at h
  exact h

/-- **The collapse map is mono.**  Injective on each summand (`cylEnd false` and the
mono junction injections), with disjoint images across summands (`junc_bot_ne` at
level 0, and `pt` has no higher cells so cross-summand collisions only occur at level
0). -/
instance collapse_mono : Mono collapse := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  obtain ⟨⟨n⟩⟩ := k
  rw [mono_iff_injective]
  intro u v huv
  rcases coprod_cell_cases u with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    rcases coprod_cell_cases v with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · -- inl, inl
    rw [collapse_app_coprodInl, collapse_app_coprodInl] at huv
    have hx : (cylEnd false pt).app (op (Box.ob n)) x = (cylEnd false pt).app (op (Box.ob n)) y :=
      app_injective_of_mono juncA n huv
    exact congrArg _ (cylEnd_app_injective false pt hx)
  · -- inl, inr: cross-summand.  Only possible at `n = 0` (pt has no higher cells);
    -- there `junc_bot_ne` rules it out.
    exfalso
    rw [collapse_app_coprodInl, collapse_app_coprodInr] at huv
    rcases n with _ | m
    · exact junc_bot_ne x y huv
    · exact (pt_cells_succ_isEmpty m).false x
  · -- inr, inl: symmetric cross-summand.
    exfalso
    rw [collapse_app_coprodInr, collapse_app_coprodInl] at huv
    rcases n with _ | m
    · exact junc_bot_ne y x huv.symm
    · exact (pt_cells_succ_isEmpty m).false x
  · -- inr, inr
    rw [collapse_app_coprodInr, collapse_app_coprodInr] at huv
    have hx : (cylEnd false pt).app (op (Box.ob n)) x = (cylEnd false pt).app (op (Box.ob n)) y :=
      app_injective_of_mono juncB n huv
    exact congrArg _ (cylEnd_app_injective false pt hx)

/-! ### The merge cobordism `mergeCob : (pt ⨿ pt) ⇒c pt`

`mergeMid := pushout (cylEnd true S) collapse`, the `Cospan.comp` of the cylinder
cospan on `S` with the *collapse cospan* `Cospan.of collapse (sink-leg)`.  Source leg
= bottom of `Cyl S` (mono); sink leg = the apex `∗` reached through the `b`-edge
(mono).  The source collar is the mono pushout injection `p₁ : Cyl S ↪ mergeMid`; the
sink collar is the `b`-edge `Cyl pt ↪ junc ↪ mergeMid`.  The sieve/cosieve fields are
discharged by the barrier lemmas of `Composition.lean`. -/

/-- Abbreviation `S := pt ⨿ pt`, the two-vertex source. -/
noncomputable abbrev mergeSrc : PrecubicalSet := pt ⨿ pt

/-- The cylinder cospan on `S` — the first stage of the merge. -/
noncomputable abbrev mergeC₁ : Cospan mergeSrc mergeSrc := cylCospan mergeSrc

/-- The **collapse cospan** `S ⇒ pt` — the second stage: source leg the collapse
`collapse`, sink leg the `b`-edge into the apex `∗`. -/
noncomputable def mergeC₂ : Cospan mergeSrc pt :=
  Cospan.of collapse (cylEnd true pt ≫ juncB)

@[simp] theorem mergeC₂_mid : mergeC₂.mid = junc := rfl
@[simp] theorem mergeC₂_inl : mergeC₂.inl = collapse := rfl
@[simp] theorem mergeC₂_inr : mergeC₂.inr = cylEnd true pt ≫ juncB := rfl

/-- The merge middle: glue the *top* of `Cyl S` to the collapse-image in the
junction. -/
noncomputable abbrev mergeMid : PrecubicalSet := pushout mergeC₁.inr mergeC₂.inl

/-- The `Cyl S` injection into `mergeMid` (the source collar; mono since `collapse`
is mono). -/
noncomputable abbrev mergeP₁ : Cyl.obj mergeSrc ⟶ mergeMid :=
  pushout.inl mergeC₁.inr mergeC₂.inl

/-- The junction injection into `mergeMid` (mono since `cylEnd true S` is mono). -/
noncomputable abbrev mergeP₂ : junc ⟶ mergeMid :=
  pushout.inr mergeC₁.inr mergeC₂.inl

/-! ### The apex of `junc` is future-closed (the sink cosieve, by hand)

The merge sink image is the apex `∗`, the *glued top* of `junc` — it is **not**
disjoint from the gluing legs (it *is* the glue point), so the barrier lemmas do not
apply.  We prove directly that the top-end image of `junc` is a cosieve, by
reachability induction lifted through the pushout: every `junc`-cell is a `juncA`- or
`juncB`-cell (joint surjectivity), and on each factor the top end is a cosieve
(`cylEnd_true_isCosieve pt`). -/

/-- Joint surjectivity for `junc`: every `n`-cell is a `juncA`- or `juncB`-cell. -/
theorem junc_cell_cases (n : ℕ) (c : junc.cells n) :
    (∃ a, juncA.app (op (Box.ob n)) a = c) ∨ (∃ b, juncB.app (op (Box.ob n)) b = c) :=
  Types.eq_or_eq_of_isPushout
    ((IsPushout.of_hasPushout (cylEnd true pt) (cylEnd true pt)).map
      (F := (evaluation Boxᵒᵖ Type).obj (op (Box.ob n)))) c

/-- The **top image of `junc`**: cells in the image of either edge's top end.  This is
the (glued) apex `{∗}` and its higher-dimensional incarnations. -/
def juncTop (z : junc.TotalCell) : Prop :=
  (∃ c, mapCell (cylEnd true pt ≫ juncA) c = z) ∨ (∃ c, mapCell (cylEnd true pt ≫ juncB) c = z)

/-- A cell in the top image of the `a`-edge is in `juncTop`. -/
theorem juncTop_of_a {z : junc.TotalCell} (h : ∃ c, mapCell (cylEnd true pt ≫ juncA) c = z) :
    juncTop z := Or.inl h

/-- A cell in the top image of the `b`-edge is in `juncTop`. -/
theorem juncTop_of_b {z : junc.TotalCell} (h : ∃ c, mapCell (cylEnd true pt ≫ juncB) c = z) :
    juncTop z := Or.inr h

/-- The image of `cylEnd true pt` in `Cyl pt` (the top end) is a cosieve — this is
`cylEnd_true_isCosieve pt`, restated as a predicate. -/
theorem cylPt_top_isCosieve :
    IsCosieve (Cyl.obj pt) (fun z => ∃ c, mapCell (cylEnd true pt) c = z) :=
  cylEnd_true_isCosieve pt

/-- **Top membership on an edge is future-closed *through* the edge inclusion.**  For a
mono edge inclusion `J : Cyl pt ⟶ junc`, the `J`-image of the top cosieve of `Cyl pt`
is closed under any `junc`-reachability step whose *bigger* cell also lies on the same
edge `J`.  (The cross-edge case never arises for `J`-lifted top cells, since the only
shared cells of the two edges are tops, which stay on both edges.)  This is the single
inductive engine for `juncTop_isCosieve`. -/
private theorem juncEdge_top_step {J : Cyl.obj pt ⟶ junc} [Mono J]
    {n : ℕ} (i : Fin (n + 1)) (c : junc.cells (n + 1)) (cⱼ : (Cyl.obj pt).cells (n + 1))
    (hcⱼ : J.app (op (Box.ob (n + 1))) cⱼ = c) :
    (∃ w, mapCell (cylEnd true pt ≫ J) w = (⟨n, junc.faceMap false i c⟩ : junc.TotalCell)) →
      ∃ w, mapCell (cylEnd true pt ≫ J) w = (⟨n + 1, c⟩ : junc.TotalCell) := by
  rintro ⟨w, hw⟩
  rw [mapCell_comp] at hw
  -- `hw : mapCell J (mapCell (cylEnd true pt) w) = ⟨n, faceMap false i c⟩`.
  obtain ⟨w', hw'eq, hw'app⟩ := mapCell_eq_sigma J (mapCell (cylEnd true pt) w) hw
  -- `w'` is the `Cyl pt`-cell whose `J`-image is `faceMap false i c`.
  have hface : junc.faceMap false i c
      = J.app (op (Box.ob n)) ((Cyl.obj pt).faceMap false i cⱼ) := by
    rw [← hcⱼ, map_faceMap J false i cⱼ]
  have hw'top : w' = (Cyl.obj pt).faceMap false i cⱼ :=
    app_injective_of_mono J n (hw'app.trans hface)
  -- `mapCell (cylEnd true pt) w = ⟨n, w'⟩ = ⟨n, faceMap false i cⱼ⟩` is a top cell;
  -- the top cosieve of `Cyl pt` pushes membership up to `cⱼ`.
  have htop_face : ∃ d, mapCell (cylEnd true pt) d
      = (⟨n, (Cyl.obj pt).faceMap false i cⱼ⟩ : (Cyl.obj pt).TotalCell) :=
    ⟨w, by rw [hw'eq, hw'top]⟩
  obtain ⟨d, hd⟩ := cylPt_top_isCosieve _ _ (Reaches.source i cⱼ) htop_face
  exact ⟨d, by rw [mapCell_comp, hd, mapCell_mk, hcⱼ]⟩

/-- Dual edge-step for a `target` reachability move. -/
private theorem juncEdge_top_step_target {J : Cyl.obj pt ⟶ junc} [Mono J]
    {n : ℕ} (i : Fin (n + 1)) (c : junc.cells (n + 1)) (cⱼ : (Cyl.obj pt).cells (n + 1))
    (hcⱼ : J.app (op (Box.ob (n + 1))) cⱼ = c) :
    (∃ w, mapCell (cylEnd true pt ≫ J) w = (⟨n + 1, c⟩ : junc.TotalCell)) →
      ∃ w, mapCell (cylEnd true pt ≫ J) w = (⟨n, junc.faceMap true i c⟩ : junc.TotalCell) := by
  rintro ⟨w, hw⟩
  rw [mapCell_comp] at hw
  obtain ⟨w', hw'eq, hw'app⟩ := mapCell_eq_sigma J (mapCell (cylEnd true pt) w) hw
  have hw'c : w' = cⱼ := app_injective_of_mono J (n + 1) (hw'app.trans hcⱼ.symm)
  have htop_c : ∃ d, mapCell (cylEnd true pt) d
      = (⟨n + 1, cⱼ⟩ : (Cyl.obj pt).TotalCell) :=
    ⟨w, by rw [hw'eq, hw'c]⟩
  obtain ⟨d, hd⟩ := cylPt_top_isCosieve _ _ (Reaches.target i cⱼ) htop_c
  refine ⟨d, ?_⟩
  rw [mapCell_comp, hd, mapCell_mk]
  exact congrArg (Sigma.mk n) (by rw [← hcⱼ, map_faceMap J true i cⱼ])

/-- **The apex of `junc` is future-closed.**  `juncTop` is a cosieve: a directed step
out of a top cell stays in the top.  We lift the bigger cell to its `juncA`/`juncB`
factor (`junc_cell_cases`); since the two top images coincide at the glued apex
(`pushout.condition`), the lifted cell is top on whichever edge it sits, and the
per-edge engine `juncEdge_top_step(_target)` carries membership across the step. -/
theorem juncTop_isCosieve : IsCosieve junc juncTop := by
  -- The two top images coincide: `cylEnd true pt ≫ juncA = cylEnd true pt ≫ juncB`.
  have hcond : cylEnd true pt ≫ juncA = cylEnd true pt ≫ juncB :=
    pushout.condition (f := cylEnd true pt) (g := cylEnd true pt)
  intro x y hxy
  induction hxy with
  | refl x => exact id
  | @source n i c =>
      intro hx
      rcases junc_cell_cases (n + 1) c with ⟨cₐ, hcₐ⟩ | ⟨cᵦ, hcᵦ⟩
      · refine juncTop_of_a (juncEdge_top_step i c cₐ hcₐ ?_)
        rcases hx with h | h
        · exact h
        · rwa [← hcond] at h
      · refine juncTop_of_b (juncEdge_top_step i c cᵦ hcᵦ ?_)
        rcases hx with h | h
        · rwa [hcond] at h
        · exact h
  | @target n i c =>
      intro hx
      rcases junc_cell_cases (n + 1) c with ⟨cₐ, hcₐ⟩ | ⟨cᵦ, hcᵦ⟩
      · refine juncTop_of_a (juncEdge_top_step_target i c cₐ hcₐ ?_)
        rcases hx with h | h
        · exact h
        · rwa [← hcond] at h
      · refine juncTop_of_b (juncEdge_top_step_target i c cᵦ hcᵦ ?_)
        rcases hx with h | h
        · rwa [hcond] at h
        · exact h
  | @trans x v w _hxv _hvw ihxv ihvw =>
      intro hPx
      exact ihvw (ihxv hPx)

/-- The merge-`C₂` sink image is exactly `juncTop`: the sink leg is the `b`-edge top,
whose image coincides with the `a`-edge top at the glued apex (`pushout.condition`). -/
theorem mergeC₂_sinkImage_eq : mergeC₂.sinkImage = juncTop := by
  have hcond : cylEnd true pt ≫ juncA = cylEnd true pt ≫ juncB :=
    pushout.condition (f := cylEnd true pt) (g := cylEnd true pt)
  funext z
  apply propext
  constructor
  · rintro ⟨y, hy⟩; exact juncTop_of_b ⟨y, hy⟩
  · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
    · refine ⟨c, ?_⟩
      change mapCell (cylEnd true pt ≫ juncB) c = z
      rw [← hc, ← hcond]
    · exact ⟨c, hc⟩

/-- **`mergeC₂` has a sink cosieve.** -/
theorem mergeC₂_sinkCosieve : mergeC₂.SinkCosieve := by
  rw [Cospan.SinkCosieve, mergeC₂_sinkImage_eq]
  exact juncTop_isCosieve

/-- **The merge-`C₂` legs are disjoint.**  The source leg `collapse` lands in the two
*bottom* vertices `{p, q}` of `junc`; the sink leg lands in the *apex* `∗` (a top).
A collision would equate a bottom and the apex, contradicting `cylEnd_disjoint pt`
through the van-Kampen pullback. -/
theorem mergeC₂_legsDisjoint : mergeC₂.LegsDisjoint := by
  intro n s y hcollide
  -- `s : (pt ⨿ pt).cells n`, `y : pt.cells n`.
  -- `mergeC₂.inr.app y = (cylEnd true pt ≫ juncB).app y = juncB (cylEnd true pt y)`.
  -- `mergeC₂.inl = collapse`, `mergeC₂.inr = cylEnd true pt ≫ juncB`.
  change collapse.app (op (Box.ob n)) s
    = (cylEnd true pt ≫ juncB).app (op (Box.ob n)) y at hcollide
  rw [NatTrans.comp_app, types_comp_apply] at hcollide
  rcases coprod_cell_cases s with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · -- `collapse (inl x) = juncA (cylEnd false pt x)`; the sink is `juncB (cylEnd true pt y)`.
    rw [collapse_app_coprodInl] at hcollide
    obtain ⟨w, hw₁, _hw₂⟩ :=
      Types.exists_of_isPullback (junc_isPullback_app n)
        ((cylEnd false pt).app (op (Box.ob n)) x)
        ((cylEnd true pt).app (op (Box.ob n)) y) hcollide
    exact cylEnd_disjoint pt x w hw₁.symm
  · rw [collapse_app_coprodInr] at hcollide
    -- `juncB (cylEnd false pt x) = juncB (cylEnd true pt y)` ⟹ `juncB` mono ⟹ false=true end.
    have := app_injective_of_mono juncB n hcollide
    exact cylEnd_disjoint pt x y this

/-! ### Tier 1 — the merge cobordism

We assemble `mergeCob : DirectedCobordism (pt ⨿ pt) pt` with underlying cospan
`mergeC₁.comp mergeC₂`.  The source sieve / sink cosieve are discharged by the
barrier lemmas (`pushout_inl_image_isSieve` / `pushout_inr_image_isCosieve`) exactly
as in `DirectedCobordism.comp`, fed the cylinder source-sieve and the (hand-built)
junction sink-cosieve; the collars are the two (mono) pushout injections. -/

/-- **Tier 1 — the merge cobordism** `(pt ⨿ pt) ⇒c pt`.  Source leg = bottom of
`Cyl S`; sink leg = the junction apex `∗` (through the `b`-edge top).  The source
collar is the mono pushout injection `mergeP₁ : Cyl S ↪ mergeMid` (its tops `p ≠ q`
survive, glued onto the junction's distinct bottoms), so the merge happens strictly
above the collar tops. -/
noncomputable def mergeCob : DirectedCobordism mergeSrc pt where
  toCospan := mergeC₁.comp mergeC₂
  legsDisjoint :=
    Cospan.LegsDisjoint.comp (cylCospan_legsDisjoint mergeSrc) mergeC₂_legsDisjoint
  srcSieve := by
    rw [Cospan.SrcSieve, comp_srcImage_eq]
    refine pushout_inl_image_isSieve mergeC₁ mergeC₂ mergeC₁.srcImage
      (cylEnd_false_isSieve mergeSrc) ?_
    -- source/sink ends of the cylinder cospan are disjoint.
    rintro a y hy ⟨x, hx⟩
    obtain ⟨m, a'⟩ := a
    obtain ⟨x', rfl, hx''⟩ := mapCell_eq_sigma mergeC₁.inl x hx
    exact cylCospan_legsDisjoint mergeSrc x' y (hx''.trans hy.symm)
  sinkCosieve := by
    rw [Cospan.SinkCosieve, comp_sinkImage_eq]
    refine pushout_inr_image_isCosieve mergeC₁ mergeC₂ mergeC₂.sinkImage
      mergeC₂_sinkCosieve ?_
    -- the merge-`C₂` legs are disjoint, so the sink image avoids the gluing image.
    rintro b y hy ⟨z, hz⟩
    obtain ⟨m, b'⟩ := b
    obtain ⟨z', rfl, hz''⟩ := mapCell_eq_sigma mergeC₂.inr z hz
    exact mergeC₂_legsDisjoint y z' (hy.trans hz''.symm)
  srcCollar :=
    { collar := mergeP₁
      mono := comp_pushout_inl_mono mergeC₁ mergeC₂
      bottom := by
        -- `(mergeC₁.comp mergeC₂).inl = cylEnd false S ≫ mergeP₁`.
        rw [Cospan.comp_inl]; rfl }
  sinkCollar :=
    { collar := juncB ≫ mergeP₂
      mono := mono_comp' (inferInstance) (comp_pushout_inr_mono mergeC₁ mergeC₂)
      top := by
        -- `cylEnd true pt ≫ (juncB ≫ mergeP₂) = (cylEnd true pt ≫ juncB) ≫ mergeP₂`.
        rw [Cospan.comp_inr, ← Category.assoc]; rfl }

@[simp] theorem mergeCob_toCospan : mergeCob.toCospan = mergeC₁.comp mergeC₂ := rfl

@[simp] theorem mergeCob_inl :
    mergeCob.inl = cylEnd false mergeSrc ≫ mergeP₁ := rfl

@[simp] theorem mergeCob_inr :
    mergeCob.inr = (cylEnd true pt ≫ juncB) ≫ mergeP₂ := rfl

/-! ### Tier 2 — the `π₀` obstruction

`π₀ S` has (at least) two classes: the two coproduct summands are
reachability-disjoint.  And `π₀.map mergeCob.inl` is **not** injective: the two
source vertices `a`, `b` both rise (through their columns and the junction) to the
common apex `∗`, so they land in the same component of `mergeMid`. -/

/-- The "lives in the left summand" predicate on total cells of `S = pt ⨿ pt`. -/
def InInl (z : (pt ⨿ pt).TotalCell) : Prop := ∃ a, z.2 = FunctorToTypes.coprodInl a

/-- A face of a `coprodInl` cell is a `coprodInl` cell (`coprod.inl` is precubical). -/
theorem coprodInl_faceMap (ε : Bool) {n : ℕ} (i : Fin (n + 1)) (a : pt.cells (n + 1)) :
    (pt ⨿ pt).faceMap ε i (FunctorToTypes.coprodInl a)
      = FunctorToTypes.coprodInl (pt.faceMap ε i a) := by
  rw [coprodInl_eq_inl_app, coprodInl_eq_inl_app, faceMap, faceMap]
  exact (NatTrans.naturality_apply (coprod.inl : pt ⟶ pt ⨿ pt) (coface ε i).op a).symm

/-- A face of a `coprodInr` cell is a `coprodInr` cell. -/
theorem coprodInr_faceMap (ε : Bool) {n : ℕ} (i : Fin (n + 1)) (b : pt.cells (n + 1)) :
    (pt ⨿ pt).faceMap ε i (FunctorToTypes.coprodInr b)
      = FunctorToTypes.coprodInr (pt.faceMap ε i b) := by
  rw [coprodInr_eq_inr_app, coprodInr_eq_inr_app, faceMap, faceMap]
  exact (NatTrans.naturality_apply (coprod.inr : pt ⟶ pt ⨿ pt) (coface ε i).op b).symm

/-- **`InInl` is invariant under any face relation.**  `faceMap ε i c` is in the left
summand iff `c` is (faces never cross between coproduct summands). -/
theorem inInl_face_iff (ε : Bool) {n : ℕ} (i : Fin (n + 1)) (c : (pt ⨿ pt).cells (n + 1)) :
    InInl ⟨n, (pt ⨿ pt).faceMap ε i c⟩ ↔ InInl ⟨n + 1, c⟩ := by
  rcases coprod_cell_cases c with ⟨c', rfl⟩ | ⟨c', rfl⟩
  · constructor
    · intro _; exact ⟨c', rfl⟩
    · intro _; exact ⟨pt.faceMap ε i c', coprodInl_faceMap ε i c'⟩
  · constructor
    · rintro ⟨a, ha⟩
      rw [coprodInr_faceMap] at ha
      exact absurd ha.symm (coprodInl_ne_coprodInr a _)
    · rintro ⟨a, ha⟩
      exact absurd ha.symm (coprodInl_ne_coprodInr a c')

/-- `InInl` is invariant under a single `Reaches` step (both directions): the left
summand is clopen for the directed structure of the coproduct `pt ⨿ pt`. -/
theorem inInl_reaches_iff {x y : (pt ⨿ pt).TotalCell} (h : Reaches (pt ⨿ pt) x y) :
    InInl x ↔ InInl y := by
  induction h with
  | refl x => rfl
  | @source n i c => exact inInl_face_iff false i c
  | @target n i c => exact (inInl_face_iff true i c).symm
  | @trans x v w _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `InInl` descends to the generated vertex equivalence on `π₀ S`. -/
theorem inInl_eqvGen_iff {v w : (pt ⨿ pt).cells 0}
    (h : Relation.EqvGen (VertexReaches (pt ⨿ pt)) v w) :
    InInl ⟨0, v⟩ ↔ InInl ⟨0, w⟩ := by
  induction h with
  | rel a b hab => exact inInl_reaches_iff hab
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Tier 2a — `π₀ S` has at least two classes.**  The two source vertices `a`, `b`
of `S = pt ⨿ pt` lie in distinct connected components: a left-summand vertex is never
generated-equivalent to a right-summand vertex (`InInl` separates them). -/
theorem π₀_src_two_classes (v w : pt.cells 0) :
    π₀.mk (FunctorToTypes.coprodInl v : (pt ⨿ pt).cells 0)
      ≠ π₀.mk (FunctorToTypes.coprodInr w) := by
  intro heq
  have hrel : Relation.EqvGen (VertexReaches (pt ⨿ pt))
      (FunctorToTypes.coprodInl v) (FunctorToTypes.coprodInr w) :=
    Quotient.exact heq
  have hiff := inInl_eqvGen_iff hrel
  -- LHS is `InInl`, RHS is not.
  have hL : InInl ⟨0, (FunctorToTypes.coprodInl v : (pt ⨿ pt).cells 0)⟩ := ⟨v, rfl⟩
  have hR : ¬ InInl ⟨0, (FunctorToTypes.coprodInr w : (pt ⨿ pt).cells 0)⟩ := by
    rintro ⟨a, ha⟩
    exact coprodInl_ne_coprodInr a w ha.symm
  exact hR (hiff.1 hL)

/-! ### A vertex's bottom reaches its top in the cylinder

The tube over a vertex `v` is a `1`-cell whose `false`/`true` interval faces are the
bottom and top copies of `v`; so `bot v → tube → top v` is a directed path. -/

/-- **Bottom reaches top in `Cyl X`.**  For a vertex `v`, the bottom copy
`cylEnd false X v` reaches the top copy `cylEnd true X v` along the tube `1`-cell. -/
theorem cyl_bot_reaches_top (X : PrecubicalSet) (v : X.cells 0) :
    Reaches (Cyl.obj X) ⟨0, (cylEnd false X).app (op (Box.ob 0)) v⟩
      ⟨0, (cylEnd true X).app (op (Box.ob 0)) v⟩ := by
  -- The tube `1`-cell `e` over `v` (`v` lives in `(realize.obj X).cells 0 = X.cells 0`).
  set v' : (realize.obj X).cells 0 := v with hv'
  set e : (Cyl.obj X).cells 1 := (cylCellEquiv X 1).symm (cellTube v') with he
  have hev : cylCellEquiv X 1 e = cellTube v' := by rw [he, Equiv.apply_symm_apply]
  -- Its `false`-interval face is the bottom copy of `v`.
  have hbot : (Cyl.obj X).faceMap false (Fin.last 0) e
      = (cylEnd false X).app (op (Box.ob 0)) v := by
    apply (cylCellEquiv X 0).injective
    rw [cylCellEquiv_faceMap, hev, cylCellEquiv_cylEnd false X v, cond_false]
    -- `cylFace … (cellTube v) = tubeFace false (last 0) v = cellBot v`.
    change tubeFace (realize.obj X) false (Fin.last 0) v = _
    rw [tubeFace_last_gen, cond_false]
  have htop : (Cyl.obj X).faceMap true (Fin.last 0) e
      = (cylEnd true X).app (op (Box.ob 0)) v := by
    apply (cylCellEquiv X 0).injective
    rw [cylCellEquiv_faceMap, hev, cylCellEquiv_cylEnd true X v, cond_true]
    change tubeFace (realize.obj X) true (Fin.last 0) v = _
    rw [tubeFace_last_gen, cond_true]
  -- `bot v → e → top v`.
  refine Reaches.trans (y := ⟨1, e⟩) ?_ ?_
  · rw [← hbot]; exact Reaches.source (Fin.last 0) e
  · rw [← htop]; exact Reaches.target (Fin.last 0) e

/-! ### Tier 2b — the source leg is not `π₀`-injective

Both source vertices rise to the common apex `∗ = mergeP₂ (juncA (top))`:
`inl a → top(a) = collapse a = p → ∗` and `inl b → top(b) = collapse b = q → ∗`,
where the two apex copies agree by `pushout.condition`. -/

/-- The single chosen vertex of `pt`. -/
noncomputable def ptVertex : pt.cells 0 := 𝟙 (Box.ob 0)

/-- The merge gluing identity at a source vertex: `mergeP₁ (top S v)` is `mergeP₂` of
the collapse-image of `v`. -/
theorem mergeP₁_top_eq_mergeP₂_collapse (v : (pt ⨿ pt).cells 0) :
    mergeP₁.app (op (Box.ob 0)) ((cylEnd true mergeSrc).app (op (Box.ob 0)) v)
      = mergeP₂.app (op (Box.ob 0)) (collapse.app (op (Box.ob 0)) v) := by
  have hc : mergeC₁.inr ≫ mergeP₁ = mergeC₂.inl ≫ mergeP₂ :=
    pushout.condition (f := mergeC₁.inr) (g := mergeC₂.inl)
  have := NatTrans.congr_app hc (op (Box.ob 0))
  apply_fun (fun φ => φ v) at this
  simpa using this

/-- Reachability from a source vertex `inl s` up to the apex `mergeP₂ (J (top))`,
on whichever edge `s`'s collapse-image sits (`J = juncA`/`juncB`, `v` the underlying
`pt`-vertex). -/
theorem src_reaches_apex (s : (pt ⨿ pt).cells 0) (v : pt.cells 0) (J : Cyl.obj pt ⟶ junc)
    (hJ : collapse.app (op (Box.ob 0)) s
      = J.app (op (Box.ob 0)) ((cylEnd false pt).app (op (Box.ob 0)) v)) :
    Reaches mergeMid
      ⟨0, mergeCob.inl.app (op (Box.ob 0)) s⟩
      ⟨0, mergeP₂.app (op (Box.ob 0)) (J.app (op (Box.ob 0))
        ((cylEnd true pt).app (op (Box.ob 0)) v))⟩ := by
  -- Step 1+2: `inl s = mergeP₁ (bot S s) → mergeP₁ (top S s)`.
  have h12 : Reaches mergeMid
      ⟨0, mergeCob.inl.app (op (Box.ob 0)) s⟩
      ⟨0, mergeP₁.app (op (Box.ob 0))
        ((cylEnd true mergeSrc).app (op (Box.ob 0)) s)⟩ := by
    have hbt := cyl_bot_reaches_top mergeSrc s
    have := hbt.map mergeP₁
    simpa [mapCell, mergeCob_inl, NatTrans.comp_app, types_comp_apply] using this
  -- Step 3: gluing `mergeP₁ (top S s) = mergeP₂ (collapse s) = mergeP₂ (J (bot pt v))`.
  rw [mergeP₁_top_eq_mergeP₂_collapse, hJ] at h12
  -- Step 5+6: in junc via `J`, `J (bot pt v) → J (top pt v)`, mapped by `mergeP₂`.
  have h56 : Reaches mergeMid
      ⟨0, mergeP₂.app (op (Box.ob 0))
        (J.app (op (Box.ob 0)) ((cylEnd false pt).app (op (Box.ob 0)) v))⟩
      ⟨0, mergeP₂.app (op (Box.ob 0))
        (J.app (op (Box.ob 0)) ((cylEnd true pt).app (op (Box.ob 0)) v))⟩ := by
    have hbt := cyl_bot_reaches_top pt v
    have hJr := hbt.map J
    have := hJr.map mergeP₂
    simpa [mapCell, NatTrans.comp_app, types_comp_apply] using this
  exact h12.trans h56

/-- The two apex copies agree: `mergeP₂ (juncA (top pt v))` and
`mergeP₂ (juncB (top pt v))` are equal (`pushout.condition` for `junc`). -/
theorem mergeP₂_juncA_top_eq_juncB_top (v : pt.cells 0) :
    mergeP₂.app (op (Box.ob 0)) (juncA.app (op (Box.ob 0))
        ((cylEnd true pt).app (op (Box.ob 0)) v))
      = mergeP₂.app (op (Box.ob 0)) (juncB.app (op (Box.ob 0))
        ((cylEnd true pt).app (op (Box.ob 0)) v)) := by
  have hcond : cylEnd true pt ≫ juncA = cylEnd true pt ≫ juncB :=
    pushout.condition (f := cylEnd true pt) (g := cylEnd true pt)
  have := NatTrans.congr_app hcond (op (Box.ob 0))
  apply_fun (fun φ => mergeP₂.app (op (Box.ob 0)) (φ v)) at this
  simpa using this

/-- **Tier 2b — the source leg is not `π₀`-injective.**  `π₀.map mergeCob.inl` sends
both source classes `mk a` and `mk b` to the apex class `mk ∗`, while `mk a ≠ mk b`. -/
theorem mergeCob_inl_π₀_not_injective :
    ¬ Function.Injective (π₀.map mergeCob.inl) := by
  intro hinj
  -- `inl a → apex` (a-edge) and `inl b → apex` (b-edge), to the SAME apex.
  have hAa : collapse.app (op (Box.ob 0)) (FunctorToTypes.coprodInl ptVertex)
      = juncA.app (op (Box.ob 0)) ((cylEnd false pt).app (op (Box.ob 0)) ptVertex) :=
    collapse_app_coprodInl ptVertex
  have hBb : collapse.app (op (Box.ob 0)) (FunctorToTypes.coprodInr ptVertex)
      = juncB.app (op (Box.ob 0)) ((cylEnd false pt).app (op (Box.ob 0)) ptVertex) :=
    collapse_app_coprodInr ptVertex
  have hReachA := src_reaches_apex (FunctorToTypes.coprodInl ptVertex) ptVertex juncA hAa
  have hReachB := src_reaches_apex (FunctorToTypes.coprodInr ptVertex) ptVertex juncB hBb
  -- Both reach the same apex (`mergeP₂_juncA_top_eq_juncB_top`).
  rw [mergeP₂_juncA_top_eq_juncB_top ptVertex] at hReachA
  -- `mk (inl a) = mk apex = mk (inl b)` in `π₀ mergeMid`.
  have hπa : π₀.map mergeCob.inl (π₀.mk (FunctorToTypes.coprodInl ptVertex))
      = π₀.map mergeCob.inl (π₀.mk (FunctorToTypes.coprodInr ptVertex)) := by
    rw [π₀.map_mk, π₀.map_mk]
    exact (π₀.sound hReachA).trans (π₀.sound hReachB).symm
  -- Injectivity would force `mk a = mk b`, contradicting `π₀_src_two_classes`.
  exact π₀_src_two_classes ptVertex ptVertex (hinj hπa)

/-! ### `idCob` keeps the two source components apart

`S = pt ⨿ pt` is *discrete* (no cells above dimension `0`, since `pt.cells (n+1)`
is empty), so `Cyl S` is two disjoint intervals.  The "underlying summand" of a
`Cyl S`-cell (bottom/top/tube of an `S`-cell) is `Reaches`-invariant, separating the
two columns; hence `π₀.map (cylEnd false S) = π₀.map (idCob S).inl` is injective. -/

/-- `S = pt ⨿ pt` has no cells above dimension `0`. -/
instance mergeSrc_cells_succ_isEmpty (n : ℕ) : IsEmpty (mergeSrc.cells (n + 1)) := by
  constructor
  intro c
  rcases coprod_cell_cases c with ⟨x, _⟩ | ⟨x, _⟩ <;> exact (pt_cells_succ_isEmpty n).false x

/-- The underlying-summand predicate on a *concrete* cylinder cell of `realize S`:
bottom/top of a left `S`-cell, or a tube over one (`tube` at dimension `0` is empty).
This descends `InInl` through `cylCellEquiv`. -/
def cellInInl : ∀ {n : ℕ}, cell (realize.obj mergeSrc) n → Prop
  | _, Sum.inl c => InInl ⟨_, c⟩
  | _, Sum.inr (Sum.inl c) => InInl ⟨_, c⟩
  | 0, Sum.inr (Sum.inr t) => t.elim
  | _ + 1, Sum.inr (Sum.inr t) => InInl ⟨_, (t : mergeSrc.cells _)⟩

/-- The "lives over the left summand" predicate on `Cyl S`-cells. -/
def InInlCyl (z : (Cyl.obj mergeSrc).TotalCell) : Prop :=
  cellInInl (cylCellEquiv mergeSrc z.1 z.2)

@[simp] theorem cellInInl_bot {n : ℕ} (c : mergeSrc.cells n) :
    cellInInl (cellBot c : cell (realize.obj mergeSrc) n) = InInl ⟨n, c⟩ := rfl

@[simp] theorem cellInInl_top {n : ℕ} (c : mergeSrc.cells n) :
    cellInInl (cellTop c : cell (realize.obj mergeSrc) n) = InInl ⟨n, c⟩ := rfl

@[simp] theorem cellInInl_tube {m : ℕ} (t : mergeSrc.cells m) :
    cellInInl (cellTube t : cell (realize.obj mergeSrc) (m + 1)) = InInl ⟨m, t⟩ := rfl

/-- A cylinder face preserves the underlying summand (`cellInInl`).  For `S` discrete
the `K`-coordinate tube face (`castSucc`) is over an empty `S.cells (m+1)`, and the
interval (`last`) tube face caps the tube to a bot/top of the same underlying vertex. -/
theorem cellInInl_cylFace (ε : Bool) {n : ℕ} (i : Fin (n + 1))
    (z : cell (realize.obj mergeSrc) (n + 1)) :
    cellInInl (cylFace (realize.obj mergeSrc) ε i z) ↔ cellInInl z := by
  match z with
  | Sum.inl c =>
      rw [cylFace_bot, cellInInl_bot, cellInInl_bot]
      exact inInl_face_iff ε i c
  | Sum.inr (Sum.inl c) =>
      rw [cylFace_top, cellInInl_top, cellInInl_top]
      exact inInl_face_iff ε i c
  | Sum.inr (Sum.inr t) =>
      -- `t : tube (realize S) (n+1) = S.cells n`.
      rw [cylFace_tube, cellInInl_tube]
      induction i using Fin.lastCases with
      | last =>
          rw [tubeFace_last_gen]
          cases ε with
          | false => rw [cond_false, cellInInl_bot]
          | true => rw [cond_true, cellInInl_top]
      | cast i' =>
          -- `K`-coordinate face: tube over `S.face ε i' t`, but a `K`-coordinate
          -- needs `t : S.cells (n+1)`, which is empty for `S` discrete.
          rcases n with _ | p
          · exact i'.elim0
          · exact (mergeSrc_cells_succ_isEmpty p).elim t

/-- `InInlCyl` of a `Cyl S`-face equals `InInlCyl` of the cell (read through
`cylCellEquiv_faceMap`). -/
theorem inInlCyl_face_iff (ε : Bool) {n : ℕ} (i : Fin (n + 1))
    (c : (Cyl.obj mergeSrc).cells (n + 1)) :
    InInlCyl ⟨n, (Cyl.obj mergeSrc).faceMap ε i c⟩ ↔ InInlCyl ⟨n + 1, c⟩ := by
  unfold InInlCyl
  rw [cylCellEquiv_faceMap]
  exact cellInInl_cylFace ε i (cylCellEquiv mergeSrc (n + 1) c)

/-- `InInlCyl` is invariant under a single `Reaches (Cyl S)` step (both directions). -/
theorem inInlCyl_reaches_iff {x y : (Cyl.obj mergeSrc).TotalCell}
    (h : Reaches (Cyl.obj mergeSrc) x y) : InInlCyl x ↔ InInlCyl y := by
  induction h with
  | refl x => rfl
  | @source n i c => exact inInlCyl_face_iff false i c
  | @target n i c => exact (inInlCyl_face_iff true i c).symm
  | @trans x v w _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `InInlCyl` descends to the generated vertex equivalence on `π₀ (Cyl S)`. -/
theorem inInlCyl_eqvGen_iff {v w : (Cyl.obj mergeSrc).cells 0}
    (h : Relation.EqvGen (VertexReaches (Cyl.obj mergeSrc)) v w) :
    InInlCyl ⟨0, v⟩ ↔ InInlCyl ⟨0, w⟩ := by
  induction h with
  | rel a b hab => exact inInlCyl_reaches_iff hab
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The bottom end of a left-summand vertex `is `InInlCyl`. -/
theorem inInlCyl_bot_coprodInl (v : pt.cells 0) :
    InInlCyl ⟨0, (cylEnd false mergeSrc).app (op (Box.ob 0)) (FunctorToTypes.coprodInl v)⟩ := by
  unfold InInlCyl
  rw [cylCellEquiv_cylEnd false mergeSrc, cond_false, cellInInl_bot]
  exact ⟨v, rfl⟩

/-- The bottom end of a right-summand vertex is *not* `InInlCyl`. -/
theorem not_inInlCyl_bot_coprodInr (v : pt.cells 0) :
    ¬ InInlCyl ⟨0, (cylEnd false mergeSrc).app (op (Box.ob 0)) (FunctorToTypes.coprodInr v)⟩ := by
  unfold InInlCyl
  rw [cylCellEquiv_cylEnd false mergeSrc, cond_false, cellInInl_bot]
  rintro ⟨a, ha⟩
  exact coprodInl_ne_coprodInr a v ha.symm

/-- `pt` has a **single** vertex: a `Box`-map `Box.ob 0 ⟶ Box.ob 0` is determined by
its value on the top cell, which lives in the singleton `StdCube.cells 0 0`. -/
instance pt_cells_zero_subsingleton : Subsingleton (pt.cells 0) := by
  constructor
  intro f g
  -- `f, g : Box.ob 0 ⟶ Box.ob 0`, i.e. `stdPre 0 ⟶ stdPre 0`.
  apply PrecubicalConstructions.hom_ext
  intro k a
  rw [StdCube.app_unique f rfl a, StdCube.app_unique g ?_ a]
  -- both top-cell values lie in the singleton `cells 0 0` (`eq_topCell`).
  rw [StdCube.eq_topCell (PrecubicalConstructions.Hom.app g 0 (StdCube.topCell 0)),
    StdCube.eq_topCell (PrecubicalConstructions.Hom.app f 0 (StdCube.topCell 0))]

/-- **`idCob` keeps the two source components apart.**  `π₀.map (idCob S).inl
= π₀.map (cylEnd false S)` is injective: distinct summand classes map to distinct
`Cyl S`-components (`InInlCyl` separates the two columns). -/
theorem idCob_src_π₀_injective :
    Function.Injective (π₀.map (idCob mergeSrc).inl) := by
  intro p₁ p₂ h
  obtain ⟨v, rfl⟩ := π₀.mk_surjective p₁
  obtain ⟨w, rfl⟩ := π₀.mk_surjective p₂
  -- `idCob.inl = cylEnd false S`; the hypothesis is `mk (bot v) = mk (bot w)`.
  rw [idCob_inl, π₀.map_mk, π₀.map_mk] at h
  have heqv : Relation.EqvGen (VertexReaches (Cyl.obj mergeSrc))
      ((cylEnd false mergeSrc).app (op (Box.ob 0)) v)
      ((cylEnd false mergeSrc).app (op (Box.ob 0)) w) := Quotient.exact h
  have hiff := inInlCyl_eqvGen_iff heqv
  -- Case the two source vertices on their summands.
  rcases coprod_cell_cases v with ⟨v', rfl⟩ | ⟨v', rfl⟩ <;>
    rcases coprod_cell_cases w with ⟨w', rfl⟩ | ⟨w', rfl⟩
  · -- both inl: `pt`-vertex subsingleton ⟹ equal vertices.
    rw [Subsingleton.elim v' w']
  · -- inl vs inr: `InInlCyl` disagrees.
    exact absurd (hiff.1 (inInlCyl_bot_coprodInl v')) (not_inInlCyl_bot_coprodInr w')
  · -- inr vs inl: symmetric.
    exact absurd (hiff.2 (inInlCyl_bot_coprodInl w')) (not_inInlCyl_bot_coprodInr v')
  · -- both inr: subsingleton.
    rw [Subsingleton.elim v' w']

/-! ### Tier 3 — non-invertibility

The source-leg `π₀`-injectivity invariant `srcLegπ₀Injective` is preserved by
*boundary-fixing isomorphisms* of cobordisms (the iso generator of `cobordismRel`):
an iso of middles commuting with the source leg post-composes the `π₀`-source-map
with a `π₀`-bijection.  It holds for the cylinder identity `idCob S`
(`idCob_src_π₀_injective`) and fails for the merge (`mergeCob_inl_π₀_not_injective`);
moreover it is **destroyed by composition** — `(mergeCob.comp V).inl` factors through
the non-injective `π₀.map mergeCob.inl`.  Hence the merge is not invertible up to a
boundary-fixing iso of the composite with the identity. -/

/-- The **source-leg `π₀`-injectivity** invariant of a cobordism. -/
def srcLegπ₀Injective {X Y : PrecubicalSet} (W : X ⇒c Y) : Prop :=
  Function.Injective (π₀.map W.inl)

/-- **Boundary-fixing isos preserve the invariant.**  An iso `e : W₁.mid ≅ W₂.mid`
with `W₁.inl ≫ e.hom = W₂.inl` post-composes `π₀.map W₁.inl` with the `π₀`-bijection
`π₀.mapEquiv e`, so injectivity transfers. -/
theorem srcLegπ₀Injective_of_cobIso {X Y : PrecubicalSet} {W₁ W₂ : X ⇒c Y}
    (φ : CobIso W₁ W₂) (h : srcLegπ₀Injective W₁) : srcLegπ₀Injective W₂ := by
  -- `π₀.map W₂.inl = π₀.mapEquiv φ.e ∘ π₀.map W₁.inl`.
  have hcomp : π₀.map W₂.inl = (π₀.mapEquiv φ.e) ∘ π₀.map W₁.inl := by
    rw [← φ.inl_hom, π₀.map_comp]
    rfl
  rw [srcLegπ₀Injective, hcomp]
  exact (π₀.mapEquiv φ.e).injective.comp h

/-- The invariant is symmetric under boundary-fixing isos. -/
theorem srcLegπ₀Injective_cobIso_iff {X Y : PrecubicalSet} {W₁ W₂ : X ⇒c Y}
    (φ : CobIso W₁ W₂) : srcLegπ₀Injective W₁ ↔ srcLegπ₀Injective W₂ :=
  ⟨srcLegπ₀Injective_of_cobIso φ, srcLegπ₀Injective_of_cobIso φ.symm⟩

/-- **Composition destroys source-leg injectivity for the merge.**  `(mergeCob.comp
V).inl = mergeCob.inl ≫ p₁`, so `π₀.map` of it factors through the non-injective
`π₀.map mergeCob.inl`; a composite that is injective would force the factor injective.
-/
theorem mergeComp_not_srcLegπ₀Injective {Y : PrecubicalSet} (V : pt ⇒c Y) :
    ¬ srcLegπ₀Injective (mergeCob.comp V) := by
  intro hinj
  -- `(mergeCob.comp V).inl = mergeCob.inl ≫ pushout.inl mergeCob.inr V.inl`.
  apply mergeCob_inl_π₀_not_injective
  -- `(mergeCob.comp V).inl = mergeCob.inl ≫ pushout.inl mergeCob.inr V.inl`.
  have hleg : (mergeCob.comp V).inl
      = mergeCob.inl ≫ pushout.inl mergeCob.inr V.inl := Cospan.comp_inl _ _
  -- The composite `π₀`-map factors as `π₀.map p₁ ∘ π₀.map mergeCob.inl`.
  have hfac : π₀.map (mergeCob.comp V).inl
      = π₀.map (pushout.inl mergeCob.inr V.inl) ∘ π₀.map mergeCob.inl := by
    rw [hleg]; exact π₀.map_comp _ _
  rw [srcLegπ₀Injective, hfac] at hinj
  -- `g ∘ f` injective ⟹ `f` injective.
  exact Function.Injective.of_comp hinj

/-- **`dCob`-equivalence of a cobordism** (an isomorphism in `dCob`): a two-sided
inverse up to the rel-∂ relation. -/
def IsEquivalenceCob {X Y : PrecubicalSet} (W : X ⇒c Y) : Prop :=
  ∃ V : Y ⇒c X, cobordismRel X X (W.comp V) (idCob X) ∧
    cobordismRel Y Y (V.comp W) (idCob Y)

/-! ### The rel-∂ invariance of `srcLegπ₀Injective`

`srcLegπ₀Injective` is invariant under **every** generator of `cobordismRel`:

* the **iso** generator — `srcLegπ₀Injective_cobIso_iff` (proved above); and
* the **unit** generators (`unitL`/`unitR`) — a π₀ van-Kampen statement
  (prepending/appending a cylinder is a `π₀`-equivalence of middles commuting with
  the source leg), discharged via the `Conjectures` lemmas `dcob_unitL_srcInj_iff` /
  `dcob_unitR_srcInj_iff`.

The full rel-∂ invariance `srcLegπ₀Injective_rel` is then an `EqvGen` induction over
these two generators, and the Tier 3 punchline `merge_not_invertible` follows with
**no extra hypothesis**. -/

/-- **The rel-∂ invariance of `srcLegπ₀Injective`.**  `cobordismRel`-related
cobordisms have the same source-leg `π₀`-injectivity: the iso generator transports it
(`srcLegπ₀Injective_cobIso_iff`) and the unit generators are π₀-van-Kampen equivalences
(`dcob_unitL_srcInj_iff` / `dcob_unitR_srcInj_iff` in `Research/Conjectures.lean`). -/
theorem srcLegπ₀Injective_rel {X Y : PrecubicalSet} {W W' : X ⇒c Y}
    (h : cobordismRel X Y W W') : srcLegπ₀Injective W ↔ srcLegπ₀Injective W' := by
  induction h with
  | rel a b hab =>
      cases hab with
      | iso φ => exact srcLegπ₀Injective_cobIso_iff φ
      | unitL => exact dcob_unitL_srcInj_iff _
      | unitR => exact dcob_unitR_srcInj_iff _
  | refl a => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Tier 3 punchline (unconditional).**  The merge is **not** a `dCob`-equivalence:
its source leg is not `π₀`-injective, the identity's is, and composition only
destroys injectivity — so no inverse `V` can make `mergeCob.comp V` rel-∂ the
identity.  The required rel-∂ invariance of the invariant is now fully discharged via
`srcLegπ₀Injective_rel` (iso-invariance plus the unit-move `dcob_unit{L,R}_srcInj_iff`
conjectures), so this needs no local hypothesis.  Hence `dCob` is **not a groupoid**. -/
theorem merge_not_invertible : ¬ IsEquivalenceCob mergeCob := by
  rintro ⟨V, hWV, _hVW⟩
  -- `mergeCob.comp V` is rel-∂ the identity `idCob S`.
  have hiff := srcLegπ₀Injective_rel hWV
  -- The identity's source leg IS `π₀`-injective.
  have hid : srcLegπ₀Injective (idCob mergeSrc) := idCob_src_π₀_injective
  -- So the composite's source leg would be `π₀`-injective — contradiction.
  exact mergeComp_not_srcLegπ₀Injective V (hiff.2 hid)

/-- **Unconditional non-triviality.**  There is *no* inverse cobordism `V` together
with a **boundary-fixing iso** of the composite `mergeCob.comp V` with the cylinder
identity `idCob S`: the composite's source leg is never `π₀`-injective (it factors
through the non-injective merge), while the identity's is, and a boundary-fixing iso
would transport injectivity between them.  This needs no unit-move invariance — only
the (proved) iso-invariance — so it is fully unconditional, and already witnesses that
`mergeCob` is non-invertible "on the nose" up to boundary-fixing iso. -/
theorem merge_no_iso_inverse (V : pt ⇒c mergeSrc)
    (φ : CobIso (mergeCob.comp V) (idCob mergeSrc)) : False :=
  mergeComp_not_srcLegπ₀Injective V
    ((srcLegπ₀Injective_cobIso_iff φ).2 idCob_src_π₀_injective)

/-! ### M6(c) — the cylinder identity is distinct from the merge

The cylinder `idCob` is the `dCob` identity (M5, `DCob.lean`).  It is a *different*
cobordism from the merge: most cleanly, the two have a different value of the
source-leg `π₀`-injectivity invariant — `idCob_src_π₀_injective` holds, while
`mergeCob_inl_π₀_not_injective` fails (and they even have different source/sink
shape, `S = pt ⨿ pt` vs `pt`). -/

/-- **M6(c).**  The cylinder identity `idCob S` and the merge `mergeCob` are distinct
cobordisms: the source-leg `π₀`-injectivity invariant separates them. -/
theorem idCob_ne_merge_invariant :
    srcLegπ₀Injective (idCob mergeSrc) ∧ ¬ srcLegπ₀Injective mergeCob :=
  ⟨idCob_src_π₀_injective, mergeCob_inl_π₀_not_injective⟩

end PrecubicalSet
