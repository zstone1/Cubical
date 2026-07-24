import CubeChains.Salvetti.Runs
import CubeChains.Chains.CoordFunctor
import CubeChains.Chains.BlockDecomp
import Mathlib.CategoryTheory.Core
import Mathlib.Algebra.BigOperators.Fin

/-!
# Salvetti/EventPerm — the event relabelling of a `RunWedge` refinement

`eventEquiv f = coordMapEquiv (wedgeMap f)` : the bijection of atomic events a refinement induces,
read off its wedge map alone — no run.  It is a **contravariant functor** to finite sets and
bijections (`eventEquiv_comp`, from `coordMap_comp`), packaged as `eventCore : RunWedge ⥤ Core Type`.

Ordering the events by the **canonical lexicographic flattening** `finSigmaFinEquiv` (no run) makes
the no-double-crossing law elementary: a refinement never un-crosses a pair (`eventCross_H`).  The
cross-bead half is `blockIdx` monotonicity; the within-bead half is that `faceEmb` is an *order*
embedding — so the whole single-cube run geometry of the old proof evaporates.
-/

open CategoryTheory CubeChain

namespace CubeChains

/-! ## The lexicographic flattening `finSigmaFinEquiv` as an order

`finSigmaFinEquiv : (Σ i, Fin (n i)) ≃ Fin (∑ n)` is the monotone enumeration of the lex order:
earlier block ⇒ strictly smaller (`finSigmaFinEquiv_lt_of_fst_lt`), and within one block the fibre
order is preserved (`finSigmaFinEquiv_within`).  Both are general `Fin`-family facts. -/

/-- Prefix sums of a `Fin m`-indexed family are monotone in the cut point. -/
private theorem sum_castLE_mono {m : ℕ} (n : Fin m → ℕ) {s t : ℕ} (hs : s ≤ m) (ht : t ≤ m)
    (hst : s ≤ t) : ∑ i : Fin s, n (Fin.castLE hs i) ≤ ∑ i : Fin t, n (Fin.castLE ht i) := by
  have hval : ∀ (u : ℕ) (hu : u ≤ m), (∑ i : Fin u, n (Fin.castLE hu i))
      = ∑ x ∈ Finset.range u, (if h : x < m then n ⟨x, h⟩ else 0) := by
    intro u hu
    rw [← Fin.sum_univ_eq_sum_range (fun x => if h : x < m then n ⟨x, h⟩ else 0) u]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dif_pos (lt_of_lt_of_le j.2 hu)]
    rfl
  rw [hval s hs, hval t ht]
  exact Finset.sum_le_sum_of_subset fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hst)

/-- **`finSigmaFinEquiv` respects the block order.**  If `p`'s block precedes `q`'s, its whole block
flattens strictly below `q`. -/
theorem finSigmaFinEquiv_lt_of_fst_lt {m : ℕ} {n : Fin m → ℕ}
    {p q : (i : Fin m) × Fin (n i)} (h : (p.1 : ℕ) < (q.1 : ℕ)) :
    finSigmaFinEquiv p < finSigmaFinEquiv q := by
  rw [Fin.lt_def, finSigmaFinEquiv_apply, finSigmaFinEquiv_apply]
  have hstep : (∑ i : Fin (p.1 : ℕ), n (Fin.castLE p.1.2.le i)) + n p.1
      ≤ ∑ i : Fin (q.1 : ℕ), n (Fin.castLE q.1.2.le i) := by
    have hle := sum_castLE_mono n (s := (p.1 : ℕ) + 1) (t := (q.1 : ℕ)) p.1.2 q.1.2.le (by omega)
    refine le_trans (le_of_eq ?_) hle
    rw [Fin.sum_univ_castSucc]
    exact congrArg₂ (· + ·)
      (Finset.sum_congr rfl fun j _ => congrArg n (Fin.ext rfl)) (congrArg n (Fin.ext rfl))
  have hk := p.2.isLt
  omega

/-- **`finSigmaFinEquiv` preserves the fibre order within a block** — the prefixes cancel. -/
theorem finSigmaFinEquiv_within {m : ℕ} {n : Fin m → ℕ} {i : Fin m} {k k' : Fin (n i)} :
    finSigmaFinEquiv (⟨i, k⟩ : (i : Fin m) × Fin (n i)) < finSigmaFinEquiv ⟨i, k'⟩ ↔ k < k' := by
  rw [Fin.lt_def, finSigmaFinEquiv_apply, finSigmaFinEquiv_apply, add_lt_add_iff_left, Fin.lt_def]

namespace RunWedge

@[simp] theorem wedgeMap_id (X : RunWedge) : wedgeMap (𝟙 X) = 𝟙 (⋁X.dims) := rfl

theorem wedgeMap_comp {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    wedgeMap (f ≫ g) = wedgeMap g ≫ wedgeMap f := rfl

/-- The event relabelling `beadEvent Y.dims ≃ beadEvent X.dims` induced by a refinement — `coordMap`
of its wedge map. -/
def eventEquiv {X Y : RunWedge} (f : X ⟶ Y) : beadEvent Y.dims ≃ beadEvent X.dims :=
  coordMapEquiv (wedgeMap f)

@[simp] theorem eventEquiv_apply {X Y : RunWedge} (f : X ⟶ Y) (e : beadEvent Y.dims) :
    eventEquiv f e = coordMap (wedgeMap f) e := rfl

@[simp] theorem eventEquiv_id (X : RunWedge) : eventEquiv (𝟙 X) = Equiv.refl _ := by
  refine Equiv.ext fun e => ?_
  rw [eventEquiv_apply, wedgeMap_id, coordMap_id, id_eq, Equiv.refl_apply]

/-- **`eventEquiv` is a contravariant functor**: a composite refinement relabels events by the
composite (reversed) relabelling.  This is `coordMap_comp`. -/
theorem eventEquiv_comp {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eventEquiv (f ≫ g) = (eventEquiv g).trans (eventEquiv f) := by
  refine Equiv.ext fun e => ?_
  rw [eventEquiv_apply, wedgeMap_comp, coordMap_comp, Function.comp_apply,
    Equiv.trans_apply, eventEquiv_apply, eventEquiv_apply]

/-- **The event-groupoid representation** `RunWedge ⥤ Core (Type)`: each execution to its set of
atomic events, each refinement to the (inverse) relabelling *as an isomorphism*.  Landing in the
groupoid `Core (Type)` — not merely `Type` — is what lets this lift along `FreeGroupoid RunWedge`,
so that `Aut` at an all-edges base becomes `Sₙ` with no `runOrder` choice. -/
def eventCore : RunWedge ⥤ Core (Type) where
  obj X := ⟨beadEvent X.dims⟩
  map f := ⟨(eventEquiv f).symm.toIso⟩
  map_id X := by refine Core.hom_ext ?_; rw [eventEquiv_id]; rfl
  map_comp f g := by refine Core.hom_ext ?_; rw [eventEquiv_comp]; rfl

/-! ## No-double-crossing: a refinement never un-crosses a pair of events

Order the events of an execution by the canonical flattening `pos = finSigmaFinEquiv` — bead first,
then the raw axis inside the bead, no run.  `eventEquiv` reads off the block form (`coordMap_eq`):
bead `i`, axis `k` ↦ bead `blockIdx i`, axis `faceEmb (blockFace i) k`.  Monotonicity of `blockIdx`
handles cross-bead pairs; `faceEmb` being an *order embedding* handles within-bead pairs. -/

/-- The block form of the relabelling: bead `i`, axis `k` lands in bead `blockIdx i`, axis
`faceEmb (blockFace i) k`. -/
theorem eventEquiv_mk {X Y : RunWedge} (f : X ⟶ Y) (i : Fin Y.dims.length)
    (k : Fin (Y.dims.get i : ℕ)) :
    eventEquiv f ⟨i, k⟩
      = ⟨blockIdx (wedgeMap f).hom i, faceEmb (blockFace (wedgeMap f).hom i) k⟩ := by
  rw [eventEquiv_apply, coordMap_eq]

/-- The bead of a relabelled event is `blockIdx` of its bead. -/
theorem eventEquiv_fst {X Y : RunWedge} (f : X ⟶ Y) (a : beadEvent Y.dims) :
    (eventEquiv f a).1 = blockIdx (wedgeMap f).hom a.1 := by
  rw [eventEquiv_apply, coordMap_fst]

/-- `blockIdx` of a refinement's wedge map is monotone. -/
theorem blockIdx_monotone {X Y : RunWedge} (f : X ⟶ Y) :
    Monotone (blockIdx (wedgeMap f).hom) :=
  serialWedge_blockIdx_monotone _ (wedgeMap f).app_init

/-- The canonical, run-free event order: flatten the beads lexicographically. -/
def pos {dims : List ℕ+} : beadEvent dims ≃ Fin (∑ i : Fin dims.length, (dims.get i : ℕ)) :=
  finSigmaFinEquiv

/-- Earlier bead ⇒ earlier in the flattening. -/
theorem pos_lt_of_fst_lt {dims : List ℕ+} {e e' : beadEvent dims} (h : (e.1 : ℕ) < e'.1) :
    pos e < pos e' :=
  finSigmaFinEquiv_lt_of_fst_lt h

/-- Within a bead, the flattening is the raw axis order. -/
theorem pos_within {dims : List ℕ+} {i : Fin dims.length} {k k' : Fin (dims.get i : ℕ)} :
    (pos (⟨i, k⟩ : beadEvent dims)) < pos ⟨i, k'⟩ ↔ k < k' :=
  finSigmaFinEquiv_within

/-- **Cross-bead: a refinement strictly preserves the bead order.** -/
theorem chainBead_refine {Y Z : RunWedge} (g : Y ⟶ Z) {a b : beadEvent Y.dims}
    (h : (a.1 : ℕ) < b.1) : (((eventEquiv g).symm a).1 : ℕ) < ((eventEquiv g).symm b).1 := by
  by_contra hcon
  rw [not_lt] at hcon
  have hmono := blockIdx_monotone g (Fin.le_def.mpr hcon)
  rw [← eventEquiv_fst, ← eventEquiv_fst, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hmono
  exact absurd h (not_lt.mpr (Fin.le_def.mp hmono))

/-- **Within a bead: a refinement preserves the event order** — one line, because `faceEmb` is an
order embedding.  (The old proof needed the whole single-cube run geometry here.) -/
theorem within_bead_agree {X Y : RunWedge} (f : X ⟶ Y) {a b : beadEvent Y.dims}
    (hbead : a.1 = b.1) :
    (pos (eventEquiv f a) < pos (eventEquiv f b) ↔ pos a < pos b) := by
  obtain ⟨iβ, ka⟩ := a
  obtain ⟨jb, kb⟩ := b
  obtain rfl : iβ = jb := hbead
  rw [eventEquiv_mk, eventEquiv_mk, pos_within, pos_within,
    (faceEmb (blockFace (wedgeMap f).hom iβ)).lt_iff_lt]

/-- **No double crossing.**  If `X` orders `e₁` before `e₂` while their `f`-preimages are ordered
oppositely in `Y` (so `f` crosses the pair), then the further refinement `g` keeps them crossed:
the crossing, once made, is never undone. -/
theorem eventCross_H {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) (e₁ e₂ : beadEvent X.dims)
    (h1 : pos e₁ < pos e₂)
    (h2 : pos ((eventEquiv f).symm e₂) < pos ((eventEquiv f).symm e₁)) :
    pos ((eventEquiv g).symm ((eventEquiv f).symm e₂))
      < pos ((eventEquiv g).symm ((eventEquiv f).symm e₁)) := by
  set a := (eventEquiv f).symm e₁ with ha
  set b := (eventEquiv f).symm e₂ with hb
  have he₁ : eventEquiv f a = e₁ := Equiv.apply_symm_apply _ _
  have he₂ : eventEquiv f b = e₂ := Equiv.apply_symm_apply _ _
  have hstep : (b.1 : ℕ) < a.1 := by
    rcases lt_trichotomy (a.1 : ℕ) (b.1 : ℕ) with hlt | heq | hgt
    · exact absurd (pos_lt_of_fst_lt hlt) (asymm h2)
    · rw [← he₁, ← he₂] at h1
      exact absurd ((within_bead_agree f (Fin.ext heq)).mp h1) (asymm h2)
    · exact hgt
  exact pos_lt_of_fst_lt (chainBead_refine g hstep)

end RunWedge
end CubeChains
