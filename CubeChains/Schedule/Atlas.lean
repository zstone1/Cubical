import CubeChains.Arrangements.BraidCone
import CubeChains.Chains.ChainPartition
import CubeChains.Schedule.Space

/-!
# Schedule/Atlas — the chart of a chain is a bijection onto its cone

`IsAtlas K` (`Schedule/Space.lean`): for every chain `a`, `chartCoord a` is injective with image
`schedCone a`.  Unpacked: every timing of `a`'s events honouring `a`'s bead order is `spread f τ`
for a **unique** refinement `f : c ⟶ a` with strictly increasing bead times `τ` — the tie-block
decomposition.

The bridge is the **bead map** `beadOf f : EventObj a → ChainCat.Bead c` (which bead of the finer
chain times each event of `a`): `spread f τ = τ ∘ beadOf f`, so the ties of a spread timing are the
beads of `c` and their order is `c`'s bead order.  Three facts drive the file:

* `bfSgnN_beadOf` — a refinement is **determined** by its bead map (its block faces are forced: a
  coordinate is free at its own bead, already `1` before it, still `0` after).  Hence
  `chartCoord_injective`, with **no side condition**: *distinct* refinements `c ⟶ a` have distinct
  bead maps, so a chart never folds.  (Thinness is what `ChartsFaithful` needs — the map that
  *forgets* the refinement — not `IsAtlas`.)
* `beadOf_prefine` — conversely, **every** ordered partition of `a`'s events (`β` surjective,
  increasing across `a`'s beads) is the bead map of a refinement, namely its tie-block chain
  `pchain β` (`Chains/ChainPartition`).  Hence `chartCoord_range`: the tie-blocks of a timing in
  the cone.
* `beadCovector_spread` — the within-bead braid covector of `spread f τ` does not depend on `τ`.
  It is the covector of the ordered partition `beadOf f`, i.e. the face of `braidDirectSum a.dims`
  that `f` names.

Gotcha: `EventObj a` is *defeq* to `beadEvent a.dims` and `schedCone a` to `beadCone a.dims`, so
the `Arrangements/BraidCone` covector API applies to chain timings on the nose.
-/

open CategoryTheory Opposite CubeChain StdCube SignType BPSet

namespace CubeChains

variable {K : BPSet}

/-! ## The bead map of a refinement -/

/-- The event of the finer chain sitting over `e` (`eventMap f` is bijective for every `K`). -/
noncomputable def preEvent {c a : Ch K} (f : c ⟶ a) (e : EventObj a) : EventObj c :=
  (eventEquiv f).symm e

@[simp] theorem eventMap_preEvent {c a : Ch K} (f : c ⟶ a) (e : EventObj a) :
    eventMap f (preEvent f e) = e :=
  (eventEquiv f).apply_symm_apply e

theorem preEvent_eventMap {c a : Ch K} (f : c ⟶ a) (x : EventObj c) :
    preEvent f (eventMap f x) = x := by
  have h1 : (eventEquiv f) x = eventMap f x := rfl
  rw [preEvent, ← h1]
  exact (eventEquiv f).symm_apply_apply x

/-- The **bead map** of a refinement `f : c ⟶ a`: which bead of `c` times each event of `a`. -/
noncomputable def beadOf {c a : Ch K} (f : c ⟶ a) (e : EventObj a) : ChainCat.Bead c :=
  (preEvent f e).1

theorem spread_apply {c a : Ch K} (f : c ⟶ a) (τ : Stratum c) (e : EventObj a) :
    spread f τ e = τ.1 (beadOf f e) := rfl

@[simp] theorem beadOf_eventMap {c a : Ch K} (f : c ⟶ a) (x : EventObj c) :
    beadOf f (eventMap f x) = x.1 := by
  rw [beadOf, preEvent_eventMap]

/-- Every bead of `c` is used: beads are positive-dimensional, so they carry an event. -/
theorem beadOf_surjective {c a : Ch K} (f : c ⟶ a) : Function.Surjective (beadOf f) := by
  intro j
  exact ⟨eventMap f ⟨j, ⟨0, (c.dims.get j).2⟩⟩, beadOf_eventMap f _⟩

/-- The bead map lands in the bead of `a` the event lives in (`eventMap` reads block data). -/
theorem blockIdx_beadOf {c a : Ch K} (f : c ⟶ a) (e : EventObj a) :
    blockIdx fᵂ (beadOf f e) = e.1 :=
  congrArg Sigma.fst (eventMap_preEvent f e)

/-! ## The covector of a spread timing does not depend on the times

`beadCovector` compares only events **within** a bead of `a`.  Under `spread f τ` two events get
equal times iff they come from the same bead of `c` (`τ` is injective), and their order is `c`'s
bead order (`τ` is strictly increasing) — so the covector is the ordered partition `beadOf f`, with
`τ` forgotten. -/

/-- Two strictly increasing timings of `Fin m` induce the same signs. -/
theorem sign_sub_strictMono {m : ℕ} {τ τ' : Fin m → ℝ} (hτ : StrictMono τ) (hτ' : StrictMono τ')
    (i j : Fin m) : sign (τ i - τ j) = sign (τ' i - τ' j) := by
  rcases lt_trichotomy i j with h | h | h
  · rw [sign_neg (by have := hτ h; linarith), sign_neg (by have := hτ' h; linarith)]
  · rw [h, sub_self, sub_self]
  · rw [sign_pos (by have := hτ h; linarith), sign_pos (by have := hτ' h; linarith)]

/-- `beadCovector` only sees the within-bead sign pattern of a timing. -/
theorem beadCovector_congr : ∀ (dims : List ℕ+) (t t' : beadEvent dims → ℝ),
    (∀ e e' : beadEvent dims, e.1 = e'.1 → sign (t e - t e') = sign (t' e - t' e')) →
    beadCovector dims t = beadCovector dims t'
  | [], _, _, _ => rfl
  | m :: rest, t, t', h => by
      have hhead : braidCovectorR (beadHead t) = braidCovectorR (beadHead t') := by
        funext e
        rw [braidCovectorR_apply, braidCovectorR_apply]
        exact h ⟨⟨0, Nat.succ_pos _⟩, e.1.1⟩ ⟨⟨0, Nat.succ_pos _⟩, e.1.2⟩ rfl
      have htail : beadCovector rest (beadTail t) = beadCovector rest (beadTail t') :=
        beadCovector_congr rest (beadTail t) (beadTail t') fun e e' he =>
          h ⟨e.1.succ, e.2⟩ ⟨e'.1.succ, e'.2⟩ (congrArg Fin.succ he)
      change Sum.elim (braidCovectorR (beadHead t)) (beadCovector rest (beadTail t))
        = Sum.elim (braidCovectorR (beadHead t')) (beadCovector rest (beadTail t'))
      rw [hhead, htail]

/-- The bead-index timing of `c`: bead `j` runs at time `j`. -/
def beadIndexStratum (c : Ch K) : Stratum c :=
  ⟨fun j => ((j : ℕ) : ℝ), fun _ _ h => Nat.cast_lt.mpr (Fin.lt_def.mp h)⟩

/-- The **face named by a refinement**: the within-bead covector of its bead map. -/
noncomputable def refineCovector {c a : Ch K} (f : c ⟶ a) : SignVec (braidDirectSumGround a.dims) :=
  beadCovector a.dims (spread f (beadIndexStratum c))

/-- **The covector forgets the times.**  `beadCovector a.dims (spread f τ)` is `refineCovector f`
for every stratum `τ` — the sign vector records only *which bead, in which order*. -/
theorem beadCovector_spread {c a : Ch K} (f : c ⟶ a) (τ : Stratum c) :
    beadCovector a.dims (spread f τ) = refineCovector f :=
  beadCovector_congr a.dims _ _ fun e e' _ =>
    sign_sub_strictMono τ.2 (beadIndexStratum c).2 (beadOf f e) (beadOf f e')

end CubeChains

/-! ## The block faces of a refinement are forced

`EventMapBij` proves the *flip* half of the monotonicity of the sign `bfSgnN φ j p` in `j`: once a
coordinate is free (its own bead), it is `1` in every later bead over the same coarse bead.  Here is
the other half — before its own bead it is still `0` — and the two together pin every entry of every
block face. -/

namespace CubeChain

variable {ad cd : List ℕ+}

/-- A face-embedded coordinate is free in its own bead. -/
theorem bfSgnN_faceEmb (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (j : Fin ad.length) (y : Fin ((ad.get j : ℕ))) :
    bfSgnN φ j ((faceEmb (blockFace φ j) y).val) = none := by
  have hlt := (faceEmb (blockFace φ j) y).isLt
  have hmem : (ev (blockFace φ j)).val (faceEmb (blockFace φ j) y) = none :=
    mem_noneSet.mp
      (Finset.orderEmbOfFin_mem _ (ev (blockFace φ j)).prop y)
  simp only [bfSgnN]
  rw [dif_pos hlt,
    show (⟨(faceEmb (blockFace φ j) y).val, hlt⟩ : Fin _) = faceEmb (blockFace φ j) y from
      Fin.ext rfl]
  exact hmem

/-- The reverse flip step: for consecutive fine beads `j, j'` over the same coarse bead, a
coordinate not already `1` in `j'` (`≠ some true`) is still `0` in `j`. -/
theorem bfSgnN_step_back
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (hinit : φ⟪0⟫ (BPSet.serialWedge ad).init = (BPSet.serialWedge cd).init)
    {j j' : Fin ad.length} (hjj' : j'.val = j.val + 1) (hb : blockIdx φ j = blockIdx φ j')
    {p : ℕ} (hp : p < (cd.get (blockIdx φ j) : ℕ)) (hj' : bfSgnN φ j' p ≠ some true) :
    bfSgnN φ j p = some false := by
  have hjunc := bfSgnN_junction φ hinit hjj' hb hp
  have hrhs : (if bfSgnN φ j' p = none then some false else bfSgnN φ j' p) = some false := by
    rcases hcase : bfSgnN φ j' p with _ | b
    · simp
    · rcases b with _ | _
      · simp
      · exact absurd hcase hj'
  rw [hrhs] at hjunc
  rcases hcase : bfSgnN φ j p with _ | b
  · rw [hcase] at hjunc; simp at hjunc
  · rcases b with _ | _
    · rfl
    · rw [hcase] at hjunc; simp at hjunc

/-- The reverse flip step relativised to a fixed interval `[i, i']` (companion of
`bfSgnN_step'`). -/
theorem bfSgnN_step_back'
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (hinit : φ⟪0⟫ (BPSet.serialWedge ad).init = (BPSet.serialWedge cd).init)
    {i i' j j' : Fin ad.length} (hr : blockIdx φ i = blockIdx φ i')
    (hij : i ≤ j) (hjj' : j'.val = j.val + 1) (hj'i' : j' ≤ i')
    {p : ℕ} (hp : p < (cd.get (blockIdx φ i) : ℕ)) (hj' : bfSgnN φ j' p ≠ some true) :
    bfSgnN φ j p = some false := by
  have hjj'le : j ≤ j' := Fin.le_def.mpr (by omega)
  have hji' : j ≤ i' := le_trans hjj'le hj'i'
  have hbj : blockIdx φ j = blockIdx φ i := blockIdx_const_of_le φ hinit hr hij hji'
  have hbj' : blockIdx φ j' = blockIdx φ i :=
    blockIdx_const_of_le φ hinit hr (le_trans hij hjj'le) hj'i'
  have hb : blockIdx φ j = blockIdx φ j' := by rw [hbj, hbj']
  have hpj : p < (cd.get (blockIdx φ j) : ℕ) := by rw [hbj]; exact hp
  exact bfSgnN_step_back φ hinit hjj' hb hpj hj'

/-- **Not yet flipped.**  If coordinate `p` is free in bead `i'`, it is still `0` in every earlier
bead `i` over the same coarse bead (the mirror of `bfSgnN_flip`). -/
theorem bfSgnN_notYet
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (hinit : φ⟪0⟫ (BPSet.serialWedge ad).init = (BPSet.serialWedge cd).init)
    {i i' : Fin ad.length} (hii : i < i') (hr : blockIdx φ i = blockIdx φ i')
    {p : ℕ} (hp : p < (cd.get (blockIdx φ i) : ℕ)) (hpi' : bfSgnN φ i' p = none) :
    bfSgnN φ i p = some false := by
  have hii' : i.val < i'.val := hii
  have key : ∀ d n, n + d + 1 = i'.val → ∀ (hn : n < ad.length), i.val ≤ n →
      bfSgnN φ ⟨n, hn⟩ p = some false := by
    intro d
    induction d with
    | zero =>
        intro n hn hn' hle
        have hstep : i'.val = n + 1 := by omega
        exact bfSgnN_step_back' (j := ⟨n, hn'⟩) (j' := i') φ hinit hr (Fin.le_def.mpr hle)
          hstep (le_refl i') hp (by rw [hpi']; simp)
    | succ d ih =>
        intro n hn hn' hle
        have hn1 : n + 1 < ad.length := by omega
        have hprev : bfSgnN φ ⟨n + 1, hn1⟩ p = some false := ih (n + 1) (by omega) hn1 (by omega)
        have hstep : n + 1 = n + 1 := rfl
        have hle' : n + 1 ≤ i'.val := by omega
        exact bfSgnN_step_back' (j := ⟨n, hn'⟩) (j' := ⟨n + 1, hn1⟩) φ hinit hr
          (Fin.le_def.mpr hle) hstep (Fin.le_def.mpr hle') hp (by rw [hprev]; simp)
  have hkey := key (i'.val - i.val - 1) i.val (by omega) i.isLt (le_refl _)
  simpa using hkey

/-! ### Transport across an equality of block indices -/

/-- Transport of a block inclusion across an equality of block indices. -/
theorem yoneda_ι_cast {dims : List ℕ+} {R R' : Fin dims.length} (h : R = R') {k : ℕ}
    (u : ▫k ⟶ ▫((dims.get R : ℕ))) :
    yoneda.map u ≫ ιᵂ dims R
      = yoneda.map (h ▸ u : ▫k ⟶ ▫((dims.get R' : ℕ)))
          ≫ ιᵂ dims R' := by
  subst h; rfl

/-- Transport of an `ev`-value read across an equality of block indices (the general-dimension
form of `ev_val_blockcast`). -/
theorem ev_val_cast {dims : List ℕ+} {R R' : Fin dims.length} (h : R = R') {k : ℕ}
    (u : ▫k ⟶ ▫((dims.get R : ℕ))) (p : ℕ)
    (hp : p < (dims.get R : ℕ)) (hp' : p < (dims.get R' : ℕ)) :
    (ev (h ▸ u : ▫k ⟶ ▫((dims.get R' : ℕ)))).val ⟨p, hp'⟩
      = (ev u).val ⟨p, hp⟩ := by
  subst h; rfl

end CubeChain

namespace CubeChains

variable {K : BPSet}

/-- **The block faces of a refinement are forced by its bead map.**  At bead `j`, a coordinate `p`
of the coarse bead is free iff its event belongs to `j`, already `1` if its event belongs to an
earlier bead, still `0` if to a later one. -/
theorem bfSgnN_beadOf {c a : Ch K} (f : c ⟶ a) (j j' : ChainCat.Bead c)
    {p : ℕ} (hp : p < (ChainCat.beadDim a (blockIdx fᵂ j)))
    (hj' : beadOf f ⟨blockIdx fᵂ j, ⟨p, hp⟩⟩ = j') :
    bfSgnN fᵂ j p = if j' = j then none else some (decide (j' < j)) := by
  set φ := fᵂ with hφ
  set e : EventObj a := ⟨blockIdx φ j, ⟨p, hp⟩⟩ with he
  have hinit : φ⟪0⟫ (BPSet.serialWedge c.dims).init
      = (BPSet.serialWedge a.dims).init := f.φ.app_init
  -- `p` is free in its own bead `j'`
  have hval : (faceEmb (blockFace φ (preEvent f e).1) (preEvent f e).2).val = p :=
    congrArg (fun x : EventObj a => (x.2 : ℕ)) (eventMap_preEvent f e)
  have hfree : bfSgnN φ j' p = none := by
    rw [← hj', beadOf, ← hval]
    exact bfSgnN_faceEmb φ _ _
  -- `j'` sits over the same coarse bead as `j`
  have hidx : blockIdx φ j' = blockIdx φ j := by
    rw [← hj']
    exact blockIdx_beadOf f e
  rcases lt_trichotomy j' j with hlt | heq | hgt
  · rw [if_neg (ne_of_lt hlt), decide_eq_true hlt]
    exact bfSgnN_flip φ hinit hlt hidx (by rw [hidx]; exact hp) hfree
  · rw [if_pos heq, ← heq]
    exact hfree
  · rw [if_neg (Ne.symm (ne_of_lt hgt)), decide_eq_false (not_lt.mpr (le_of_lt hgt))]
    exact bfSgnN_notYet φ hinit hgt hidx.symm hp hfree

/-- The `ℕ`-indexed sign is the block face's `ev`-value at an in-range coordinate. -/
theorem bfSgnN_ev {c a : Ch K} (f : c ⟶ a) (j : ChainCat.Bead c)
    (p : Fin ((ChainCat.beadDim a (blockIdx fᵂ j)))) :
    bfSgnN fᵂ j p.val = (ev (blockFace fᵂ j)).val p := by
  simp only [bfSgnN, dif_pos p.isLt]

/-- Two events of `a` with equal bead and equal coordinate value are equal. -/
theorem event_ext {a : Ch K} {R R' : ChainCat.Bead a} (h : R = R') {p : ℕ}
    (hp : p < (ChainCat.beadDim a R)) (hp' : p < (ChainCat.beadDim a R')) :
    (⟨R, ⟨p, hp⟩⟩ : EventObj a) = ⟨R', ⟨p, hp'⟩⟩ := by
  subst h; rfl

/-- A `Box`-map is determined by its sign vector. -/
theorem box_ext {k n : ℕ} {u v : ▫k ⟶ ▫n} (h : ev u = ev v) : u = v :=
  calc u = canonicalMap (ev u) :=
        ((cubeRepr (stdPre n) k).left_inv u).symm
    _ = canonicalMap (ev v) := by rw [h]
    _ = v := (cubeRepr (stdPre n) k).left_inv v

/-! ## Injectivity of the chart

A chart point is a refinement plus its bead times.  The times are read off the timing at any event
of each bead; the refinement is read off the tie pattern (`bfSgnN_beadOf`).  **No thinness**: even
when two refinements `c ⟶ a` differ (a self-linked cube) their bead maps differ, so their chart
points differ.  Thinness is what `ChartsFaithful` (which *forgets* the refinement) needs. -/

/-- The fibre of the bead map over `j` is bead `j` of the finer chain. -/
theorem card_fiber_beadOf {c a : Ch K} (f : c ⟶ a) (j : ChainCat.Bead c) :
    (Finset.univ.filter (fun e : EventObj a => beadOf f e = j)).card = (c.dims.get j : ℕ) := by
  classical
  have hinj : Function.Injective
      (fun δ : Fin ((ChainCat.beadDim c j)) => eventMap f (⟨j, δ⟩ : EventObj c)) := by
    intro δ δ' hδ
    have h := eventMap_injective_hom f hδ
    exact Fin.ext (congrArg (fun x : EventObj c => (x.2 : ℕ)) h)
  have himg : Finset.univ.filter (fun e : EventObj a => beadOf f e = j)
      = Finset.image (fun δ : Fin ((ChainCat.beadDim c j)) => eventMap f (⟨j, δ⟩ : EventObj c))
          Finset.univ := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      obtain ⟨⟨i, δ⟩, hx1, hx2⟩ : ∃ x : EventObj c, eventMap f x = e ∧ x.1 = j :=
        ⟨preEvent f e, eventMap_preEvent f e, hj⟩
      subst hx2
      exact ⟨δ, hx1⟩
    · rintro ⟨δ, rfl⟩
      exact beadOf_eventMap f _
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- Two surjections onto `Fin`s ordering their fibres alike are the same ordered partition. -/
theorem eq_of_orderedPartition {X : Type*} {m m' : ℕ} {u : X → Fin m} {v : X → Fin m'}
    (hu : Function.Surjective u) (hv : Function.Surjective v)
    (hlt : ∀ x y, u x < u y ↔ v x < v y) :
    m = m' ∧ ∀ x, (u x : ℕ) = (v x : ℕ) := by
  classical
  have hwd : ∀ x y, u x = u y → v x = v y := by
    intro x y hxy
    have h1 : ¬ v x < v y := fun hc => by
      have := (hlt x y).mpr hc
      rw [hxy] at this
      exact lt_irrefl _ this
    have h2 : ¬ v y < v x := fun hc => by
      have := (hlt y x).mpr hc
      rw [hxy] at this
      exact lt_irrefl _ this
    exact le_antisymm (not_lt.mp h2) (not_lt.mp h1)
  set w : Fin m → Fin m' := fun j => v (Function.surjInv hu j) with hw
  have hwu : ∀ x, w (u x) = v x := fun x => hwd _ _ (Function.surjInv_eq hu (u x))
  have hwmono : StrictMono w := by
    intro j j' hjj'
    have h1 : u (Function.surjInv hu j) < u (Function.surjInv hu j') := by
      rw [Function.surjInv_eq hu j, Function.surjInv_eq hu j']; exact hjj'
    exact (hlt _ _).mp h1
  have hwsurj : Function.Surjective w := by
    intro k
    obtain ⟨x, hx⟩ := hv k
    exact ⟨u x, by rw [hwu x, hx]⟩
  have hwbij : Function.Bijective w := ⟨hwmono.injective, hwsurj⟩
  have hm : m = m' := by simpa using Fintype.card_of_bijective hwbij
  refine ⟨hm, fun x => ?_⟩
  set e := Equiv.ofBijective w hwbij with he
  have h1 : ∀ j, e.symm (w j) = j := fun j => e.symm_apply_apply j
  have h2 : ∀ k, w (e.symm k) = k := fun k => e.apply_symm_apply k
  have hSmono : Monotone (fun k => e.symm k) := by
    intro x y hxy
    by_contra hc
    rw [not_le] at hc
    have hle : w (e.symm y) ≤ w (e.symm x) := le_of_lt (hwmono hc)
    rw [h2, h2] at hle
    have hxy' : x = y := hxy.antisymm hle
    rw [hxy'] at hc
    exact absurd hc (lt_irrefl _)
  have hval := monotone_bij_fin_cast hm hwmono.monotone hSmono h1 h2 (u x)
  rw [hwu x] at hval
  exact hval.symm

/-- **The chart of a chain is injective** — for every `K`, with no side condition. -/
theorem chartCoord_injective (a : Ch K) : Function.Injective (chartCoord a) := by
  classical
  rintro ⟨c, f, τ⟩ ⟨c', f', τ'⟩ h
  have ht : ∀ e : EventObj a, τ.1 (beadOf f e) = τ'.1 (beadOf f' e) := congrFun h
  have hlt : ∀ e e' : EventObj a, beadOf f e < beadOf f e' ↔ beadOf f' e < beadOf f' e' := by
    intro e e'
    constructor
    · intro hb
      have h1 : τ.1 (beadOf f e) < τ.1 (beadOf f e') := τ.2 hb
      rw [ht e, ht e'] at h1
      exact τ'.2.lt_iff_lt.mp h1
    · intro hb
      have h1 : τ'.1 (beadOf f' e) < τ'.1 (beadOf f' e') := τ'.2 hb
      rw [← ht e, ← ht e'] at h1
      exact τ.2.lt_iff_lt.mp h1
  obtain ⟨hlen, hbn⟩ :=
    eq_of_orderedPartition (beadOf_surjective f) (beadOf_surjective f') hlt
  obtain ⟨cd, cm⟩ := c
  obtain ⟨cd', cm'⟩ := c'
  -- the bead sizes are the fibres of the bead map, so the dimension lists agree
  have hdims : cd = cd' := by
    apply List.ext_getElem hlen
    intro k h1 h2
    change cd.get ⟨k, h1⟩ = cd'.get ⟨k, h2⟩
    apply PNat.coe_injective
    rw [← card_fiber_beadOf f ⟨k, h1⟩, ← card_fiber_beadOf f' ⟨k, h2⟩]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro he
      exact Fin.ext (by rw [← hbn e, he])
    · intro he
      exact Fin.ext (by rw [hbn e, he])
  subst hdims
  have hbf : ∀ e : EventObj a, beadOf f e = beadOf f' e := fun e => Fin.ext (hbn e)
  -- the bead times are read off the timing at any event of the bead
  have hτ : τ = τ' := by
    apply Subtype.ext
    funext j
    have hδ : (0 : ℕ) < (cd.get j : ℕ) := (cd.get j).2
    have h1 := ht (eventMap f ⟨j, ⟨0, hδ⟩⟩)
    have h2 : beadOf f' (eventMap f (⟨j, ⟨0, hδ⟩⟩ : EventObj _)) = j := by
      rw [← hbf, beadOf_eventMap f]
    rw [beadOf_eventMap f, h2] at h1
    exact h1
  -- the two refinements have the same block indices …
  have hR : ∀ j : Fin cd.length, blockIdx fᵂ j = blockIdx f'ᵂ j := by
    intro j
    have hδ : (0 : ℕ) < (cd.get j : ℕ) := (cd.get j).2
    have h4 := blockIdx_beadOf f (eventMap f ⟨j, ⟨0, hδ⟩⟩)
    have h5 := blockIdx_beadOf f' (eventMap f ⟨j, ⟨0, hδ⟩⟩)
    rw [beadOf_eventMap f] at h4
    rw [← hbf, beadOf_eventMap f] at h5
    rw [h4, h5]
  -- … and, by `bfSgnN_beadOf`, the same block faces
  have hsgn : ∀ (j : Fin cd.length) (p : ℕ), bfSgnN fᵂ j p = bfSgnN f'ᵂ j p := by
    intro j p
    by_cases hp : p < (ChainCat.beadDim a (blockIdx fᵂ j))
    · have hp' : p < (ChainCat.beadDim a (blockIdx f'ᵂ j)) := by rw [← hR j]; exact hp
      have hE : (⟨blockIdx f'ᵂ j, ⟨p, hp'⟩⟩ : EventObj a)
          = ⟨blockIdx fᵂ j, ⟨p, hp⟩⟩ := event_ext (hR j).symm hp' hp
      have hj0 := hbf (⟨blockIdx fᵂ j, ⟨p, hp⟩⟩ : EventObj a)
      rw [bfSgnN_beadOf f j _ hp hj0, bfSgnN_beadOf f' j _ hp' (by rw [hE])]
    · have hp' : ¬ p < (ChainCat.beadDim a (blockIdx f'ᵂ j)) := by rw [← hR j]; exact hp
      simp only [bfSgnN, dif_neg hp, dif_neg hp']
  have hcomp : ∀ j : Fin cd.length,
      ιᵂ cd j ≫ fᵂ = ιᵂ cd j ≫ f'ᵂ := by
    intro j
    have hbfj : (hR j ▸ blockFace fᵂ j :
          ▫((cd.get j : ℕ)) ⟶ ▫((ChainCat.beadDim a (blockIdx f'ᵂ j))))
        = blockFace f'ᵂ j := by
      refine box_ext (Subtype.ext (funext fun p => ?_))
      have hpj : (p : ℕ) < (ChainCat.beadDim a (blockIdx fᵂ j)) := by rw [hR j]; exact p.isLt
      rw [ev_val_cast (hR j) (blockFace fᵂ j) (p : ℕ) hpj p.isLt,
        ← bfSgnN_ev f j ⟨(p : ℕ), hpj⟩, ← bfSgnN_ev f' j p, hsgn j (p : ℕ)]
    rw [blockFace_spec fᵂ j, blockFace_spec f'ᵂ j, ← hbfj]
    exact yoneda_ι_cast (hR j) (blockFace fᵂ j)
  have hφ : fᵂ = f'ᵂ :=
    serialWedge_hom_ext cd fᵂ f'ᵂ hcomp (by rw [f.φ.app_init, f'.φ.app_init])
  have hφ' : f.φ = f'.φ := hom_ext hφ
  -- the finer chain's classifying map is `φ ≫ a.map`, so the chains agree
  have hmap : cm = cm' := by
    have hw : f.φ ≫ a.map = cm := f.w
    have hw' : f'.φ ≫ a.map = cm' := f'.w
    rw [← hw, ← hw', hφ']
  subst hmap
  have hff : f = f' := ChainCat.hom_ext' hφ'
  subst hff
  rw [hτ]

/-! ## The bead map of the tie-block refinement

The tie-block chain `pchain β` of an ordered partition `β` of `a`'s events refines `a`; its bead
map is `β` back again, which is what turns the tie-blocks of a timing in `a`'s cone into a
refinement. -/

section Partition

variable {K : BPSet} {a : Ch K} {m : ℕ} (β : EventObj a → Fin m)
  (hβ : Function.Surjective β)
  (hmo : ∀ e e' : EventObj a, (e.1 : ℕ) < (e'.1 : ℕ) → β e < β e')

/-- The bead map of the tie-block refinement is the partition itself. -/
theorem beadOf_prefine (e : EventObj a) :
    ((beadOf (prefine β hβ hmo) e : Fin (pchain β hβ hmo).dims.length) : ℕ)
      = ((β e : Fin m) : ℕ) := by
  have h := beta_eventMap β hβ hmo (preEvent (prefine β hβ hmo) e)
  rw [eventMap_preEvent] at h
  exact h.symm

end Partition

/-! ## The atlas

Injectivity plus the tie-block decomposition: the chart of a chain is a bijection onto its cone. -/

/-- **Range**: every timing honouring `a`'s bead order is spread from a refinement of `a` with
strictly increasing bead times — its tie-blocks. -/
theorem chartCoord_range (a : Ch K) : Set.range (chartCoord a) = schedCone a := by
  classical
  refine Set.Subset.antisymm ?_ fun t ht => ?_
  · rintro s ⟨p, rfl⟩
    exact chartCoord_mem_cone a p
  · -- the distinct values of `t`, in increasing order
    set vals : Finset ℝ := Finset.image t Finset.univ with hvals
    set τ : Fin vals.card ↪o ℝ := vals.orderEmbOfFin rfl with hτ
    have hrange : Set.range τ = ↑vals := Finset.range_orderEmbOfFin vals rfl
    have hex : ∀ e : EventObj a, ∃ j : Fin vals.card, τ j = t e := by
      intro e
      have hmem : t e ∈ Set.range τ := by
        rw [hrange]
        exact Finset.mem_coe.mpr (Finset.mem_image_of_mem t (Finset.mem_univ e))
      obtain ⟨j, hj⟩ := hmem
      exact ⟨j, hj⟩
    choose β hβt using hex
    have hβsurj : Function.Surjective β := by
      intro j
      have hmem : (τ j : ℝ) ∈ vals := by
        rw [← Finset.mem_coe, ← hrange]
        exact Set.mem_range_self j
      obtain ⟨e, -, he⟩ := Finset.mem_image.mp hmem
      exact ⟨e, τ.injective ((hβt e).trans he)⟩
    have hmono : ∀ e e' : EventObj a, (e.1 : ℕ) < (e'.1 : ℕ) → β e < β e' := by
      intro e e' hlt
      have h1 : τ (β e) < τ (β e') := by rw [hβt e, hβt e']; exact ht e e' hlt
      exact τ.lt_iff_lt.mp h1
    have hlen := pchain_dims_length β hβsurj hmono
    have hbead := beadOf_prefine β hβsurj hmono
    refine ⟨⟨pchain β hβsurj hmono, prefine β hβsurj hmono,
      ⟨fun j => τ (Fin.cast hlen j), fun x y hxy => τ.strictMono (by
        rw [Fin.lt_def] at hxy ⊢; exact hxy)⟩⟩, ?_⟩
    funext e
    have hcast : Fin.cast hlen (beadOf (prefine β hβsurj hmono) e) = β e := Fin.ext (hbead e)
    change τ (Fin.cast hlen (beadOf (prefine β hβsurj hmono) e)) = t e
    rw [hcast, hβt e]

/-- **The chart of a chain is a bijection onto its cone**, for every `K` — no side condition.
Injectivity does *not* need thinness: a refinement is determined by its bead map. -/
theorem isAtlas (K : BPSet) : IsAtlas K :=
  fun a => ⟨chartCoord_injective a, chartCoord_range a⟩

end CubeChains
