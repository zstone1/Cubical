import CubeChains.Schedule.Atlas
import CubeChains.Schedule.LocalCOM

/-!
# Schedule/COMSheaf — the local COM is the localization of any chart's COM

A refinement `f : c ⟶ a` is a schedule of stratum `c` seen in the chart `a`.  Its covector there is
`refineCovector f` — the times drop out (`beadCovector_spread`) — and the **zero set** of that
covector, i.e. the walls of `a`'s braid arrangement through the point, is exactly the set of
within-bead pairs of `c` (`zeroSetEquiv`).  Localizing there returns the finer chain's own COM:

    (braidDirectSum a.dims).localAt _  =  COM.map (zeroSetEquiv f).symm (braidDirectSum c.dims)

So `localCOM x` is an invariant of the **point**, not of the chart (`localAt_eq_localCOM`), and
moving to a finer stratum **deletes** walls: the chart's covectors restrict *onto* the local ones
along the ground-set embedding `groundEmb f` (`covectors_comap_image`) — upper semicontinuity, and
the degeneration is a COM minor.

Gotchas: `EventObj a` is defeq to `beadEvent a.dims`, so `eventMap`/`beadOf` apply to the ground-set
combinatorics on the nose.  `braidDirectSumGround dims` is a nested `Sum`; the working normal form
is `groundEvents` — a ground element **is** the ordered pair of events it compares.
-/

open CategoryTheory Opposite CubeChain SignType

namespace CubeChains

/-! ## Transport of a COM along a relabelling of the ground set -/

namespace COM

variable {E E' : Type*}

theorem ext_covectors : ∀ {L L' : COM E}, L.covectors = L'.covectors → L = L'
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, h => by cases h; rfl

/-- Transport a COM along a bijection of ground sets.  Stated as a **preimage** (`Y ∘ σ` is a
covector of `L`) because `comp`, `sep` and `faceLE` are pointwise, so FS/SE reindex on the nose;
`map_covectors` is the image form. -/
def map (σ : E ≃ E') (L : COM E) : COM E' where
  covectors := {Y | (fun e => Y (σ e)) ∈ L.covectors}
  carrier_nonempty := by
    obtain ⟨X, hX⟩ := L.carrier_nonempty
    refine ⟨fun e' => X (σ.symm e'), ?_⟩
    change (fun e => X (σ.symm (σ e))) ∈ L.covectors
    simpa only [Equiv.symm_apply_apply] using hX
  faceSymm X hX Y hY := L.faceSymm _ hX _ hY
  strongElim X hX Y hY e' he' := by
    have hmem : ∀ f' : E', σ.symm f' ∈ SignVec.sep (fun e => X (σ e)) (fun e => Y (σ e)) ↔
        f' ∈ SignVec.sep X Y := by
      intro f'
      simp only [SignVec.sep, Set.mem_setOf_eq, σ.apply_symm_apply]
    obtain ⟨Z, hZ, hZe, hZf⟩ := L.strongElim _ hX _ hY (σ.symm e') ((hmem e').mpr he')
    refine ⟨fun f' => Z (σ.symm f'), ?_, hZe, fun f' hf' => ?_⟩
    · change (fun e => Z (σ.symm (σ e))) ∈ L.covectors
      simpa only [Equiv.symm_apply_apply] using hZ
    · have h := hZf (σ.symm f') (fun hc => hf' ((hmem f').mp hc))
      simpa only [SignVec.comp, σ.apply_symm_apply] using h

@[simp] theorem mem_map_covectors {σ : E ≃ E'} {L : COM E} {Y : SignVec E'} :
    Y ∈ (L.map σ).covectors ↔ (fun e => Y (σ e)) ∈ L.covectors := Iff.rfl

/-- The covectors of the transported COM are the reindexed covectors. -/
theorem map_covectors (σ : E ≃ E') (L : COM E) :
    (L.map σ).covectors = (fun X : SignVec E => fun e' => X (σ.symm e')) '' L.covectors := by
  ext Y
  constructor
  · intro hY
    refine ⟨fun e => Y (σ e), hY, funext fun e' => ?_⟩
    change Y (σ (σ.symm e')) = Y e'
    rw [σ.apply_symm_apply]
  · rintro ⟨X, hX, rfl⟩
    change (fun e => X (σ.symm (σ e))) ∈ L.covectors
    simpa only [Equiv.symm_apply_apply] using hX

end COM

/-! ## A ground element is the pair of events it compares

`braidDirectSumGround dims` is a nested `Sum` of braid ground sets, one per bead.  `groundEvents`
sends a ground element to the two events it compares: same bead, first coordinate before the
second. -/

/-- Two events of a chain with the same bead and the same coordinate value are equal. -/
theorem beadEvent_ext {dims : List ℕ+} {e e' : beadEvent dims} (h1 : e.1 = e'.1)
    (h2 : (e.2 : ℕ) = (e'.2 : ℕ)) : e = e' := by
  obtain ⟨i, p⟩ := e
  obtain ⟨j, q⟩ := e'
  have hij : i = j := h1
  subst hij
  exact congrArg (fun x => (⟨i, x⟩ : beadEvent dims)) (Fin.ext (h2 : (p : ℕ) = (q : ℕ)))

/-- The **pair of events compared** by a ground element of `braidDirectSum dims`. -/
def groundEvents : (dims : List ℕ+) → braidDirectSumGround dims → beadEvent dims × beadEvent dims
  | [] => fun g => g.1.1.elim0
  | _ :: rest =>
      Sum.elim
        (fun e => (⟨⟨0, Nat.succ_pos _⟩, e.1.1⟩, ⟨⟨0, Nat.succ_pos _⟩, e.1.2⟩))
        (fun g => (⟨(groundEvents rest g).1.1.succ, (groundEvents rest g).1.2⟩,
                   ⟨(groundEvents rest g).2.1.succ, (groundEvents rest g).2.2⟩))

/-- The two events of a ground element share a bead. -/
theorem groundEvents_bead : ∀ (dims : List ℕ+) (g : braidDirectSumGround dims),
    (groundEvents dims g).1.1 = (groundEvents dims g).2.1
  | [], g => g.1.1.elim0
  | _ :: rest, g => by
      rcases g with e | g
      · rfl
      · exact congrArg Fin.succ (groundEvents_bead rest g)

/-- The two events of a ground element are in increasing coordinate order. -/
theorem groundEvents_lt : ∀ (dims : List ℕ+) (g : braidDirectSumGround dims),
    ((groundEvents dims g).1.2 : ℕ) < ((groundEvents dims g).2.2 : ℕ)
  | [], g => g.1.1.elim0
  | _ :: rest, g => by
      rcases g with e | g
      · exact e.2
      · exact groundEvents_lt rest g

theorem groundEvents_injective : ∀ dims : List ℕ+, Function.Injective (groundEvents dims)
  | [] => fun g _ _ => g.1.1.elim0
  | n :: rest => by
      rintro (e | g) (e' | g') h
      · have h1 : (e.1.1 : ℕ) = (e'.1.1 : ℕ) :=
          congrArg (fun pr : beadEvent (n :: rest) × beadEvent (n :: rest) => (pr.1.2 : ℕ)) h
        have h2 : (e.1.2 : ℕ) = (e'.1.2 : ℕ) :=
          congrArg (fun pr : beadEvent (n :: rest) × beadEvent (n :: rest) => (pr.2.2 : ℕ)) h
        exact congrArg Sum.inl (Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2)))
      · exfalso
        have h1 : (0 : ℕ) = ((groundEvents rest g').1.1 : ℕ) + 1 :=
          congrArg (fun pr : beadEvent (n :: rest) × beadEvent (n :: rest) => (pr.1.1 : ℕ)) h
        omega
      · exfalso
        have h1 : ((groundEvents rest g).1.1 : ℕ) + 1 = 0 :=
          congrArg (fun pr : beadEvent (n :: rest) × beadEvent (n :: rest) => (pr.1.1 : ℕ)) h
        omega
      · have hb1 : ((groundEvents rest g).1.1 : ℕ) + 1 = ((groundEvents rest g').1.1 : ℕ) + 1 :=
          congrArg (fun pr : beadEvent (n :: rest) × beadEvent (n :: rest) => (pr.1.1 : ℕ)) h
        have hb2 : ((groundEvents rest g).2.1 : ℕ) + 1 = ((groundEvents rest g').2.1 : ℕ) + 1 :=
          congrArg (fun pr : beadEvent (n :: rest) × beadEvent (n :: rest) => (pr.2.1 : ℕ)) h
        have hv1 : ((groundEvents rest g).1.2 : ℕ) = ((groundEvents rest g').1.2 : ℕ) :=
          congrArg (fun pr : beadEvent (n :: rest) × beadEvent (n :: rest) => (pr.1.2 : ℕ)) h
        have hv2 : ((groundEvents rest g).2.2 : ℕ) = ((groundEvents rest g').2.2 : ℕ) :=
          congrArg (fun pr : beadEvent (n :: rest) × beadEvent (n :: rest) => (pr.2.2 : ℕ)) h
        refine congrArg Sum.inr (groundEvents_injective rest (Prod.ext ?_ ?_))
        · exact beadEvent_ext (Fin.ext (by omega)) hv1
        · exact beadEvent_ext (Fin.ext (by omega)) hv2

/-- **Every within-bead ordered pair of events is a ground element.** -/
theorem groundEvents_exists : ∀ (dims : List ℕ+) (e e' : beadEvent dims), e.1 = e'.1 →
    ((e.2 : ℕ) < (e'.2 : ℕ)) → ∃ g, groundEvents dims g = (e, e')
  | [], e, _, _, _ => e.1.elim0
  | n :: rest, e, e', h1, h2 => by
      obtain ⟨⟨i, hi⟩, p⟩ := e
      obtain ⟨⟨i', hi'⟩, q⟩ := e'
      have hii : i = i' := congrArg (fun j : Fin (n :: rest).length => (j : ℕ)) h1
      subst hii
      have hpr : hi = hi' := rfl
      subst hpr
      cases i with
      | zero => exact ⟨Sum.inl ⟨(p, q), Fin.lt_def.mpr h2⟩, rfl⟩
      | succ i =>
          have hi0 : i < rest.length := Nat.lt_of_succ_lt_succ hi
          obtain ⟨g, hg⟩ := groundEvents_exists rest (⟨⟨i, hi0⟩, p⟩ : beadEvent rest)
            (⟨⟨i, hi0⟩, q⟩ : beadEvent rest) rfl h2
          have hb1 : ((groundEvents rest g).1.1 : ℕ) = i :=
            congrArg (fun pr : beadEvent rest × beadEvent rest => (pr.1.1 : ℕ)) hg
          have hb2 : ((groundEvents rest g).2.1 : ℕ) = i :=
            congrArg (fun pr : beadEvent rest × beadEvent rest => (pr.2.1 : ℕ)) hg
          refine ⟨Sum.inr g, Prod.ext (beadEvent_ext (Fin.ext ?_) ?_)
            (beadEvent_ext (Fin.ext ?_) ?_)⟩
          · change ((groundEvents rest g).1.1 : ℕ) + 1 = i + 1
            omega
          · exact congrArg (fun pr : beadEvent rest × beadEvent rest => (pr.1.2 : ℕ)) hg
          · change ((groundEvents rest g).2.1 : ℕ) + 1 = i + 1
            omega
          · exact congrArg (fun pr : beadEvent rest × beadEvent rest => (pr.2.2 : ℕ)) hg

/-- The ground element comparing a within-bead ordered pair of events. -/
noncomputable def groundOf (dims : List ℕ+) (e e' : beadEvent dims) (h1 : e.1 = e'.1)
    (h2 : (e.2 : ℕ) < (e'.2 : ℕ)) : braidDirectSumGround dims :=
  (groundEvents_exists dims e e' h1 h2).choose

@[simp] theorem groundEvents_groundOf (dims : List ℕ+) (e e' : beadEvent dims) (h1 : e.1 = e'.1)
    (h2 : (e.2 : ℕ) < (e'.2 : ℕ)) : groundEvents dims (groundOf dims e e' h1 h2) = (e, e') :=
  (groundEvents_exists dims e e' h1 h2).choose_spec

/-- **The covector of a timing, read off the pair of events.**  This is the bridge from the nested
`Sum` to the geometry: a coordinate of `beadCovector` is the comparison of two events. -/
theorem beadCovector_apply : ∀ (dims : List ℕ+) (t : beadEvent dims → ℝ)
    (g : braidDirectSumGround dims),
    beadCovector dims t g = sign (t (groundEvents dims g).1 - t (groundEvents dims g).2)
  | [], _, g => g.1.1.elim0
  | _ :: rest, t, g => by
      rcases g with e | g
      · rfl
      · exact beadCovector_apply rest (beadTail t) g

/-! ## The zero set of a refinement's covector -/

variable {K : BPSet} {c a : Ch K}

theorem eventMap_fst (f : c ⟶ a) (x : EventObj c) :
    (eventMap f x).1 = blockIdx fᵂ x.1 := rfl

/-- Inside one bead of the finer chain the event map preserves and reflects the coordinate order
(it is the order embedding `faceEmb` of that bead's block face). -/
theorem eventMap_val_lt_iff (f : c ⟶ a) {x y : EventObj c} (hb : x.1 = y.1) :
    (((eventMap f x).2 : ℕ) < ((eventMap f y).2 : ℕ)) ↔ ((x.2 : ℕ) < (y.2 : ℕ)) := by
  obtain ⟨j, u⟩ := x
  obtain ⟨j', v⟩ := y
  have hj : j = j' := hb
  subst hj
  change ((faceEmb (blockFace fᵂ j) u : Fin _) : ℕ)
      < ((faceEmb (blockFace fᵂ j) v : Fin _) : ℕ) ↔ _
  rw [← Fin.lt_def, ← Fin.lt_def]
  exact (faceEmb (blockFace fᵂ j)).lt_iff_lt

/-- **The wall inclusion.**  A within-bead pair of the finer chain `c` is a within-bead pair of the
chart `a` — the wall of `a` that still passes through the point. -/
noncomputable def groundMap (f : c ⟶ a) (w : braidDirectSumGround c.dims) :
    braidDirectSumGround a.dims :=
  groundOf a.dims (eventMap f (groundEvents c.dims w).1) (eventMap f (groundEvents c.dims w).2)
    (by rw [eventMap_fst, eventMap_fst, groundEvents_bead])
    ((eventMap_val_lt_iff f (groundEvents_bead c.dims w)).mpr (groundEvents_lt c.dims w))

@[simp] theorem groundEvents_groundMap (f : c ⟶ a) (w : braidDirectSumGround c.dims) :
    groundEvents a.dims (groundMap f w)
      = (eventMap f (groundEvents c.dims w).1, eventMap f (groundEvents c.dims w).2) :=
  groundEvents_groundOf _ _ _ _ _

theorem groundMap_injective (f : c ⟶ a) : Function.Injective (groundMap f) := by
  intro w w' h
  have hE : (eventMap f (groundEvents c.dims w).1, eventMap f (groundEvents c.dims w).2)
      = (eventMap f (groundEvents c.dims w').1, eventMap f (groundEvents c.dims w').2) := by
    rw [← groundEvents_groundMap, ← groundEvents_groundMap, h]
  exact groundEvents_injective c.dims
    (Prod.ext (eventMap_injective_hom f (congrArg Prod.fst hE))
      (eventMap_injective_hom f (congrArg Prod.snd hE)))

/-! ### `refineCovector` reads the bead map -/

theorem refineCovector_apply (f : c ⟶ a) (g : braidDirectSumGround a.dims) :
    refineCovector f g
      = sign (((beadOf f (groundEvents a.dims g).1 : ℕ) : ℝ)
          - ((beadOf f (groundEvents a.dims g).2 : ℕ) : ℝ)) := by
  rw [refineCovector, beadCovector_apply]
  rfl

/-- **The walls through the point are the ties.**  A wall of the chart survives at the schedule
exactly when its two events fire in the same bead of the finer chain. -/
theorem refineCovector_eq_zero_iff (f : c ⟶ a) (g : braidDirectSumGround a.dims) :
    refineCovector f g = 0 ↔
      beadOf f (groundEvents a.dims g).1 = beadOf f (groundEvents a.dims g).2 := by
  rw [refineCovector_apply, sign_eq_zero_iff, sub_eq_zero]
  exact ⟨fun h => Fin.ext (Nat.cast_injective h), fun h => by rw [h]⟩

theorem refineCovector_groundMap (f : c ⟶ a) (w : braidDirectSumGround c.dims) :
    refineCovector f (groundMap f w) = 0 := by
  rw [refineCovector_eq_zero_iff, groundEvents_groundMap]
  simp only [beadOf_eventMap]
  exact groundEvents_bead c.dims w

/-- The covector of a schedule is a covector of its chart's COM (any timing realizes one). -/
theorem refineCovector_mem (f : c ⟶ a) : refineCovector f ∈ (braidDirectSum a.dims).covectors :=
  beadCovector_mem a.dims _

/-- **The zero set is the finer chain's ground set.**  Deleting the walls that miss the point leaves
exactly the within-bead pairs of `c`. -/
noncomputable def zeroSetEquiv (f : c ⟶ a) :
    {g : braidDirectSumGround a.dims // refineCovector f g = 0} ≃ braidDirectSumGround c.dims :=
  (Equiv.ofBijective
    (fun w : braidDirectSumGround c.dims =>
      (⟨groundMap f w, refineCovector_groundMap f w⟩ :
        {g : braidDirectSumGround a.dims // refineCovector f g = 0}))
    ⟨fun w w' h => groundMap_injective f (congrArg Subtype.val h), by
      rintro ⟨g, hg⟩
      obtain ⟨x, hx⟩ : ∃ x : EventObj c, eventMap f x = (groundEvents a.dims g).1 :=
        ⟨preEvent f _, eventMap_preEvent f _⟩
      obtain ⟨y, hy⟩ : ∃ y : EventObj c, eventMap f y = (groundEvents a.dims g).2 :=
        ⟨preEvent f _, eventMap_preEvent f _⟩
      have hbead : x.1 = y.1 := by
        have hx1 : beadOf f (eventMap f x) = x.1 := beadOf_eventMap f x
        have hy1 : beadOf f (eventMap f y) = y.1 := beadOf_eventMap f y
        rw [hx] at hx1
        rw [hy] at hy1
        rw [← hx1, ← hy1]
        exact (refineCovector_eq_zero_iff f g).mp hg
      have hlt : (x.2 : ℕ) < (y.2 : ℕ) := by
        refine (eventMap_val_lt_iff f hbead).mp ?_
        rw [hx, hy]
        exact groundEvents_lt a.dims g
      obtain ⟨w, hw⟩ := groundEvents_exists c.dims x y hbead hlt
      refine ⟨w, Subtype.ext (groundEvents_injective a.dims ?_)⟩
      rw [groundEvents_groundMap, hw, hx, hy]
      rfl⟩).symm

@[simp] theorem zeroSetEquiv_symm_apply (f : c ⟶ a) (w : braidDirectSumGround c.dims) :
    ((zeroSetEquiv f).symm w : braidDirectSumGround a.dims) = groundMap f w := rfl

theorem groundMap_zeroSetEquiv (f : c ⟶ a)
    (u : {g : braidDirectSumGround a.dims // refineCovector f g = 0}) :
    groundMap f (zeroSetEquiv f u) = u.1 :=
  congrArg Subtype.val ((zeroSetEquiv f).symm_apply_apply u)

/-! ## Deletion and lifting of covectors -/

/-- **Deletion.**  Restricting a chart covector to the walls through the point gives a covector of
the finer chain's COM: restrict the realizing timing along `eventMap`. -/
theorem comap_mem_covectors (f : c ⟶ a) {Y : SignVec (braidDirectSumGround a.dims)}
    (hY : Y ∈ (braidDirectSum a.dims).covectors) :
    (fun w => Y (groundMap f w)) ∈ (braidDirectSum c.dims).covectors := by
  obtain ⟨t, -, rfl⟩ := beadCovector_surjOn a.dims Y hY
  have hfun : (fun w => beadCovector a.dims t (groundMap f w))
      = beadCovector c.dims (fun x : EventObj c => t (eventMap f x)) := by
    funext w
    rw [beadCovector_apply, beadCovector_apply, groundEvents_groundMap]
  rw [hfun]
  exact beadCovector_mem c.dims _

/-- A unit-separated leading term dominates a bounded perturbation. -/
private theorem sign_dominant {M u d : ℝ} (hM : 1 ≤ M) (hd1 : -(M - 1) ≤ d) (hd2 : d ≤ M - 1)
    (hu : 1 ≤ u ∨ u ≤ -1) : sign (M * u + d) = sign u := by
  rcases hu with h | h
  · have h1 : M * 1 ≤ M * u := mul_le_mul_of_nonneg_left h (by linarith)
    rw [mul_one] at h1
    rw [sign_pos (by linarith), sign_pos (by linarith)]
  · have h1 : M * u ≤ M * (-1) := mul_le_mul_of_nonneg_left h (by linarith)
    rw [mul_neg_one] at h1
    rw [sign_neg (by linarith), sign_neg (by linarith)]

/-- **Lifting.**  Every covector of the finer chain's COM is the restriction of a chart covector
*above the point*: perturb the point's bead-index timing by a small copy of the local one, so the
strict cross-bead comparisons survive (`sign_dominant`) and the ties resolve as prescribed. -/
theorem exists_covector_faceLE (f : c ⟶ a) {W : SignVec (braidDirectSumGround c.dims)}
    (hW : W ∈ (braidDirectSum c.dims).covectors) :
    ∃ Y ∈ (braidDirectSum a.dims).covectors,
      refineCovector f ⊑ Y ∧ ∀ w, Y (groundMap f w) = W w := by
  obtain ⟨s, -, rfl⟩ := beadCovector_surjOn c.dims W hW
  obtain ⟨A, hA⟩ := (Set.finite_range s).bddAbove
  obtain ⟨B, hB⟩ := (Set.finite_range s).bddBelow
  set M : ℝ := A - B + 1 with hMdef
  set t : EventObj a → ℝ := fun e => M * ((beadOf f e : ℕ) : ℝ) + s (preEvent f e) with htdef
  have hbnd : ∀ e e' : EventObj a,
      -(M - 1) ≤ s (preEvent f e) - s (preEvent f e') ∧ s (preEvent f e) - s (preEvent f e') ≤ M - 1
        ∧ (1 : ℝ) ≤ M := by
    intro e e'
    have h1 : B ≤ s (preEvent f e) := hB (Set.mem_range_self _)
    have h2 : s (preEvent f e) ≤ A := hA (Set.mem_range_self _)
    have h3 : B ≤ s (preEvent f e') := hB (Set.mem_range_self _)
    have h4 : s (preEvent f e') ≤ A := hA (Set.mem_range_self _)
    refine ⟨by rw [hMdef]; linarith, by rw [hMdef]; linarith, by rw [hMdef]; linarith⟩
  refine ⟨beadCovector a.dims t, beadCovector_mem a.dims t, fun g => ?_, fun w => ?_⟩
  · -- the strict comparisons of the point are preserved
    by_cases h0 : refineCovector f g = 0
    · exact Or.inl h0
    refine Or.inr ?_
    obtain ⟨hd1, hd2, hM⟩ := hbnd (groundEvents a.dims g).1 (groundEvents a.dims g).2
    have hne : beadOf f (groundEvents a.dims g).1 ≠ beadOf f (groundEvents a.dims g).2 :=
      fun hc => h0 ((refineCovector_eq_zero_iff f g).mpr hc)
    have hu : (1 : ℝ) ≤ ((beadOf f (groundEvents a.dims g).1 : ℕ) : ℝ)
          - ((beadOf f (groundEvents a.dims g).2 : ℕ) : ℝ)
        ∨ ((beadOf f (groundEvents a.dims g).1 : ℕ) : ℝ)
          - ((beadOf f (groundEvents a.dims g).2 : ℕ) : ℝ) ≤ -1 := by
      have hval : (beadOf f (groundEvents a.dims g).1 : ℕ)
          ≠ (beadOf f (groundEvents a.dims g).2 : ℕ) := fun hc => hne (Fin.ext hc)
      rcases Nat.lt_or_ge (beadOf f (groundEvents a.dims g).1 : ℕ)
        (beadOf f (groundEvents a.dims g).2 : ℕ) with hlt | hge
      · right
        have : ((beadOf f (groundEvents a.dims g).1 : ℕ) : ℝ) + 1
            ≤ ((beadOf f (groundEvents a.dims g).2 : ℕ) : ℝ) := by exact_mod_cast hlt
        linarith
      · left
        have hgt : (beadOf f (groundEvents a.dims g).2 : ℕ)
            < (beadOf f (groundEvents a.dims g).1 : ℕ) := lt_of_le_of_ne hge (Ne.symm hval)
        have : ((beadOf f (groundEvents a.dims g).2 : ℕ) : ℝ) + 1
            ≤ ((beadOf f (groundEvents a.dims g).1 : ℕ) : ℝ) := by exact_mod_cast hgt
        linarith
    rw [refineCovector_apply, beadCovector_apply]
    have hdiff : t (groundEvents a.dims g).1 - t (groundEvents a.dims g).2
        = M * (((beadOf f (groundEvents a.dims g).1 : ℕ) : ℝ)
            - ((beadOf f (groundEvents a.dims g).2 : ℕ) : ℝ))
          + (s (preEvent f (groundEvents a.dims g).1) - s (preEvent f (groundEvents a.dims g).2)) :=
      by rw [htdef]; ring
    rw [hdiff, sign_dominant hM hd1 hd2 hu]
  · -- on the walls through the point the perturbation is all there is
    rw [beadCovector_apply, beadCovector_apply, groundEvents_groundMap]
    have hb : (groundEvents c.dims w).1.1 = (groundEvents c.dims w).2.1 :=
      groundEvents_bead c.dims w
    have hval : t (eventMap f (groundEvents c.dims w).1) - t (eventMap f (groundEvents c.dims w).2)
        = s (groundEvents c.dims w).1 - s (groundEvents c.dims w).2 := by
      rw [htdef]
      simp only [beadOf_eventMap, preEvent_eventMap, hb]
      ring
    rw [hval]

/-! ## The theorem: the local COM is the chart's COM, localized -/

/-- **The local COM at a schedule is the localization of any chart's COM at the schedule's
covector.**  Its ground set is the walls of the chart through the point (`zeroSetEquiv`) and its
covectors are their restrictions: deletion (`comap_mem_covectors`) and lifting
(`exists_covector_faceLE`) are inverse. -/
theorem localAt_refineCovector (f : c ⟶ a) :
    (braidDirectSum a.dims).localAt (refineCovector_mem f)
      = COM.map (zeroSetEquiv f).symm (braidDirectSum c.dims) := by
  refine COM.ext_covectors (Set.ext fun Z => ⟨?_, ?_⟩)
  · rintro ⟨Y, hY, -, rfl⟩
    exact comap_mem_covectors f hY
  · intro hZ
    obtain ⟨Y, hY, hface, hval⟩ := exists_covector_faceLE f hZ
    refine ⟨Y, hY, hface, funext fun u => ?_⟩
    have h := hval (zeroSetEquiv f u)
    rw [groundMap_zeroSetEquiv, (zeroSetEquiv f).symm_apply_apply] at h
    exact h.symm

/-! ## Corollaries: chart-independence, and walls are deleted -/

/-- The covector of the schedule `x` in the chart `a`: the bead times drop out. -/
theorem beadCovector_sched (x : Sched K) {a : Ch K} (f : x.chain ⟶ a) :
    beadCovector a.dims (spread f x.2) = refineCovector f :=
  beadCovector_spread f x.2

/-- **Chart-independence.**  In *any* chart `a` containing `x` (`f : x.chain ⟶ a`), localizing the
chart's COM at `x`'s covector returns `localCOM x`.  The local COM is an invariant of the point. -/
theorem localAt_eq_localCOM (x : Sched K) {a : Ch K} (f : x.chain ⟶ a) :
    (braidDirectSum a.dims).localAt (refineCovector_mem f)
      = COM.map (zeroSetEquiv f).symm (localCOM x) :=
  localAt_refineCovector f

/-- The walls of the chart that survive at the point are exactly the ground set of the local COM. -/
theorem range_groundMap (f : c ⟶ a) :
    Set.range (groundMap f) = {g : braidDirectSumGround a.dims | refineCovector f g = 0} := by
  ext g
  constructor
  · rintro ⟨w, rfl⟩
    exact refineCovector_groundMap f w
  · intro hg
    exact ⟨zeroSetEquiv f ⟨g, hg⟩, groundMap_zeroSetEquiv f ⟨g, hg⟩⟩

/-- **Upper semicontinuity.**  The ground set of the finer (more generic) chain's COM embeds into
the chart's as the walls through the point; all other walls of the chart are strict there, hence
locally constant, hence deleted. -/
noncomputable def groundEmb (f : c ⟶ a) :
    braidDirectSumGround c.dims ↪ braidDirectSumGround a.dims :=
  ⟨groundMap f, groundMap_injective f⟩

/-- **The degeneration is a COM minor.**  Restriction along the wall inclusion carries the chart's
covectors *onto* those of the local COM — the finer COM is the chart's COM with the missed walls
deleted. -/
theorem covectors_comap_image (f : c ⟶ a) :
    (fun (Y : SignVec (braidDirectSumGround a.dims)) w => Y (groundMap f w))
        '' (braidDirectSum a.dims).covectors
      = (braidDirectSum c.dims).covectors := by
  ext W
  constructor
  · rintro ⟨Y, hY, rfl⟩
    exact comap_mem_covectors f hY
  · intro hW
    obtain ⟨Y, hY, -, hval⟩ := exists_covector_faceLE f hW
    exact ⟨Y, hY, funext hval⟩

end CubeChains
