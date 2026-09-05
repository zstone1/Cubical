import CubeChains.Concurrency.Presentation.SliceFunctor

/-!
# Concurrency/Presentation/SliceExchange — the slice, presented by its run-arrows

The localized slice over any `d` is the weak order on the crossing permutations that `d`'s blocks
allow.  Two halves: a **grading** (`weakOver_le_of_loc_hom`), `CubeWeakOrder`'s argument at an
arbitrary base with nothing cube-specific in it; and one **geometric** fact — a run-arrow permutes
each block of `d` and no more (`index_crossPerm`), so a crossing at `k` says `k` and `k+1` share a
block, which is exactly the arrow out of the `k`-th atom shape.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv Polygraph

namespace ChainCat

variable {d : Ch Zbp} {N : ℕ}

/-! ## The weak order on a slice

`CubeCrossing`/`CubeWeakOrder` at an arbitrary base: `cross` becomes `crossOver`, and no step of
the argument mentions the cube. -/

theorem over_left_dimSum (h : dimSum d.dims = N) (y : Over d) : dimSum y.left.dims = N :=
  (dimSum_eq_of_hom y.hom).trans h

/-- **How much an object of the slice has braided**: the crossing permutation of its own arrow to
the top of the slice. -/
noncomputable def crossOver (h : dimSum d.dims = N) (y : Over d) : Perm (Fin N) :=
  crossPerm (over_left_dimSum h y) y.hom

/-- The crossing count, which is what descends to the localized slice. -/
noncomputable def degOver (h : dimSum d.dims = N) (y : Over d) : ℕ := permLen (crossOver h y)

/-- **Crossings add along an arrow of the slice** — `permLen_crossPerm_comp` at the top. -/
theorem degOver_eq_add (h : dimSum d.dims = N) {y y' : Over d} (m : y ⟶ y') :
    degOver h y = permLen (crossPerm (over_left_dimSum h y) m.left) + degOver h y' := by
  rw [degOver, crossOver, ← Over.w m, permLen_crossPerm_comp]
  rfl

theorem degOver_le (h : dimSum d.dims = N) {y y' : Over d} (m : y ⟶ y') :
    degOver h y' ≤ degOver h y := by rw [degOver_eq_add h m]; omega

theorem degOver_eq_of_W (h : dimSum d.dims = N) {y y' : Over d} {m : y ⟶ y'}
    (hm : (W Zbp).over m) : degOver h y ≤ degOver h y' := by
  have hadd := degOver_eq_add h m
  rw [crossPerm_eq_one_of_W _ hm, permLen_one] at hadd
  omega

/-- **The crossing count on the localized slice** — `Machinery/Grading`'s `deg_le_of_loc_hom`, at a
degree that arrows lower and merges keep. -/
theorem degOver_loc (h : dimSum d.dims = N) {y y' : Over d}
    (g : ((W Zbp).over (X := d)).Q.obj y ⟶ ((W Zbp).over (X := d)).Q.obj y') :
    degOver h y' ≤ degOver h y :=
  deg_le_of_loc_hom (degOver h) (degOver_le h) ((W Zbp).over (X := d)) (degOver_eq_of_W h) g

/-- **Crossings multiply along an arrow of the slice** — `crossPerm_comp` at the top. -/
theorem crossOver_eq_mul (h : dimSum d.dims = N) {y y' : Over d} (m : y ⟶ y') :
    crossOver h y = crossOver h y' * crossPerm (over_left_dimSum h y) m.left := by
  rw [crossOver, ← Over.w m, crossPerm_comp]
  rfl

/-- The weak-order class of an object of the slice. -/
noncomputable def weakOver (h : dimSum d.dims = N) (y : Over d) : WeakOrder N :=
  WeakOrder.of (crossOver h y)

/-- **An arrow of the slice descends the weak order**, by length-additivity of the crossings. -/
theorem weakOver_le (h : dimSum d.dims = N) {y y' : Over d} (m : y ⟶ y') :
    weakOver h y' ≤ weakOver h y := by
  have hmul : crossOver h y' * crossPerm (over_left_dimSum h y) m.left = crossOver h y :=
    (crossOver_eq_mul h m).symm
  have hlen : permLen (crossOver h y') + permLen (crossPerm (over_left_dimSum h y) m.left)
      = permLen (crossOver h y' * crossPerm (over_left_dimSum h y) m.left) := by
    rw [hmul]
    have hadd := degOver_eq_add h m
    rw [degOver, degOver] at hadd
    omega
  have hle := WeakOrder.le_of_mul hlen
  rw [hmul] at hle
  exact hle

theorem weakOver_eq_of_W (h : dimSum d.dims = N) {y y' : Over d} {m : y ⟶ y'}
    (hm : (W Zbp).over m) : weakOver h y = weakOver h y' := by
  rw [weakOver, weakOver, crossOver_eq_mul h m, crossPerm_eq_one_of_W _ hm, mul_one]

/-- **An arrow of the localized slice descends the weak order** — `deg_le_of_loc_hom` at a degree
valued in the weak order rather than in `ℕ`. -/
theorem weakOver_le_of_loc_hom (h : dimSum d.dims = N) {y y' : Over d}
    (g : ((W Zbp).over (X := d)).Q.obj y ⟶ ((W Zbp).over (X := d)).Q.obj y') :
    weakOver h y' ≤ weakOver h y :=
  deg_le_of_loc_hom (weakOver h) (weakOver_le h) ((W Zbp).over (X := d))
    (fun hm => le_of_eq (weakOver_eq_of_W h hm)) g

/-! ## The geometry: an arrow permutes each block and no more -/

/-- **An arrow permutes each block of its target and no more.**  Read the target in its own
standard chart: the source's firing order inverts `crossPerm` (`crossPerm_flatten`), and a
coarsening's beads are the target's blocks read in that order (`beadOf_of_hom`). -/
theorem index_crossPerm {c : Ch Zbp} (hd : dimSum d.dims = N) (hc : dimSum c.dims = N)
    (a : c ⟶ d) (r : Fin N) :
    ((dimComp d.dims hd).index (crossPerm hc a r) : ℕ) = ((dimComp d.dims hd).index r : ℕ) := by
  have hf : (⟨c.dims, a.φ ≫ stdChart hd⟩ : Ch (□N)) ⟶ ⟨d.dims, stdChart hd⟩ := ⟨a.φ, rfl⟩
  have hcross : ∀ q : Fin N,
      crossPerm hc a (flatten (⟨c.dims, a.φ ≫ stdChart hd⟩ : Ch (□N)) q) = q := fun q => by
    have h := crossPerm_flatten hc a (stdChart hd) q
    rwa [flatten_stdChart hd, Perm.one_apply] at h
  have hblock : ∀ q : Fin N, ((dimComp d.dims hd).index q : ℕ)
      = ((dimComp d.dims hd).index
          (flatten (⟨c.dims, a.φ ≫ stdChart hd⟩ : Ch (□N)) q) : ℕ) := fun q => by
    have h1 := beadOf_of_hom hf q
    rw [beadOf_stdChart hd q] at h1
    exact h1
  obtain ⟨q, rfl⟩ := (flatten (⟨c.dims, a.φ ≫ stdChart hd⟩ : Ch (□N))).surjective r
  rw [hcross q, hblock q]

/-- **Distinct blocks are ordered by their members** — `index_monotone` read as an iff. -/
theorem index_lt_iff_lt (hd : dimSum d.dims = N) {x y : Fin N}
    (hne : ((dimComp d.dims hd).index x : ℕ) ≠ ((dimComp d.dims hd).index y : ℕ)) :
    ((dimComp d.dims hd).index x : ℕ) < ((dimComp d.dims hd).index y : ℕ) ↔ x < y := by
  have hmono := (dimComp d.dims hd).index_monotone
  constructor
  · intro hlt
    by_contra hc
    have := hmono (not_lt.mp hc)
    dsimp only at this
    omega
  · intro hlt
    have := hmono (le_of_lt hlt)
    dsimp only at this
    omega

/-- **A crossing forces the cut to be interior**: two events in different blocks of `d` never
cross, so a descent of a run-arrow at `k` says that `k` and `k+1` share a block of `d`. -/
theorem index_adj_eq_of_descent (hd : dimSum d.dims = N) (a : zObj (𝟙^N) ⟶ d) {k : Fin (N - 1)}
    (hdesc : crossPerm (dimSum_replicate N) a (adjHi k)
      < crossPerm (dimSum_replicate N) a (adjLo k)) :
    ((dimComp d.dims hd).index (adjLo k) : ℕ) = ((dimComp d.dims hd).index (adjHi k) : ℕ) := by
  have hmono := (dimComp d.dims hd).index_monotone
  have h1 := hmono (le_of_lt hdesc)
  have h2 := hmono (le_of_lt (show adjLo k < adjHi k by
    rw [Fin.lt_def, adjLo_val, adjHi_val]; omega))
  simp only [index_crossPerm hd (dimSum_replicate N) a] at h1
  dsimp only at h2
  omega

/-- …and that is exactly an arrow out of the `k`-th atom shape. -/
theorem nonempty_atomComp_of_descent (hd : dimSum d.dims = N) (a : zObj (𝟙^N) ⟶ d)
    {k : Fin (N - 1)}
    (hdesc : crossPerm (dimSum_replicate N) a (adjHi k)
      < crossPerm (dimSum_replicate N) a (adjLo k)) :
    Nonempty (zObj (atomComp N k) ⟶ d) := by
  have hsame := index_adj_eq_of_descent hd a hdesc
  refine (nonempty_hom_of_index (dimSum_atomComp N k) hd ?_).map
    fun v => v ≫ eqToHom (eq_zObj d)
  intro x y hxy
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · obtain ⟨rfl, rfl⟩ := eq_adj_of_index_eq N k hxy hlt
    exact Fin.ext hsame
  · rfl
  · obtain ⟨rfl, rfl⟩ := eq_adj_of_index_eq N k hxy.symm hgt
    exact Fin.ext hsame.symm


/-! ## The exchange

At a descent the shortened crossing permutation is realised too, and the step between the two is
the atom square.  This is the whole of fullness that the crossing count cannot supply. -/

/-- **At a descent, the shortened crossing permutation is realised too** —
`exists_crossPerm_of_blocks` at the run: the only pair `adjT k` reorders is `{k, k+1}`, which
`index_adj_eq_of_descent` puts inside a single block of `d`. -/
theorem exists_run_mul_adjT (hd : dimSum d.dims = N) (a : zObj (𝟙^N) ⟶ d) {k : Fin (N - 1)}
    (hdesc : crossPerm (dimSum_replicate N) a (adjHi k)
      < crossPerm (dimSum_replicate N) a (adjLo k)) :
    ∃ a' : zObj (𝟙^N) ⟶ d,
      crossPerm (dimSum_replicate N) a' = crossPerm (dimSum_replicate N) a * adjT k := by
  obtain ⟨l, rfl⟩ : ∃ l : List ℕ+, d = zObj l := ⟨d.dims, (eq_zObj d).symm⟩
  have hsame := index_adj_eq_of_descent hd a hdesc
  have hblk : ∀ x : Fin N, ((dimComp (zObj l).dims hd).index
      ((crossPerm (dimSum_replicate N) a)⁻¹ x) : ℕ)
      = ((dimComp (zObj l).dims hd).index x : ℕ) := fun x => by
    have h := index_crossPerm hd (dimSum_replicate N) a
      ((crossPerm (dimSum_replicate N) a)⁻¹ x)
    simpa using h.symm
  have hadj : ∀ x : Fin N, ((dimComp (zObj l).dims hd).index (adjT k x) : ℕ)
      = ((dimComp (zObj l).dims hd).index x : ℕ) := fun x => by
    by_cases h1 : (x : ℕ) = (k : ℕ)
    · rw [show x = adjLo k from Fin.ext (by rw [adjLo_val]; exact h1), adjT_lo, hsame]
    by_cases h2 : (x : ℕ) = (k : ℕ) + 1
    · rw [show x = adjHi k from Fin.ext (by rw [adjHi_val]; exact h2), adjT_hi, hsame]
    · rw [WeakOrder.adjT_apply_of_ne h1 h2]
  have hinv : ∀ x : Fin N, ((dimComp (zObj l).dims hd).index
      ((crossPerm (dimSum_replicate N) a * adjT k)⁻¹ x) : ℕ)
      = ((dimComp (zObj l).dims hd).index x : ℕ) := fun x => by
    rw [mul_inv_rev, adjT_inv, Perm.mul_apply, hadj, hblk]
  obtain ⟨f, hf⟩ := exists_crossPerm_of_blocks (dimSum_replicate N) hd
    (crossPerm (dimSum_replicate N) a * adjT k)
    (fun p q hpq hlt => by
      have h := congrArg Fin.val hpq
      rw [index_ones, index_ones] at h
      exact absurd (((crossPerm (dimSum_replicate N) a * adjT k)⁻¹).injective (Fin.ext h))
        (ne_of_lt hlt))
    (fun p q hne => by
      rw [index_ones, index_ones, ← hinv p, ← hinv q]
      exact (index_lt_iff_lt hd (by rw [hinv p, hinv q]; exact hne)).trans Fin.lt_def)
  exact ⟨f, hf⟩

theorem RunOver.left_dimSum (h : dimSum d.dims = N) (u : RunOver d) :
    dimSum u.1.left.dims = N := (dimSum_eq_of_hom u.1.hom).trans h

/-- **The source of a run-arrow is forced**: it is the run on `d`'s own events. -/
theorem RunOver.left_eq (h : dimSum d.dims = N) (u : RunOver d) : u.1.left = zObj (𝟙^N) := by
  refine Obj.eq_of_dims ?_
  have hlen : u.1.left.dims.length = N :=
    (dimSum_eq_length_of_ones u.2).symm.trans (RunOver.left_dimSum h u)
  exact hlen ▸ eq_replicate_of_ones u.2

/-- The crossing permutation of a run-arrow, read at `d`'s own event count. -/
noncomputable def RunOver.perm (h : dimSum d.dims = N) (u : RunOver d) : Perm (Fin N) :=
  crossPerm (RunOver.left_dimSum h u) u.1.hom

/-- **A run-arrow is pinned by its crossing permutation.** -/
theorem RunOver.perm_injective (h : dimSum d.dims = N) : Function.Injective (RunOver.perm h) := by
  intro u v huv
  obtain ⟨⟨lu, ⟨⟩, gu⟩, hu⟩ := u
  obtain ⟨⟨lv, ⟨⟩, gv⟩, hv⟩ := v
  obtain rfl : lu = zObj (𝟙^N) := RunOver.left_eq h ⟨Over.mk gu, hu⟩
  obtain rfl : lv = zObj (𝟙^N) := RunOver.left_eq h ⟨Over.mk gv, hv⟩
  obtain rfl : gu = gv := hom_ext_of_crossPerm huv
  rfl

/-- **A descent is a generating step.**  The atom leg out of the shorter run-arrow is the longer
one (`exists_atom_step` at the ascent), and the merge leg is the shorter one. -/
theorem runStep_of_descent (hd : dimSum d.dims = N) {a a' : RunOver d} {k : Fin (N - 1)}
    (hdesc : RunOver.perm hd a (adjHi k) < RunOver.perm hd a (adjLo k))
    (hperm : RunOver.perm hd a' = RunOver.perm hd a * adjT k) : RunStep a a' := by
  obtain ⟨⟨la, ⟨⟩, ga⟩, ha⟩ := a
  obtain ⟨⟨lb, ⟨⟩, gb⟩, hb⟩ := a'
  obtain rfl : la = zObj (𝟙^N) := RunOver.left_eq hd ⟨Over.mk ga, ha⟩
  obtain rfl : lb = zObj (𝟙^N) := RunOver.left_eq hd ⟨Over.mk gb, hb⟩
  replace hdesc : crossPerm (dimSum_replicate N) ga (adjHi k)
      < crossPerm (dimSum_replicate N) ga (adjLo k) := hdesc
  replace hperm : crossPerm (dimSum_replicate N) gb
      = crossPerm (dimSum_replicate N) ga * adjT k := hperm
  have hnk : Nonempty (zObj (atomComp N k) ⟶ d) := nonempty_atomComp_of_descent hd ga hdesc
  have hasc : crossPerm (dimSum_replicate N) gb (adjLo k)
      < crossPerm (dimSum_replicate N) gb (adjHi k) := by
    rw [hperm, Perm.mul_apply, Perm.mul_apply, adjT_lo, adjT_hi]
    exact hdesc
  obtain ⟨w, hmerge, hatom⟩ := exists_atom_step hd k hnk
    (rfl : crossPerm (dimSum_replicate N) gb = crossPerm (dimSum_replicate N) gb) hasc
  have hga : atomOnes N k ≫ w = ga :=
    hom_ext_of_crossPerm (h := dimSum_replicate N) (by rw [hatom, hperm, mul_adjT_adjT]; rfl)
  exact ⟨zObj (atomComp N k), atomOnes N k, mergeOnes N k, w,
    by rw [permLen_crossPerm (dimSum_replicate N), crossPerm_atomOnes]
       exact permLen_adjT k,
    W_mergeOnes N k, hga, hmerge⟩


/-! ## The presentation

The localized slice is a poset, so `Presents.ofThin` asks only that the steps span and the runs
cover.  Spanning is the induction above; covering is the merge out of each object's own run. -/

/-- **A generating step is an arrow of the localized slice**: the atom leg, followed by the
inverted merge leg. -/
theorem nonempty_locOver_hom_of_runStep {a b : RunOver d} (h : RunStep a b) :
    Nonempty (((W Zbp).over (X := d)).Q.obj a.1 ⟶ ((W Zbp).over (X := d)).Q.obj b.1) := by
  obtain ⟨e, t, m, z, -, hm, hta, hmb⟩ := h
  haveI : IsIso (((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)) :=
    Localization.inverts ((W Zbp).over (X := d)).Q ((W Zbp).over (X := d)) _ hm
  exact ⟨((W Zbp).over (X := d)).Q.map (Over.homMk t hta : a.1 ⟶ Over.mk z)
    ≫ inv (((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z))⟩

/-- **The exchange, on 0-cells**: at a descent the shortened run-arrow is a run-arrow over `d`. -/
theorem exists_runOver_mul_adjT (hd : dimSum d.dims = N) (a : RunOver d) {k : Fin (N - 1)}
    (hdesc : RunOver.perm hd a (adjHi k) < RunOver.perm hd a (adjLo k)) :
    ∃ a' : RunOver d, RunOver.perm hd a' = RunOver.perm hd a * adjT k := by
  obtain ⟨⟨la, ⟨⟩, ga⟩, ha⟩ := a
  obtain rfl : la = zObj (𝟙^N) := RunOver.left_eq hd ⟨Over.mk ga, ha⟩
  replace hdesc : crossPerm (dimSum_replicate N) ga (adjHi k)
      < crossPerm (dimSum_replicate N) ga (adjLo k) := hdesc
  obtain ⟨g', hg'⟩ := exists_run_mul_adjT hd ga hdesc
  exact ⟨⟨Over.mk g', fun _ hc => List.eq_of_mem_replicate hc⟩, hg'⟩

/-- **Fullness**: the weak order is spelled by generating steps.  Induction on the crossing count:
`exists_cover_of_lt` picks a descent, and the exchange realises it. -/
theorem nonempty_path_of_le (hd : dimSum d.dims = N) (a b : RunOver d)
    (hle : weakOver hd b.1 ≤ weakOver hd a.1) :
    Nonempty (Quiver.Path (⟨a⟩ : GenObj (runPoly d).Gen) ⟨b⟩) := by
  generalize hn : permLen (RunOver.perm hd a) = n
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    by_cases hab : RunOver.perm hd b = RunOver.perm hd a
    · obtain rfl : b = a := RunOver.perm_injective hd hab
      exact ⟨Quiver.Path.nil⟩
    · obtain ⟨k, hdesc, hcov⟩ := WeakOrder.exists_cover_of_lt hle hab
      obtain ⟨a', ha'⟩ := exists_runOver_mul_adjT hd a hdesc
      have hlen : permLen (RunOver.perm hd a) = permLen (RunOver.perm hd a') + 1 := by
        rw [ha']; exact permLen_mul_adjT_of_descent hdesc
      obtain ⟨p⟩ := ih (permLen (RunOver.perm hd a')) (by omega) a'
        (show weakOver hd b.1 ≤ WeakOrder.of (RunOver.perm hd a') by rw [ha']; exact hcov) rfl
      exact ⟨(Quiver.Hom.toPath (show (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨a'⟩ from
        ⟨runStep_of_descent hd hdesc ha'⟩)).comp p⟩

/-- **Essential surjectivity**: every object of the slice is entered from a run by a merge, which
the localization inverts. -/
theorem exists_runOver_iso (hd : dimSum d.dims = N) (y : Over d) :
    ∃ a : RunOver d, Nonempty (((W Zbp).over (X := d)).Q.obj a.1
      ≅ ((W Zbp).over (X := d)).Q.obj y) := by
  refine ⟨⟨Over.mk (runMerge y.left (over_left_dimSum hd y) ≫ y.hom),
    fun _ hc => List.eq_of_mem_replicate hc⟩, ?_⟩
  haveI : IsIso (((W Zbp).over (X := d)).Q.map
      (Over.homMk (runMerge y.left (over_left_dimSum hd y)) rfl :
        Over.mk (runMerge y.left (over_left_dimSum hd y) ≫ y.hom) ⟶ y)) :=
    Localization.inverts ((W Zbp).over (X := d)).Q ((W Zbp).over (X := d)) _
      (W_runMerge y.left (over_left_dimSum hd y))
  exact ⟨asIso (((W Zbp).over (X := d)).Q.map
    (Over.homMk (runMerge y.left (over_left_dimSum hd y)) rfl : _ ⟶ y))⟩

/-- **The localized slice is presented by its run-arrows**, for every `d`: 0-cells the runs over
`d`, 1-cells one crossing apart, and every parallel pair related — the slice is a poset. -/
noncomputable def runPresentation (hd : dimSum d.dims = N) :
    Presents (runPoly d) (((W Zbp).over (X := d)).Localization) :=
  Presents.ofThin
    { obj := fun a => Localization.Construction.objEquiv ((W Zbp).over (X := d)) a.as.1
      map := fun {_ _} e => (nonempty_locOver_hom_of_runStep e.down).some }
    (fun a b f => nonempty_path_of_le hd a.as b.as (weakOver_le_of_loc_hom hd f))
    (fun c => by
      obtain ⟨y, rfl⟩ : ∃ y : Over d,
          Localization.Construction.objEquiv ((W Zbp).over (X := d)) y = c :=
        ⟨(Localization.Construction.objEquiv _).symm c,
          (Localization.Construction.objEquiv _).apply_symm_apply c⟩
      obtain ⟨a, ⟨i⟩⟩ := exists_runOver_iso hd y
      exact ⟨⟨a⟩, ⟨i⟩⟩)

/-- The 0-cells name their own slice objects, on the nose. -/
theorem runPresentation_at (hd : dimSum d.dims = N) (a : RunOver d) :
    (runPresentation hd).at' ⟨a⟩
      = Localization.Construction.objEquiv ((W Zbp).over (X := d)) (runLabels.ob d a) := rfl

/-- **The family of slice presentations the glue route wants** — at every `d`, unconditionally. -/
noncomputable def runSlicePresentation (d : Ch Zbp) :
    Presents (runPoly d) (((W Zbp).over (X := d)).Localization) :=
  runPresentation (N := dimSum d.dims) rfl

theorem runSlicePresentation_at (d : Ch Zbp) (a : RunOver d) :
    (runSlicePresentation d).at' ⟨a⟩
      = Localization.Construction.objEquiv ((W Zbp).over (X := d)) (runLabels.ob d a) := rfl

/-- **`Ch(K)[W⁻¹]` is presented by the colimit of the slices, for every `K`.**  0-cells the runs
over a chain, 1-cells one crossing apart, 2-cells the weak order in each slice — glued along the
arrows of `Ch K`. -/
noncomputable def presentsChainsRunGlue (K : BPSet) :
    Presents (glue (wedgeHoms K) runPolyFunctor) ((W K).Localization) :=
  presentsChainsRunGlueOf K runSlicePresentation runSlicePresentation_at

end ChainCat
