import CubeChains.Concurrency.Presentation.PartialAtom
import CubeChains.Concurrency.Merge.CubeThin
import CubeChains.Machinery.Braid.Matsumoto
import CubeChains.Concurrency.Presentation.ChartFibre

/-!
# Concurrency/Presentation/CubeChartAction — the cube's atoms are an Artin family

`atomAct` is a *partial* map on the charts of `□n` over the run, and `chartActionAt` is the monoid
hom `PosBraid n →* _` it generates — `IsArtinFamily` is the whole input, so nothing chooses a
presentation of the braid monoid.

The step is computed rather than bounded: `atomAct` is defined exactly at an *ascent* of the
chart's crossing permutation, and multiplies it by `adjT k` (`atomAct_eq_some_iff`).  Both Artin
relations then read off `adjT`: each three-letter route is defined exactly when the window it
touches is increasing, so no codimension-two cell is named.

Nothing here depends on `hasDiamonds_cube` or on `Merge/CubeFaces`' meet layer, which are what
`word_unique` — hence thinness — rests on.

This is `ChartFibre`'s machine at `Y N = RunChart (□n) N`; `SliceFibre` is the other instance, and
reaches the same weak order through the base's slice rather than through the cube's own squares.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

variable {n : ℕ}

/-- Charts of `K` over the run of `N` events. -/
abbrev RunChart (K : BPSet) (N : ℕ) : Type := (wedgeHoms K).obj (op (zObj (𝟙^N)))

theorem exists_square_atomAct {K : BPSet} (h : SeparatesMerges K) {N : ℕ} {k : Fin (N - 1)}
    {x y : RunChart K N} (hp : atomAct h k x = some y) :
    ∃ z : ⋁(atomComp N k) ⟶ K,
      Hom.φ (mergeOnes N k) ≫ z = x ∧ Hom.φ (atomOnes N k) ≫ z = y := by
  rw [atomAct, Option.map_eq_some_iff] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  exact ⟨z, (mergeLift_eq_some_iff _ x z).mp hz, rfl⟩

noncomputable def crossOnes (x : RunChart (□n) n) : Perm (Fin n) :=
  cross (chartChain (zObj (𝟙^n)).dims x)

theorem crossOnes_injective : Function.Injective (crossOnes (n := n)) := by
  intro x y h
  have he := run_eq_of_cross_eq (r := chartChain (𝟙^n) x) (r' := chartChain (𝟙^n) y) rfl rfl h
  obtain ⟨hd, hm⟩ := Obj.eq_mk_of_eq he
  rw [Subsingleton.elim hd rfl] at hm
  simpa using hm

/-- A chart of the run is a run of the cube, and a run is its firing order. -/
theorem crossOnes_eq_crossRun (x : RunChart (□n) n) :
    crossOnes x = crossRun (onesChartEquiv n x) := rfl

theorem crossOnes_surjective : Function.Surjective (crossOnes (n := n)) := fun σ => by
  obtain ⟨r, hr⟩ := crossRun_bijective.2 σ
  exact ⟨(onesChartEquiv n).symm r, by rw [crossOnes_eq_crossRun, Equiv.apply_symm_apply, hr]⟩

/-- **A chart over the run is its crossing permutation.** -/
noncomputable def crossOnesEquiv (n : ℕ) : RunChart (□n) n ≃ Perm (Fin n) :=
  Equiv.ofBijective crossOnes ⟨crossOnes_injective, crossOnes_surjective⟩

@[simp] theorem crossOnesEquiv_apply (x : RunChart (□n) n) : crossOnesEquiv n x = crossOnes x := rfl

@[simp] theorem crossOnes_symm (σ : Perm (Fin n)) : crossOnes ((crossOnesEquiv n).symm σ) = σ :=
  (crossOnesEquiv n).apply_symm_apply σ

/-- A cartesian lift crosses what it lies over. -/
theorem crossPerm_homOfRestrict {K : BPSet} {a b : Ch Zbp} {N : ℕ} (hN : dimSum a.dims = N)
    (w : a ⟶ b) {x : ⋁a.dims ⟶ K} {y : ⋁b.dims ⟶ K}
    (h : (wedgeHoms K).map w.op y = x) :
    crossPerm (a := chartChain a.dims x) (b := chartChain b.dims y) hN (homOfRestrict w h)
      = crossPerm hN w := rfl

/-- …so a lift's `cross` drops by the base arrow's crossing permutation. -/
theorem cross_homOfRestrict {a b : Ch Zbp} (hN : dimSum a.dims = n) (w : a ⟶ b)
    {x : ⋁a.dims ⟶ □n} {y : ⋁b.dims ⟶ □n} (h : (wedgeHoms (□n)).map w.op y = x) :
    cross (chartChain a.dims x) = cross (chartChain b.dims y) * crossPerm hN w := by
  rw [cross_eq_mul (homOfRestrict (K := □n) w h)]
  exact congrArg _ (crossPerm_homOfRestrict hN w h)

/-- **A defined atom step swaps the `k`-th pair**, and is defined only where that pair is not yet
crossed: the merge leg crosses nothing, the atom leg crosses exactly `adjT k`. -/
theorem crossOnes_atomAct {k : Fin (n - 1)} {x y : RunChart (□n) n}
    (hp : atomAct (separatesMerges_cube n) k x = some y) :
    crossOnes y = crossOnes x * adjT k ∧
      crossOnes x (adjLo k) < crossOnes x (adjHi k) := by
  obtain ⟨z, hm, ha⟩ := exists_square_atomAct _ hp
  have hu0 := cross_homOfRestrict (a := zObj (𝟙^n)) (dimSum_replicate n) (mergeOnes n k) hm
  rw [crossPerm_eq_one_of_W _ (W_mergeOnes n k), mul_one] at hu0
  have hu : crossOnes x = cross (chartChain (atomComp n k) z) := hu0
  have hv0 := cross_homOfRestrict (a := zObj (𝟙^n)) (dimSum_replicate n) (atomOnes n k) ha
  rw [crossPerm_atomOnes] at hv0
  have hv : crossOnes y = cross (chartChain (atomComp n k) z) * adjT k := hv0
  have hvk : crossPerm (a := chartChain (zObj (𝟙^n)).dims y)
      (b := chartChain (zObj (atomComp n k)).dims z) (dimSum_replicate n)
      (homOfRestrict (atomOnes n k) ha) = adjT k := by
    rw [crossPerm_homOfRestrict (dimSum_replicate n) (atomOnes n k) ha, crossPerm_atomOnes]
  have hdesc := cross_descent_of_crossPerm_adjT (homOfRestrict (atomOnes n k) ha) hvk
  refine ⟨by rw [hv, hu], ?_⟩
  have hx : crossOnes x = crossOnes y * adjT k := by rw [hv, hu, mul_assoc, adjT_mul_self, mul_one]
  rw [hx]
  simpa only [Perm.mul_apply, adjT_lo, adjT_hi] using hdesc

/-- **…and it is defined at every ascent**: the square is the atom face of the flipped run, and the
leg from `x` into it crosses nothing, so it is *the* merge (`existsUnique_W_ones`). -/
theorem atomAct_isSome {k : Fin (n - 1)} {x : RunChart (□n) n}
    (hasc : crossOnes x (adjLo k) < crossOnes x (adjHi k)) :
    (atomAct (separatesMerges_cube n) k x).isSome := by
  have hd : (crossOnes x * adjT k) (adjHi k) < (crossOnes x * adjT k) (adjLo k) := by
    simpa only [Perm.mul_apply, adjT_lo, adjT_hi] using hasc
  have hr : cross (runAt (crossOnes x * adjT k)).chain = crossOnes x * adjT k := cross_runAt _
  obtain ⟨d, -, hcd, hdd⟩ := exists_atom_face
    (r := (runAt (crossOnes x * adjT k)).chain)
    (fun t ht => List.eq_of_mem_replicate
      (by rw [← run_dims (runAt (crossOnes x * adjT k))]; exact ht))
    (by rw [hr]; exact hd)
  rw [hr, mul_assoc, adjT_mul_self, mul_one] at hcd
  obtain ⟨dd, dm⟩ := d
  dsimp only at hcd hdd
  subst hdd
  -- the leg from `x`'s run into the square
  obtain ⟨v⟩ := nonempty_runHom (⟨atomComp n k, dm⟩ : Ch (□n))
  rw [hcd] at v
  rw [← run_eq_of_cross_eq (r := chartChain (zObj (𝟙^n)).dims x) rfl
    (run_dims (runAt (crossOnes x))) (cross_runAt (crossOnes x)).symm] at v
  -- it crosses nothing, so it is the merge
  have hW : W Zbp (zHom (Hom.φ v)) := by
    rw [W_iff_crossPerm_eq_one (dimSum_replicate n), crossPerm_zHom (dimSum_replicate n) v,
      ← W_iff_crossPerm_eq_one (dimSum_replicate n) v]
    exact W_of_cross_eq v hcd.symm
  have hmerge : Hom.φ v = Hom.φ (mergeOnes n k) := by
    rw [← zHom_φ (Hom.φ v), (existsUnique_W_ones (dimSum_atomComp n k)).unique hW
      (W_mergeOnes n k)]
  have hlift : mergeLift (separatesMerges_cube n _ (W_mergeOnes n k)) x = some dm :=
    (mergeLift_eq_some_iff (w := mergeOnes n k) _ x dm).mpr
      (by change Hom.φ (mergeOnes n k) ≫ dm = x; rw [← hmerge]; exact v.w)
  rw [atomAct, hlift]
  rfl

/-- **The cube's atom step in closed form**: defined exactly at an ascent, where it multiplies the
crossing permutation by `adjT k`. -/
theorem atomAct_eq_some_iff {k : Fin (n - 1)} {x y : RunChart (□n) n} :
    atomAct (separatesMerges_cube n) k x = some y ↔
      crossOnes x (adjLo k) < crossOnes x (adjHi k) ∧ crossOnes y = crossOnes x * adjT k := by
  refine ⟨fun hp => ⟨(crossOnes_atomAct hp).2, (crossOnes_atomAct hp).1⟩, ?_⟩
  rintro ⟨hasc, hy⟩
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp (atomAct_isSome hasc)
  rw [hy']
  exact congrArg _ (crossOnes_injective (((crossOnes_atomAct hy').1).trans hy.symm))

/-- **The atom family of the cube**, as partial endomorphisms of the charts over the run. -/
noncomputable def cubeAtom (n : ℕ) (k : Fin (n - 1)) :
    Function.End (Option (RunChart (□n) n)) :=
  fun o => o.bind (atomAct (separatesMerges_cube n) k)

theorem cubeAtom_eq_some_iff {k : Fin (n - 1)} {o : Option (RunChart (□n) n)}
    {y : RunChart (□n) n} :
    cubeAtom n k o = some y ↔ ∃ z, o = some z ∧
      crossOnes z (adjLo k) < crossOnes z (adjHi k) ∧ crossOnes y = crossOnes z * adjT k := by
  rw [cubeAtom, Option.bind_eq_some_iff]
  exact ⟨fun ⟨z, hz, h⟩ => ⟨z, hz, (atomAct_eq_some_iff.mp h).1, (atomAct_eq_some_iff.mp h).2⟩,
    fun ⟨z, hz, ha, hc⟩ => ⟨z, hz, atomAct_eq_some_iff.mpr ⟨ha, hc⟩⟩⟩

/-- A step out of an ascent exists, with its value named. -/
theorem exists_cubeAtom {k : Fin (n - 1)} {x : RunChart (□n) n}
    (hasc : crossOnes x (adjLo k) < crossOnes x (adjHi k)) :
    ∃ z, cubeAtom n k (some x) = some z ∧ crossOnes z = crossOnes x * adjT k := by
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (atomAct_isSome hasc)
  exact ⟨z, hz, (crossOnes_atomAct hz).1⟩

/-! ### The Artin relations

Both are the same shape: a two- (resp. three-) step composite is defined exactly when the window it
touches is increasing, and its value is read off `adjT`.  Only `adjT`'s own relations are used. -/

/-- A far-apart swap leaves the other window's ascent alone. -/
theorem ascent_mul_adjT_far {σ : Perm (Fin n)} {i j : Fin (n - 1)} (h : (i : ℕ) + 1 < (j : ℕ)) :
    (σ * adjT j) (adjLo i) < (σ * adjT j) (adjHi i) ↔ σ (adjLo i) < σ (adjHi i) := by
  rw [Perm.mul_apply, Perm.mul_apply,
    WeakOrder.adjT_apply_of_ne (by simp only [adjLo_val]; omega) (by simp only [adjLo_val]; omega),
    WeakOrder.adjT_apply_of_ne (by simp only [adjHi_val]; omega) (by simp only [adjHi_val]; omega)]

theorem ascent_mul_adjT_far' {σ : Perm (Fin n)} {i j : Fin (n - 1)} (h : (i : ℕ) + 1 < (j : ℕ)) :
    (σ * adjT i) (adjLo j) < (σ * adjT i) (adjHi j) ↔ σ (adjLo j) < σ (adjHi j) := by
  rw [Perm.mul_apply, Perm.mul_apply,
    WeakOrder.adjT_apply_of_ne (by simp only [adjLo_val]; omega) (by simp only [adjLo_val]; omega),
    WeakOrder.adjT_apply_of_ne (by simp only [adjHi_val]; omega) (by simp only [adjHi_val]; omega)]

/-- **Far-apart atoms commute.**  Each leaves the other's window untouched, so the two composites
are defined at the same charts, and `adjT_comm` gives them the same value. -/
theorem cubeAtom_comm {i j : Fin (n - 1)} (h : (i : ℕ) + 1 < (j : ℕ)) :
    cubeAtom n i * cubeAtom n j = cubeAtom n j * cubeAtom n i := by
  funext o
  refine Option.ext fun y => ?_
  simp only [Function.End.mul_def, Function.comp_apply, cubeAtom_eq_some_iff]
  constructor
  · rintro ⟨z, ⟨w, rfl, hjw, hzw⟩, hiz, hyz⟩
    obtain ⟨z', hz', hcz'⟩ := exists_cubeAtom (x := w) (k := i)
      ((ascent_mul_adjT_far h).mp (hzw ▸ hiz))
    exact ⟨z', ⟨w, rfl, (ascent_mul_adjT_far h).mp (hzw ▸ hiz), hcz'⟩,
      by rw [hcz']; exact (ascent_mul_adjT_far' h).mpr hjw,
      by rw [hyz, hzw, hcz', mul_assoc, mul_assoc, adjT_comm i j h]⟩
  · rintro ⟨z, ⟨w, rfl, hiw, hzw⟩, hjz, hyz⟩
    obtain ⟨z', hz', hcz'⟩ := exists_cubeAtom (x := w) (k := j)
      ((ascent_mul_adjT_far' h).mp (hzw ▸ hjz))
    exact ⟨z', ⟨w, rfl, (ascent_mul_adjT_far' h).mp (hzw ▸ hjz), hcz'⟩,
      by rw [hcz']; exact (ascent_mul_adjT_far h).mpr hiw,
      by rw [hyz, hzw, hcz', mul_assoc, mul_assoc, adjT_comm i j h]⟩

/-- **A three-letter word, in closed form**: defined exactly where each successive window ascends,
with the value read off `adjT`.  Written once and used for both sides of the braid. -/
theorem cubeAtom_three_iff (k₁ k₂ k₃ : Fin (n - 1)) {o : Option (RunChart (□n) n)}
    {y : RunChart (□n) n} :
    (cubeAtom n k₃ * cubeAtom n k₂ * cubeAtom n k₁) o = some y ↔
      ∃ w, o = some w ∧
        crossOnes w (adjLo k₁) < crossOnes w (adjHi k₁) ∧
        (crossOnes w * adjT k₁) (adjLo k₂) < (crossOnes w * adjT k₁) (adjHi k₂) ∧
        (crossOnes w * adjT k₁ * adjT k₂) (adjLo k₃)
          < (crossOnes w * adjT k₁ * adjT k₂) (adjHi k₃) ∧
        crossOnes y = crossOnes w * adjT k₁ * adjT k₂ * adjT k₃ := by
  simp only [Function.End.mul_def, Function.comp_apply, cubeAtom_eq_some_iff]
  constructor
  · rintro ⟨z₂, ⟨z₁, ⟨w, rfl, h₁, hc₁⟩, h₂, hc₂⟩, h₃, hc₃⟩
    exact ⟨w, rfl, h₁, hc₁ ▸ h₂, by rw [← hc₁, ← hc₂]; exact h₃, by rw [hc₃, hc₂, hc₁]⟩
  · rintro ⟨w, rfl, h₁, h₂, h₃, hy⟩
    obtain ⟨z₁, hz₁, hc₁⟩ := exists_cubeAtom h₁
    obtain ⟨z₂, hz₂, hc₂⟩ := exists_cubeAtom (k := k₂) (x := z₁) (by rw [hc₁]; exact h₂)
    refine ⟨z₂, ⟨z₁, ⟨w, rfl, h₁, hc₁⟩, hc₁ ▸ h₂, hc₂⟩, ?_, ?_⟩
    · rw [hc₂, hc₁]; exact h₃
    · rw [hy, hc₂, hc₁]

/-- **Consecutive atoms braid.**  Both three-letter words are defined exactly when the window they
touch is increasing — the same three inequalities in a different order — and `adjT_braid` gives
them the same value.  No cell of `□n` beyond the two squares each route already names. -/
theorem cubeAtom_braid {i j : Fin (n - 1)} (hij : (j : ℕ) = (i : ℕ) + 1) :
    cubeAtom n i * cubeAtom n j * cubeAtom n i
      = cubeAtom n j * cubeAtom n i * cubeAtom n j := by
  have hm : adjLo j = adjHi i := WeakOrder.adjLo_eq_adjHi hij
  -- the six ways the two swaps move the three window positions
  have eA : ∀ τ : Perm (Fin n), (τ * adjT i) (adjLo i) = τ (adjHi i) := fun τ => by
    rw [Perm.mul_apply, adjT_lo]
  have eB : ∀ τ : Perm (Fin n), (τ * adjT i) (adjHi i) = τ (adjLo i) := fun τ => by
    rw [Perm.mul_apply, adjT_hi]
  have eC : ∀ τ : Perm (Fin n), (τ * adjT i) (adjHi j) = τ (adjHi j) := fun τ => by
    rw [Perm.mul_apply, WeakOrder.adjT_apply_of_ne (by simp only [adjHi_val]; omega)
      (by simp only [adjHi_val]; omega)]
  have eD : ∀ τ : Perm (Fin n), (τ * adjT j) (adjLo i) = τ (adjLo i) := fun τ => by
    rw [Perm.mul_apply, WeakOrder.adjT_apply_of_ne (by simp only [adjLo_val]; omega)
      (by simp only [adjLo_val]; omega)]
  have eE : ∀ τ : Perm (Fin n), (τ * adjT j) (adjHi i) = τ (adjHi j) := fun τ => by
    rw [Perm.mul_apply, ← hm, adjT_lo]
  have eF : ∀ τ : Perm (Fin n), (τ * adjT j) (adjHi j) = τ (adjHi i) := fun τ => by
    rw [Perm.mul_apply, adjT_hi, hm]
  have hval : ∀ τ : Perm (Fin n),
      τ * adjT i * adjT j * adjT i = τ * adjT j * adjT i * adjT j := fun τ =>
    calc τ * adjT i * adjT j * adjT i = τ * (adjT i * adjT j * adjT i) := by group
      _ = τ * (adjT j * adjT i * adjT j) := by rw [adjT_braid i j hij]
      _ = τ * adjT j * adjT i * adjT j := by group
  funext o
  refine Option.ext fun y => ?_
  rw [cubeAtom_three_iff i j i, cubeAtom_three_iff j i j]
  simp only [hm, eA, eB, eC, eD, eE, eF, hval]
  constructor
  · rintro ⟨w, rfl, h₁, h₂, h₃, hy⟩
    exact ⟨w, rfl, h₃, h₂, h₁, hy⟩
  · rintro ⟨w, rfl, h₁, h₂, h₃, hy⟩
    exact ⟨w, rfl, h₃, h₂, h₁, hy⟩

/-- **The cube's atoms are an Artin family** — commutation from `separatesMerges_cube`, braid from
the cube's own cells. -/
theorem isArtinFamily_cubeAtom (n : ℕ) : IsArtinFamily (cubeAtom n) where
  comm _ _ h := cubeAtom_comm h
  braid _ _ h := cubeAtom_braid h

/-- The atom family at strand count `N`, as partial maps of the charts of `□n` over that run. -/
noncomputable def cubeAtomAt (n N : ℕ) (k : Fin (N - 1)) : strictEnd (RunChart (□n) N) :=
  ⟨fun o => o.bind (atomAct (separatesMerges_cube n) k), rfl⟩

/-- Off the cube's own strand count there are no charts at all. -/
theorem isEmpty_runChart {n N : ℕ} (h : N ≠ n) : IsEmpty (RunChart (□n) N) :=
  ⟨fun x => h ((dimSum_replicate N).symm.trans (dimSum_dims_cube (chartChain (𝟙^N) x)))⟩

/-- **The atoms are an Artin family at every strand count** — the cube's own count by
`isArtinFamily_cubeAtom`, the others because there is nothing there to act on. -/
theorem isArtinFamily_cubeAtomAt (n N : ℕ) : IsArtinFamily (cubeAtomAt n N) := by
  rcases eq_or_ne N n with rfl | hne
  · exact ⟨fun i j h => Subtype.ext (cubeAtom_comm h), fun i j h => Subtype.ext (cubeAtom_braid h)⟩
  · haveI := isEmpty_runChart hne
    haveI := subsingleton_strictEnd (X := RunChart (□n) N)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩

/-- **The positive braid monoid acts partially on the charts over the run at each strand count.**
The `ᵐᵒᵖ` is the base's composition order, and it costs nothing: `IsArtinFamily.op`. -/
noncomputable def chartActionAt (n N : ℕ) :
    PosBraid N →* (strictEnd (RunChart (□n) N))ᵐᵒᵖ :=
  PosBraid.liftArtin _ (isArtinFamily_cubeAtomAt n N).op

/-! ### The action in closed form

One atom is one ascent of the crossing permutation, and a hom out of `PosBraid n` is its atoms, so
the whole action is `Machinery/Braid/WeakAction`'s: right multiplication of the crossing
permutation where the lengths add — the right weak order, read as a partial action. -/

/-- **The cube's atom action is the weak action on all of `Sₙ`**, a chart over the run being its
crossing permutation and nothing else.  Both sides are homs out of `PosBraid n`, so it is enough
that the atoms agree — and each is defined exactly at an ascent, where it multiplies by `adjT k`. -/
theorem chartActionAt_eq_weakActionOn (n : ℕ) :
    chartActionAt n n
      = weakActionOn _ ((crossOnesEquiv n).trans (weakSetUniv n).symm) weakDown_univ :=
  (PosBraid.eq_liftArtin (isArtinFamily_cubeAtomAt n n).op _ fun _ =>
    MulOpposite.unop_injective (strictEnd_ext fun _ _ => by
      rw [weakActionOn_adjT_eq_some_iff]
      exact atomAct_eq_some_iff.symm)).symm

/-- **The braid monoid acts by length-additive right multiplication of the crossing permutation**:
`β` is defined at a chart exactly when every one of its crossings is new there.  In particular a
defined `β` is *reduced* — its length is that of its permutation — so it is a simple. -/
theorem chartActionAt_eq_some_iff (β : PosBraid n) (x y : RunChart (□n) n) :
    (chartActionAt n n β).unop.val (some x) = some y ↔
      crossOnes y = crossOnes x * posPermHom n β ∧
        permLen (crossOnes x) + Multiplicative.toAdd (posLen n β) = permLen (crossOnes y) :=
  weakChartUniv_eq_some_iff (chartActionAt n) (crossOnesEquiv n)
    (chartActionAt_eq_weakActionOn n) β x y

end ChainCat
