import CubeChains.Concurrency.Presentation.PartialAtom
import CubeChains.Concurrency.Merge.CubeThin
import CubeChains.Machinery.Braid.Matsumoto
import CubeChains.Concurrency.Presentation.BasePresentation

/-!
# Concurrency/Presentation/CubeChartAction — the cube's atoms are an Artin family

`atomAct` is a *partial* map on the charts of `□n` over the run, and `chartAction` is the monoid
hom `PosBraid n →* _` it generates.  This is the **presentation-independent** lifting datum:
`Presents.partialElements` takes an arbitrary `Presents P C`, so a functor built once serves
Garside and Artin alike, with no `hsound` per style.

The step is computed rather than bounded: `atomAct` is defined exactly at an *ascent* of the
chart's crossing permutation, and multiplies it by `adjT k` (`atomAct_eq_some_iff`).  Both Artin
relations then read off `adjT`: each three-letter route is defined exactly when the window it
touches is increasing, so no codimension-two cell is named.

Nothing here depends on `hasDiamonds_cube` or on `Merge/CubeFaces`' meet layer.  Those stay
load-bearing for `word_unique`, hence for thinness; this is a second, independent route to the
cube's structure, and it does not need the geometry.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

variable {n : ℕ}

/-- Charts of `K` over the run of `N` events. -/
abbrev RunChart (K : BPSet) (N : ℕ) : Type := (wedgeHoms K).obj (op (zObj (𝟙^N)))

theorem wedgeHoms_map_op' {K : BPSet} {a b : Ch Zbp} (g : a ⟶ b) (z : ⋁b.dims ⟶ K) :
    (wedgeHoms K).map g.op z = Hom.φ g ≫ z := rfl

/-- The two legs of a defined atom step, with their wedge maps named. -/
theorem exists_square_atomAct {K : BPSet} (h : SeparatesMerges K) {N : ℕ} {k : Fin (N - 1)}
    {x y : RunChart K N} (hp : atomAct h k x = some y) :
    ∃ z : ⋁(atomComp N k) ⟶ K,
      Hom.φ (mergeOnes N k) ≫ z = x ∧ Hom.φ (atomOnes N k) ≫ z = y := by
  rw [atomAct, Option.map_eq_some_iff] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  exact ⟨z, (mergeLift_eq_some_iff _ x z).mp hz, rfl⟩

/-- A `Ch Zbp` morphism is its own wedge map, re-wrapped. -/
theorem zHom_self {a b : Ch Zbp} (g : a ⟶ b) : zHom (Hom.φ g) = g := hom_ext' rfl

/-! ### The cube's atom step, computed -/

/-- The crossing permutation of a chart over the run. -/
noncomputable def crossOnes (x : RunChart (□n) n) : Perm (Fin n) :=
  cross (chartChain (zObj (𝟙^n)).dims x)

theorem crossOnes_injective : Function.Injective (crossOnes (n := n)) := by
  intro x y h
  have he := run_eq_of_cross_eq (r := chartChain (𝟙^n) x) (r' := chartChain (𝟙^n) y) rfl rfl h
  obtain ⟨hd, hm⟩ := Obj.eq_mk_of_eq he
  rw [Subsingleton.elim hd rfl] at hm
  simpa using hm

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

/-- **The positive braid monoid acts partially on the charts over the run.**  This is the
presentation-independent lifting datum: `Presents.partialElements` consumes the functor it induces
for *every* presentation of the base at once, with no `hsound` to discharge per style. -/
noncomputable def chartAction (n : ℕ) :
    PosBraid n →* Function.End (Option (RunChart (□n) n)) :=
  (CubeChains.ArtinPosBraid.lift (cubeAtom n) (isArtinFamily_cubeAtom n)).comp
    (posBraid_equiv_artinPos n).toMonoidHom

/-! ### The presheaf on the localized base, and the lift

`Presents.partialElements` takes an arbitrary `Presents P C`, so the whole point is to produce the
presheaf **without** naming a presentation.  `strictEnd` is what makes the undefined point absorbing
by construction rather than by a generation argument on the image. -/

/-- The `none`-preserving endomorphisms of `Option X` — the partial maps of `X`, as a submonoid. -/
def strictEnd (X : Type*) : Submonoid (Function.End (Option X)) where
  carrier := {f | f none = none}
  mul_mem' {f g} hf hg := show f (g none) = none by rw [hg]; exact hf
  one_mem' := rfl

@[simp] theorem mem_strictEnd {X : Type*} {f : Function.End (Option X)} :
    f ∈ strictEnd X ↔ f none = none := Iff.rfl

/-- The atom family at strand count `N`, as partial maps of the charts of `□n` over that run. -/
noncomputable def cubeAtomAt (n N : ℕ) (k : Fin (N - 1)) : strictEnd (RunChart (□n) N) :=
  ⟨fun o => o.bind (atomAct (separatesMerges_cube n) k), rfl⟩

/-- Off the cube's own strand count there are no charts at all. -/
theorem isEmpty_runChart {n N : ℕ} (h : N ≠ n) : IsEmpty (RunChart (□n) N) :=
  ⟨fun x => h ((dimSum_replicate N).symm.trans (dimSum_dims_cube (chartChain (𝟙^N) x)))⟩

theorem subsingleton_strictEnd {X : Type*} [IsEmpty X] : Subsingleton (strictEnd X) :=
  ⟨fun f g => Subtype.ext (funext fun o => by
    cases o with
    | none => rw [f.2, g.2]
    | some x => exact isEmptyElim x)⟩

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
  (CubeChains.ArtinPosBraid.lift _ (isArtinFamily_cubeAtomAt n N).op).comp
    (posBraid_equiv_artinPos N).toMonoidHom

/-- **A partial action of `M` is a presheaf on its one-object category.**  Contravariance is the
`ᵒᵖ`; landing in `strictEnd` is what makes the undefined point absorbing. -/
def partialActionFunctor {M : Type*} [Monoid M] {X : Type} (φ : M →* (strictEnd X)ᵐᵒᵖ) :
    (SingleObj M)ᵒᵖ ⥤ Type where
  obj _ := Option X
  map f := ↾((φ f.unop).unop.val)
  map_id _ := by
    change ↾((φ (1 : M)).unop.val) = _
    rw [φ.map_one]
    rfl
  map_comp f g := by
    change ↾((φ (f.unop * g.unop)).unop.val) = _
    rw [φ.map_mul]
    rfl

@[simp] theorem partialActionFunctor_map_none {M : Type*} [Monoid M] {X : Type}
    (φ : M →* (strictEnd X)ᵐᵒᵖ) {a b : (SingleObj M)ᵒᵖ} (f : a ⟶ b) :
    (partialActionFunctor φ).map f none = none := (φ f.unop).unop.2

/-- **The charts of `□n`, as a presheaf on the localized base.**  One fibre per strand count, the
positive braid monoid of that count acting partially on it — built once, with no presentation in
sight. -/
noncomputable def cubeFibre (n : ℕ) : ((W Zbp).op).Localization ⥤ Type :=
  strandDecomposition.functor ⋙ Sigma.desc fun N =>
    (strandComponentGarside N).inverse ⋙ partialActionFunctor (chartActionAt n N)

/-- `none` is absorbing in each fibre, hence in the descent. -/
theorem sigmaDesc_map_none (n : ℕ) :
    ∀ (A B : Σ N : ℕ, (AtStrands N).FullSubcategory) (f : A ⟶ B),
      (Sigma.desc fun N => (strandComponentGarside N).inverse
        ⋙ partialActionFunctor (chartActionAt n N)).map f none = none := by
  rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨f⟩
  exact partialActionFunctor_map_none _ _

/-- The undefined chart, at every object. -/
noncomputable def cubeBot (n : ℕ) (c : ((W Zbp).op).Localization) : (cubeFibre n).obj c := none

theorem cubeBot_absorbing (n : ℕ) {c c' : ((W Zbp).op).Localization} (g : c ⟶ c') :
    (cubeFibre n).map g (cubeBot n c) = cubeBot n c' :=
  sigmaDesc_map_none n _ _ (strandDecomposition.functor.map g)

/-- **The lift, for an arbitrary presentation of the base.**  0-cells the defined charts, 1-cells
the base's generators where they act, 2-cells its relations there.  `p` is unconstrained: the
presheaf was built without one, so every spelling of the base is served by this one lemma. -/
noncomputable def cubeChartPresentation (n : ℕ) {P : Polygraph}
    (p : Presents P (((W Zbp).op).Localization)) :
    Presents ((p.elements (cubeFibre n)).restrictPoly
        (Presents.defined (cubeFibre n) (cubeBot n)))
      (Presents.defined (cubeFibre n) (cubeBot n)).FullSubcategory :=
  Presents.partialElements (cubeFibre n) (cubeBot n) (fun {_ _} g => cubeBot_absorbing n g) p

/-- **The Garside spelling**: the base's germ presentation, lifted. -/
noncomputable def cubeChartGarside (n : ℕ) := cubeChartPresentation n zLocPresentation

/-- **The Artin spelling**: commutation and braid on `N−1` generators per strand count, lifted —
the same lemma at a different `p`. -/
noncomputable def cubeChartArtin (n : ℕ) := cubeChartPresentation n zLocArtinPresentation

end ChainCat
