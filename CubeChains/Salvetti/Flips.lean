import CubeChains.Salvetti.Runs
import CubeChains.Salvetti.ChainBraidFace
import CubeChains.Chains.CoordFunctor
import CubeChains.Braid.Germ
import CubeChains.Braid.Category
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

/-!
# Salvetti/Flips — the `K`-free domain of the braid

A refinement of complexified chains reads only its wedge map and the two runs it intertwines; the
map to `K` is scenery.  `RunWedge` is that `K`-free data — a serial wedge together with a run,
carried (as in `ChStar`) by its classifying map to `runPresheaf` — and `proj K : Ch⋆ K ⥤ RunWedge`
forgets the map to `K`.  All of `K` lives in *which* morphisms `proj` realises (it is faithful,
never full); the braid, to be built here as `Flips : RunWedge ⥤ Braids`, reads only the codomain,
so `ConcPos K = proj K ⋙ Flips` uniformly in `K`.

`RunWedge` is the wedge part of `(BPSet ↓ runPresheaf)`: `Lines` with the base widened from `Ch K`
to all serial wedges — the generic `Ch⋆`.
-/

open CategoryTheory Opposite BPSet ChainCat CubeChain Equiv

namespace CubeChains

variable {K : BPSet}

/-! ## The `K`-free domain: wedges with runs -/

/-- A serial wedge together with a run refining it, carried by its classifying map to `runPresheaf`
(as `ChStar` carries its `.2`).  Every `x : Ch⋆ K` projects to one of these by forgetting its map
to `K` (`proj`). -/
structure RunWedge where
  /-- The bead-dimension sequence of the wedge. -/
  dims : List ℕ+
  /-- The run refining `⋁dims`, as a map to `runPresheaf`. -/
  cls : (⋁dims).toPsh ⟶ runPresheaf

namespace RunWedge

/-- The run refining `⋁dims`, recovered from the classifying map. -/
def run (X : RunWedge) : Run (⋁X.dims) := runPshEquiv X.dims X.cls

/-- A morphism is a wedge map intertwining the classifiers — the `K`-free part of a refinement.
Contravariant on wedges, matching `wedgeOf`: a refinement `x ⟶ y` runs `⋁y ⟶ ⋁x`. -/
instance : Category RunWedge where
  Hom X Y := {φ : ⋁Y.dims ⟶ ⋁X.dims // φ.hom ≫ X.cls = Y.cls}
  id X := ⟨𝟙 (⋁X.dims), by rw [id_hom, Category.id_comp]⟩
  comp {X Y Z} f g := ⟨g.1 ≫ f.1, by rw [comp_hom, Category.assoc, f.2, g.2]⟩
  id_comp f := Subtype.ext (Category.comp_id f.1)
  comp_id f := Subtype.ext (Category.id_comp f.1)
  assoc f g h := Subtype.ext (Category.assoc h.1 g.1 f.1).symm

/-- The wedge map underlying a morphism. -/
abbrev wedgeMap {X Y : RunWedge} (f : X ⟶ Y) : ⋁Y.dims ⟶ ⋁X.dims := f.1

/-- The event count of a wedge-with-run: its total bead dimension. -/
def Nev (X : RunWedge) : ℕ := dimSum X.dims

/-! ### Run-compatibility and the reduction to cube targets

A morphism carries `X`'s run to `Y`'s (`run_restrict`), and that transport is local to `Y`'s beads:
bead `iβ`'s local run (`runProj … iβ`, a run of the single cube `□(Y.dims.get iβ)`) is bead
`blockIdx (wedgeMap f) iβ` of `X`, restricted along a `Box` face (`runProj_restrict`).  So a
morphism's whole content is a family of cube-level restrictions `□ ⟶ runPresheaf` — the Segal
decomposition of the wedge into its cube beads. -/

/-- The stored classifier is `pshOfRun` of the run. -/
theorem pshOfRun_run (X : RunWedge) : pshOfRun X.dims X.run = X.cls :=
  pshOfRun_runOfPsh X.dims X.cls

/-- **Run-compatibility, `runRestrict` form** — `chStar_run_eq` at the `K`-free level: a morphism's
wedge map carries `X`'s run to `Y`'s. -/
theorem run_restrict {X Y : RunWedge} (f : X ⟶ Y) : runRestrict (wedgeMap f) X.run = Y.run := by
  rw [runRestrict, pshOfRun_run, f.2]; rfl

/-- **The cube reduction.**  Bead `iβ`'s local run of `Y` (of the cube `□(Y.dims.get iβ)`) is bead
`blockIdx (wedgeMap f) iβ` of `X`, restricted along the `Box` face `blockFace (wedgeMap f) iβ` — a
relation between two cube runs. -/
theorem runProj_restrict {X Y : RunWedge} (f : X ⟶ Y) (iβ : Fin Y.dims.length) :
    runProj Y.run iβ = runPresheaf.map (blockFace (wedgeMap f).hom iβ).op
      (runProj X.run (blockIdx (wedgeMap f).hom iβ)) := by
  rw [← run_restrict f]
  exact runProj_runRestrict (wedgeMap f) X.run iβ

/-! ### The event relabelling

The `K`-free relocation of `Salvetti/Conc`'s event layer: everything is a function of `wedgeMap`
and the runs, so it lives here, and `Conc`'s `Ch⋆ K` versions are its pullback along `proj`. -/

@[simp] theorem wedgeMap_id (X : RunWedge) : wedgeMap (𝟙 X) = 𝟙 (⋁X.dims) := rfl

theorem wedgeMap_comp {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    wedgeMap (f ≫ g) = wedgeMap g ≫ wedgeMap f := rfl

/-- Refinement preserves the event count. -/
theorem Nev_eq {X Y : RunWedge} (f : X ⟶ Y) : Nev X = Nev Y :=
  (serialWedge_dimSum_eq (wedgeMap f)).symm

/-- The event relabelling `beadEvent Y ≃ beadEvent X` — `coordMap` of the wedge map. -/
def eventEquiv {X Y : RunWedge} (f : X ⟶ Y) :
    beadEvent Y.dims ≃ beadEvent X.dims :=
  coordMapEquiv (wedgeMap f)

theorem eventEquiv_apply {X Y : RunWedge} (f : X ⟶ Y) (e : beadEvent Y.dims) :
    eventEquiv f e = coordMap (wedgeMap f) e :=
  coordMapEquiv_apply (wedgeMap f) e

theorem eventEquiv_comp {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eventEquiv (f ≫ g) = (eventEquiv g).trans (eventEquiv f) := by
  refine Equiv.ext fun e => ?_
  simp only [eventEquiv_apply, Equiv.trans_apply, wedgeMap_comp, coordMap_comp, Function.comp_apply]

theorem eventEquiv_id (X : RunWedge) : eventEquiv (𝟙 X) = Equiv.refl _ := by
  refine Equiv.ext fun e => ?_
  rw [eventEquiv_apply, wedgeMap_id, coordMap_id, Equiv.refl_apply, id_eq]

/-- The relabelled event, coordinatized (`coordMap_eq`). -/
theorem eventEquiv_val {X Y : RunWedge} (f : X ⟶ Y) (iβ : Fin Y.dims.length)
    (k : Fin (Y.dims.get iβ : ℕ)) :
    eventEquiv f ⟨iβ, k⟩
      = ⟨blockIdx (wedgeMap f).hom iβ, faceEmb (blockFace (wedgeMap f).hom iβ) k⟩ := by
  rw [eventEquiv_apply, coordMap_eq]

/-- The chain-bead of `eventEquiv f a` is `blockIdx (wedgeMap f)` of `a`'s bead. -/
theorem eventEquiv_bead {X Y : RunWedge} (f : X ⟶ Y) (a : beadEvent Y.dims) :
    (eventEquiv f a).1 = blockIdx (wedgeMap f).hom a.1 := by
  rw [eventEquiv_apply, coordMap_fst]

/-- `blockIdx` is monotone for the wedge map underlying a morphism. -/
theorem blockIdx_monotone {X Y : RunWedge} (f : X ⟶ Y) : Monotone (blockIdx (wedgeMap f).hom) :=
  serialWedge_blockIdx_monotone (wedgeMap f).hom (wedgeMap f).app_init

/-! ### The run's rank -/

/-- `dimSum` as the sum of bead dimensions. -/
private theorem dimSum_eq_sum (a : List ℕ+) : (∑ i : Fin a.length, (a.get i : ℕ)) = dimSum a := by
  rw [sum_get_eq_sum_map a (fun d : ℕ+ => (d : ℕ)), ← dimSum_sum]

/-- **The lex order of the sigma-flattening.**  If `i` precedes `i'`, its whole block flattens
below `i'`'s. -/
private theorem dims_prefix_lt {a : List ℕ+} {i i' : Fin a.length}
    (hii : (i : ℕ) < i') (k : Fin (a.get i : ℕ)) (k' : Fin (a.get i' : ℕ)) :
    (∑ j : Fin (i : ℕ), (a.get (Fin.castLE i.2.le j) : ℕ)) + (k : ℕ)
      < (∑ j : Fin (i' : ℕ), (a.get (Fin.castLE i'.2.le j) : ℕ)) + (k' : ℕ) := by
  have hval : ∀ (t : ℕ) (ht : t ≤ a.length),
      (∑ j : Fin t, (a.get (Fin.castLE ht j) : ℕ)) = ∑ s ∈ Finset.range t, (a.getD s 1 : ℕ) := by
    intro t ht
    rw [← Fin.sum_univ_eq_sum_range (fun s => (a.getD s 1 : ℕ)) t]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hjm : (j : ℕ) < a.length := lt_of_lt_of_le j.2 ht
    simp only [List.getD_eq_getElem a 1 hjm, List.get_eq_getElem, Fin.val_castLE]
  have hget : (a.get i : ℕ) = (a.getD (i : ℕ) 1 : ℕ) := by
    simp only [List.getD_eq_getElem a 1 i.2, List.get_eq_getElem]
  have key : (∑ j : Fin (i : ℕ), (a.get (Fin.castLE i.2.le j) : ℕ)) + (a.get i : ℕ)
      ≤ ∑ j : Fin (i' : ℕ), (a.get (Fin.castLE i'.2.le j) : ℕ) := by
    rw [hval (i : ℕ) i.2.le, hval (i' : ℕ) i'.2.le, hget, ← Finset.sum_range_succ]
    exact Finset.sum_le_sum_of_subset
      (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega))
  have hk : (k : ℕ) < (a.get i : ℕ) := k.2
  omega

/-- Bead `i`'s local run has `dᵢ` beads. -/
theorem runProj_dims_length (w : RunWedge) (i : Fin w.dims.length) :
    (runProj w.run i).chain.dims.length = (w.dims.get i : ℕ) := by
  rw [← dimSum_eq_length_of_ones (runProj w.run i).ones]
  exact wedgeDimSum_eq (runProj w.run i).map

/-- Bead `i`'s local run order, as a permutation of its `dᵢ` coordinates.  Computable: the inverse
is `Fintype.bijInv`, not `Equiv.ofBijective`'s choice. -/
def beadPerm (w : RunWedge) (i : Fin w.dims.length) :
    Fin (w.dims.get i : ℕ) ≃ Fin (w.dims.get i : ℕ) :=
  have hbij : Function.Bijective
      (fun k => finCongr (runProj_dims_length w i) (beadOf (runProj w.run i).chain k)) :=
    Finite.surjective_iff_bijective.mp fun j => by
      obtain ⟨k, hk⟩ := beadOf_surjective (runProj w.run i).chain
        (finCongr (runProj_dims_length w i).symm j)
      exact ⟨k, by rw [hk]; simp⟩
  { toFun := fun k => finCongr (runProj_dims_length w i) (beadOf (runProj w.run i).chain k)
    invFun := Fintype.bijInv hbij
    left_inv := Fintype.leftInverse_bijInv hbij
    right_inv := Fintype.rightInverse_bijInv hbij }

@[simp] theorem beadPerm_val (w : RunWedge) (i : Fin w.dims.length)
    (k : Fin (w.dims.get i : ℕ)) :
    (beadPerm w i k : ℕ) = (beadOf (runProj w.run i).chain k : ℕ) := rfl

/-- The run's rank: events ordered bead-by-bead, then within each bead by its local run, flattened
lexicographically. -/
def rankEquiv (w : RunWedge) : beadEvent w.dims ≃ Fin (Nev w) :=
  (Equiv.sigmaCongrRight (beadPerm w)).trans
    (finSigmaFinEquiv.trans (finCongr (dimSum_eq_sum w.dims)))

theorem rankEquiv_val (w : RunWedge) (i : Fin w.dims.length) (k : Fin (w.dims.get i : ℕ)) :
    (rankEquiv w ⟨i, k⟩ : ℕ)
      = (∑ j : Fin (i : ℕ), (w.dims.get (Fin.castLE i.2.le j) : ℕ))
        + (beadOf (runProj w.run i).chain k : ℕ) := by
  simp only [rankEquiv, Equiv.trans_apply, Equiv.sigmaCongrRight_apply, finCongr_apply,
    Fin.val_cast, finSigmaFinEquiv_apply, beadPerm_val]

/-- **The run refines the chain order.**  An event in an earlier chain-bead has an earlier rank. -/
theorem rankEquiv_lt_of_chainBead {w : RunWedge} {e e' : beadEvent w.dims}
    (h : (e.1 : ℕ) < e'.1) : rankEquiv w e < rankEquiv w e' := by
  obtain ⟨i, k⟩ := e
  obtain ⟨i', k'⟩ := e'
  rw [Fin.lt_def, rankEquiv_val, rankEquiv_val, ← beadPerm_val w i k, ← beadPerm_val w i' k']
  exact dims_prefix_lt h (beadPerm w i k) (beadPerm w i' k')

/-- **Within a bead, the rank order is the local run order.** -/
theorem rankEquiv_within_bead (w : RunWedge) (i : Fin w.dims.length)
    (k k' : Fin (w.dims.get i : ℕ)) :
    (rankEquiv w ⟨i, k⟩ < rankEquiv w ⟨i, k'⟩
      ↔ beadOf (runProj w.run i).chain k < beadOf (runProj w.run i).chain k') := by
  rw [Fin.lt_def, Fin.lt_def, rankEquiv_val, rankEquiv_val]
  omega

/-! ### The crossing permutation -/

/-- Transport a permutation across an equality of strand counts. -/
def permCast {m n : ℕ} (h : m = n) : Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin n) :=
  Equiv.permCongr (finCongr h)

/-- The reordering from `X`'s run order to `Y`'s, before regrading. -/
def rawPerm {X Y : RunWedge} (f : X ⟶ Y) : Fin (Nev X) ≃ Fin (Nev Y) :=
  (rankEquiv X).symm.trans ((eventEquiv f).symm.trans (rankEquiv Y))

theorem rawPerm_comp {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rawPerm (f ≫ g) = (rawPerm f).trans (rawPerm g) := by
  refine Equiv.ext fun i => ?_
  simp only [rawPerm, eventEquiv_comp, Equiv.trans_apply, Equiv.symm_trans_apply,
    Equiv.symm_apply_apply]

theorem rawPerm_id (X : RunWedge) : rawPerm (𝟙 X) = finCongr (Nev_eq (𝟙 X)) := by
  refine Equiv.ext fun i => ?_
  simp only [rawPerm, eventEquiv_id, Equiv.refl_symm, Equiv.refl_trans, Equiv.symm_trans_self,
    Equiv.refl_apply, finCongr_apply]
  rfl

/-- The crossing permutation of a refinement (the run-based `crossPerm`). -/
def permOf {X Y : RunWedge} (f : X ⟶ Y) : Equiv.Perm (Fin (Nev X)) :=
  (rawPerm f).trans (finCongr (Nev_eq f)).symm

theorem permOf_id (X : RunWedge) : permOf (𝟙 X) = 1 := by
  rw [permOf, rawPerm_id, Equiv.self_trans_symm]; rfl

private theorem permOf_comp_aux {m n k : ℕ} (hmn : m = n) (hnk : n = k) (hmk : m = k)
    (Rf : Fin m ≃ Fin n) (Rg : Fin n ≃ Fin k) :
    ((Rf.trans Rg).trans (finCongr hmk).symm)
      = permCast hmn.symm (Rg.trans (finCongr hnk).symm) * (Rf.trans (finCongr hmn).symm) := by
  refine Equiv.ext fun i => ?_
  simp only [permCast, Equiv.Perm.mul_apply, Equiv.permCongr_apply, Equiv.trans_apply]
  have harg : (finCongr hmn.symm).symm ((finCongr hmn).symm (Rf i)) = Rf i := by apply Fin.ext; simp
  rw [harg]; apply Fin.ext; simp

/-- The cocycle law, matching `permBraidFunctor`'s convention `p (f ≫ g) = p g * p f`. -/
theorem permOf_comp {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    permOf (f ≫ g) = permCast (Nev_eq f).symm (permOf g) * permOf f := by
  have h := permOf_comp_aux (Nev_eq f) (Nev_eq g) (Nev_eq (f ≫ g)) (rawPerm f) (rawPerm g)
  rw [← rawPerm_comp] at h
  exact h

/-! ### Length-additivity — the run-order no-double-cross -/

theorem rawPerm_rankEquiv {X Y : RunWedge} (f : X ⟶ Y) (e : beadEvent X.dims) :
    rawPerm f (rankEquiv X e) = rankEquiv Y ((eventEquiv f).symm e) := by
  simp only [rawPerm, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem permOf_rankEquiv_val {X Y : RunWedge} (f : X ⟶ Y) (e : beadEvent X.dims) :
    (permOf f (rankEquiv X e) : ℕ) = (rankEquiv Y ((eventEquiv f).symm e) : ℕ) := by
  rw [permOf, Equiv.trans_apply, finCongr_symm, finCongr_apply, Fin.val_cast, rawPerm_rankEquiv]

theorem rho_sigma_val {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) (e : beadEvent X.dims) :
    ((permCast (Nev_eq f).symm (permOf g)) (permOf f (rankEquiv X e)) : ℕ)
      = (rankEquiv Z ((eventEquiv g).symm ((eventEquiv f).symm e)) : ℕ) := by
  rw [permCast, Equiv.permCongr_apply, finCongr_apply, Fin.val_cast]
  have harg : (finCongr (Nev_eq f).symm).symm (permOf f (rankEquiv X e))
      = rankEquiv Y ((eventEquiv f).symm e) :=
    Fin.ext (by rw [finCongr_symm, finCongr_apply, Fin.val_cast, permOf_rankEquiv_val])
  rw [harg, permOf_rankEquiv_val]

/-- **A refinement refines the chain-bead order.** -/
theorem chainBead_refine {Y Z : RunWedge} (g : Y ⟶ Z) {a b : beadEvent Y.dims}
    (h : (a.1 : ℕ) < b.1) : (((eventEquiv g).symm a).1 : ℕ) < ((eventEquiv g).symm b).1 := by
  by_contra hcon
  rw [not_lt] at hcon
  have hmono := blockIdx_monotone g (Fin.le_def.mpr hcon)
  rw [← eventEquiv_bead, ← eventEquiv_bead, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hmono
  exact absurd h (not_lt.mpr (Fin.le_def.mp hmono))

end RunWedge

/-! ## The single-cube geometry: face restriction preserves run order

The one genuinely geometric fact — the atomic input, shared by the braid (`within_bead_agree`) and
the tope machinery (`Salvetti/TopeLines`).  Everything else is bookkeeping; this is where the cube's
combinatorics enter, isolated to a single `Run (□d)` and a single `Box` face. -/

/-- The `i`-th survivor of `filterMap` reads `fn` of the `i`-th kept element. -/
private theorem filterMap_getElem?_bind {α β : Type*} (fn : α → Option β) :
    ∀ (L : List α) (i : ℕ),
      (L.filterMap fn)[i]? = ((L.filter (fun c => (fn c).isSome))[i]?).bind fn
  | [], _ => by simp
  | c :: rest, i => by
      rcases hc : fn c with _ | b
      · have hfil : (c :: rest).filter (fun c => (fn c).isSome)
            = rest.filter (fun c => (fn c).isSome) := List.filter_cons_of_neg (by simp [hc])
        rw [List.filterMap_cons_none hc, hfil]
        exact filterMap_getElem?_bind fn rest i
      · have hfil : (c :: rest).filter (fun c => (fn c).isSome)
            = c :: rest.filter (fun c => (fn c).isSome) := List.filter_cons_of_pos (by simp [hc])
        rw [List.filterMap_cons_some hc, hfil]
        rcases i with _ | j
        · rw [List.getElem?_cons_zero, List.getElem?_cons_zero]
          change some b = fn c
          rw [hc]
        · rw [List.getElem?_cons_succ, List.getElem?_cons_succ]
          exact filterMap_getElem?_bind fn rest j

/-- Projecting a surviving cube reads its sign along `faceEmb`. -/
private theorem sign_restrictCube_eq {n b : ℕ} (face : ▫n ⟶ ▫b)
    {c : Σ d : ℕ+, (□b).cells (d : ℕ)} {c'' : Σ d : ℕ+, (□n).cells (d : ℕ)}
    (h : restrictCube face c = some c'') :
    (Box.sign c''.2).val = restrictCoord face (Box.sign c.2) := by
  rw [restrictCube_eq] at h
  by_cases hpos : 0 < (StdCube.noneSet (restrictCoord face (Box.sign c.2))).card
  · rw [cubeOfCoord_pos hpos] at h
    obtain rfl := (Option.some_inj.mp h).symm
    change (Box.sign (Box.ofSign ⟨restrictCoord face (Box.sign c.2), rfl⟩)).val = _
    rw [Box.sign_ofSign]
  · rw [cubeOfCoord_neg hpos] at h; exact absurd h (by simp)

/-- Coordinate `q` reads `none` at the `j`-th cube exactly when `q` is the bead it flips. -/
private theorem sign_wedgeToCubes_eq_none {m : ℕ} (b : Ch (□m)) (q : Fin m) (j : ℕ)
    (hj : j < (wedgeToCubes ⟨b.dims, b.map.hom⟩).length) :
    (Box.sign ((wedgeToCubes ⟨b.dims, b.map.hom⟩)[j]'hj).2).val q = none
      ↔ (beadOf b q : ℕ) = j := by
  have hjlen : j < b.dims.length := (wedgeToCubes_length b.dims b.map.hom) ▸ hj
  rw [show (wedgeToCubes ⟨b.dims, b.map.hom⟩)[j]'hj
        = (wedgeToCubes ⟨b.dims, b.map.hom⟩).get ⟨j, hj⟩ from rfl,
     wedgeToCubes_get b.dims b.map.hom ⟨j, hj⟩]
  change (StdCube.ev (beadFace b.map.hom ⟨j, hjlen⟩)).val q = none ↔ (beadOf b q : ℕ) = j
  rw [ev_beadFace_eq_none_iff b ⟨j, hjlen⟩ q]
  exact Fin.ext_iff

/-- **Face restriction preserves cube-run order** (the single-cube geometry). -/
theorem beadOf_restrict_lt {d e : ℕ} (C : Run (□d)) (g : ▫e ⟶ ▫d) (k k' : Fin e) :
    (beadOf ((runPresheaf.map g.op C : Run (□e)).chain) k
        < beadOf ((runPresheaf.map g.op C : Run (□e)).chain) k'
      ↔ beadOf C.chain (faceEmb g k) < beadOf C.chain (faceEmb g k')) := by
  set C' : Run (□e) := runPresheaf.map g.op C with hC'eq
  have hcubes : wedgeToCubes ⟨C'.chain.dims, C'.chain.map.hom⟩
      = restrictChain g (wedgeToCubes ⟨C.chain.dims, C.chain.map.hom⟩) := by
    have hC' : Run.equivEdgeChain (□e) C'
        = EdgeChain.restrict g (Run.equivEdgeChain (□d) C) := by
      have hcalc : C' = (Run.equivEdgeChain (□e)).symm
          (EdgeChain.restrict g (Run.equivEdgeChain (□d) C)) := hC'eq
      rw [hcalc, Equiv.apply_symm_apply]
    calc wedgeToCubes ⟨C'.chain.dims, C'.chain.map.hom⟩
        = (Run.equivEdgeChain (□e) C').1.cubes := (cubes_equivEdgeChain C').symm
      _ = (EdgeChain.restrict g (Run.equivEdgeChain (□d) C)).1.cubes := by rw [hC']
      _ = restrictChain g (Run.equivEdgeChain (□d) C).1.cubes := rfl
      _ = restrictChain g (wedgeToCubes ⟨C.chain.dims, C.chain.map.hom⟩) := by
            rw [cubes_equivEdgeChain C]
  obtain ⟨emb, hemb0⟩ := List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp
    (List.filter_sublist (p := fun c => (restrictCube g c).isSome)
      (l := wedgeToCubes ⟨C.chain.dims, C.chain.map.hom⟩))
  have hemb : ∀ i, ((wedgeToCubes ⟨C.chain.dims, C.chain.map.hom⟩).filterMap (restrictCube g))[i]?
      = ((wedgeToCubes ⟨C.chain.dims, C.chain.map.hom⟩)[emb i]?).bind (restrictCube g) := by
    intro i
    rw [filterMap_getElem?_bind (restrictCube g) (wedgeToCubes ⟨C.chain.dims, C.chain.map.hom⟩) i,
      hemb0 i]
  have hemb' : ∀ i, (wedgeToCubes ⟨C'.chain.dims, C'.chain.map.hom⟩)[i]?
      = ((wedgeToCubes ⟨C.chain.dims, C.chain.map.hom⟩)[emb i]?).bind (restrictCube g) := by
    intro i; rw [hcubes]; exact hemb i
  have key : ∀ q : Fin e,
      (beadOf C.chain (faceEmb g q) : ℕ) = emb (beadOf C'.chain q : ℕ) := by
    intro q
    set i₀ : ℕ := (beadOf C'.chain q : ℕ) with hi₀def
    have hi₀ : i₀ < (wedgeToCubes ⟨C'.chain.dims, C'.chain.map.hom⟩).length := by
      rw [wedgeToCubes_length]; exact (beadOf C'.chain q).isLt
    have hL'get : (wedgeToCubes ⟨C'.chain.dims, C'.chain.map.hom⟩)[i₀]?
        = some ((wedgeToCubes ⟨C'.chain.dims, C'.chain.map.hom⟩)[i₀]'hi₀) :=
      List.getElem?_eq_getElem hi₀
    rw [hemb' i₀] at hL'get
    obtain ⟨corig, hX, hrc⟩ := Option.bind_eq_some_iff.mp hL'get
    obtain ⟨hbound, hLeq⟩ := List.getElem?_eq_some_iff.mp hX
    have hnone' : (Box.sign ((wedgeToCubes ⟨C'.chain.dims, C'.chain.map.hom⟩)[i₀]'hi₀).2).val q
        = none := (sign_wedgeToCubes_eq_none C'.chain q i₀ hi₀).mpr rfl
    have hsign := sign_restrictCube_eq g hrc
    have hval : (Box.sign corig.2).val (faceEmb g q) = none := by
      have hc := congrFun hsign q
      rw [hnone'] at hc
      exact hc.symm
    rw [← hLeq] at hval
    rw [sign_wedgeToCubes_eq_none C.chain (faceEmb g q) (emb i₀) hbound] at hval
    exact hval
  rw [Fin.lt_def, Fin.lt_def, key k, key k']
  exact emb.lt_iff_lt.symm

namespace RunWedge

/-- **Within a bead the refinement preserves the run order** — the within-block case, now a
one-line consequence of `runProj_restrict` (the cube reduction) and the single-cube geometry. -/
theorem within_bead_agree {X Y : RunWedge} (f : X ⟶ Y) {a b : beadEvent Y.dims}
    (hbead : a.1 = b.1) :
    (rankEquiv X (eventEquiv f a) < rankEquiv X (eventEquiv f b)
      ↔ rankEquiv Y a < rankEquiv Y b) := by
  obtain ⟨iβ, ka⟩ := a
  obtain ⟨jb, kb⟩ := b
  subst hbead
  rw [eventEquiv_val, eventEquiv_val,
    rankEquiv_within_bead X (blockIdx (wedgeMap f).hom iβ)
      (faceEmb (blockFace (wedgeMap f).hom iβ) ka) (faceEmb (blockFace (wedgeMap f).hom iβ) kb),
    rankEquiv_within_bead Y iβ ka kb, runProj_restrict f iβ]
  exact (beadOf_restrict_lt (runProj X.run (blockIdx (wedgeMap f).hom iβ))
    (blockFace (wedgeMap f).hom iβ) ka kb).symm

/-- **The run-order no-double-cross.**  If `X` orders `e₁` before `e₂` while `Y` orders their
`f`-preimages oppositely, then `Z` keeps `Y`'s order. -/
theorem runOrder_H {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) (e₁ e₂ : beadEvent X.dims)
    (h1 : rankEquiv X e₁ < rankEquiv X e₂)
    (h2 : rankEquiv Y ((eventEquiv f).symm e₂) < rankEquiv Y ((eventEquiv f).symm e₁)) :
    rankEquiv Z ((eventEquiv g).symm ((eventEquiv f).symm e₂))
      < rankEquiv Z ((eventEquiv g).symm ((eventEquiv f).symm e₁)) := by
  set a := (eventEquiv f).symm e₁ with ha
  set b := (eventEquiv f).symm e₂ with hb
  have he₁ : eventEquiv f a = e₁ := by rw [ha, Equiv.apply_symm_apply]
  have he₂ : eventEquiv f b = e₂ := by rw [hb, Equiv.apply_symm_apply]
  have hstep1 : (b.1 : ℕ) < a.1 := by
    rcases lt_trichotomy (a.1 : ℕ) (b.1 : ℕ) with hlt | heq | hgt
    · exact absurd (rankEquiv_lt_of_chainBead hlt) (asymm h2)
    · rw [← he₁, ← he₂] at h1
      exact absurd ((within_bead_agree f (Fin.ext heq)).mp h1) (asymm h2)
    · exact hgt
  exact rankEquiv_lt_of_chainBead (chainBead_refine g hstep1)

theorem permLen_permCast {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin m)) :
    permLen (permCast h σ) = permLen σ := by subst h; rfl

/-- **Length-additivity: each pair of events crosses at most once.** -/
theorem permOf_noDoubleCross {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    permLen (permOf (f ≫ g)) = permLen (permOf f) + permLen (permOf g) := by
  have H : ∀ i j : Fin (Nev X), i < j → permOf f j < permOf f i →
      (permCast (Nev_eq f).symm (permOf g)) (permOf f j)
        < (permCast (Nev_eq f).symm (permOf g)) (permOf f i) := by
    intro i j hij hfl
    obtain ⟨e₁, rfl⟩ := (rankEquiv X).surjective i
    obtain ⟨e₂, rfl⟩ := (rankEquiv X).surjective j
    have hlt : rankEquiv Y ((eventEquiv f).symm e₂) < rankEquiv Y ((eventEquiv f).symm e₁) := by
      rw [Fin.lt_def, ← permOf_rankEquiv_val, ← permOf_rankEquiv_val]; exact hfl
    have := runOrder_H f g e₁ e₂ hij hlt
    rw [Fin.lt_def, rho_sigma_val, rho_sigma_val]
    exact this
  rw [permOf_comp, permLen_mul_of_noDoubleCross H, permLen_permCast]

end RunWedge

/-! ## The projection forgetting the map to `K` -/

/-- **The projection `Ch⋆ K ⥤ RunWedge`.**  A refinement, stripped to its wedge map and the runs it
intertwines — everything the braid reads.  All of `K` is discarded here; it survives only as the
image (which refinements exist).  On the nose it keeps the run classifier `x.2` and drops the map to
`K`, so the morphism condition is exactly the `Elements` compatibility `f.2`. -/
def proj (K : BPSet) : Ch⋆ K ⥤ RunWedge where
  obj x := ⟨x.chain.dims, x.2⟩
  map {x y} f := ⟨f.1.unop.φ, f.2⟩
  map_id x := Subtype.ext rfl
  map_comp f g := Subtype.ext rfl

@[simp] theorem proj_obj_dims (x : Ch⋆ K) : ((proj K).obj x).dims = x.chain.dims := rfl

@[simp] theorem proj_obj_run (x : Ch⋆ K) : ((proj K).obj x).run = x.run := rfl

@[simp] theorem proj_Nev (x : Ch⋆ K) : ((proj K).obj x).Nev = dimSum x.chain.dims := rfl

/-! ## The graded braid functor -/

namespace RunWedge

/-- Transport a braid across an equality of strand counts. -/
def braidTransport {m n : ℕ} (h : m = n) (b : Braid m) : Braid n := h ▸ b

theorem braidTransport_ofPerm {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin m)) :
    braidTransport h (ofPerm σ) = ofPerm (permCast h σ) := by subst h; rfl

theorem braidHom_comp {n : ℕ} (a b : Braid n) : braidHom a ≫ braidHom b = braidHom (b * a) := rfl

/-- `eqToHom` slides past a braid, conjugating it across the strand-count equality. -/
theorem eqToHom_comp_braidHom {m n : ℕ} (h : m = n) (b : Braid n) :
    eqToHom (congrArg strands h) ≫ braidHom b
      = braidHom (braidTransport h.symm b) ≫ eqToHom (congrArg strands h) := by
  subst h; simp [braidTransport]

/-- The graded-functoriality skeleton: a single-fibre braid identity plus `eqToHom` conjugation. -/
theorem graded_map_comp {m n k : ℕ} (hmn : m = n) (hnk : n = k) (hmk : m = k)
    (bf bg' bfg : Braid m) (bg : Braid n)
    (hbg : braidHom bg' ≫ eqToHom (congrArg strands hmn)
             = eqToHom (congrArg strands hmn) ≫ braidHom bg)
    (hbfg : bfg = bg' * bf) :
    braidHom bfg ≫ eqToHom (congrArg strands hmk)
      = (braidHom bf ≫ eqToHom (congrArg strands hmn))
        ≫ (braidHom bg ≫ eqToHom (congrArg strands hnk)) := by
  subst hmn; subst hnk
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hbg ⊢
  rw [hbfg, ← braidHom_comp, hbg]

end RunWedge

open RunWedge in
/-- **The concurrency braid functor**, `K`-free: a wedge-with-run to `strands (Nev)`, a refinement
to the positive braid `ofPerm (permOf f)`.  Length-additivity (`permOf_noDoubleCross`) is what makes
it a functor; everything above it is the graded bookkeeping into `Braids`. -/
def Flips : RunWedge ⥤ Braids where
  obj X := strands (Nev X)
  map {X Y} f := braidHom (ofPerm (permOf f)) ≫ eqToHom (congrArg strands (Nev_eq f))
  map_id X := by
    have he : eqToHom (congrArg strands (Nev_eq (𝟙 X))) = 𝟙 (strands (Nev X)) := by
      rw [Subsingleton.elim (congrArg strands (Nev_eq (𝟙 X))) rfl, eqToHom_refl]
    rw [permOf_id, ofPerm_one, he, Category.comp_id]
    rfl
  map_comp {X Y Z} f g := by
    have hlen : permLen (permCast (Nev_eq f).symm (permOf g) * permOf f)
        = permLen (permCast (Nev_eq f).symm (permOf g)) + permLen (permOf f) := by
      rw [← permOf_comp, permLen_permCast, permOf_noDoubleCross]; ring
    have hmul : ofPerm (permCast (Nev_eq f).symm (permOf g)) * ofPerm (permOf f)
        = ofPerm (permOf (f ≫ g)) := by rw [ofPerm_mul hlen, ← permOf_comp]
    have hbg : braidHom (ofPerm (permCast (Nev_eq f).symm (permOf g)))
          ≫ eqToHom (congrArg strands (Nev_eq f))
        = eqToHom (congrArg strands (Nev_eq f)) ≫ braidHom (ofPerm (permOf g)) := by
      rw [← braidTransport_ofPerm]
      exact (eqToHom_comp_braidHom (Nev_eq f) (ofPerm (permOf g))).symm
    exact graded_map_comp (Nev_eq f) (Nev_eq g) (Nev_eq (f ≫ g)) (ofPerm (permOf f))
      (ofPerm (permCast (Nev_eq f).symm (permOf g))) (ofPerm (permOf (f ≫ g))) (ofPerm (permOf g))
      hbg hmul.symm

end CubeChains
