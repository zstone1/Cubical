import CubeChains.Salvetti.Runs
import CubeChains.Chains.CoordFunctor
import CubeChains.Chains.WedgeExtend
import CubeChains.Chains.WedgeMap
import CubeChains.Salvetti.ChainBraidFace
import CubeChains.Braid.Category
import CubeChains.Braid.Germ
import CubeChains.Braid.SalvettiConstruction
import CubeChains.Foundations.FreeGroupoidLift
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin

/-!
# Salvetti/Conc — the positive-braid functor of a complexified chain

`ConcPos K : Ch⋆ K ⥤ Braids` sends a chain-with-run to the positive braid of the reordering its
run performs, and `Conc K` is its free-groupoid lift.  The Salvetti construction on chains: `permOf`
is `crossPerm` with the run's order in place of the tope's, and length-additivity ("each pair of
events crosses at most once") is `permOf_noDoubleCross`.
-/

open CategoryTheory Opposite BPSet ChainCat CubeChain Equiv

namespace CubeChains

variable {K : BPSet}

/-! ## Events and their count -/

/-- The atomic events of a complexified chain. -/
def Nev (x : Ch⋆ K) : ℕ := dimSum x.chain.dims

/-- The refinement's underlying wedge map (`y → x`, from the `op`). -/
def wedgeOf {x y : Ch⋆ K} (f : x ⟶ y) : ⋁y.chain.dims ⟶ ⋁x.chain.dims := (f.val.unop).φ

theorem wedgeOf_comp {x y z : Ch⋆ K} (f : x ⟶ y) (g : y ⟶ z) :
    wedgeOf (f ≫ g) = wedgeOf g ≫ wedgeOf f := rfl

/-- Refinement preserves the event count — `dimSum` invariance. -/
theorem Nev_eq {x y : Ch⋆ K} (f : x ⟶ y) : Nev x = Nev y :=
  (serialWedge_dimSum_eq (wedgeOf f)).symm

/-! ## The staircase: a wedge maps to a cube (the one geometric helper).

Any bijection `Fin (dimSum c) ≃ beadEvent c` gives a bead-index surjection `stairβ` whose
`ofBlockMap` (`ChainBraidFace`) reconstruction has block sizes `c`; `wedgeOfChain` reads off the
staircase, transported along `dims = c`.  No new bead recursion — the recursion is `ofBlockMap`'s
own `List.ofFn`. -/

theorem beadEvent_card (c : List ℕ+) : Fintype.card (beadEvent c) = dimSum c := by
  simp only [beadEvent, Fintype.card_sigma, Fintype.card_fin]
  rw [sum_get_eq_sum_map c (fun d : ℕ+ => (d : ℕ)), ← dimSum_sum]

/-- Some coordinatization of the events; only its existence matters (`coordLift_map_bijective`
supplies injectivity downstream). -/
noncomputable def beadFin (c : List ℕ+) : Fin (dimSum c) ≃ beadEvent c :=
  (Fintype.equivFinOfCardEq (beadEvent_card c)).symm

/-- The bead a coordinate lands in — the height whose blocks are `c`. -/
noncomputable def stairβ (c : List ℕ+) (q : Fin (dimSum c)) : Fin c.length := (beadFin c q).1

theorem stairβ_surjective (c : List ℕ+) : Function.Surjective (stairβ c) := fun j =>
  ⟨(beadFin c).symm ⟨j, ⟨0, (c.get j).pos⟩⟩, by rw [stairβ, Equiv.apply_symm_apply]⟩

/-- The fibre of the first projection of `beadEvent` over `j` is `Fin (c.get j)`. -/
def sigmaFstFiber {c : List ℕ+} (j : Fin c.length) :
    {p : beadEvent c // p.1 = j} ≃ Fin (c.get j : ℕ) where
  toFun p := Fin.cast (by rw [p.2]) p.1.2
  invFun k := ⟨⟨j, k⟩, rfl⟩
  left_inv := by rintro ⟨⟨i, k⟩, rfl⟩; rfl
  right_inv k := rfl

/-- The fibre-over-`j` of the bead-index map has `c.get j` elements. -/
theorem stairβ_fiber_card (c : List ℕ+) (j : Fin c.length) :
    (Finset.univ.filter (fun q => stairβ c q = j)).card = (c.get j : ℕ) := by
  have e1 : {q : Fin (dimSum c) // stairβ c q = j} ≃ {p : beadEvent c // p.1 = j} :=
    Equiv.subtypeEquiv (beadFin c) (fun _ => Iff.rfl)
  rw [← Fintype.card_subtype, Fintype.card_congr (e1.trans (sigmaFstFiber j)), Fintype.card_fin]

/-- The staircase chain of `□(dimSum c)`, whose dimension sequence is `c` — reconstructed straight
from the bead-index surjection `stairβ` (no height function). -/
noncomputable def stairChain (c : List ℕ+) : CubeChain (□(dimSum c)) :=
  ofBlockMap (stairβ c) (stairβ_surjective c)

theorem stairChain_dims (c : List ℕ+) : (stairChain c).dims = c := by
  have h : (stairChain c).dims
      = List.ofFn (fun j : Fin c.length =>
          (⟨(StdCube.noneSet (blockSign (stairβ c) j)).card,
              blockSize_pos (stairβ c) (stairβ_surjective c) j⟩ : ℕ+)) := by
    show (blockCubes (stairβ c) (stairβ_surjective c)).map (·.1) = _
    rw [blockCubes, List.map_ofFn]; rfl
  rw [h]
  conv_rhs => rw [← List.ofFn_get c]
  refine congrArg List.ofFn (funext fun j => ?_)
  apply PNat.coe_injective
  show (StdCube.noneSet (blockSign (stairβ c) j)).card = (c.get j : ℕ)
  rw [noneSet_blockSign]
  exact stairβ_fiber_card c j

/-- A bipointed staircase `⋁c ⟶ □(dimSum c)`, realizing the wedge as a chain filling the cube. -/
noncomputable def stair (c : List ℕ+) : ⋁c ⟶ □(dimSum c) :=
  eqToHom (congrArg BPSet.serialWedge (stairChain_dims c).symm) ≫ (wedgeOfChain (stairChain c)).2

/-! ## Wedge→wedge coordinate bijectivity, from the cube case via `stair`. -/

noncomputable instance coordWedgeFintype (a : List ℕ+) :
    Fintype (Cotensor Coord (⋁a).toPsh) :=
  Fintype.ofEquiv _ (coordWedge a).symm

theorem coord_card (a : List ℕ+) :
    Fintype.card (Cotensor Coord (⋁a).toPsh) = dimSum a := by
  have hc : Fintype.card (Cotensor Coord (⋁a).toPsh)
      = Fintype.card (Σ i : Fin a.length, Fin (a.get i : ℕ)) := Fintype.card_congr (coordWedge a)
  rw [hc, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [sum_get_eq_sum_map a (fun d : ℕ+ => (d : ℕ)), ← dimSum_sum]

/-- The coend map of a wedge map is bijective: cube target (via `stair`) + functoriality + count. -/
theorem coordWedgeMap_bijective {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) :
    Function.Bijective (Cotensor.map Coord φ.hom) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by rw [coord_card, coord_card, serialWedge_dimSum_eq φ]⟩
  have hcomp : Cotensor.map Coord (stair b).hom ∘ Cotensor.map Coord φ.hom
      = Cotensor.map Coord (φ ≫ stair b).hom := by rw [comp_hom, Cotensor.map_comp]
  have hcube : Function.Injective (Cotensor.map Coord (φ ≫ stair b).hom) := by
    have h := (coordLift_map_bijective (φ ≫ stair b)).injective
    rwa [cotensorLift_map_eq_coordFlip'] at h
  rw [← hcomp] at hcube
  exact hcube.of_comp

/-- The coend map, as an `Equiv`. -/
noncomputable def coordEquiv {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) :
    Cotensor Coord (⋁a).toPsh ≃ Cotensor Coord (⋁b).toPsh :=
  Equiv.ofBijective _ (coordWedgeMap_bijective φ)

theorem coordEquiv_comp {a b c : List ℕ+} (u : ⋁a ⟶ ⋁b) (v : ⋁b ⟶ ⋁c) :
    coordEquiv (u ≫ v) = (coordEquiv u).trans (coordEquiv v) := by
  ext t
  change Cotensor.map Coord (u ≫ v).hom t = Cotensor.map Coord v.hom (Cotensor.map Coord u.hom t)
  rw [comp_hom, Cotensor.map_comp]; rfl

/-! ## Event relabelling along a refinement (bijective) — conjugate `coordEquiv` by `coordWedge`. -/

/-- The recoordinatization `beadEvent y ≃ beadEvent x` induced by the refinement. -/
noncomputable def eventEquiv {x y : Ch⋆ K} (f : x ⟶ y) :
    beadEvent y.chain.dims ≃ beadEvent x.chain.dims :=
  (coordWedge y.chain.dims).symm.trans ((coordEquiv (wedgeOf f)).trans (coordWedge x.chain.dims))

theorem eventEquiv_apply {x y : Ch⋆ K} (f : x ⟶ y) (e : beadEvent y.chain.dims) :
    eventEquiv f e
      = coordWedge x.chain.dims (coordEquiv (wedgeOf f) ((coordWedge y.chain.dims).symm e)) := rfl

theorem eventEquiv_comp {x y z : Ch⋆ K} (f : x ⟶ y) (g : y ⟶ z) :
    eventEquiv (f ≫ g) = (eventEquiv g).trans (eventEquiv f) := by
  refine Equiv.ext fun e => ?_
  rw [Equiv.trans_apply, eventEquiv_apply, eventEquiv_apply, eventEquiv_apply, wedgeOf_comp,
    coordEquiv_comp, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem eventEquiv_id (x : Ch⋆ K) : eventEquiv (𝟙 x) = Equiv.refl _ := by
  have hco : coordEquiv (wedgeOf (𝟙 x)) = Equiv.refl _ := by
    refine Equiv.ext fun t => ?_
    change Cotensor.map Coord (wedgeOf (𝟙 x)).hom t = t
    rw [show wedgeOf (𝟙 x) = 𝟙 (⋁x.chain.dims) from rfl, id_hom, Cotensor.map_id]; rfl
  refine Equiv.ext fun e => ?_
  rw [eventEquiv_apply, hco, Equiv.refl_apply, Equiv.apply_symm_apply, Equiv.refl_apply]

/-! ## The run's rank -/

/-- `dimSum` as the sum of bead dimensions. -/
theorem dimSum_eq_sum (a : List ℕ+) : (∑ i : Fin a.length, (a.get i : ℕ)) = dimSum a := by
  rw [sum_get_eq_sum_map a (fun d : ℕ+ => (d : ℕ)), ← dimSum_sum]

/-- **The lex order of the sigma-flattening.**  If `i` precedes `i'`, its whole block flattens
below `i'`'s — the prefix at `i` plus a within-block offset stays under the prefix at `i'`. -/
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
    simp only [List.getD_eq_getElem a 1 hjm, List.get_eq_getElem, Fin.coe_castLE]
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
theorem runProj_dims_length (w : Ch⋆ K) (i : Fin w.chain.dims.length) :
    (runProj w.run i).chain.dims.length = (w.chain.dims.get i : ℕ) := by
  rw [← dimSum_eq_length_of_ones (runProj w.run i).ones]
  exact wedgeDimSum_eq (runProj w.run i).map

/-- Bead `i`'s local run order, as a permutation of its `dᵢ` coordinates: the position each
coordinate takes in bead `i`'s local run. -/
noncomputable def beadPerm (w : Ch⋆ K) (i : Fin w.chain.dims.length) :
    Fin (w.chain.dims.get i : ℕ) ≃ Fin (w.chain.dims.get i : ℕ) :=
  Equiv.ofBijective
    (fun k => finCongr (runProj_dims_length w i) (beadOf (runProj w.run i).chain k))
    (Finite.surjective_iff_bijective.mp fun j => by
      obtain ⟨k, hk⟩ := beadOf_surjective (runProj w.run i).chain
        (finCongr (runProj_dims_length w i).symm j)
      exact ⟨k, by rw [hk]; simp⟩)

@[simp] theorem beadPerm_val (w : Ch⋆ K) (i : Fin w.chain.dims.length)
    (k : Fin (w.chain.dims.get i : ℕ)) :
    (beadPerm w i k : ℕ) = (beadOf (runProj w.run i).chain k : ℕ) := rfl

/-- The run's rank: the chain's events, ordered bead-by-bead, and within each bead by that bead's
local run (`beadPerm`), then flattened lexicographically. -/
noncomputable def rankEquiv (w : Ch⋆ K) : beadEvent w.chain.dims ≃ Fin (Nev w) :=
  (Equiv.sigmaCongrRight (beadPerm w)).trans
    (finSigmaFinEquiv.trans (finCongr (dimSum_eq_sum w.chain.dims)))

theorem rankEquiv_val (w : Ch⋆ K) (i : Fin w.chain.dims.length)
    (k : Fin (w.chain.dims.get i : ℕ)) :
    (rankEquiv w ⟨i, k⟩ : ℕ)
      = (∑ j : Fin (i : ℕ), (w.chain.dims.get (Fin.castLE i.2.le j) : ℕ))
        + (beadOf (runProj w.run i).chain k : ℕ) := by
  simp only [rankEquiv, Equiv.trans_apply, Equiv.sigmaCongrRight_apply, finCongr_apply,
    Fin.coe_cast, finSigmaFinEquiv_apply, beadPerm_val]

/-! ## The crossing permutation -/

/-- Transport an equiv/perm across an equality of strand counts. -/
def finCast {m n : ℕ} (h : m = n) : Fin m ≃ Fin n := Equiv.cast (congrArg Fin h)

/-- Transport a permutation across an equality of strand counts. -/
def permCast {m n : ℕ} (h : m = n) : Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin n) :=
  Equiv.permCongr (finCast h)

/-- The reordering from `x`'s run order to `y`'s (via the event relabelling), before regrading. -/
noncomputable def rawPerm {x y : Ch⋆ K} (f : x ⟶ y) : Fin (Nev x) ≃ Fin (Nev y) :=
  (rankEquiv x).symm.trans ((eventEquiv f).symm.trans (rankEquiv y))

theorem rawPerm_comp {x y z : Ch⋆ K} (f : x ⟶ y) (g : y ⟶ z) :
    rawPerm (f ≫ g) = (rawPerm f).trans (rawPerm g) := by
  refine Equiv.ext fun i => ?_
  simp only [rawPerm, eventEquiv_comp, Equiv.trans_apply, Equiv.symm_trans_apply,
    Equiv.symm_apply_apply]

theorem rawPerm_id (x : Ch⋆ K) : rawPerm (𝟙 x) = finCast (Nev_eq (𝟙 x)) := by
  refine Equiv.ext fun i => ?_
  simp only [rawPerm, eventEquiv_id, Equiv.refl_symm, Equiv.refl_trans, Equiv.symm_trans_self,
    Equiv.refl_apply, finCast]
  rw [Subsingleton.elim (congrArg Fin (Nev_eq (𝟙 x))) rfl]; rfl

/-- The crossing permutation of a refinement (the run-based `crossPerm`). -/
noncomputable def permOf {x y : Ch⋆ K} (f : x ⟶ y) : Equiv.Perm (Fin (Nev x)) :=
  (rawPerm f).trans (finCast (Nev_eq f)).symm

theorem permOf_id (x : Ch⋆ K) : permOf (𝟙 x) = 1 := by
  rw [permOf, rawPerm_id, Equiv.self_trans_symm]; rfl

@[simp] theorem finCast_coe {m n : ℕ} (h : m = n) (i : Fin m) : (finCast h i : ℕ) = (i : ℕ) := by
  subst h; rfl

@[simp] theorem finCast_symm_coe {m n : ℕ} (h : m = n) (i : Fin n) :
    ((finCast h).symm i : ℕ) = (i : ℕ) := by
  subst h; rfl

theorem permOf_comp_aux {m n k : ℕ} (hmn : m = n) (hnk : n = k) (hmk : m = k)
    (Rf : Fin m ≃ Fin n) (Rg : Fin n ≃ Fin k) :
    ((Rf.trans Rg).trans (finCast hmk).symm)
      = permCast hmn.symm (Rg.trans (finCast hnk).symm) * (Rf.trans (finCast hmn).symm) := by
  refine Equiv.ext fun i => ?_
  simp only [permCast, Equiv.Perm.mul_apply, Equiv.permCongr_apply, Equiv.trans_apply]
  have harg : (finCast hmn.symm).symm ((finCast hmn).symm (Rf i)) = Rf i := by apply Fin.ext; simp
  rw [harg]; apply Fin.ext; simp

/-- The cocycle law, matching `permBraidFunctor`'s convention `p (f ≫ g) = p g * p f`. -/
theorem permOf_comp {x y z : Ch⋆ K} (f : x ⟶ y) (g : y ⟶ z) :
    permOf (f ≫ g) = permCast (Nev_eq f).symm (permOf g) * permOf f := by
  have h := permOf_comp_aux (Nev_eq f) (Nev_eq g) (Nev_eq (f ≫ g)) (rawPerm f) (rawPerm g)
  rw [← rawPerm_comp] at h
  exact h

/-- The **image of a coordinate** under a wedge map, coordinatized: source bead `i`'s `k`-th
coordinate lands in target bead `blockIdx φ i`, at coordinate `faceEmb (blockFace φ i) k`. -/
theorem coordEquiv_val {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) (i : Fin ad.length)
    (k : Fin (ad.get i : ℕ)) :
    coordWedge cd (coordEquiv φ ((coordWedge ad).symm ⟨i, k⟩))
      = ⟨blockIdx φ.hom i, faceEmb (blockFace φ.hom i) k⟩ := by
  have e1 : coordEquiv φ ((coordWedge ad).symm ⟨i, k⟩)
      = Cotensor.map Coord (ιᵂ ad i ≫ φ.hom) ((coordCube (ad.get i : ℕ)).symm k) := by
    show Cotensor.map Coord φ.hom _ = _
    rw [coordWedge_symm_apply, Cotensor.map_map]
  have hinner : Cotensor.map Coord (yoneda.map (blockFace φ.hom i)) ((coordCube (ad.get i : ℕ)).symm k)
      = (coordCube (cd.get (blockIdx φ.hom i) : ℕ)).symm (faceEmb (blockFace φ.hom i) k) := by
    apply (coordCube _).injective
    rw [Equiv.apply_symm_apply]
    erw [coordCube_map_symm]
  have hstep : coordEquiv φ ((coordWedge ad).symm ⟨i, k⟩)
      = Cotensor.map Coord (ιᵂ cd (blockIdx φ.hom i))
          ((coordCube (cd.get (blockIdx φ.hom i) : ℕ)).symm (faceEmb (blockFace φ.hom i) k)) := by
    rw [e1, blockFace_spec φ.hom i, ← hinner]
    exact (Cotensor.map_map Coord (yoneda.map (blockFace φ.hom i)) (ιᵂ cd (blockIdx φ.hom i)) _).symm
  rw [hstep]
  exact coordWedge_apply_map cd (blockIdx φ.hom i) (faceEmb (blockFace φ.hom i) k)

/-- The **bead of a coordinate's image** under a wedge map is `blockIdx` of its source bead —
independent of the sub-coordinate. -/
theorem coordEquiv_bead {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) (i : Fin ad.length)
    (k : Fin (ad.get i : ℕ)) :
    (coordWedge cd (coordEquiv φ ((coordWedge ad).symm ⟨i, k⟩))).1
      = blockIdx φ.hom i := by
  rw [coordEquiv_val]

/-- The chain-bead of `eventEquiv f a` is `blockIdx (wedgeOf f)` of `a`'s bead. -/
theorem eventEquiv_bead {x y : Ch⋆ K} (f : x ⟶ y) (a : beadEvent y.chain.dims) :
    (eventEquiv f a).1 = blockIdx (wedgeOf f).hom a.1 := by
  rw [eventEquiv_apply, ← Sigma.eta a, coordEquiv_bead]

/-- The relabelled event, coordinatized: `eventEquiv f ⟨iβ, k⟩` lands in x-bead
`blockIdx (wedgeOf f) iβ` at coordinate `faceEmb (blockFace (wedgeOf f) iβ) k`. -/
theorem eventEquiv_val {x y : Ch⋆ K} (f : x ⟶ y) (iβ : Fin y.chain.dims.length)
    (k : Fin (y.chain.dims.get iβ : ℕ)) :
    eventEquiv f ⟨iβ, k⟩
      = ⟨blockIdx (wedgeOf f).hom iβ, faceEmb (blockFace (wedgeOf f).hom iβ) k⟩ := by
  rw [eventEquiv_apply, coordEquiv_val]

/-- `blockIdx` is monotone for a bi-pointed wedge map (packaging `serialWedge_blockIdx_monotone`
with the endpoint condition every `BPSet` map carries). -/
theorem blockIdx_monotone {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) : Monotone (blockIdx φ.hom) :=
  serialWedge_blockIdx_monotone φ.hom φ.app_init

/-! ## Length-additivity — the run-order no-double-cross

`permOf f` compares `x`'s run-order to `y`'s (through `eventEquiv f`).  Length-additivity is the
run-order analog of `crossPerm_noDoubleCross`: a pair whose order disagrees between `x` and `y` must
agree between `y` and `z` — once a refinement resolves a formerly-concurrent pair, further
refinement keeps that resolution. -/

/-- The cocycle relation before regrading: `rawPerm` carries a rank in `x` to the rank of the
same event in `y`. -/
theorem rawPerm_rankEquiv {x y : Ch⋆ K} (f : x ⟶ y) (e : beadEvent x.chain.dims) :
    rawPerm f (rankEquiv x e) = rankEquiv y ((eventEquiv f).symm e) := by
  simp only [rawPerm, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- `permOf f` carries a rank in `x` to the (same-valued) rank of the same event in `y`. -/
theorem permOf_rankEquiv_val {x y : Ch⋆ K} (f : x ⟶ y) (e : beadEvent x.chain.dims) :
    (permOf f (rankEquiv x e) : ℕ) = (rankEquiv y ((eventEquiv f).symm e) : ℕ) := by
  rw [permOf, Equiv.trans_apply, finCast_symm_coe, rawPerm_rankEquiv]

/-- The composite `ρ ∘ σ` (`ρ = permCast … (permOf g)`, `σ = permOf f`) carries a rank in `x` to the
rank of the same event in `z`. -/
theorem rho_sigma_val {x y z : Ch⋆ K} (f : x ⟶ y) (g : y ⟶ z) (e : beadEvent x.chain.dims) :
    ((permCast (Nev_eq f).symm (permOf g)) (permOf f (rankEquiv x e)) : ℕ)
      = (rankEquiv z ((eventEquiv g).symm ((eventEquiv f).symm e)) : ℕ) := by
  rw [permCast, Equiv.permCongr_apply, finCast_coe]
  have harg : (finCast (Nev_eq f).symm).symm (permOf f (rankEquiv x e))
      = rankEquiv y ((eventEquiv f).symm e) :=
    Fin.ext (by rw [finCast_symm_coe, permOf_rankEquiv_val])
  rw [harg, permOf_rankEquiv_val]

/-- **The run refines the chain order.**  An event in an earlier chain-bead has an earlier rank —
the run visits the beads in order (`blockIdx` monotonicity of the run map). -/
theorem rankEquiv_lt_of_chainBead {w : Ch⋆ K} {e e' : beadEvent w.chain.dims}
    (h : (e.1 : ℕ) < e'.1) : rankEquiv w e < rankEquiv w e' := by
  obtain ⟨i, k⟩ := e
  obtain ⟨i', k'⟩ := e'
  rw [Fin.lt_def, rankEquiv_val, rankEquiv_val, ← beadPerm_val w i k, ← beadPerm_val w i' k']
  exact dims_prefix_lt h (beadPerm w i k) (beadPerm w i' k')

/-- **Within a bead, the rank order is the local run order.**  The bead-prefix offsets cancel, so
`rankEquiv` restricted to a single bead is exactly `beadOf` of that bead's local run. -/
theorem rankEquiv_within_bead (w : Ch⋆ K) (i : Fin w.chain.dims.length)
    (k k' : Fin (w.chain.dims.get i : ℕ)) :
    (rankEquiv w ⟨i, k⟩ < rankEquiv w ⟨i, k'⟩
      ↔ beadOf (runProj w.run i).chain k < beadOf (runProj w.run i).chain k') := by
  rw [Fin.lt_def, Fin.lt_def, rankEquiv_val, rankEquiv_val]
  omega

/-- **A refinement refines the chain-bead order.**  If `a` precedes `b` in `y`'s bead order, their
`g`-preimages keep that order in `z` (`blockIdx` monotonicity of `wedgeOf g`). -/
theorem chainBead_refine {y z : Ch⋆ K} (g : y ⟶ z) {a b : beadEvent y.chain.dims}
    (h : (a.1 : ℕ) < b.1) : (((eventEquiv g).symm a).1 : ℕ) < ((eventEquiv g).symm b).1 := by
  by_contra hcon
  rw [not_lt] at hcon
  have hmono := blockIdx_monotone (wedgeOf g) (Fin.le_def.mpr hcon)
  rw [← eventEquiv_bead, ← eventEquiv_bead, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hmono
  exact absurd h (not_lt.mpr (Fin.le_def.mp hmono))

/-- The refinement pulls the run back: `y`'s classifying map is `x`'s precomposed with `wedgeOf f`
(functoriality of `Lines`/`pshExtFunctor`). -/
theorem chStar_hom_eq {x y : Ch⋆ K} (f : x ⟶ y) : y.2 = (wedgeOf f).hom ≫ x.2 := f.2.symm

/-- **`y`'s run is `x`'s run restricted along `wedgeOf f`.** -/
theorem chStar_run_eq {x y : Ch⋆ K} (f : x ⟶ y) : y.run = runRestrict (wedgeOf f) x.run := by
  rw [ChStar.run, chStar_hom_eq f, runRestrict]
  congr 1
  rw [ChStar.run, pshOfRun, Equiv.symm_apply_apply]

/-- **The localization diagram** (at the `.2`/`runPresheaf` level, functorial — no induction).  Bead
`iβ` of `y`'s classifying map factors through bead `blockIdx … iβ` of `x`'s, via the face
`blockFace … iβ`.  Reading into `runPresheaf`: `y`'s local run at `iβ` is `x`'s local run at
`blockIdx … iβ` restricted along that face. -/
theorem chStar_hom_local {x y : Ch⋆ K} (f : x ⟶ y) (iβ : Fin y.chain.dims.length) :
    ιᵂ y.chain.dims iβ ≫ y.2
      = yoneda.map (blockFace (wedgeOf f).hom iβ)
          ≫ (ιᵂ x.chain.dims (blockIdx (wedgeOf f).hom iβ) ≫ x.2) := by
  rw [chStar_hom_eq f, ← Category.assoc, blockFace_spec (wedgeOf f).hom iβ]
  exact Category.assoc _ _ _

/-- **Reading bead `i`'s bottom vertex.**  Coordinate `q` reads `true` there exactly when its own
bead precedes `i` — the junction-vertex form of the master lemma, via `readVec_mono` on the spine.
Holds for any chain of `□d` (no run hypothesis). -/
theorem readVec_beadBot_eq {d : ℕ} (C : Ch (□d)) (i : Fin C.dims.length) (q : Fin d) :
    readVec (C.map.hom⟪0⟫ (beadBot C.dims i)) q = decide ((beadOf C q : ℕ) < (i : ℕ)) := by
  have hqflip : q ∈ Set.range (faceEmb (beadFace C.map.hom (beadOf C q))) := beadFlips_beadOf C q
  have hbot : readVec (C.map.hom⟪0⟫ (beadBot C.dims (beadOf C q))) q = false :=
    readVec_beadBot_flip C.map.hom (beadOf C q) hqflip
  rcases lt_trichotomy (beadOf C q : ℕ) (i : ℕ) with hlt | heq | hgt
  · have htop : readVec (C.map.hom⟪0⟫ (beadTop C.dims (beadOf C q))) q = true :=
      readVec_beadTop_flip C.map.hom (beadOf C q) hqflip
    have hmono := readVec_mono C.map.hom (beadTop_reaches_beadBot C.dims (beadOf C q) i hlt) q
    rw [htop] at hmono
    rw [le_antisymm (Bool.le_true _) hmono]
    simp [hlt]
  · obtain rfl : beadOf C q = i := Fin.ext heq
    rw [hbot]
    simp
  · have hmono := readVec_mono C.map.hom
      (beadBot_reaches_beadBot C.dims i (beadOf C q) (le_of_lt hgt)) q
    rw [hbot] at hmono
    rw [le_antisymm hmono (Bool.false_le _)]
    simp [Nat.not_lt.mpr (le_of_lt hgt)]

/-- The `i`-th survivor of `filterMap` reads `fn` of the `i`-th kept element (`filter`), whose
positions embed strict-monotonically into the source — the reindexing under a `filterMap`. -/
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

/-- Projecting a surviving cube reads its sign along `faceEmb`: `restrictCube` keeps the sign
vector, restricted to the coordinates `face` uses. -/
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

/-- Coordinate `q` reads `none` at the `j`-th cube of a chain's read-off cube list exactly when `q`
is the bead that cube flips — the cube-list form of `BeadFlips`. -/
private theorem sign_wedgeToCubes_eq_none {m : ℕ} (b : Ch (□m)) (q : Fin m) (j : ℕ)
    (hj : j < (wedgeToCubes ⟨b.dims, b.map.hom⟩).length) :
    (Box.sign ((wedgeToCubes ⟨b.dims, b.map.hom⟩)[j]'hj).2).val q = none
      ↔ (beadOf b q : ℕ) = j := by
  have hjlen : j < b.dims.length := (wedgeToCubes_length b.dims b.map.hom) ▸ hj
  rw [show (wedgeToCubes ⟨b.dims, b.map.hom⟩)[j]'hj
        = (wedgeToCubes ⟨b.dims, b.map.hom⟩).get ⟨j, hj⟩ from rfl,
     wedgeToCubes_get b.dims b.map.hom ⟨j, hj⟩]
  change (StdCube.ev (beadFace b.map.hom ⟨j, hjlen⟩)).val q = none ↔ (beadOf b q : ℕ) = j
  rw [← mem_range_faceEmb (beadFace b.map.hom ⟨j, hjlen⟩) q]
  constructor
  · intro h
    rw [(beadFlips_existsUnique b q).unique (beadFlips_beadOf b q) h]
  · intro h
    have hbe : beadOf b q = ⟨j, hjlen⟩ := Fin.ext h
    rw [← hbe]; exact beadFlips_beadOf b q

/-- **Face restriction preserves cube-run order** (the single-cube geometry).  Restricting a run of
`□d` along a `Box` face `g : ▫e ⟶ ▫d` keeps the relative order of the coordinates it retains:
`beadOf` of the restriction at `k` compares like `beadOf` of the original at `faceEmb g k`.

The restricted run's cube list is the `filterMap` of the original's along `restrictCube g`; each
surviving edge flips `k` exactly when the edge it comes from flips `faceEmb g k`, and the survivor
positions embed strict-monotonically, so the two `beadOf` orders agree. -/
theorem beadOf_restrict_lt {d e : ℕ} (C : Run (□d)) (g : ▫e ⟶ ▫d) (k k' : Fin e) :
    (beadOf ((runPresheaf.map g.op C : Run (□e)).chain) k
        < beadOf ((runPresheaf.map g.op C : Run (□e)).chain) k'
      ↔ beadOf C.chain (faceEmb g k) < beadOf C.chain (faceEmb g k')) := by
  set C' : Run (□e) := runPresheaf.map g.op C with hC'eq
  -- The restricted run's cube list is the projection of the original's.
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
  -- The survivor-position order embedding.
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
  -- The order-preserving identity: `beadOf` of the restriction embeds into `beadOf` of `C`.
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
    -- `q` reads `none` at the `i₀`-th cube of `C'` (it flips there).
    have hnone' : (Box.sign ((wedgeToCubes ⟨C'.chain.dims, C'.chain.map.hom⟩)[i₀]'hi₀).2).val q
        = none := (sign_wedgeToCubes_eq_none C'.chain q i₀ hi₀).mpr rfl
    -- Transport the reading through `restrictCube` and `faceEmb g`.
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

/-- **Within a bead the refinement preserves the run order.**  For events concurrent in `y`
(same bead), the pull-back along `f` cannot reorder them: `x`'s run and `y`'s run agree.  This is the
restriction-preserves-order content of `crossPerm_H`'s within-block case. -/
theorem within_bead_agree {x y : Ch⋆ K} (f : x ⟶ y) {a b : beadEvent y.chain.dims}
    (hbead : a.1 = b.1) :
    (rankEquiv x (eventEquiv f a) < rankEquiv x (eventEquiv f b)
      ↔ rankEquiv y a < rankEquiv y b) := by
  obtain ⟨iβ, ka⟩ := a
  obtain ⟨jb, kb⟩ := b
  subst hbead
  have hyrun : runProj y.run iβ
      = runPresheaf.map (blockFace (wedgeOf f).hom iβ).op
          (runProj x.run (blockIdx (wedgeOf f).hom iβ)) := by
    rw [chStar_run_eq f]
    exact runProj_runRestrict (wedgeOf f) x.run iβ
  rw [eventEquiv_val, eventEquiv_val,
    rankEquiv_within_bead x (blockIdx (wedgeOf f).hom iβ)
      (faceEmb (blockFace (wedgeOf f).hom iβ) ka) (faceEmb (blockFace (wedgeOf f).hom iβ) kb),
    rankEquiv_within_bead y iβ ka kb, hyrun]
  exact (beadOf_restrict_lt (runProj x.run (blockIdx (wedgeOf f).hom iβ))
    (blockFace (wedgeOf f).hom iβ) ka kb).symm

/-- **The run-order no-double-cross condition.**  If `x` orders `e₁` before `e₂` while `y` orders
their `f`-preimages the opposite way, then `z` keeps `y`'s order.  This is `crossPerm_H`'s content
with the run's rank replacing the tope. -/
theorem runOrder_H {x y z : Ch⋆ K} (f : x ⟶ y) (g : y ⟶ z) (e₁ e₂ : beadEvent x.chain.dims)
    (h1 : rankEquiv x e₁ < rankEquiv x e₂)
    (h2 : rankEquiv y ((eventEquiv f).symm e₂) < rankEquiv y ((eventEquiv f).symm e₁)) :
    rankEquiv z ((eventEquiv g).symm ((eventEquiv f).symm e₂))
      < rankEquiv z ((eventEquiv g).symm ((eventEquiv f).symm e₁)) := by
  set a := (eventEquiv f).symm e₁ with ha
  set b := (eventEquiv f).symm e₂ with hb
  have he₁ : eventEquiv f a = e₁ := by rw [ha, Equiv.apply_symm_apply]
  have he₂ : eventEquiv f b = e₂ := by rw [hb, Equiv.apply_symm_apply]
  -- Step 1: `b` strictly precedes `a` in `y`'s bead order.
  have hstep1 : (b.1 : ℕ) < a.1 := by
    rcases lt_trichotomy (a.1 : ℕ) (b.1 : ℕ) with hlt | heq | hgt
    · exact absurd (rankEquiv_lt_of_chainBead hlt) (asymm h2)
    · rw [← he₁, ← he₂] at h1
      exact absurd ((within_bead_agree f (Fin.ext heq)).mp h1) (asymm h2)
    · exact hgt
  -- Steps 2–3: the separation lifts to `z`, and `z`'s run refines it.
  exact rankEquiv_lt_of_chainBead (chainBead_refine g hstep1)

private theorem permLen_permCast_aux {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin m)) :
    permLen (permCast h σ) = permLen σ := by subst h; rfl

/-- Length-additivity: each pair of events crosses at most once. -/
theorem permOf_noDoubleCross {x y z : Ch⋆ K} (f : x ⟶ y) (g : y ⟶ z) :
    permLen (permOf (f ≫ g)) = permLen (permOf f) + permLen (permOf g) := by
  have H : ∀ i j : Fin (Nev x), i < j → permOf f j < permOf f i →
      (permCast (Nev_eq f).symm (permOf g)) (permOf f j)
        < (permCast (Nev_eq f).symm (permOf g)) (permOf f i) := by
    intro i j hij hfl
    obtain ⟨e₁, rfl⟩ := (rankEquiv x).surjective i
    obtain ⟨e₂, rfl⟩ := (rankEquiv x).surjective j
    -- restate the three inequalities as rank comparisons and invoke `runOrder_H`
    have hlt : rankEquiv y ((eventEquiv f).symm e₂) < rankEquiv y ((eventEquiv f).symm e₁) := by
      rw [Fin.lt_def, ← permOf_rankEquiv_val, ← permOf_rankEquiv_val]; exact hfl
    have := runOrder_H f g e₁ e₂ hij hlt
    rw [Fin.lt_def, rho_sigma_val, rho_sigma_val]
    exact this
  rw [permOf_comp, permLen_mul_of_noDoubleCross H, permLen_permCast_aux]

/-! ## The graded braid functor -/

theorem permLen_permCast {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin m)) :
    permLen (permCast h σ) = permLen σ := by subst h; rfl

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

/-- The graded braid functor: `x ↦ strands (Nev x)`, a refinement to the positive braid `ofPerm`. -/
noncomputable def ConcPos (K : BPSet) : Ch⋆ K ⥤ Braids where
  obj x := strands (Nev x)
  map {x y} f := braidHom (ofPerm (permOf f)) ≫ eqToHom (congrArg strands (Nev_eq f))
  map_id x := by
    have he : eqToHom (congrArg strands (Nev_eq (𝟙 x))) = 𝟙 (strands (Nev x)) := by
      rw [Subsingleton.elim (congrArg strands (Nev_eq (𝟙 x))) rfl, eqToHom_refl]
    rw [permOf_id, ofPerm_one, he, Category.comp_id]
    rfl
  map_comp {x y z} f g := by
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

/-- The concurrency braid functor: the free-groupoid lift of `ConcPos`. -/
noncomputable def Conc (K : BPSet) : FreeGroupoid (Ch⋆ K) ⥤ Braids :=
  FreeGroupoid.lift (ConcPos K)

end CubeChains
