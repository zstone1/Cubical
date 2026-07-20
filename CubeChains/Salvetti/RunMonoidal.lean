import CubeChains.Chains.Segal
import CubeChains.Chains.BlockDecomp
import CubeChains.Foundations.WedgeMonoidal
import CubeChains.Chains.SerialWedgeFunctor
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Algebra.FreeMonoid.Basic
import CubeChains.Foundations.GeoTensor

/-!
# Salvetti/RunMonoidal — the all-edges runs and `run` as a monoidal functor

`run n = ⋁(1ⁿ)` is the finest chain shape; `runPlus`/`runSl`/`runSr` are its wedge-splitting isos,
and `run` is packaged as a (strong) monoidal functor `(ℕ,+) ⥤ (WedgeBP, ∨)` with tensorator
`runPlus`.  The retraction machinery (`Run`, `runRetract`, `Chains/Salvetti/Lines`) builds on this.
-/

open CategoryTheory Opposite CubeChain StdCube ChainCat
open BPSet MonoidalCategory

namespace CubeChains

/-- `n ↦ 1ⁿ`, the all-edges word; `Multiplicative` so that `⊗` on the source is `ℕ`'s `+`. -/
def onesObj (n : Multiplicative ℕ) : FreeMonoid ℕ+ :=
  FreeMonoid.ofList (List.replicate n.toAdd 1)

/-- The tensorator's content: concatenating all-edges words adds their lengths. -/
theorem onesObj_mul (m n : Multiplicative ℕ) :
    onesObj m * onesObj n = onesObj (m * n) :=
  congrArg FreeMonoid.ofList (List.replicate_append_replicate ..)

def Ones : Discrete (Multiplicative ℕ) ⥤ DimList :=
  Discrete.functor (fun n => (Discrete.mk (onesObj n)))

/-- Strong monoidal: the coherence squares are equations in the thin category `DimList`. -/
instance : Ones.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Discrete.eqToIso rfl
      μIso := fun X Y => Discrete.eqToIso (onesObj_mul X.as Y.as)
      μIso_hom_natural_left := fun _ _ => Subsingleton.elim _ _
      μIso_hom_natural_right := fun _ _ => Subsingleton.elim _ _
      associativity := fun _ _ _ => Subsingleton.elim _ _
      left_unitality := fun _ => Subsingleton.elim _ _
      right_unitality := fun _ => Subsingleton.elim _ _ }

def OneD : Discrete (Multiplicative ℕ) ⥤ BPSet := Ones ⋙ serialWedgeFunctor

instance : OneD.LaxMonoidal := inferInstanceAs ((Ones ⋙ serialWedgeFunctor).LaxMonoidal)

def Run (k : List ℕ+) : Type :=
  BPSet.Hom (OneD.obj (Discrete.mk (BPSet.dimSum k))) (⋁ k)

def runConsL (x : Run (a :: b)) : Run [a] := sorry
def runConsR (x : Run (a :: b)) : Run b := sorry

/-! ### Retracting a run onto a face

`runRetractFace face x` restricts the run `x` of `□ᵇ` along `face`: project every cell's sign
vector onto the directions `face` uses.  No recursion, no induction on dimension.

The projection is **not** a precubical map — `Box` has no degeneracies, and it drops the dimension
of any cell whose free coordinate `face` omits.  It lifts once pushed through a run, because a run
meets each direction in exactly one edge, and `runObj b` has cells only in dimensions `0` and `1`.

Everything goes through `faceEmb`, and that is forced: the retraction depends on `face` only
through the directions it uses, never through its `ε`s, so nothing natural in `face` *as a cube
map* can be it.  (Postcomposition `Ch □ⁿ ⥤ Ch □ᵇ` does have a right adjoint — pullback, `Ch` being
a slice on wedge-domains — but it computes the `ε`-dependent geometric intersection, which is the
wrong object.)  Do not look for a universal property over `Box`; there isn't one. -/

/-- `□^∨(1ⁿ)`, the all-edges chain shape. -/
abbrev runObj (n : ℕ) : BPSet := OneD.obj (Discrete.mk (Multiplicative.ofAdd n))

/-- **The projection.**  Restrict a sign vector to the directions `face` uses.  A plain function:
it does not preserve cell dimension, hence is not a precubical map. -/
def restrictCoord {n b : ℕ} (face : ▫n ⟶ ▫b) {k : ℕ} (c : Cell b k) : Fin n → Option Bool :=
  fun i => c.val (faceEmb face i)

@[simp] theorem restrictCoord_id {b k : ℕ} (c : Cell b k) :
    restrictCoord (𝟙 ▫b) c = c.val :=
  funext fun i => congrArg c.val (faceEmb_id b i)

theorem restrictCoord_comp {m n b k : ℕ} (f : ▫m ⟶ ▫n) (g : ▫n ⟶ ▫b) (c : Cell b k) (i : Fin m) :
    restrictCoord (f ≫ g) c i = restrictCoord g c (faceEmb f i) :=
  congrArg c.val (faceEmb_comp f g i)

/-- Vertices project to vertices: dimension `0` is total. -/
theorem card_restrictCoord_zero {n b : ℕ} (face : ▫n ⟶ ▫b) (c : Cell b 0) :
    (noneSet (restrictCoord face c)).card = 0 := by
  have hc : ∀ j, c.val j ≠ none := fun j hj => by
    have hmem : j ∈ noneSet c.val := mem_noneSet.mpr hj
    rw [Finset.card_eq_zero.mp c.prop] at hmem
    exact Finset.notMem_empty _ hmem
  refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun i hi => ?_)
  have h1 : restrictCoord face c i = none := mem_noneSet.mp hi
  exact hc (faceEmb face i) h1

/-- A `1`-cell's only free coordinate is `nones c 0`. -/
theorem noneSet_one {b : ℕ} (c : Cell b 1) : noneSet c.val = {nones c 0} := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp c.prop
  have hmem : nones c 0 ∈ noneSet c.val := nones_mem c 0
  rw [ha] at hmem ⊢
  rw [Finset.mem_singleton] at hmem
  rw [hmem]

/-- `j` is free in `a` exactly when it is in the range of `nones a`; for `a = Box.sign face` this
is "`face` uses direction `j`". -/
theorem val_eq_none_iff {b k : ℕ} (a : Cell b k) (j : Fin b) :
    a.val j = none ↔ ∃ i, nones a i = j :=
  ⟨fun h => ⟨nonesIdx a j (mem_noneSet.mpr h), nones_nonesIdx a j _⟩,
   fun ⟨i, hi⟩ => hi ▸ val_nones a i⟩

/-- An edge projects to an edge exactly when `face` uses its direction, and to a vertex otherwise.
This dichotomy is the entire obstruction to the projection being a precubical map. -/
theorem card_restrictCoord_one {n b : ℕ} (face : ▫n ⟶ ▫b) (c : Cell b 1) :
    (noneSet (restrictCoord face c)).card
      = if ∃ i, faceEmb face i = nones c 0 then 1 else 0 := by
  have key : noneSet (restrictCoord face c)
      = Finset.filter (fun i => faceEmb face i = nones c 0) Finset.univ := by
    ext i
    rw [mem_noneSet, Finset.mem_filter]
    constructor
    · intro h
      refine ⟨Finset.mem_univ _, ?_⟩
      have hmem : faceEmb face i ∈ noneSet c.val := mem_noneSet.mpr h
      rw [noneSet_one c, Finset.mem_singleton] at hmem
      exact hmem
    · rintro ⟨-, h⟩
      change c.val (faceEmb face i) = none
      rw [h]; exact val_nones c 0
  rw [key]
  by_cases h : ∃ i, faceEmb face i = nones c 0
  · obtain ⟨i₀, hi₀⟩ := h
    rw [if_pos ⟨i₀, hi₀⟩, Finset.card_eq_one]
    refine ⟨i₀, ?_⟩
    ext j
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hj⟩
      exact (faceEmb face).injective (hj.trans hi₀.symm)
    · rintro rfl
      exact ⟨Finset.mem_univ _, hi₀⟩
  · rw [if_neg h, Finset.card_eq_zero]
    exact Finset.eq_empty_iff_forall_notMem.mpr fun i hi =>
      h ⟨i, (Finset.mem_filter.mp hi).2⟩

/-- **The retraction.**  `x`'s cells, projected along `face`; a hom because exactly `n` of the `b`
edges survive and the rest collapse to vertices. -/
def runRetractFace {n b : ℕ} (face : ▫n ⟶ ▫b) (x : runObj b ⟶ cube b) :
    runObj n ⟶ cube n := sorry

/-- Restricting along the identity face does nothing (`restrictCoord_id`). -/
theorem runRetractFace_id {b : ℕ} (x : runObj b ⟶ cube b) :
    runRetractFace (𝟙 ▫b) x = x := sorry

/-- Restriction is functorial (`restrictCoord_comp`). -/
theorem runRetractFace_comp {m n b : ℕ} (f : ▫m ⟶ ▫n) (g : ▫n ⟶ ▫b) (x : runObj b ⟶ cube b) :
    runRetractFace (f ≫ g) x = runRetractFace f (runRetractFace g x) := sorry


--def runRetractFace {b n : ℕ} (face : (cube n).toPsh ⟶ (cube b).toPsh)
--    (x : run b ⟶ cube b) : run n ⟶ cube n := sorry
--
--def runRetractCube {b : ℕ} : (a : List ℕ+) → (f : (⋁a).toPsh ⟶ (cube b).toPsh) →
--    (x : run b ⟶ cube b) → Run a
--  | [],      _, _ => 𝟙 _
--  | a :: as, f, x => by
--      -- head bead `□↑a` and tail `⋁as` include (as presheaf maps) into `⋁(a :: as)`;
--      -- restrict the run onto the head face, recurse on the tail, concatenate.
--      have l := runRetractFace (Glue.inl (cube ↑a).finalVertex (⋁as).initVertex ≫ f) x
--      have r := runRetractCube as (Glue.inr (cube ↑a).finalVertex (⋁as).initVertex ≫ f) x
--      refine eqToHom (congrArg BPSet.serialWedge ?_) ≫ concatChainMap _ _
--        {dims := _, map := l} {dims := _, map := r}
--      -- ⊢ runDims (dimSum (a :: as)) = runDims ↑a ++ runDims (dimSum as)
--      simp only [dimSum_sum, List.map_cons, List.sum_cons, runDims_replicate,
--        List.replicate_append_replicate]
--
--def runRetract : (b : List ℕ+) → (a : List ℕ+) → (f : ⋁ a ⟶ ⋁ b) → (x : Run b) → Run a
--  | [], a, f, x => by
--      suffices h : a = [] by subst h; exact x
--      apply dimSum0_nil
--      rw [show 0 = dimSum [] from (by simp)]
--      exact serialWedge_dimSum_eq f
--  | b0 :: bs , a, f, x => by
--     simp only [serialWedge] at f
--     simp only [Run_eq] at x
--     have alt : ((□↑b0).wedge2 ⋁bs).AdmitsAltitude :=
--       wedge2_admitsAltitude (cube_admitsAltitude b0) (serialWedge_admitsAltitude bs)
--     let eqv := ChainCat.chSegal (cube ↑b0) (⋁bs) alt
--     let pq := eqv.inverse.obj {dims := a, map := f}
--     let κ := eqv.counitIso.app {dims := a, map := f}      -- the Segal counit: ⋁(pq₁ ++ pq₂) ≅ ⋁a
--     let recursed := runRetract bs pq.2.dims pq.2.map (runConsR x)
--     let cubef := runRetractCube pq.1.dims pq.1.map.hom (runConsL x ≫ (serialWedge1 b0).hom)
--     let foo := concatChainMap _ _ {dims := _, map := cubef} {dims := _, map := recursed}
--     -- glue the two retracts, re-append the halves, transport back along the counit
--     refine eqToHom (congrArg BPSet.serialWedge ?_) ≫ foo
--       ≫ (serialWedgeAppend pq.1.dims pq.2.dims).hom ≫ ChainCat.Hom.φ κ.hom
--     -- ⊢ runDims (dimSum a) = runDims (dimSum pq.1.dims) ++ runDims (dimSum pq.2.dims)
--     simp only [dimSum_sum, runDims_replicate, List.replicate_append_replicate,
--       List.replicate_inj, or_true, and_true]
--     rw [← List.sum_append_nat, ← List.map_append, ← dimSum_sum, ← dimSum_sum]
--     apply serialWedge_dimSum_eq
--     exact ChainCat.Hom.φ κ.inv


end CubeChains
