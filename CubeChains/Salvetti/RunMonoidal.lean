import CubeChains.Chains.Segal
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

/-! ### Splitting a sign vector: the destructor for `appendCell`

`appendCell` builds a `Box` map into a tensor; `splitCell` takes one apart.  Together they say
`Hom(▫n, ▫N₁ ⊗ ▫N₂) ≃ Σ_{n₁+n₂=n} Hom(▫n₁, ▫N₁) × Hom(▫n₂, ▫N₂)` — a map into a tensor *is* a
tensor of maps.  Block dimensions are read off the sign vector, not chosen.  Belongs in
`Foundations/BoxMonoidal` beside `appendCell`. -/

section SplitCell
variable {N₁ N₂ n : ℕ}

/-- The left block of a sign vector on `Fin (N₁ + N₂)`. -/
def takeCell (N₂ : ℕ) (c : Cell (N₁ + N₂) n) :
    Cell N₁ (noneSet fun i => c.val (Fin.castAdd N₂ i)).card :=
  ⟨fun i => c.val (Fin.castAdd N₂ i), rfl⟩

/-- The right block of a sign vector on `Fin (N₁ + N₂)`. -/
def dropCell (N₁ : ℕ) (c : Cell (N₁ + N₂) n) :
    Cell N₂ (noneSet fun i => c.val (Fin.natAdd N₁ i)).card :=
  ⟨fun i => c.val (Fin.natAdd N₁ i), rfl⟩

theorem append_takeCell_dropCell (c : Cell (N₁ + N₂) n) :
    Fin.append (takeCell N₂ c).val (dropCell N₁ c).val = c.val := by
  funext j
  cases j using Fin.addCases with
  | left i => rw [Fin.append_left]; rfl
  | right i => rw [Fin.append_right]; rfl

theorem card_takeCell_add_dropCell (c : Cell (N₁ + N₂) n) :
    (noneSet (takeCell N₂ c).val).card + (noneSet (dropCell N₁ c).val).card = n := by
  rw [← card_noneSet_append, append_takeCell_dropCell]
  exact c.prop

/-- **A `Box` map into a tensor is a tensor of maps.** -/
def splitCell (c : Cell (N₁ + N₂) n) :
    Σ' (n₁ n₂ : ℕ) (_ : n₁ + n₂ = n) (c₁ : Cell N₁ n₁) (c₂ : Cell N₂ n₂),
      c.val = Fin.append c₁.val c₂.val :=
  ⟨_, _, card_takeCell_add_dropCell c, takeCell N₂ c, dropCell N₁ c,
    (append_takeCell_dropCell c).symm⟩

/-- Split off a **single** coordinate at block position `p`; `n₂ ∈ {0,1}` is miss vs hit, and `n₁`
is the source position of the surviving direction. -/
def splitCellAt (p q : ℕ) {n : ℕ} (c : Cell (p + (1 + q)) n) :
    Σ' (n₁ n₂ n₃ : ℕ) (_ : n₁ + (n₂ + n₃) = n)
       (c₁ : Cell p n₁) (c₂ : Cell 1 n₂) (c₃ : Cell q n₃),
      c.val = Fin.append c₁.val (Fin.append c₂.val c₃.val) := by
  obtain ⟨n₁, n₂₃, h₁, c₁, r, hr⟩ := splitCell c
  obtain ⟨n₂, n₃, h₂, c₂, c₃, hc⟩ := splitCell r
  exact ⟨n₁, n₂, n₃, by omega, c₁, c₂, c₃, by rw [hr, hc]⟩

/-- `[ε, none^q]`: one fixed coordinate followed by `q` free ones. -/
def edgeCell (ε : Bool) (q : ℕ) : Cell (1 + q) q :=
  ⟨Fin.append (constVertex 1 ε).val (topCell q).val, by
    rw [card_noneSet_append, (constVertex 1 ε).prop, (topCell q).prop]; omega⟩

/-- The coface inserting a coordinate fixed at `ε` at block position `p`. -/
def spliceFace (ε : Bool) (p q : ℕ) : ▫(p + q) ⟶ ▫(p + (1 + q)) :=
  Box.ofSign (appendCell (topCell p) (edgeCell ε q))

end SplitCell

/-! ### Retracting a run onto a face

`runRetractFace face x` restricts the run `x` of `□ᵇ` along `face`.  No recursion and no
dimension induction: `face` names all its free coordinates at once, so we project once.

The projection `□ᵇ → □ⁿ` is **not** a precubical map — `Box` has no degeneracies, and restricting
a sign vector drops the dimension of any cell whose free coordinate `face` omits.  It becomes a
map after being pushed through a run, because a run meets each direction in exactly one edge: the
`n` surviving edges stay edges, the other `b - n` collapse to vertices, and nothing else can go
wrong since `runObj b` has cells only in dimensions `0` and `1`. -/

/-- `□^∨(1ⁿ)`, the all-edges chain shape. -/
abbrev runObj (n : ℕ) : BPSet := OneD.obj (Discrete.mk (Multiplicative.ofAdd n))

/-! #### Step 1: the projection, as a plain function -/

/-- Restrict a sign vector to the free coordinates of `face`: the projection of `□ᵇ` onto that
face.  Just a function — it does not preserve cell dimension. -/
def restrictCoord {n b : ℕ} (face : ▫n ⟶ ▫b) {k : ℕ} (c : Cell b k) : Fin n → Option Bool :=
  fun i => c.val (nones (Box.sign face) i)

/-- An edge restricts to an edge exactly when `face` uses its direction; otherwise it collapses.
This dichotomy is the whole obstruction to being a precubical map. -/
theorem card_restrictCoord_one {n b : ℕ} (face : ▫n ⟶ ▫b) (c : Cell b 1) :
    (noneSet (restrictCoord face c)).card
      = if (Box.sign face).val (nones c 0) = none then 1 else 0 := sorry

/-! #### Step 2: the universal property of `⋁(1ⁿ)`

`⋁(1ⁿ)` is the colimit of the zigzag that glues each edge's final vertex to the next edge's
initial one.  One glue step, and the cocone condition it imposes on a map to `K`:

```
            □⁰                          eᵢ ∘ final = eᵢ₊₁ ∘ init
      final ╱  ╲ init                        ‖
           ╱    ╲                            ‖  Yoneda: □¹ ⟶ K is a 1-cell,
        □¹ᵢ      □¹ᵢ₊₁                       ‖          □⁰ ⟶ K is a 0-cell
           ╲    ╱                            ‖
        eᵢ  ╲  ╱ eᵢ₊₁                        ↓
             ↘↙                       vertex₁ (eᵢ) = vertex₀ (eᵢ₊₁) = vᵢ₊₁
              K
```

So a hom out of `⋁(1ⁿ)` is exactly `n+1` vertices and `n` edges with matching faces — a **path**.
Both pieces are representable, so nothing functorial survives: no naturality, no cells above
dimension `1`.  In `BPSet` the two ends are pinned as well (`starts`, `ends`).

That is the escape hatch.  Build a hom by handing over a path, computed however you like, and
reason downstream through the equivalence instead of unfolding cells:

```
                        runHomEquiv b
    (runObj b ⟶ cube b)  ─────≃─────→  RunPath b (cube b)
                                              │
      runRetractFace face                     │ RunPath.restrict face
                                              ↓
    (runObj n ⟶ cube n)  ←────≃─────   RunPath n (cube n)
                    (runHomEquiv n).symm
```

`runRetractFace` is *defined* as the bottom route; the arbitrary computation lives in
`RunPath.restrict`, on plain data, and is paid for once.  Existence is `Glue.desc`, uniqueness is
`ChainCat.concat_hom_ext`. -/

/-- A path of `n` composable edges in `K`, from `init` to `final`. -/
structure RunPath (n : ℕ) (K : BPSet) where
  vert : Fin (n + 1) → K.cells 0
  edge : Fin n → K.cells 1
  src : ∀ i, PrecubicalSet.vertex₀ K.toPsh (edge i) = vert i.castSucc
  tgt : ∀ i, PrecubicalSet.vertex₁ K.toPsh (edge i) = vert i.succ
  starts : vert 0 = K.init
  ends : vert (Fin.last n) = K.final

/-- **The universal property.**  Homs out of the all-edges chain shape *are* paths. -/
def runHomEquiv (n : ℕ) (K : BPSet) : (runObj n ⟶ K) ≃ RunPath n K := sorry

/-! #### Step 3: the retraction

All of the awkwardness — which edges survive, in what order, how their sign vectors restrict —
happens inside `RunPath.restrict`, on plain data.  It is paid for once. -/

/-- Restrict a path of `□ᵇ` along `face`: keep the edges whose direction `face` uses (there are
exactly `n`, since a run meets each direction once) and restrict every cell's sign vector. -/
def RunPath.restrict {n b : ℕ} (face : ▫n ⟶ ▫b) (P : RunPath b (cube b)) :
    RunPath n (cube n) := sorry

/-- **The retraction.**  A path in, a path out. -/
def runRetractFace {n b : ℕ} (face : ▫n ⟶ ▫b) (x : runObj b ⟶ cube b) : runObj n ⟶ cube n :=
  (runHomEquiv n (cube n)).symm (RunPath.restrict face (runHomEquiv b (cube b) x))


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
