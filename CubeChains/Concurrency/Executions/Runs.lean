import CubeChains.Concurrency.Grading.Degree
import CubeChains.Precubical.Chains.ChainRestrictions
import CubeChains.Concurrency.Salvetti.ChainBraidFace
import CubeChains.Precubical.Segal.PshExtMonoidal
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Elements
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Concurrency/Executions/Runs — the category of runs

A **run** is a cube chain every bead of which is an edge: `Run K` is the full subcategory of
`Ch K` cut out by `IsRun`.  Two facts carry the whole layer.

* `Run K` is **discrete** (`Run.eq_of_hom`, `Run.functor_ext`).  `Ch K` is skeletal, and an
  all-edges chain's bead count *is* its `dimSum`, which every chain map preserves — so a map of
  runs has equal bead counts at both ends and collapses.  Hence a functor into `Run K` is
  determined by its action on objects, which is what makes the coherence below free.
* `IsRun` is closed under `chConcat` (`isRun_chConcat`).  That single fact is all it takes to
  restrict `chFunctor`'s lax monoidal structure (`Precubical/Segal/WedgeLaxMonoidal`)
  to `runFunctor`.
-/

open CategoryTheory MonoidalCategory Opposite ChainCat CubeChain BPSet

namespace CubeChains

/-- `⋁≡h` — lift an equality of shapes to the induced map of wedges.  *Notation*, so the term is
still `eqToHom (congrArg …)` and `eqToHom` simp lemmas fire through it. -/
notation:max "⋁≡" h:max => eqToHom (congrArg BPSet.serialWedge h)

/-! ### The category of runs -/

/-- A chain is a **run** when every one of its beads is an edge. -/
def IsRun (K : BPSet) : ObjectProperty (Ch K) := fun a => ∀ d ∈ a.dims, d = 1

/-- **The runs are the degree-`0` chains** — they are the bottom of the grading on `Ch K`. -/
theorem isRun_iff_degree_eq_zero {K : BPSet} (a : Ch K) :
    IsRun K a ↔ ChainCat.degree a = 0 :=
  (ChainCat.degree_eq_zero_iff a).symm

/-- `Run K` — the all-edges chains of `K`, full in `Ch K`. -/
abbrev Run (K : BPSet) := (IsRun K).FullSubcategory

/-- The chain underlying a run. -/
abbrev Run.chain {K : BPSet} (r : Run K) : Ch K := r.obj

/-- A run's dimension sequence — all ones, by `Run.ones`. -/
abbrev Run.dims {K : BPSet} (r : Run K) : List ℕ+ := r.chain.dims

/-- A run's classifying map. -/
abbrev Run.map {K : BPSet} (r : Run K) : ⋁r.dims ⟶ K := r.chain.map

theorem Run.ones {K : BPSet} (r : Run K) : ∀ d ∈ r.dims, d = 1 := r.property

theorem Run.ext {K : BPSet} {r s : Run K} (h : r.chain = s.chain) : r = s :=
  ObjectProperty.FullSubcategory.ext h

/-- **`Run K` is discrete.**  `serialWedge_dimSum_eq` pins the two bead counts against each other
(`dimSum_eq_length_of_ones`), and `Ch K` is skeletal at equal bead counts. -/
theorem Run.eq_of_hom {K : BPSet} {r s : Run K} (f : r ⟶ s) : r = s := by
  refine Run.ext (ChainCat.eq_of_hom_of_dims_length_eq f.hom ?_)
  rw [← dimSum_eq_length_of_ones r.ones, ← dimSum_eq_length_of_ones s.ones]
  exact serialWedge_dimSum_eq f.hom.φ

instance {K : BPSet} : Quiver.IsThin (Run K) := fun r s => by
  constructor
  intro f g
  obtain rfl : r = s := Run.eq_of_hom f
  exact ObjectProperty.hom_ext _ ((endo_eq_id f.hom).trans (endo_eq_id g.hom).symm)

/-- **Functors into `Run K` are determined on objects** — the discreteness, in the form every
coherence proof below uses. -/
theorem Run.functor_ext {D : Type*} [Category D] {K : BPSet} {F G : D ⥤ Run K}
    (h : ∀ d, F.obj d = G.obj d) : F = G :=
  CategoryTheory.Functor.ext h (fun _ _ _ => Subsingleton.elim _ _)

/-- **Two functors into `Run K` agree as soon as they agree after `ι`.**  This is what a
faithful-inclusion argument would give in mathlib's `Monoidal.induced`; here discreteness makes it
cheaper still — only the object components have to match. -/
theorem Run.functor_ext_of_ι {D : Type*} [Category D] {K : BPSet} {F G : D ⥤ Run K}
    (h : F ⋙ (IsRun K).ι = G ⋙ (IsRun K).ι) : F = G :=
  Run.functor_ext fun d => Run.ext (CategoryTheory.Functor.congr_obj h d)

/-! ### A run of `□n` *is* a permutation of its axes

`flatten` is the **firing order**, axis ↦ step; its inverse sends a word to the all-edges chain
whose beads are the singleton blocks of that order (`blockChain`).  Everything about runs of a cube
below — restriction along a face, reversal — is stated on this bijection. -/

/-- **The run of `□n` performing the axes in the order `w`** — one singleton bead per step. -/
def wordRun {n : ℕ} (w : Equiv.Perm (Fin n)) : Run (□n) :=
  ⟨blockChain ⇑w.symm w.symm.surjective,
    ones_of_dimSum_eq_length
      ((wedgeDimSum_eq (blockChain ⇑w.symm w.symm.surjective).map).trans
        (length_blockChain ⇑w.symm w.symm.surjective).symm)⟩

@[simp] theorem chain_wordRun {n : ℕ} (w : Equiv.Perm (Fin n)) :
    (wordRun w).chain = blockChain ⇑w.symm w.symm.surjective := rfl

@[simp] theorem flatten_wordRun {n : ℕ} (w : Equiv.Perm (Fin n)) :
    flatten (wordRun w).chain = w⁻¹ :=
  Equiv.ext fun q =>
    Fin.ext ((flatten_eq_beadOf_of_ones (wordRun w).ones q).trans
      (beadOf_blockChain ⇑w.symm w.symm.surjective q))

/-- A run is the run of its own word — `eq_of_beadOf`, since a run's `flatten` *is* `beadOf`. -/
theorem wordRun_flatten {n : ℕ} (r : Run (□n)) : wordRun (flatten r.chain)⁻¹ = r :=
  Run.ext (eq_of_beadOf fun q =>
    (beadOf_blockChain _ (flatten r.chain).surjective q).trans (flatten_eq_beadOf_of_ones r.ones q))

/-- **A run of `□n` is a linear order on its `n` axes.**  `toFun` is `flatten` on the nose. -/
def runPermEquiv (n : ℕ) : Run (□n) ≃ Equiv.Perm (Fin n) where
  toFun := fun r => flatten r.chain
  invFun := fun σ => wordRun σ⁻¹
  left_inv := wordRun_flatten
  right_inv σ := (flatten_wordRun σ⁻¹).trans (inv_inv σ)

@[simp] theorem runPermEquiv_apply {n : ℕ} (r : Run (□n)) :
    runPermEquiv n r = flatten r.chain := rfl

@[simp] theorem runPermEquiv_symm_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (runPermEquiv n).symm σ = wordRun σ⁻¹ := rfl

/-- **A run of `□n` is the word it spells** — the same bijection read step-to-axis, i.e.
`runPermEquiv` inverted.  Spelled directly rather than as `.trans (Equiv.inv _)` so that both
`runWordEquiv_apply` and `runWordEquiv_symm_apply` are `rfl` with no double inversion for `whnf`
to chew through.  Every "run word" in the tree (of an execution, of a tope) is this at some run. -/
def runWordEquiv (n : ℕ) : Run (□n) ≃ Equiv.Perm (Fin n) where
  toFun r := (flatten r.chain)⁻¹
  invFun := wordRun
  left_inv := wordRun_flatten
  right_inv w := (congrArg Inv.inv (flatten_wordRun w)).trans (inv_inv w)

@[simp] theorem runWordEquiv_apply {n : ℕ} (r : Run (□n)) :
    runWordEquiv n r = (flatten r.chain)⁻¹ := rfl

@[simp] theorem runWordEquiv_symm_apply {n : ℕ} (w : Equiv.Perm (Fin n)) :
    (runWordEquiv n).symm w = wordRun w := rfl

@[simp] theorem runWordEquiv_wordRun {n : ℕ} (w : Equiv.Perm (Fin n)) :
    runWordEquiv n (wordRun w) = w := (runWordEquiv n).apply_symm_apply w

/-- **The all-edges chain performing the axes in the order `w`.** -/
def wordChain {n : ℕ} (w : Equiv.Perm (Fin n)) : Ch (□n) := (wordRun w).chain

theorem beadOf_wordChain {n : ℕ} (w : Equiv.Perm (Fin n)) (q : Fin n) :
    (beadOf (wordChain w) q : ℕ) = (w.symm q : ℕ) := beadOf_blockChain _ _ q

theorem length_wordChain {n : ℕ} (w : Equiv.Perm (Fin n)) : (wordChain w).dims.length = n :=
  length_blockChain _ _

theorem ones_wordChain {n : ℕ} (w : Equiv.Perm (Fin n)) : ∀ d ∈ (wordChain w).dims, d = 1 :=
  (wordRun w).ones

/-- **A run's chain is the word chain of its word.** -/
theorem Run.chain_eq_wordChain {n : ℕ} (r : Run (□n)) : r.chain = wordChain (runWordEquiv n r) :=
  congrArg Run.chain ((runWordEquiv n).symm_apply_apply r).symm

/-- **A run is pinned by the chain it linearizes**, so the word it spells is too. -/
theorem runWordEquiv_eq_of_chain {n : ℕ} {r : Run (□n)} {w : Equiv.Perm (Fin n)}
    (h : r.chain = wordChain w) : runWordEquiv n r = w :=
  (congrArg (runWordEquiv n) (Run.ext h)).trans ((runWordEquiv n).apply_symm_apply w)

/-! ### `Run` is a subfunctor of `Ch` -/

/-- Post-composition preserves runs: it does not touch the dimension sequence. -/
def Run.pushforward {K L : BPSet} (f : K ⟶ L) : Run K ⥤ Run L :=
  (IsRun L).lift ((IsRun K).ι ⋙ ChainCat.pushforward f) (fun r => r.ones)

theorem Run.pushforward_id (K : BPSet) : Run.pushforward (𝟙 K) = 𝟭 (Run K) := rfl

theorem Run.pushforward_comp {K L M : BPSet} (f : K ⟶ L) (g : L ⟶ M) :
    Run.pushforward (f ≫ g) = Run.pushforward f ⋙ Run.pushforward g := rfl

/-- The run functor `BPSet ⥤ Cat`: `K ↦ Run K`, `f ↦` post-composition. -/
def runFunctor : BPSet ⥤ Cat where
  obj K := Cat.of (Run K)
  map f := (Run.pushforward f).toCatHom
  map_id K := Cat.ext (Run.pushforward_id K)
  map_comp f g := Cat.ext (Run.pushforward_comp f g)

/-! ### The monoidal structure

`runFunctor` is lax monoidal `(BPSet, ∨) ⥤ (Cat, ×)` by restriction, not by a parallel proof.
Mathlib's `ObjectProperty.IsMonoidal` does not apply — it wants the *ambient* category monoidal,
whereas here the tensor changes the base (`Ch X × Ch Y ⥤ Ch (X ∨ Y)`), so what carries the
structure is the functor `chFunctor`, not `Ch K`.

What replaces it: `runConcat ⋙ ι = (ι × ι) ⋙ chConcat` and `Run.pushforward f ⋙ ι =
ι ⋙ pushforward f` both hold by `rfl`, so each coherence square, composed with `ι`, *is*
`chFunctor`'s own square whiskered by a product of `ι`s — and `Run.functor_ext_of_ι` says that
is enough.  Discreteness is what makes that last step cheap. -/

/-- **`IsRun` is closed under concatenation** — the dimension sequences append.  This is the only
content in the instance below. -/
theorem isRun_chConcat {X Y : BPSet} (a : Run X) (b : Run Y) :
    IsRun (wedge2 X Y) ((chConcat X Y).obj (a.chain, b.chain)) := fun d hd =>
  (List.mem_append.mp hd).elim (a.ones d) (b.ones d)

/-- `chConcat`, restricted to runs. -/
def runConcat (X Y : BPSet) : Run X × Run Y ⥤ Run (wedge2 X Y) :=
  (IsRun (wedge2 X Y)).lift (((IsRun X).ι.prod (IsRun Y).ι) ⋙ chConcat X Y)
    (fun ab => isRun_chConcat ab.1 ab.2)

/-- The empty chain of `□⁰` is a run, vacuously — the monoidal unit.  Spelled at `𝟙_ BPSet`, the
form the coherence laws meet; `Run (□0)` is the same type but not at instance transparency. -/
def runUnit : Run (𝟙_ BPSet) :=
  ⟨(default : Ch (□0)), show ∀ d ∈ ([] : List ℕ+), d = 1 by simp⟩

instance : Inhabited (Run (□0)) := ⟨runUnit⟩

/-- **Runs concatenate**, with all three coherence laws — each field is `chFunctor`'s own,
whiskered by `ι`. -/
instance : runFunctor.LaxMonoidal where
  ε := (Cat.fromChosenTerminalEquiv.symm runUnit).toCatHom
  μ X Y := (runConcat X Y).toCatHom
  μ_natural_left f X' := by
    refine Cat.ext (Run.functor_ext_of_ι ?_)
    exact congrArg (fun H => ((IsRun _).ι.prod (IsRun _).ι) ⋙ H)
      (congrArg Cat.Hom.toFunctor (chConcat_μ_natural_left f X'))
  μ_natural_right X' f := by
    refine Cat.ext (Run.functor_ext_of_ι ?_)
    exact congrArg (fun H => ((IsRun _).ι.prod (IsRun _).ι) ⋙ H)
      (congrArg Cat.Hom.toFunctor (chConcat_μ_natural_right X' f))
  associativity X Y Z := by
    refine Cat.ext (Run.functor_ext_of_ι ?_)
    exact congrArg (fun H => (((IsRun X).ι.prod (IsRun Y).ι).prod (IsRun Z).ι) ⋙ H)
      (congrArg Cat.Hom.toFunctor (chConcat_associativity X Y Z))
  -- the unit fields carry `ε`, whose two spellings (`runUnit` vs `default : Ch (□0)`) the
  -- unifier will not reconcile inside `λ_`/`ρ_`'s implicit arguments — so read the `Ch` law at a
  -- point instead of whiskering it.
  left_unitality X := by
    refine Cat.ext (Run.functor_ext fun tx => Run.ext ?_)
    exact CategoryTheory.Functor.congr_obj
      (congrArg Cat.Hom.toFunctor (chConcat_left_unitality X)) (tx.1, tx.2.chain)
  right_unitality X := by
    refine Cat.ext (Run.functor_ext fun xt => Run.ext ?_)
    exact CategoryTheory.Functor.congr_obj
      (congrArg Cat.Hom.toFunctor (chConcat_right_unitality X)) (xt.1.chain, xt.2)

/-! ### Segal: a run of a wedge is a pair of runs

`splitObj` is a two-sided inverse to `chConcat` (`Precubical/Segal/Split`), and both halves of a
split run are again all edges because their dimension sequences concatenate to the whole's. 
Restricting that inverse pair to runs costs nothing — no transports, since a run carries its own
dims. -/

/-- The altitude witness for `⋁(c :: rest) = □c ∨ ⋁rest`, spelled once. -/
def consAltitude (c : ℕ+) (rest : List ℕ+) : (wedge2 (□(c : ℕ)) (⋁rest)).AdmitsAltitude :=
  wedge2_admitsAltitude (cube_admitsAltitude (c : ℕ)) (serialWedge_admitsAltitude rest)

/-- **Both halves of a split run are runs** — their dims concatenate to the whole's. -/
theorem isRun_splitObj {X Y : BPSet} (h : (wedge2 X Y).AdmitsAltitude) (r : Run (wedge2 X Y)) :
    IsRun X (splitObj h r.chain).1 ∧ IsRun Y (splitObj h r.chain).2 := by
  have hd : (splitObj h r.chain).1.dims ++ (splitObj h r.chain).2.dims = r.dims :=
    congrArg ChainCat.Obj.dims (chConcat_obj_splitObj h r.chain)
  exact ⟨fun d hd' => r.ones d (hd ▸ List.mem_append_left _ hd'),
    fun d hd' => r.ones d (hd ▸ List.mem_append_right _ hd')⟩

/-- `splitObj`, restricted to runs. -/
def runSplit {X Y : BPSet} (h : (wedge2 X Y).AdmitsAltitude) (r : Run (wedge2 X Y)) :
    Run X × Run Y :=
  (⟨(splitObj h r.chain).1, (isRun_splitObj h r).1⟩,
   ⟨(splitObj h r.chain).2, (isRun_splitObj h r).2⟩)

@[simp] theorem runConcat_runSplit {X Y : BPSet} (h : (wedge2 X Y).AdmitsAltitude)
    (r : Run (wedge2 X Y)) : (runConcat X Y).obj (runSplit h r) = r :=
  Run.ext (chConcat_obj_splitObj h r.chain)

@[simp] theorem runSplit_runConcat {X Y : BPSet} (h : (wedge2 X Y).AdmitsAltitude)
    (a : Run X) (b : Run Y) : runSplit h ((runConcat X Y).obj (a, b)) = (a, b) := by
  have hs := splitObj_chConcat_obj h a.chain b.chain
  exact congrArg₂ Prod.mk (Run.ext (congrArg Prod.fst hs)) (Run.ext (congrArg Prod.snd hs))

/-- **Segal for runs.**  A run of `X ∨ Y` *is* a run of `X` together with a run of `Y`. -/
def runSplitEquiv {X Y : BPSet} (h : (wedge2 X Y).AdmitsAltitude) :
    Run (wedge2 X Y) ≃ Run X × Run Y where
  toFun := runSplit h
  invFun ab := (runConcat X Y).obj ab
  left_inv := runConcat_runSplit h
  right_inv ab := by rw [runSplit_runConcat]

/- **Seal `runSplit`.**  `splitObj` is *computable* — it sorts a cube list with `xCubes` — so a
unifier meeting `runSplit h x` will try to evaluate it, and on a symbolic chain that runs away
(`xCubes` alone burns the entire heartbeat budget).  Nothing below needs `runSplit` to reduce: the
two round trips above characterise it completely. -/
attribute [irreducible] runSplit

/-! ### Runs are the all-edges cube chains

`chCubes` (`Precubical/Chains/Category`) is the correspondence between a chain and its cube list;
cut down to all-edges chains it is `Run.equivEdgeChain`.  That is the route a *geometric* statement
about a run — reversal above all — travels to reach `Run K`. -/

/-- The dimension sequence and the cube list say the same thing about being all edges. -/
theorem CubeChain.ones_iff {K : BPSet} (C : CubeChain K) :
    (∀ d ∈ C.dims, d = 1) ↔ ∀ c ∈ C.cubes, (c.1 : ℕ) = 1 := by
  simp only [CubeChain.dims, List.mem_map]
  constructor
  · rintro h c hc
    exact congrArg PNat.val (h c.1 ⟨c, hc, rfl⟩)
  · rintro h d ⟨c, hc, rfl⟩
    exact PNat.coe_injective (h c hc)

/-- **Runs are exactly the all-edges cube chains.**  Both directions are the identity on the
dimension sequence — a run carries its own, so no transport appears. -/
def Run.equivEdgeChain (K : BPSet) : Run K ≃ EdgeChain K where
  toFun r := ⟨chCubes K r.chain,
    (CubeChain.ones_iff _).mp (by rw [chCubes_dims]; exact r.ones)⟩
  invFun e := ⟨(chCubes K).symm e.1, (CubeChain.ones_iff e.1).mpr e.2⟩
  left_inv r := Run.ext ((chCubes K).left_inv r.chain)
  right_inv e := Subtype.ext ((chCubes K).right_inv e.1)

/-- The cube list of a run is the flat view of the beads its chain reads off.  Stated before the
seal below, since it is the only thing anyone needs from the transport's innards. -/
theorem cubes_equivEdgeChain {K : BPSet} (r : Run K) :
    (Run.equivEdgeChain K r).1.cubes = (beadCell r.map.hom).toList := rfl

/-- …and its dimension sequence is the run's own — the other half of what the seal lets through. -/
@[simp] theorem dims_equivEdgeChain {K : BPSet} (r : Run K) :
    (Run.equivEdgeChain K r).1.dims = r.dims :=
  (congrArg (List.map (fun c : Σ n : ℕ+, K.cells (n : ℕ) => c.1))
    (cubes_equivEdgeChain r)).trans (Beads.map_fst_toList _)

/- **Seal the run↔cube-list transport.**  Same hazard as `runSplit`: it is computable (`beadCell`
walks the blocks, `wedgeDescHom` rebuilds the glued map), so a unifier that meets it evaluates it
and runs away.  `cubes_equivEdgeChain`, `dims_equivEdgeChain` and the two round trips are all
anything above it needs. -/
attribute [irreducible] Run.equivEdgeChain

/-! ### Runs of a cube, as a presheaf on `Box`

Restricting a run along a face keeps the axes the face uses, in the order the run gives them — so
the restricted run performs axis `i` at the **rank** of `runPermEquiv r (faceEmb g i)`, and that
rank map is `(Tuple.sort …)⁻¹`.  Both functor laws come from sorting: the identity from
`Tuple.sort_perm`, composition from `Tuple.sort_congr`, which says sorting sees only a tuple's
order type and so lets a rank map stand in for the tuple it ranks.  No cube list is projected and
no cell is dropped: a run of `□n` *is* an order on its axes. -/

/-- The axes a face uses, ordered by the run — injective, being a permutation after an
embedding. -/
theorem injective_faceOrder {k m : ℕ} (g : ▫k ⟶ ▫m) (r : Run (□m)) :
    Function.Injective fun i => runPermEquiv m r (faceEmb g i) :=
  (runPermEquiv m r).injective.comp (faceEmb g).injective

/-- **Restriction of a run along a `Box` face** — the order the run induces on the face's axes. -/
def runFace {k m : ℕ} (g : ▫k ⟶ ▫m) (r : Run (□m)) : Run (□k) :=
  (runPermEquiv k).symm (Tuple.sort fun i => runPermEquiv m r (faceEmb g i))⁻¹

@[simp] theorem runPermEquiv_runFace {k m : ℕ} (g : ▫k ⟶ ▫m) (r : Run (□m)) :
    runPermEquiv k (runFace g r) = (Tuple.sort fun i => runPermEquiv m r (faceEmb g i))⁻¹ :=
  (runPermEquiv k).apply_symm_apply _

theorem runFace_id {m : ℕ} (r : Run (□m)) : runFace (𝟙 ▫m) r = r := by
  rw [runFace, show (fun i => runPermEquiv m r (faceEmb (𝟙 ▫m) i)) = ⇑(runPermEquiv m r) from
      funext fun i => congrArg _ (faceEmb_id m i),
    Tuple.sort_perm, inv_inv, Equiv.symm_apply_apply]

theorem runFace_comp {j k m : ℕ} (f : ▫j ⟶ ▫k) (g : ▫k ⟶ ▫m) (r : Run (□m)) :
    runFace (f ≫ g) r = runFace f (runFace g r) := by
  refine (runPermEquiv j).injective ?_
  rw [runPermEquiv_runFace, runPermEquiv_runFace, runPermEquiv_runFace,
    show (fun i => runPermEquiv m r (faceEmb (f ≫ g) i))
        = fun i => runPermEquiv m r (faceEmb g (faceEmb f i)) from
      funext fun i => congrArg _ (faceEmb_comp f g i)]
  exact congrArg Inv.inv (Tuple.sort_congr
    (((runPermEquiv m r).injective.comp (faceEmb g).injective).comp (faceEmb f).injective)
    fun x y => (Tuple.sort_inv_lt_iff (injective_faceOrder g r) _ _).symm)

/-- **Runs of a cube form a presheaf on `Box`.** -/
def runPresheaf : Boxᵒᵖ ⥤ Type where
  obj X := Run (□X.unop.dim)
  map f := ↾fun r => runFace f.unop r
  map_id _ := by apply ConcreteCategory.hom_ext; intro r; exact runFace_id r
  map_comp f g := by apply ConcreteCategory.hom_ext; intro r; exact runFace_comp g.unop f.unop r

@[simp] theorem runPresheaf_map_apply {X Y : Boxᵒᵖ} (f : X ⟶ Y) (r : Run (□X.unop.dim)) :
    runPresheaf.map f r = runFace f.unop r := rfl

/-- **Restriction along a face preserves the firing order**: the restricted run's order is the rank
map of the original's, and a rank map compares exactly as the tuple it ranks. -/
theorem flatten_restrict_lt_iff {k m : ℕ} (g : ▫k ⟶ ▫m) (r : Run (□m)) (i j : Fin k) :
    flatten (runPresheaf.map g.op r).chain i < flatten (runPresheaf.map g.op r).chain j
      ↔ flatten r.chain (faceEmb g i) < flatten r.chain (faceEmb g j) := by
  change runPermEquiv k (runFace g r) i < runPermEquiv k (runFace g r) j ↔ _
  rw [runPermEquiv_runFace]
  exact Tuple.sort_inv_lt_iff (injective_faceOrder g r) i j

/-! ### `runPresheaf` classifies runs of a cube
`runPresheaf` is a presheaf on `Box` — that is, a *precubical set* — so by Yoneda a run of `□b` is
the same data as a map of precubical sets `(□b).toPsh ⟶ runPresheaf`.  Under that transpose,
restriction along a face is **precomposition**.  Everything the wedge recursion needs about faces
follows from that one line. -/

theorem run_cube0_eq (r s : Run (□0)) : r = s := Run.ext (obj_cube0_eq r.chain s.chain)

/-- `runBp` — the run presheaf as a bi-pointed set; its single vertex forces the pointing. -/
def runBp : BPSet where
  toPsh := runPresheaf
  init := (default : Run (□0))
  final := (default : Run (□0))

@[simp] theorem runBp_toPsh : runBp.toPsh = runPresheaf := rfl

instance : Subsingleton (runBp.cells 0) := ⟨run_cube0_eq⟩

/-- …hence maps `□⁰ ⟶ runPresheaf` are unique.  Both `yonedaEquiv` applications are written out:
left as metavariables, unifying `runPresheaf.obj ⟨▫0⟩` with `Run (□0)` sends `isDefEq` hunting
through the whole of `runPresheaf`. -/
theorem runPresheaf_point_ext (f g : (□0).toPsh ⟶ runPresheaf) : f = g := by
  apply yonedaEquiv.injective
  apply run_cube0_eq

/-- A run of a cube is a map into `runPresheaf` — cube Yoneda.  Crossing the definitional
`runPresheaf.obj ⟨▫n⟩ = Run (□n)` once, here, keeps it out of every downstream unification. -/
def cubeRunEquiv (n : ℕ) : Run (□n) ≃ ((□n).toPsh ⟶ runPresheaf) :=
  (yonedaEquiv (X := ▫n) (F := runPresheaf)).symm

/-- **Segal, iterated**: a run of `⋁a` is one run per bead. -/
def runSegalProd : (a : List ℕ+) → Run (⋁a) ≃ pshExtProdType runPresheaf a
  | [] =>
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => (default : Run (□0))
        left_inv := fun _ => run_cube0_eq _ _
        right_inv := fun _ => rfl }
  | c :: rest =>
      (runSplitEquiv (consAltitude c rest)).trans
        ((cubeRunEquiv (c : ℕ)).prodCongr (runSegalProd rest))

/-- **`runPresheaf` classifies runs of a serial wedge** — the contravariant lift's monoidality
(`pshExtProd`, `Precubical/Segal/WedgeExtend`) followed by iterated Segal splitting. -/
def runPshEquiv (a : List ℕ+) : ((⋁a).toPsh ⟶ runPresheaf) ≃ Run (⋁a) :=
  (pshExtProd runPresheaf (cubeRunEquiv 0 default) runPresheaf_point_ext a).trans
    (runSegalProd a).symm

/-- The left leg of a run's classifier at a cons.  Stated rather than rewritten to:
`wedge2Desc_inl`'s pattern sits behind `≫`'s object slot, spelled `⋁(c :: rest)` here and
`□c ∨ ⋁rest` there. -/
theorem runPshEquiv_symm_inl (c : ℕ+) (rest : List ℕ+) (r : Run (⋁(c :: rest))) :
    wedgeInl (□(c : ℕ)) (⋁rest) ≫ (runPshEquiv (c :: rest)).symm r
      = yonedaEquiv.symm (runSplit (consAltitude c rest) r).1 :=
  wedge2Desc_inl _ _ _

/-! ### The general restriction

With runs classified, restricting along *any* wedge map is transpose–precompose–assemble, and the
two functor laws are associativity of `≫` plus a round trip.  No recursion on the target, no
splitting of the wedge map, no transports. -/

/-- **Restriction of a run along a wedge map.** -/
def runRestrict {a b : List ℕ+} (f : ⋁a ⟶ ⋁b) (r : Run (⋁b)) : Run (⋁a) :=
  runPshEquiv a (f.hom ≫ (runPshEquiv b).symm r)

@[simp] theorem runRestrict_id {a : List ℕ+} (r : Run (⋁a)) : runRestrict (𝟙 (⋁a)) r = r := by
  rw [runRestrict, id_hom, Category.id_comp, Equiv.apply_symm_apply]

/-! ### Per-bead local runs

A run of `⋁a` is one local run per bead (`runSegalProd`); `runProj r i` extracts bead `i`'s, as the
run classified by `ιᵂ a i ≫ (runPshEquiv a).symm r`.  Restriction commutes with projection through
the block
factorization — the `.2`-side localization diagram (`runProj_runRestrict`), the single fact carrying
the run order across a refinement. -/

/-- **Bead `i`'s local run** of a run of `⋁a` — its classifying map read at bead `i`. -/
def runProj {a : List ℕ+} (r : Run (⋁a)) (i : Fin a.length) :
    Run (□(a.get i : ℕ)) :=
  beadCell ((runPshEquiv a).symm r) i

/-- **The `.2`-side localization diagram.**  Bead `iβ` of a restricted run is bead
`blockIdx φ iβ` of the original, restricted along the block face `blockFace φ iβ` — the bead
of a composite (`beadCell_comp_block`), no `run.map` coend. -/
theorem runProj_runRestrict {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (r : Run (⋁b)) (iβ : Fin a.length) :
    runProj (runRestrict φ r) iβ
      = runPresheaf.map (blockFace φ.hom iβ).op (runProj r (blockIdx φ.hom iβ)) := by
  rw [runProj, show (runPshEquiv a).symm (runRestrict φ r) = φ.hom ≫ (runPshEquiv b).symm r from by
    rw [runRestrict, Equiv.symm_apply_apply]]
  exact beadCell_comp_block φ.hom ((runPshEquiv b).symm r) iβ

/-- The wedge underlying a chain, functorially: `a ↦ ⋁a.dims`, `f ↦ f.φ`. -/
def linesWedge (K : BPSet) : Ch K ⥤ BPSet where
  obj a := ⋁a.dims
  map f := f.φ
  map_id a := ChainCat.id_φ a
  map_comp f g := ChainCat.comp_φ f g

/-- **The run presheaf.**  `Lines K a = (⋁a.dims).toPsh ⟶ runPresheaf`, the maps refining `a` — the
literal contravariant lift `pshExtFunctor runPresheaf` along `linesWedge`; functoriality is free. -/
def Lines (K : BPSet) : (Ch K)ᵒᵖ ⥤ Type := (linesWedge K).op ⋙ pshExtFunctor runPresheaf

/-! ### Complexified chains -/

/-- `Ch⋆ K` — a chain of `K` together with a run refining it.  The Salvetti construction read on
chains: a face paired with a chamber above it. -/
abbrev ChStar (K : BPSet) : Type := (Lines K).Elements

@[inherit_doc] notation:max "Ch⋆ " K:max => CubeChains.ChStar K

/-- The chain a complexified chain sits over. -/
abbrev ChStar.chain {K : BPSet} (x : Ch⋆ K) : Ch K := x.1.unop

/-! ## The `K`-free domain of a run: `RunWedge`

`ChStar K` bundles a wedge with a map to `K` (the chain) *and* a map to `runPresheaf` (the run);
the run alone is `RunWedge` — a serial wedge with a classifying map to `runPresheaf`, i.e. an object
of the slice `BPSet ↓ runPresheaf` on wedge domains.  `proj K : Ch⋆ K ⥤ RunWedge` forgets the map
to `K`; the braid a refinement performs (`Concurrency/Salvetti/EventBraid`) reads only this. -/

/-- A serial wedge together with a run refining it, carried by its classifying map to `runPresheaf`
(as `ChStar` carries its `.2`). -/
structure RunWedge where
  /-- The bead-dimension sequence of the wedge. -/
  dims : List ℕ+
  /-- The run refining `⋁dims`, as a map to `runPresheaf`. -/
  cls : (⋁dims).toPsh ⟶ runPresheaf

namespace RunWedge

/-- The run refining `⋁dims`, recovered from the classifying map. -/
def run (X : RunWedge) : Run (⋁X.dims) := runPshEquiv X.dims X.cls

/-- A morphism is a wedge map intertwining the classifiers — the `K`-free part of a refinement.
Contravariant on wedges: a refinement `x ⟶ y` runs `⋁y ⟶ ⋁x`. -/
instance : Category RunWedge where
  Hom X Y := {φ : ⋁Y.dims ⟶ ⋁X.dims // φ.hom ≫ X.cls = Y.cls}
  id X := ⟨𝟙 (⋁X.dims), by rw [id_hom, Category.id_comp]⟩
  comp {X Y Z} f g := ⟨g.1 ≫ f.1, by rw [comp_hom, Category.assoc, f.2, g.2]⟩
  id_comp f := Subtype.ext (Category.comp_id f.1)
  comp_id f := Subtype.ext (Category.id_comp f.1)
  assoc f g h := Subtype.ext (Category.assoc h.1 g.1 f.1).symm

/-- The wedge map underlying a morphism. -/
abbrev wedgeMap {X Y : RunWedge} (f : X ⟶ Y) : ⋁Y.dims ⟶ ⋁X.dims := f.1

/-! `wedgeMap` *is* the category structure, so its two contravariant functoriality laws are `rfl`.
They are what carries a statement about wedge maps — `coordMapEquiv`'s functoriality above all —
onto refinements, where the composite is spelled `f ≫ g` rather than `wedgeMap g ≫ wedgeMap f`. -/

theorem wedgeMap_id (X : RunWedge) : wedgeMap (𝟙 X) = 𝟙 (⋁X.dims) := rfl

theorem wedgeMap_comp {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    wedgeMap (f ≫ g) = wedgeMap g ≫ wedgeMap f := rfl

/-- The stored classifier is the transpose of the run. -/
theorem symm_run (X : RunWedge) : (runPshEquiv X.dims).symm X.run = X.cls :=
  (runPshEquiv X.dims).symm_apply_apply X.cls

/-- **Run-compatibility, `runRestrict` form** — a morphism's wedge map carries `X`'s run to
`Y`'s. -/
theorem run_restrict {X Y : RunWedge} (f : X ⟶ Y) : runRestrict (wedgeMap f) X.run = Y.run := by
  rw [runRestrict, symm_run, f.2]; rfl

/-- **The cube reduction.**  Bead `iβ`'s local run of `Y` is bead `blockIdx (wedgeMap f) iβ` of `X`,
restricted along the `Box` face `blockFace (wedgeMap f) iβ`. -/
theorem runProj_restrict {X Y : RunWedge} (f : X ⟶ Y) (iβ : Fin Y.dims.length) :
    runProj Y.run iβ = runPresheaf.map (blockFace (wedgeMap f).hom iβ).op
      (runProj X.run (blockIdx (wedgeMap f).hom iβ)) := by
  rw [← run_restrict f]
  exact runProj_runRestrict (wedgeMap f) X.run iβ

end RunWedge

/-- **The projection `Ch⋆ K ⥤ RunWedge`** — forget the map to `K`, keep the wedge and its run.  On
the nose it keeps the run classifier `x.2`, so the morphism condition is the `Elements`
compatibility `f.2`.  All of `K` is discarded here; it survives only as the image. -/
def proj (K : BPSet) : Ch⋆ K ⥤ RunWedge where
  obj x := ⟨x.chain.dims, x.2⟩
  map f := ⟨f.1.unop.φ, f.2⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

@[simp] theorem proj_obj_dims {K : BPSet} (x : Ch⋆ K) : ((proj K).obj x).dims = x.chain.dims := rfl

/-- The run a complexified chain carries — its `RunWedge`'s, so there is one reading, not two. -/
abbrev ChStar.run {K : BPSet} (x : Ch⋆ K) : Run (⋁x.chain.dims) := ((proj K).obj x).run

end CubeChains
