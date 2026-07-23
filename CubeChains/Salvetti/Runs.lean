import CubeChains.Chains.WedgeLaxMonoidal
import CubeChains.Chains.ChainSkeletal
import CubeChains.Chains.ChainRestrictions
import CubeChains.Chains.Correspondence
import CubeChains.Chains.WedgeExtend
import CubeChains.Chains.PshExtMonoidal
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Elements

/-!
# Salvetti/Runs — the category of runs

A **run** is a cube chain every bead of which is an edge: `Run K` is the full subcategory of
`Ch K` cut out by `IsRun`.  Two facts carry the whole layer.

* `Run K` is **discrete** (`Run.eq_of_hom`, `Run.functor_ext`).  `Ch K` is skeletal, and an
  all-edges chain's bead count *is* its `dimSum`, which every chain map preserves — so a map of
  runs has equal bead counts at both ends and collapses.  Hence a functor into `Run K` is
  determined by its action on objects, which is what makes the coherence below free.
* `IsRun` is closed under `chConcat` (`isRun_chConcat`).  That single fact is all it takes to
  restrict `chFunctor`'s lax monoidal structure (`Chains/WedgeLaxMonoidal`) to `runFunctor`.
-/

open CategoryTheory MonoidalCategory Opposite ChainCat CubeChain BPSet

namespace CubeChains

/-- `𝟙^n` — the all-edges shape of length `n`.  *Notation*, not a definition, so the elaborated
term is still `List.replicate n 1` and mathlib's `List.replicate` lemmas keep firing. -/
notation:max "𝟙^" n:max => List.replicate n (1 : ℕ+)

/-- `⋁≡h` — lift an equality of shapes to the induced map of wedges.  *Notation*, so the term is
still `eqToHom (congrArg …)` and `eqToHom` simp lemmas fire through it. -/
notation:max "⋁≡" h:max => eqToHom (congrArg BPSet.serialWedge h)

/-! ### All-edges shapes -/

/-- `dimSum` of an all-edges shape is its length. -/
@[simp] theorem dimSum_replicate (n : ℕ) : dimSum (𝟙^n) = n := by
  simp [dimSum, List.map_replicate, List.sum_replicate]

/-- An all-edges shape is the replicate of its own length. -/
theorem eq_replicate_of_ones {l : List ℕ+} (h : ∀ d ∈ l, d = 1) : l = 𝟙^l.length :=
  List.eq_replicate_of_mem h

/-- **The bead count of an all-edges shape is its total dimension.**  This is what makes runs
rigid: `dimSum` is preserved by every wedge map, so the bead count is too. -/
theorem dimSum_eq_length_of_ones {l : List ℕ+} (h : ∀ d ∈ l, d = 1) : dimSum l = l.length := by
  conv_lhs => rw [eq_replicate_of_ones h]
  exact dimSum_replicate _

/-! ### The category of runs -/

/-- A chain is a **run** when every one of its beads is an edge. -/
def IsRun (K : BPSet) : ObjectProperty (Ch K) := fun a => ∀ d ∈ a.dims, d = 1

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

`splitObj` is a two-sided inverse to `chConcat` (`Chains/WedgeSplit`), and both halves of a split
run are again all edges because their dimension sequences concatenate to the whole's.  Restricting
that inverse pair to runs costs nothing — no transports, since a run carries its own dims. -/

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

/-! ### Runs of a cube, as a presheaf on `Box`

`Chains/ChainRestrictions` already assembles cube chains into `chainPresheaf : Boxᵒᵖ ⥤ Type`, and
being all-edges is stable under restriction — so runs cut out a subpresheaf.  Recording it as a
presheaf is what makes `runRestrictFace` functorial for free: its laws are `runPresheaf`'s own,
transported along `cubeFace`. -/

/-- `Ch K` is the structure form of the sigma type `equivWedgeHom` lands in. -/
def objEquivSigma (K : BPSet) : Ch K ≃ Σ dims : List ℕ+, (⋁dims ⟶ K) where
  toFun a := ⟨a.dims, a.map⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A chain is a cube chain.**  The two presentations of §3, packaged. -/
def chEquivCubeChain (K : BPSet) : Ch K ≃ CubeChain K :=
  (objEquivSigma K).trans (equivWedgeHom K).symm

@[simp] theorem chEquivCubeChain_dims (K : BPSet) (a : Ch K) :
    (chEquivCubeChain K a).dims = a.dims :=
  wedgeToCubes_dims a.dims a.map.hom

@[simp] theorem chEquivCubeChain_symm_dims (K : BPSet) (C : CubeChain K) :
    ((chEquivCubeChain K).symm C).dims = C.dims := rfl

/-- The cube list of a chain-as-cube-chain is the one `wedgeToCubes` reads off its descent map.
Proved here, before the transports below are sealed `irreducible`. -/
@[simp] theorem chEquivCubeChain_cubes (K : BPSet) (a : Ch K) :
    (chEquivCubeChain K a).cubes = wedgeToCubes ⟨a.dims, a.map.hom⟩ := rfl

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
  toFun r := ⟨chEquivCubeChain K r.chain,
    (CubeChain.ones_iff _).mp (by rw [chEquivCubeChain_dims]; exact r.ones)⟩
  invFun e := ⟨(chEquivCubeChain K).symm e.1, (CubeChain.ones_iff e.1).mpr e.2⟩
  left_inv r := Run.ext ((chEquivCubeChain K).left_inv r.chain)
  right_inv e := Subtype.ext ((chEquivCubeChain K).right_inv e.1)

/-- The cube list of a run, read through `Run.equivEdgeChain`, is the one `wedgeToCubes` reads off
its chain.  Stated before the seal below, since it is the only thing anyone needs from the
transport's innards. -/
theorem cubes_equivEdgeChain {K : BPSet} (r : Run K) :
    (Run.equivEdgeChain K r).1.cubes = wedgeToCubes ⟨r.dims, r.map.hom⟩ := rfl

/- **Seal the chain↔run transports.**  Same hazard as `runSplit`: these are computable
(`chainOfWedge` walks the cube list, `wedgeDescHom` rebuilds the glued map), so a unifier that
meets one under `runPresheaf.map` evaluates it and runs away.  Their `_dims` lemmas and the two
round trips are all anything below needs; `runPresheaf.map` itself stays reducible, which is what
keeps `runRestrictFace_eq` a `rfl`. -/
attribute [irreducible] objEquivSigma chEquivCubeChain Run.equivEdgeChain

/-- **Runs of a cube form a presheaf on `Box`** — the all-edges subpresheaf of `chainPresheaf`. -/
def runPresheaf : Boxᵒᵖ ⥤ Type where
  obj X := Run (□X.unop.dim)
  map f := ↾fun r =>
    (Run.equivEdgeChain _).symm (EdgeChain.restrict f.unop (Run.equivEdgeChain _ r))
  map_id X := by
    apply ConcreteCategory.hom_ext; intro r
    change (Run.equivEdgeChain _).symm (EdgeChain.restrict (𝟙 _) _) = r
    rw [EdgeChain.restrict_id]
    exact (Run.equivEdgeChain _).symm_apply_apply r
  map_comp f g := by
    apply ConcreteCategory.hom_ext; intro r
    change (Run.equivEdgeChain _).symm (EdgeChain.restrict (g.unop ≫ f.unop) _) = _
    rw [EdgeChain.restrict_comp]
    change _ = (Run.equivEdgeChain _).symm (EdgeChain.restrict g.unop
      (Run.equivEdgeChain _ ((Run.equivEdgeChain _).symm (EdgeChain.restrict f.unop _))))
    rw [Equiv.apply_symm_apply]

/-! ### `runPresheaf` classifies runs of a cube
`runPresheaf` is a presheaf on `Box` — that is, a *precubical set* — so by Yoneda a run of `□b` is
the same data as a map of precubical sets `(□b).toPsh ⟶ runPresheaf`.  Under that transpose,
restriction along a face is **precomposition**.  Everything the wedge recursion needs about faces
follows from that one line. -/

theorem run_cube0_eq (r s : Run (□0)) : r = s := Run.ext (obj_cube0_eq r.chain s.chain)

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
(`pshExtProd`, `Chains/WedgeExtend`) followed by iterated Segal splitting. -/
def runPshEquiv (a : List ℕ+) : ((⋁a).toPsh ⟶ runPresheaf) ≃ Run (⋁a) :=
  (pshExtProd runPresheaf (cubeRunEquiv 0 default) runPresheaf_point_ext a).trans
    (runSegalProd a).symm

/-- **A map into `runPresheaf` assembles into a run.** -/
def runOfPsh (a : List ℕ+) (φ : (⋁a).toPsh ⟶ runPresheaf) : Run (⋁a) := runPshEquiv a φ

/-- **A run of a wedge, transposed to a map into `runPresheaf`.** -/
def pshOfRun (a : List ℕ+) (r : Run (⋁a)) : (⋁a).toPsh ⟶ runPresheaf := (runPshEquiv a).symm r

/-- The two legs of `pshOfRun` at a cons.  Stated rather than rewritten to: `wedge2Desc_inl`'s
pattern sits behind `≫`'s object slot, spelled `⋁(c :: rest)` here and `□c ∨ ⋁rest` there. -/
theorem pshOfRun_inl (c : ℕ+) (rest : List ℕ+) (r : Run (⋁(c :: rest))) :
    wedgeInl (□(c : ℕ)) (⋁rest) ≫ pshOfRun (c :: rest) r
      = yonedaEquiv.symm (runSplit (consAltitude c rest) r).1 :=
  wedge2Desc_inl _ _ _

theorem pshOfRun_inr (c : ℕ+) (rest : List ℕ+) (r : Run (⋁(c :: rest))) :
    wedgeInr (□(c : ℕ)) (⋁rest) ≫ pshOfRun (c :: rest) r
      = pshOfRun rest (runSplit (consAltitude c rest) r).2 :=
  wedge2Desc_inr _ _ _

theorem runOfPsh_pshOfRun (a : List ℕ+) (r : Run (⋁a)) : runOfPsh a (pshOfRun a r) = r :=
  (runPshEquiv a).apply_symm_apply r

theorem pshOfRun_runOfPsh (a : List ℕ+) (φ : (⋁a).toPsh ⟶ runPresheaf) :
    pshOfRun a (runOfPsh a φ) = φ :=
  (runPshEquiv a).symm_apply_apply φ

/-! ### The general restriction

With runs classified, restricting along *any* wedge map is transpose–precompose–assemble, and the
two functor laws are associativity of `≫` plus a round trip.  No recursion on the target, no
splitting of the wedge map, no transports. -/

/-- **Restriction of a run along a wedge map.** -/
def runRestrict {a b : List ℕ+} (f : ⋁a ⟶ ⋁b) (r : Run (⋁b)) : Run (⋁a) :=
  runOfPsh a (f.hom ≫ pshOfRun b r)

@[simp] theorem runRestrict_id {a : List ℕ+} (r : Run (⋁a)) : runRestrict (𝟙 (⋁a)) r = r := by
  rw [runRestrict, id_hom, Category.id_comp, runOfPsh_pshOfRun]

theorem runRestrict_comp {a b c : List ℕ+} (p : ⋁a ⟶ ⋁b) (q : ⋁b ⟶ ⋁c) (r : Run (⋁c)) :
    runRestrict (p ≫ q) r = runRestrict p (runRestrict q r) := by
  rw [runRestrict, runRestrict, runRestrict, pshOfRun_runOfPsh, comp_hom, Category.assoc]

/-! ### Per-bead local runs

A run of `⋁a` is one local run per bead (`runSegalProd`); `runProj r i` extracts bead `i`'s, as the
run classified by `ιᵂ a i ≫ pshOfRun r`.  Restriction commutes with projection through the block
factorization — the `.2`-side localization diagram (`runProj_runRestrict`), the single fact carrying
the run order across a refinement. -/

/-- **Bead `i`'s local run** of a run of `⋁a` — its classifying map read at bead `i`. -/
noncomputable def runProj {a : List ℕ+} (r : Run (⋁a)) (i : Fin a.length) :
    Run (□(a.get i : ℕ)) :=
  yonedaEquiv (ιᵂ a i ≫ pshOfRun a r)

/-- **The `.2`-side localization diagram.**  Bead `iβ` of a restricted run is bead
`blockIdx φ iβ` of the original, restricted along the block face `blockFace φ iβ` — no `run.map`
coend, just `blockFace_spec` under `yonedaEquiv`. -/
theorem runProj_runRestrict {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (r : Run (⋁b)) (iβ : Fin a.length) :
    runProj (runRestrict φ r) iβ
      = runPresheaf.map (blockFace φ.hom iβ).op (runProj r (blockIdx φ.hom iβ)) := by
  have hmap : ιᵂ a iβ ≫ pshOfRun a (runRestrict φ r)
      = yoneda.map (blockFace φ.hom iβ) ≫ (ιᵂ b (blockIdx φ.hom iβ) ≫ pshOfRun b r) := by
    rw [show pshOfRun a (runRestrict φ r) = φ.hom ≫ pshOfRun b r from by
        rw [runRestrict, pshOfRun_runOfPsh],
      ← Category.assoc, blockFace_spec φ.hom iβ]
    exact Category.assoc _ _ _
  exact (congrArg yonedaEquiv hmap).trans
    (yonedaEquiv_naturality (ιᵂ b (blockIdx φ.hom iβ) ≫ pshOfRun b r) (blockFace φ.hom iβ)).symm

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
chains: a face paired with a chamber above it.  Written `Int(Lines K)` in the prose. -/
abbrev ChStar (K : BPSet) : Type := (Lines K).Elements

@[inherit_doc] notation:max "Ch⋆ " K:max => CubeChains.ChStar K

/-- The chain a complexified chain sits over. -/
abbrev ChStar.chain {K : BPSet} (x : Ch⋆ K) : Ch K := x.1.unop

/-- The run it carries — recovered from the classifying map via `runPshEquiv`. -/
def ChStar.run {K : BPSet} (x : Ch⋆ K) : Run (⋁x.chain.dims) := runPshEquiv x.chain.dims x.2

end CubeChains
