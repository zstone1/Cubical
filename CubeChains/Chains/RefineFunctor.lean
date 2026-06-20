import CubeChains.Chains.Lifting

/-!
# Functoriality of the refinement category in `K` (`Refine.pushforward`)

`Chains/Refine.lean` builds, for a fixed bi-pointed `K` and endpoints `a, b`, the
**refinement category** `RefineObj a b` (the face-poset / subdivision category, PZ
Lemma 2.11(c)).  This file makes that construction **functorial in `K`**: a
bi-pointed map `φ : A ⟶ B` post-composes every chain, giving a genuine functor

`Refine.pushforward φ : RefineObj (K := A) a b ⥤ RefineObj (K := B) (φ a) (φ b)`.

This is the refinement-side analogue of `ChainCat.pushforward` (the wedge-map side,
`Chains/Category.lean`) and of `Ch'.pushforward` (`Chains/Endpoints.lean`), and is the
piece the cylinder ⟹ pointed-functor program needs to build the leg-functors
`Lgrpd`/`Rgrpd` on the d-path groupoid `FreeGroupoid (RefineObj K.init K.final)`.

**Why a fresh proof (not `refineAut` reused).**  `Lifting.lean`'s `refineAut σ`
(the action of an automorphism) also pushes chains forward, but it obtains
functoriality *for free from thinness* (`refineObj_hom_subsingleton`), which needs
`NonSelfLinked + AdmitsAltitude`.  The cylinder program runs on **self-linked** `K`
(rel-interface cylinders force a basepoint self-loop, which breaks both side
conditions), so thinness is unavailable and functoriality is proved **directly**.

The mechanism (the same `cube relabelling` as `refineAut`, generalised to a map
between different `BPSet`s): the per-cube inclusions `incl` and the reindexing
`refinement` are kept *verbatim*, with only `List.get`/`List.map` length casts and
dimension-equality transports inserted; `inclSpec` transfers through the naturality
of `φ`.  Functoriality is then `ChainRefine.ext` with the reindexings **definitionally
equal** (`Fin.cast` round-trips collapse by structure-eta + proof irrelevance) and the
inclusions matched by `eqToHom` cancellation — exactly the pattern `refineCategory`
uses for `id_comp`/`assoc`.
-/

open CategoryTheory Opposite

namespace CubeChain

/-! ### Pushing one cube, and reading it back off the mapped list -/

/-- Push a single dimension-tagged cube of `A` forward along a bi-pointed map `φ`,
keeping its dimension.  (The cross-`BPSet` generalisation of `mapCube`.) -/
noncomputable def mapCubeHom {A B : BPSet} (φ : A ⟶ B)
    (c : Σ n : ℕ+, A.toPsh.cells (n : ℕ)) : Σ n : ℕ+, B.toPsh.cells (n : ℕ) :=
  ⟨c.1, φ.hom.app (op (Box.ob (c.1 : ℕ))) c.2⟩

/-- Reading the `i`-th mapped cube: it is the map of the `i`-th original cube (a
`List.get`/`List.map` commutation modulo the length cast). -/
theorem get_mapCubeHom {A B : BPSet} (φ : A ⟶ B)
    (l : List (Σ n : ℕ+, A.toPsh.cells (n : ℕ))) (i : Fin (l.map (mapCubeHom φ)).length) :
    (l.map (mapCubeHom φ)).get i = mapCubeHom φ (l.get (i.cast (by rw [List.length_map]))) := by
  simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]

/-! ### The object map -/

/-- **Pushforward of a refinement object.**  Relabel every cube of the chain `x` by
`φ`; the chain condition survives because `φ` carries cube chains to cube chains
(`isCubeChain_map`).  The endpoints move to `φ a`, `φ b`. -/
@[reducible] noncomputable def refinePushObj {A B : BPSet} (φ : A ⟶ B) {a b : A.toPsh.cells 0}
    (x : RefineObj (K := A) a b) :
    RefineObj (K := B) (φ.hom.app (op (Box.ob 0)) a) (φ.hom.app (op (Box.ob 0)) b) where
  cubes := x.cubes.map (mapCubeHom φ)
  isChain := isCubeChain_map φ x.cubes a b x.isChain

@[simp] theorem refinePushObj_cubes {A B : BPSet} (φ : A ⟶ B) {a b : A.toPsh.cells 0}
    (x : RefineObj (K := A) a b) : (refinePushObj φ x).cubes = x.cubes.map (mapCubeHom φ) := rfl

/-! ### The morphism map -/

/-- **Pushforward of a refinement morphism.**  Keep the reindexing `f.refinement` and
the inclusions `f.incl` verbatim (only `List.get`/`List.map` length casts and
dimension-equality transports are inserted); `inclSpec` transfers through the
naturality of `φ` (`φ` commutes with `B.toPsh.map`) applied to `f.inclSpec`.  The
cross-`BPSet` generalisation of `refineAutMap`. -/
noncomputable def refinePushMap {A B : BPSet} (φ : A ⟶ B) {a b : A.toPsh.cells 0}
    {x y : RefineObj (K := A) a b} (f : x ⟶ y) : refinePushObj φ x ⟶ refinePushObj φ y := by
  have hlx : (x.cubes.map (mapCubeHom φ)).length = x.cubes.length := by rw [List.length_map]
  have hly : (y.cubes.map (mapCubeHom φ)).length = y.cubes.length := by rw [List.length_map]
  have hsrc : ∀ i : Fin (x.cubes.map (mapCubeHom φ)).length,
      ((x.cubes.map (mapCubeHom φ)).get i).1 = (x.cubes.get (i.cast hlx)).1 := by
    intro i; simp only [List.get_eq_getElem, List.getElem_map, mapCubeHom, Fin.val_cast]
  have htgt : ∀ i : Fin (x.cubes.map (mapCubeHom φ)).length,
      (y.cubes.get (f.refinement (i.cast hlx))).1
        = ((y.cubes.map (mapCubeHom φ)).get ((f.refinement (i.cast hlx)).cast hly.symm)).1 := by
    intro i; simp only [List.get_eq_getElem, List.getElem_map, mapCubeHom, Fin.val_cast]
  refine
    { chainx := (refinePushObj φ x).isChain
      chainy := (refinePushObj φ y).isChain
      refinement := fun i => (f.refinement (i.cast hlx)).cast hly.symm
      refinementMono := ?mono
      incl := fun i =>
        eqToHom (congrArg (fun m : ℕ+ => Box.ob (m : ℕ)) (hsrc i))
          ≫ f.incl (i.cast hlx)
          ≫ eqToHom (congrArg (fun m : ℕ+ => Box.ob (m : ℕ)) (htgt i))
      inclSpec := ?spec }
  case mono =>
    intro i j hij
    rw [Fin.le_def]
    exact Fin.le_def.mp (f.refinementMono (i.cast hlx) (j.cast hlx)
      (by rw [Fin.le_def]; exact Fin.le_def.mp hij))
  case spec =>
    intro i
    have hb : ((y.cubes.map (mapCubeHom φ)).get ((f.refinement (i.cast hlx)).cast hly.symm)).2
        ≍ φ.hom.app (op (Box.ob ((y.cubes.get (f.refinement (i.cast hlx))).1 : ℕ)))
            (y.cubes.get (f.refinement (i.cast hlx))).2 :=
      (Sigma.ext_iff.mp
        (get_mapCubeHom φ y.cubes ((f.refinement (i.cast hlx)).cast hly.symm))).2
    have T1 := map_eqToHom_op_cell (K := B)
      (congrArg (fun m : ℕ+ => Box.ob (m : ℕ)) (htgt i)) hb
    have T2 : B.toPsh.map (f.incl (i.cast hlx)).op
          (φ.hom.app (op (Box.ob ((y.cubes.get (f.refinement (i.cast hlx))).1 : ℕ)))
            (y.cubes.get (f.refinement (i.cast hlx))).2)
        = φ.hom.app (op (Box.ob ((x.cubes.get (i.cast hlx)).1 : ℕ)))
            (x.cubes.get (i.cast hlx)).2 :=
      (NatTrans.naturality_apply φ.hom (f.incl (i.cast hlx)).op
        (y.cubes.get (f.refinement (i.cast hlx))).2).symm.trans
        (congrArg (φ.hom.app _) (f.inclSpec (i.cast hlx)).symm)
    have ha : ((x.cubes.map (mapCubeHom φ)).get i).2
        ≍ φ.hom.app (op (Box.ob ((x.cubes.get (i.cast hlx)).1 : ℕ)))
            (x.cubes.get (i.cast hlx)).2 :=
      (Sigma.ext_iff.mp (get_mapCubeHom φ x.cubes i)).2
    have T3 := map_eqToHom_op_cell (K := B)
      (congrArg (fun m : ℕ+ => Box.ob (m : ℕ)) (hsrc i)) ha.symm
    rw [op_comp, op_comp, B.toPsh.map_comp, B.toPsh.map_comp, types_comp_apply,
      types_comp_apply, T1, T2, T3]

/-! ### The functor (functoriality proved directly, without thinness) -/

/-- Move a refinement's inclusion across an index equality, inserting the canonical
domain/codomain `eqToHom` transports.  Proved by `subst` (so robust to the `Fin.cast`
round-trips that the pushforward's reindexing introduces). -/
private theorem incl_index_eq {K : BPSet} {a b : K.toPsh.cells 0}
    {Y Z : RefineObj (K := K) a b} (g : Y ⟶ Z) {j j' : Fin Y.cubes.length} (h : j = j') :
    CubeChain.ChainRefine.incl g j
      = eqToHom (congrArg (fun l => Box.ob ((Y.cubes.get l).1 : ℕ)) h)
        ≫ CubeChain.ChainRefine.incl g j'
        ≫ eqToHom (congrArg (fun l => Box.ob ((Z.cubes.get (g.refinement l)).1 : ℕ)) h.symm) := by
  subst h; simp

/-- **The pushforward functor on refinement categories.**  Post-compose every chain
by the bi-pointed map `φ`.  Functoriality is proved **directly** (no thinness): the
reindexings are definitionally equal (`Fin.cast` round-trips collapse), so
`ChainRefine.ext rfl` reduces both laws to pointwise `eqToHom` cancellation. -/
noncomputable def Refine.pushforward {A B : BPSet} (φ : A ⟶ B) {a b : A.toPsh.cells 0} :
    RefineObj (K := A) a b ⥤ RefineObj (K := B) (φ.hom.app (op (Box.ob 0)) a)
      (φ.hom.app (op (Box.ob 0)) b) where
  obj x := refinePushObj φ x
  map f := refinePushMap φ f
  map_id x := by
    refine ChainRefine.ext rfl (heq_of_eq ?_)
    funext i
    -- `incl i = eqToHom _ ≫ (𝟙 x).incl _ ≫ eqToHom _`; the middle is `𝟙` by defeq.
    change eqToHom _ ≫ 𝟙 _ ≫ eqToHom _ = 𝟙 _
    rw [Category.id_comp, eqToHom_trans]
    exact eqToHom_refl _ _
  map_comp f g := by
    refine ChainRefine.ext rfl (heq_of_eq ?_)
    funext i
    -- `(f ≫ g).incl = f.incl ≫ g.incl (f.refinement)` by defeq; the inner `eqToHom`s cancel.
    change eqToHom _ ≫ (f.incl _ ≫ g.incl _) ≫ eqToHom _
      = (eqToHom _ ≫ f.incl _ ≫ eqToHom _) ≫ (eqToHom _ ≫ g.incl _ ≫ eqToHom _)
    simp only [Category.assoc]
    slice_rhs 3 4 => rw [eqToHom_trans]
    -- LHS/RHS now agree up to the defeq `g.incl` index and the `eqToHom η` between defeq
    -- objects; rewrite the `g`-inclusion across the index round-trip, then `eqToHom` cancels.
    rw [incl_index_eq g (show f.refinement (Fin.cast (by rw [List.length_map]) i)
      = Fin.cast (by rw [List.length_map]) ((refinePushMap φ f).refinement i) from rfl)]
    simp

end CubeChain
