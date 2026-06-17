import CubeChains.Chains.Correspondence
import CubeChains.Chains.Category

/-!
# The lifted automorphism preserves refinement shape (`incl`)

An automorphism `σ : Aut K` lifts to an automorphism `Aut.liftToCh K σ` of `Ch K`
(`Chains/Category.lean`).  That lift is *orientation-preserving*: it preserves the
dimension sequence of every chain (`Aut.liftToCh_orientationPreserving`).

Under the side conditions `NonSelfLinked` + `AdmitsAltitude`, `Ch K` is equivalent
to the **refinement category** `RefineObj K.init K.final` (`equivWedgeCat`), whose
morphisms carry, per cube, an explicit standard-cube *inclusion* `incl`
(`Chains/Refine.lean`).  This file proves that the induced functor on the
refinement category preserves **all** of that inclusion data — not just dimensions.

The mechanism is simple: `Aut.liftToCh K σ` leaves the underlying wedge map of every
morphism unchanged (`liftToCh_hom_map_φ`), only post-composing the *classifying*
maps by `σ`.  Translated to the refinement side this is the **geometric action**
`refineAut σ`, which relabels the cubes of a chain by `σ` but keeps the reindexing
(`refinement`) and the inclusions (`incl`) of every refinement morphism verbatim
(`refineAut_map_incl`).  We then show `refineAut σ` *is* the lifted functor:
conjugating `Aut.liftToCh K σ` through the equivalence lands on `refineAut σ`
(`inducedRefine_obj`, `inducedRefineIso`).
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace CubeChain

variable {K : BPSet}

/-! ### Pushing a chain forward along a bi-pointed map -/

/-- **A bi-pointed map carries cube chains to cube chains.**  Applying `φ` cube-wise
to a chain `a → cubes → b` in `A` yields a chain `φ a → φ·cubes → φ b` in `B`; the
link/endpoint conditions transfer through `map_vertex₀`/`map_vertex₁`. -/
theorem isCubeChain_map {A B : BPSet} (φ : A ⟶ B) :
    ∀ (cubes : List (Σ n : ℕ+, A.toPsh.cells (n : ℕ))) (a b : A.toPsh.cells 0),
      IsCubeChain a cubes b →
      IsCubeChain (φ.hom.app (op (Box.ob 0)) a)
        (cubes.map (fun c => ⟨c.1, φ.hom.app (op (Box.ob (c.1 : ℕ))) c.2⟩))
        (φ.hom.app (op (Box.ob 0)) b)
  | [], _, _, h => congrArg (φ.hom.app (op (Box.ob 0))) h
  | ⟨n, c⟩ :: rest, _, b, h => by
      obtain ⟨h1, h2⟩ := h
      exact ⟨by rw [← map_vertex₀ φ c]; exact congrArg _ h1,
        by rw [← map_vertex₁ φ c]; exact isCubeChain_map φ rest (A.toPsh.vertex₁ c) b h2⟩

/-! ### The geometric action of `σ` on the refinement category -/

/-- The cube relabelling induced by an automorphism `σ` of `K`: send a cube `c` (of
dimension `c.1`) to `σ c`, keeping its dimension. -/
noncomputable def mapCube (σ : Aut K) (c : Σ n : ℕ+, K.toPsh.cells (n : ℕ)) :
    Σ n : ℕ+, K.toPsh.cells (n : ℕ) :=
  ⟨c.1, σ.hom.hom.app (op (Box.ob (c.1 : ℕ))) c.2⟩

/-- Reading the `i`-th relabelled cube: it is the relabelling of the `i`-th original
cube (a `List.get`/`List.map` commutation, modulo the length cast). -/
theorem get_mapCube (σ : Aut K) (l : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ)))
    (i : Fin (l.map (mapCube σ)).length) :
    (l.map (mapCube σ)).get i = mapCube σ (l.get (i.cast (by rw [List.length_map]))) := by
  simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]

/-- **The σ-relabelled chain.**  Object part of the geometric action: relabel every
cube of `x` by `σ`.  The chain condition survives because `σ` is a bi-pointed map
(`isCubeChain_map`) fixing `init`/`final`.  Marked `reducible` so that the cube list
`(refineAutObj σ x).cubes` unfolds to `x.cubes.map (mapCube σ)` for rewriting. -/
@[reducible] noncomputable def refineAutObj (σ : Aut K) (x : RefineObj K.init K.final) :
    RefineObj K.init K.final where
  cubes := x.cubes.map (mapCube σ)
  isChain := by
    have h := isCubeChain_map σ.hom x.cubes K.init K.final x.isChain
    rwa [σ.hom.app_init, σ.hom.app_final] at h

/-- **The σ-relabelled refinement.**  Morphism part of the geometric action: keep the
reindexing `f.refinement` and the inclusions `f.incl` *verbatim* (only the
`List.get`/`List.map` length casts and the dimension-equality transports are
inserted).  `inclSpec` transfers through the naturality of `σ` (`σ` commutes with
`K.toPsh.map`) applied to `f.inclSpec`. -/
noncomputable def refineAutMap (σ : Aut K) {x y : RefineObj K.init K.final}
    (f : x ⟶ y) : refineAutObj σ x ⟶ refineAutObj σ y := by
  have hlx : (x.cubes.map (mapCube σ)).length = x.cubes.length := by rw [List.length_map]
  have hly : (y.cubes.map (mapCube σ)).length = y.cubes.length := by rw [List.length_map]
  have hsrc : ∀ i : Fin (x.cubes.map (mapCube σ)).length,
      ((x.cubes.map (mapCube σ)).get i).1 = (x.cubes.get (i.cast hlx)).1 := by
    intro i; simp only [List.get_eq_getElem, List.getElem_map, mapCube, Fin.val_cast]
  have htgt : ∀ i : Fin (x.cubes.map (mapCube σ)).length,
      (y.cubes.get (f.refinement (i.cast hlx))).1
        = ((y.cubes.map (mapCube σ)).get ((f.refinement (i.cast hlx)).cast hly.symm)).1 := by
    intro i; simp only [List.get_eq_getElem, List.getElem_map, mapCube, Fin.val_cast]
  refine
    { chainx := (refineAutObj σ x).isChain
      chainy := (refineAutObj σ y).isChain
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
    -- innermost: strip the codomain transport, exposing `σ (y-cube)`.
    have hb : ((y.cubes.map (mapCube σ)).get ((f.refinement (i.cast hlx)).cast hly.symm)).2
        ≍ σ.hom.hom.app (op (Box.ob ((y.cubes.get (f.refinement (i.cast hlx))).1 : ℕ)))
            (y.cubes.get (f.refinement (i.cast hlx))).2 :=
      (Sigma.ext_iff.mp
        (get_mapCube σ y.cubes ((f.refinement (i.cast hlx)).cast hly.symm))).2
    have T1 := map_eqToHom_op_cell
      (congrArg (fun m : ℕ+ => Box.ob (m : ℕ)) (htgt i)) hb
    -- middle: naturality of `σ` applied to `f.inclSpec`.
    have T2 : K.toPsh.map (f.incl (i.cast hlx)).op
          (σ.hom.hom.app (op (Box.ob ((y.cubes.get (f.refinement (i.cast hlx))).1 : ℕ)))
            (y.cubes.get (f.refinement (i.cast hlx))).2)
        = σ.hom.hom.app (op (Box.ob ((x.cubes.get (i.cast hlx)).1 : ℕ)))
            (x.cubes.get (i.cast hlx)).2 :=
      (NatTrans.naturality_apply σ.hom.hom (f.incl (i.cast hlx)).op
        (y.cubes.get (f.refinement (i.cast hlx))).2).symm.trans
        (congrArg (σ.hom.hom.app _) (f.inclSpec (i.cast hlx)).symm)
    -- outermost: re-insert the domain transport, recovering `σ (x-cube)`.
    have ha : ((x.cubes.map (mapCube σ)).get i).2
        ≍ σ.hom.hom.app (op (Box.ob ((x.cubes.get (i.cast hlx)).1 : ℕ)))
            (x.cubes.get (i.cast hlx)).2 :=
      (Sigma.ext_iff.mp (get_mapCube σ x.cubes i)).2
    have T3 := map_eqToHom_op_cell
      (congrArg (fun m : ℕ+ => Box.ob (m : ℕ)) (hsrc i)) ha.symm
    rw [op_comp, op_comp, K.toPsh.map_comp, K.toPsh.map_comp, types_comp_apply,
      types_comp_apply, T1, T2, T3]

/-- **The geometric action of `σ` on the refinement category.**  Relabels chains by
`σ`, keeping every refinement's reindexing and inclusions.  Functoriality is free
from thinness of the refinement category (`refineObj_hom_subsingleton`). -/
noncomputable def refineAut (σ : Aut K) (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    RefineObj K.init K.final ⥤ RefineObj K.init K.final where
  obj := refineAutObj σ
  map f := refineAutMap σ f
  map_id _ := Subsingleton.elim (h := refineObj_hom_subsingleton h₁ h₂ _ _) _ _
  map_comp _ _ := Subsingleton.elim (h := refineObj_hom_subsingleton h₁ h₂ _ _) _ _

/-- **The inclusion data is preserved.**  The refinement `refineAut σ` carries the
inclusion `f.incl i` of every refinement morphism *unchanged* (up only to the
canonical `List.get`/`List.map` and dimension-equality transports).  This is the
sense in which the lifted automorphism preserves the *shape* of refinements, not
merely their dimensions.  True by construction of `refineAutMap`. -/
theorem refineAut_map_incl (σ : Aut K) (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f : x ⟶ y)
    (i : Fin (x.cubes.map (mapCube σ)).length) :
    ((refineAut σ h₁ h₂).map f).incl i
      = eqToHom (congrArg (fun m : ℕ+ => Box.ob (m : ℕ))
          (congrArg Sigma.fst (get_mapCube σ x.cubes i)))
        ≫ f.incl (i.cast (by rw [List.length_map]))
        ≫ eqToHom (congrArg (fun m : ℕ+ => Box.ob (m : ℕ))
          (congrArg Sigma.fst (get_mapCube σ y.cubes
            ((f.refinement (i.cast (by rw [List.length_map]))).cast
              (by rw [List.length_map])))).symm) :=
  rfl

/-! ### `refineAut σ` *is* the lifted functor -/

/-- The functor on `RefineObj` induced by `Aut.liftToCh K σ`, by conjugating through
the equivalence `equivWedgeCat`. -/
noncomputable def inducedRefine (σ : Aut K) (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    RefineObj K.init K.final ⥤ RefineObj K.init K.final :=
  (equivWedgeCat h₁ h₂).functor ⋙ (Aut.liftToCh K σ).hom.toFunctor
    ⋙ (equivWedgeCat h₁ h₂).inverse

/-- **On objects, the lifted functor relabels cubes by `σ`.**  Conjugating
`liftToCh σ` post-composes a chain's classifying map by `σ`, and reading the cubes
back off that map applies `σ` cube-wise (`wedgeToCubes_wedgeDesc_comp`). -/
theorem inducedRefine_obj (σ : Aut K) (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (x : RefineObj K.init K.final) :
    (inducedRefine σ h₁ h₂).obj x = refineAutObj σ x := by
  apply RefineObj.ext'
  change wedgeToCubes ⟨(refineToWedgeObj x).dims, ((refineToWedgeObj x).map ≫ σ.hom).hom⟩
      = x.cubes.map (mapCube σ)
  rw [BPSet.comp_hom]
  exact wedgeToCubes_wedgeDesc_comp σ.hom.hom K.init K.final x.cubes x.isChain

/-- **`refineAut σ` is the lifted functor.**  The conjugate of `Aut.liftToCh K σ`
through `equivWedgeCat` is naturally isomorphic to the geometric action `refineAut σ`
— so the geometric description (which manifestly preserves `incl`) really is the
induced functor.  Object components are the strict relabelling equality
(`inducedRefine_obj`); naturality is free from thinness. -/
noncomputable def inducedRefineIso (σ : Aut K) (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    inducedRefine σ h₁ h₂ ≅ refineAut σ h₁ h₂ :=
  NatIso.ofComponents
    (fun x => eqToIso (inducedRefine_obj σ h₁ h₂ x))
    (fun _ => Subsingleton.elim (h := refineObj_hom_subsingleton h₁ h₂ _ _) _ _)

/-! ### The `Ch K`-native statement: the lift preserves the inducing map `r`

Working **entirely inside `Ch K`**, with **no** side conditions on `K`.  A morphism
`f : P ⟶ Q` of `Ch K` *is* a wedge map `r := f.φ : □^∨(P.dims) ⟶ □^∨(Q.dims)` with
`r ≫ Q = P` over `K` (the data of `ChainCat.Hom`).  The lift `F := Aut.liftToCh K σ`
fixes the dimension sequences *definitionally* — `F.obj P = ⟨P.dims, P.map ≫ σ⟩`
(`ChainCat.liftToCh_hom_obj`) — so `F.obj P`, `F.obj Q` have the **same** domains
`□^∨(P.dims)`, `□^∨(Q.dims)` as `P`, `Q`, and `F f` is induced by the **same** `r`.

This is the clean, unconditional `Ch K`-native form of the refinement-side
`refineAut_map_incl`: there, preserving the per-cube inclusions `incl` needs
`NonSelfLinked` + `AdmitsAltitude` (to pass through `equivWedgeCat`); here all that
inclusion data is packaged into the single morphism `r = f.φ`, whose preservation is
literally definitional (`ChainCat.liftToCh_hom_map_φ`). -/

/-- **The lift preserves the inducing map `r` (unconditional).**  `F f` is precisely
the morphism of `Ch K` induced by the *same* wedge map `r = f.φ` as `f`; its triangle
over `K` is `f`'s triangle post-composed by `σ`.  More than the `φ`-projection lemma
`ChainCat.liftToCh_hom_map_φ`: it exhibits the whole morphism `F f` in `r`-induced
form.  No side conditions on `K`. -/
theorem liftToCh_map_eq (σ : Aut K) {P Q : ChainCat.Obj K} (f : P ⟶ Q) :
    (Aut.liftToCh K σ).hom.toFunctor.map f
      = { φ := f.φ
          w := by simp only [ChainCat.liftToCh_hom_obj]; rw [← Category.assoc, f.w] } :=
  ChainCat.hom_ext' rfl

end CubeChain
