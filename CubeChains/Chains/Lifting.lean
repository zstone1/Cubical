import CubeChains.Chains.RefineFunctor
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

**`refineAut σ` is a special case of the pushforward.**  The geometric action is
nothing but `Refine.pushforward σ.hom.hom` (`Chains/RefineFunctor.lean`) — the
functoriality of `RefineObj` in `K` — applied to the underlying presheaf map of `σ`,
with the endpoints re-based to `K.init`/`K.final` via `σ.hom.app_init`/`app_final`
(the same `▸`-transport `Refine.pushforwardBP` uses).  In particular `σ` being an
isomorphism is irrelevant to the *construction*: `refineAut σ` needs **no** side
conditions on `K` (the general pushforward is proved without thinness).
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace CubeChain

variable {K : BPSet}

/-! ### The geometric action of `σ` on the refinement category -/

/-- A functor into `RefineObj b₀ b₁` re-based across endpoint equalities `h₀ : b₀' = b₀`,
`h₁ : b₁' = b₁` (so the result lands in `RefineObj b₀' b₁'`).  Built by `subst`; the
`RefineObj` index does not enter `.cubes`, so the recast is invisible there
(`refineAut_recast_cubes`). -/
private noncomputable def refineRecast {𝒞 : Type*} [Category 𝒞]
    {b₀ b₁ b₀' b₁' : K.toPsh.cells 0} (h₀ : b₀' = b₀) (h₁ : b₁' = b₁)
    (F : 𝒞 ⥤ RefineObj (K := K) b₀ b₁) : 𝒞 ⥤ RefineObj (K := K) b₀' b₁' := by
  subst h₀; subst h₁; exact F

private theorem refineRecast_cubes {𝒞 : Type*} [Category 𝒞]
    {b₀ b₁ b₀' b₁' : K.toPsh.cells 0} (h₀ : b₀' = b₀) (h₁ : b₁' = b₁)
    (F : 𝒞 ⥤ RefineObj (K := K) b₀ b₁) (a : 𝒞) :
    ((refineRecast h₀ h₁ F).obj a).cubes = (F.obj a).cubes := by
  subst h₀; subst h₁; rfl

/-- **The geometric action of `σ` on the refinement category.**  Relabels chains by
`σ`, keeping every refinement's reindexing and inclusions.  This is the pushforward
`Refine.pushforward σ.hom.hom` along the underlying presheaf map of `σ`, with the
endpoints re-based to `K.init`/`K.final` by `σ.hom.app_init`/`app_final` (`σ` fixes
the basepoints).  No side conditions on `K` are needed: functoriality is the general
one from `RefineFunctor.lean`, proved without thinness. -/
noncomputable def refineAut (σ : Aut K) :
    RefineObj K.init K.final ⥤ RefineObj K.init K.final :=
  refineRecast σ.hom.app_init.symm σ.hom.app_final.symm
    (Refine.pushforward (a := K.init) (b := K.final) σ.hom.hom)

/-- **Reading the cubes of `refineAut σ`.**  The endpoint recast is invisible to
`.cubes`, so the relabelled chain's cubes are literally `x.cubes` mapped cube-wise by
`σ`. -/
@[simp] theorem refineAut_obj_cubes (σ : Aut K) (x : RefineObj K.init K.final) :
    ((refineAut σ).obj x).cubes = x.cubes.map (mapCubeHom σ.hom.hom) := by
  rw [refineAut, refineRecast_cubes]
  rfl

/-- **The inclusion data is preserved.**  The refinement `refineAut σ` carries the
inclusion `f.incl i` of every refinement morphism *unchanged* (up only to the
canonical `List.get`/`List.map` and dimension-equality transports).  This is the
sense in which the lifted automorphism preserves the *shape* of refinements, not
merely their dimensions.  True by construction of `refineAut` from
`Refine.pushforward` (whose morphism part is `refinePushMap`, keeping `incl`
verbatim). -/
theorem refineAut_map_incl (σ : Aut K)
    {x y : RefineObj K.init K.final} (f : x ⟶ y)
    (i : Fin (x.cubes.map (mapCubeHom σ.hom.hom)).length) :
    ((Refine.pushforward σ.hom.hom).map f).incl i
      = eqToHom (congrArg (fun m : ℕ+ => Box.ob (m : ℕ))
          (congrArg Sigma.fst (get_mapCubeHom σ.hom.hom x.cubes i)))
        ≫ f.incl (i.cast (by rw [List.length_map]))
        ≫ eqToHom (congrArg (fun m : ℕ+ => Box.ob (m : ℕ))
          (congrArg Sigma.fst (get_mapCubeHom σ.hom.hom y.cubes
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
back off that map applies `σ` cube-wise (`wedgeToCubes_wedgeDesc_comp`); this agrees
with the geometric action `refineAut σ` (`refineAut_obj_cubes`). -/
theorem inducedRefine_obj (σ : Aut K) (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (x : RefineObj K.init K.final) :
    (inducedRefine σ h₁ h₂).obj x = (refineAut σ).obj x := by
  apply RefineObj.ext'
  rw [refineAut_obj_cubes]
  change wedgeToCubes ⟨(refineToWedgeObj x).dims, ((refineToWedgeObj x).map ≫ σ.hom).hom⟩
      = x.cubes.map (mapCubeHom σ.hom.hom)
  rw [BPSet.comp_hom]
  exact wedgeToCubes_wedgeDesc_comp σ.hom.hom K.init K.final x.cubes x.isChain

/-- **`refineAut σ` is the lifted functor.**  The conjugate of `Aut.liftToCh K σ`
through `equivWedgeCat` is naturally isomorphic to the geometric action `refineAut σ`
— so the geometric description (which manifestly preserves `incl`) really is the
induced functor.  Object components are the strict relabelling equality
(`inducedRefine_obj`); naturality is free from thinness. -/
noncomputable def inducedRefineIso (σ : Aut K) (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    inducedRefine σ h₁ h₂ ≅ refineAut σ :=
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
