import CubeChains.Precubical.Chains.Refine
import CubeChains.Precubical.Chains.Embedding
import CubeChains.Concurrency.Grading.BlockDecomp

/-!
# Precubical/Chains/Correspondence

The refinement↔chain correspondence: `equivWedgeCat : RefineObj K ≌ Ch K` under `NonSelfLinked` +
`AdmitsAltitude`.  Forward, a refinement's inclusion data is bead data (`homOfBeads`, which needs
the target chain to be a monomorphism); backward, a wedge map's block decomposition is a refinement
with no hypothesis at all.  Both categories are thin, so functoriality is free.
-/

open CategoryTheory CategoryTheory.Limits Opposite StdCube BPSet

namespace CubeChain

variable {K : BPSet}

/-- Object part of the forward functor `refine ⥤ wedge`: a chain `↦` its descent map. -/
def refineToWedgeObj (x : RefineObj K.init K.final) : Ch K where
  dims := x.dims
  map := wedgeDescHom x.cubes x.isChain

/-- The wedge map a refinement induces: its inclusions, read as bead data. -/
def refineWedgeMap (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f : x ⟶ y) : refineToWedgeObj x ⟶ refineToWedgeObj y :=
  haveI := descent_mono h₁ h₂ (refineToWedgeObj y)
  homOfBeads f.refinement f.incl fun i =>
    (congrFun (beadCell_wedgeDescHom _ _) i).trans ((f.inclSpec i).trans
      (congrArg _ (congrFun (beadCell_wedgeDescHom y.cubes y.isChain) (f.refinement i)).symm))

/-- The forward functor `refine ⥤ wedge`; functoriality is free from thinness of `Ch K`. -/
def refineToWedge (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    RefineObj K.init K.final ⥤ Ch K :=
  haveI : Quiver.IsThin (Ch K) := chainCat_hom_subsingleton h₁ h₂
  { obj := refineToWedgeObj
    map f := refineWedgeMap h₁ h₂ f
    map_id _ := Subsingleton.elim _ _
    map_comp _ _ := Subsingleton.elim _ _ }

/-- **Block index is determined**: two refinements `x ⟶ y` place each `x`-bead in the same
`y`-bead — their wedge maps agree (`Ch K` is thin), and a positive cell lies in one block. -/
theorem refinement_eq (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    {x y : RefineObj K.init K.final} (f g : x ⟶ y) (i : Fin x.dims.length) :
    f.refinement i = g.refinement i := by
  haveI := descent_mono h₁ h₂ (refineToWedgeObj y)
  have hcell : placedCell (a := refineToWedgeObj x) (b := refineToWedgeObj y) f.refinement f.incl
      = placedCell (a := refineToWedgeObj x) (b := refineToWedgeObj y) g.refinement g.incl := by
    have h := congrArg (fun m : refineToWedgeObj x ⟶ refineToWedgeObj y => beadCell m.φ.hom)
      (Subsingleton.elim (h := chainCat_hom_subsingleton h₁ h₂ _ _)
        (refineWedgeMap h₁ h₂ f) (refineWedgeMap h₁ h₂ g))
    simpa only [refineWedgeMap, beadCell_homOfBeads] using h
  exact serialWedge_block_unique y.dims (x.dims.get i).2 _ _ _
    ⟨yonedaEquiv (yoneda.map (f.incl i)), (yonedaEquiv_comp _ _).symm⟩
    ⟨yonedaEquiv (yoneda.map (g.incl i)), (yonedaEquiv_comp _ _).symm.trans (congrFun hcell i).symm⟩

/-- **The refinement category is thin** under `NonSelfLinked` + `AdmitsAltitude`: the block index
is forced (`refinement_eq`), and then `NonSelfLinked` recovers each inclusion from the cube it pulls
back. -/
theorem refineObj_hom_subsingleton (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (x y : RefineObj K.init K.final) : Subsingleton (x ⟶ y) := by
  refine ⟨fun f g => ?_⟩
  have href : f.refinement = g.refinement := funext (refinement_eq h₁ h₂ f g)
  obtain ⟨_, _, incf, sf⟩ := f
  obtain ⟨_, _, incg, sg⟩ := g
  obtain rfl := href
  refine ChainRefine.ext rfl (heq_of_eq (funext fun i => ?_))
  refine h₁ _ (y.cubes _) _ ?_
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply, yonedaEquiv_symm_app_apply,
    ← sf i, ← sg i]

/-- Object part of the backward functor `wedge ⥤ refine`: a wedge map `↦` the beads read off it. -/
def wedgeToRefineObj (a : Ch K) : RefineObj K.init K.final where
  dims := a.dims
  cubes := beadCell a.map.hom
  isChain := (ChainCat.chCubes K a).2

/-- The refinement read off a wedge-map morphism: its block decomposition, ordered by the serial
wedge's own altitude (`serialWedge_blockIdx_monotone` needs no hypothesis on `K`). -/
def wedgeToRefineMap {a b : Ch K} (g : a ⟶ b) :
    wedgeToRefineObj a ⟶ wedgeToRefineObj b where
  refinement := blockIdx gᵂ
  refinementMono _ _ hij := serialWedge_blockIdx_monotone gᵂ (ChainCat.Hom.φ g).app_init hij
  incl := blockFace gᵂ
  inclSpec i := by
    have hw : gᵂ ≫ b.map.hom = a.map.hom := by
      have h := congrArg BPSet.Hom.hom g.w; rwa [comp_hom] at h
    change beadCell a.map.hom i = K.toPsh.map (blockFace gᵂ i).op (beadCell b.map.hom _)
    rw [← hw]; exact beadCell_comp_block gᵂ b.map.hom i

/-- The backward functor `wedge ⥤ refine`; functoriality is free from thinness. -/
def wedgeToRefine (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    Ch K ⥤ RefineObj K.init K.final :=
  haveI : Quiver.IsThin (RefineObj K.init K.final) := refineObj_hom_subsingleton h₁ h₂
  { obj := wedgeToRefineObj
    map g := wedgeToRefineMap g
    map_id _ := Subsingleton.elim _ _
    map_comp _ _ := Subsingleton.elim _ _ }

/-- A refinement object at a given shape is determined by its beads (`isChain` is a `Prop`). -/
theorem RefineObj.ext' {a b : K.cells 0} {d : List ℕ+} {c c' : Beads K.toPsh d}
    {h : IsCubeChain a c.toList b} {h' : IsCubeChain a c'.toList b} (e : c = c') :
    (⟨d, c, h⟩ : RefineObj a b) = ⟨d, c', h'⟩ := by subst e; rfl

/-- **Unit round-trip (strict)**: reading the beads back off a descent map recovers the chain. -/
theorem wedgeToRefineObj_refineToWedgeObj (x : RefineObj K.init K.final) :
    wedgeToRefineObj (refineToWedgeObj x) = x := by
  obtain ⟨d, c, hc⟩ := x
  exact RefineObj.ext' (beadCell_wedgeDescHom c hc)

/-- **Counit round-trip (strict)**: descending the beads read off `a` recovers `a`. -/
theorem refineToWedgeObj_wedgeToRefineObj (a : Ch K) :
    refineToWedgeObj (wedgeToRefineObj a) = a := by
  obtain ⟨d, m⟩ := a
  exact congrArg (ChainCat.Obj.mk d)
    (bpset_hom_ext_of_beadCell (congrFun (beadCell_wedgeDescHom _ _)))

/-- **The refine ≌ wedge equivalence**: both round trips are equalities of objects, so unit and
counit are `eqToIso`s, and naturality and the triangle are free from thinness. -/
def equivWedgeCat (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    RefineObj K.init K.final ≌ Ch K :=
  haveI : Quiver.IsThin (RefineObj K.init K.final) := refineObj_hom_subsingleton h₁ h₂
  haveI : Quiver.IsThin (Ch K) := chainCat_hom_subsingleton h₁ h₂
  { functor := refineToWedge h₁ h₂
    inverse := wedgeToRefine h₁ h₂
    unitIso := NatIso.ofComponents
      (fun x => eqToIso (wedgeToRefineObj_refineToWedgeObj x).symm)
      (fun _ => Subsingleton.elim _ _)
    counitIso := NatIso.ofComponents
      (fun a => eqToIso (refineToWedgeObj_wedgeToRefineObj a))
      (fun _ => Subsingleton.elim _ _)
    functor_unitIso_comp _ := Subsingleton.elim _ _ }

end CubeChain
