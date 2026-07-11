import CubeChains.Chains.BlockDecomp
import Mathlib.Order.RelClasses

/-!
# Salvetti/Lines — the chamber presheaf `Lines`

`Lines K : (ChainCat.Obj K)ᵒᵖ ⥤ Type` sends a cube chain `a` to the tuple of chambers of its
beads, `∏ᵢ Chamber (a.dims.get i)`, and a chain map to restriction (`linesRestrict`), pulling
each target bead's chamber back along the block data (`blockIdx`/`blockFace`/`faceEmb`,
`Chains/BlockDecomp`).  A `Chamber d` is a strict total order on the `d` directions of `□ᵈ`.
-/

open CategoryTheory Opposite CubeChain StdCube

namespace FinalBraid

/-! ### Chambers of the standard cube -/

/-- A **chamber** of the standard cube `□ᵈ`: a maximal chain of the Boolean lattice
`{0,1}ᵈ`, encoded as a strict total order `lt` on the `d` coordinate directions
(`i ≺ j` means `i` flips first).  There are `d!` chambers. -/
structure Chamber (d : ℕ) where
  /-- The strict total order on the `d` directions: `lt i j` means `i` flips first. -/
  lt : Fin d → Fin d → Prop
  /-- `lt` is a strict total order (irreflexive, transitive, trichotomous). -/
  sto : IsStrictTotalOrder (Fin d) lt

/-- A chamber is determined by its order relation. -/
@[ext] theorem Chamber.ext {d : ℕ} {c₁ c₂ : Chamber d} (h : c₁.lt = c₂.lt) : c₁ = c₂ := by
  cases c₁; cases c₂; cases h; rfl

/-- Pull back a chamber along an injective `g : Fin d → Fin e`: `i ≺' j ↔ g i ≺ g j`. -/
def Chamber.restrict {d e : ℕ} (c : Chamber e) (g : Fin d → Fin e)
    (hg : Function.Injective g) : Chamber d where
  lt a b := c.lt (g a) (g b)
  sto :=
    haveI := c.sto
    { trichotomous := fun a b h1 h2 => hg (Std.Trichotomous.trichotomous (g a) (g b) h1 h2)
      irrefl := fun a => Std.Irrefl.irrefl (g a)
      trans := fun a b c' hab hbc => IsTrans.trans (g a) (g b) (g c') hab hbc }

@[simp] theorem Chamber.restrict_lt {d e : ℕ} (c : Chamber e) (g : Fin d → Fin e)
    (hg : Function.Injective g) (a b : Fin d) :
    (c.restrict g hg).lt a b = c.lt (g a) (g b) := rfl

/-- Restricting along a pointwise-identity reindexing is the identity. -/
theorem Chamber.restrict_id_of {d : ℕ} (c : Chamber d) {g : Fin d → Fin d}
    (hg : Function.Injective g) (h : ∀ x, g x = x) : c.restrict g hg = c := by
  apply Chamber.ext; funext a b
  change c.lt (g a) (g b) = c.lt a b
  rw [h a, h b]

/-- Restricting twice composes the reindexings. -/
theorem Chamber.restrict_restrict {d e m : ℕ} (c : Chamber m)
    (g₁ : Fin d → Fin e) (h₁ : Function.Injective g₁)
    (g₂ : Fin e → Fin m) (h₂ : Function.Injective g₂) :
    (c.restrict g₂ h₂).restrict g₁ h₁ = c.restrict (g₂ ∘ g₁) (h₂.comp h₁) :=
  Chamber.ext rfl

/-- Two pointwise-equal reindexings give the same restriction. -/
theorem Chamber.restrict_congr {d e : ℕ} (c : Chamber e) {g g' : Fin d → Fin e}
    (hg : Function.Injective g) (hg' : Function.Injective g') (h : ∀ x, g x = g' x) :
    c.restrict g hg = c.restrict g' hg' := by
  apply Chamber.ext; funext a b
  change c.lt (g a) (g b) = c.lt (g' a) (g' b)
  rw [h a, h b]

/-! ### The chamber presheaf `Lines` (on the `ChainCat` base) -/

variable {K : BPSet}

/-- Chambers refining `a`: one chamber per bead (depends only on `a.dims`). -/
def LinesObj (a : ChainCat.Obj K) : Type :=
  ∀ i : Fin a.dims.length, Chamber ((a.dims.get i) : ℕ)

/-- Restriction of chambers along `f : a ⟶ b`: each `a`-bead `i` takes its target bead's
chamber `L (blockIdx f i)` restricted along the free-coordinate embedding of
`blockFace f i`. -/
noncomputable def linesRestrict {a b : ChainCat.Obj K} (f : a ⟶ b) (L : LinesObj b) :
    LinesObj a :=
  fun i => (L (blockIdx f.φ.hom i)).restrict
    (faceEmb (blockFace f.φ.hom i)) (faceEmb (blockFace f.φ.hom i)).injective

/-- Any block factorization `ι_i ≫ φ = g ≫ ι_r` computes the same restriction. -/
theorem restrict_factor {ad cd : List ℕ+}
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh) (i : Fin ad.length)
    (r : Fin cd.length) (g : Box.ob ((ad.get i) : ℕ) ⟶ Box.ob ((cd.get r) : ℕ))
    (h : BPSet.serialWedge.ι ad i ≫ φ = yoneda.map g ≫ BPSet.serialWedge.ι cd r)
    (L : ∀ j : Fin cd.length, Chamber ((cd.get j) : ℕ)) :
    (L (blockIdx φ i)).restrict (faceEmb (blockFace φ i)) (faceEmb (blockFace φ i)).injective
      = (L r).restrict (faceEmb g) (faceEmb g).injective := by
  obtain rfl : r = blockIdx φ i := blockIdx_eq_of_factor φ i r g h
  have hg : blockFace φ i = g := by
    apply serialWedge_ι_app_injective cd (blockIdx φ i)
    have hy := congrArg yonedaEquiv ((blockFace_spec φ i).symm.trans h)
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map] at hy
  rw [hg]

/-- Restricting along the identity chain map is the identity. -/
theorem linesRestrict_id {a : ChainCat.Obj K} (L : LinesObj a) :
    linesRestrict (𝟙 a) L = L := by
  funext i
  have h : BPSet.serialWedge.ι a.dims i ≫ 𝟙 ((BPSet.serialWedge a.dims).toPsh)
      = yoneda.map (𝟙 (Box.ob ((a.dims.get i) : ℕ))) ≫ BPSet.serialWedge.ι a.dims i := by
    simp
  calc linesRestrict (𝟙 a) L i
      = (L i).restrict (faceEmb (𝟙 (Box.ob ((a.dims.get i) : ℕ))))
          (faceEmb (𝟙 (Box.ob ((a.dims.get i) : ℕ)))).injective :=
        restrict_factor (𝟙 ((BPSet.serialWedge a.dims).toPsh)) i i
          (𝟙 (Box.ob ((a.dims.get i) : ℕ))) h L
    _ = L i := (L i).restrict_id_of _ (faceEmb_id _)

/-- `linesRestrict (p ≫ q) = linesRestrict p ∘ linesRestrict q`. -/
theorem linesRestrict_comp {a b c : ChainCat.Obj K} (p : a ⟶ b) (q : b ⟶ c)
    (L : LinesObj c) :
    linesRestrict (p ≫ q) L = linesRestrict p (linesRestrict q L) := by
  funext i
  have h : BPSet.serialWedge.ι a.dims i ≫ (p ≫ q).φ.hom
      = yoneda.map (blockFace p.φ.hom i ≫ blockFace q.φ.hom (blockIdx p.φ.hom i))
        ≫ BPSet.serialWedge.ι c.dims (blockIdx q.φ.hom (blockIdx p.φ.hom i)) :=
    blockFace_spec_comp p.φ.hom q.φ.hom i
  calc linesRestrict (p ≫ q) L i
      = (L (blockIdx q.φ.hom (blockIdx p.φ.hom i))).restrict
          (faceEmb (blockFace p.φ.hom i ≫ blockFace q.φ.hom (blockIdx p.φ.hom i)))
          (faceEmb (blockFace p.φ.hom i ≫ blockFace q.φ.hom (blockIdx p.φ.hom i))).injective :=
        restrict_factor (p ≫ q).φ.hom i (blockIdx q.φ.hom (blockIdx p.φ.hom i))
          (blockFace p.φ.hom i ≫ blockFace q.φ.hom (blockIdx p.φ.hom i)) h L
    _ = linesRestrict p (linesRestrict q L) i := by
        simp only [linesRestrict]
        rw [Chamber.restrict_restrict]
        exact Chamber.restrict_congr _ _ _
          (fun x => faceEmb_comp (blockFace p.φ.hom i) (blockFace q.φ.hom (blockIdx p.φ.hom i)) x)

/-- The chamber presheaf `Lines K : (ChainCat.Obj K)ᵒᵖ ⥤ Type`: chains ↦ their refining
chambers, chain maps ↦ restriction. -/
noncomputable def Lines (K : BPSet) : (ChainCat.Obj K)ᵒᵖ ⥤ Type where
  obj X := LinesObj X.unop
  map φ := TypeCat.ofHom (linesRestrict φ.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro L
    rw [TypeCat.ofHom_apply, types_id_apply]
    exact linesRestrict_id L
  map_comp φ ψ := by
    apply ConcreteCategory.hom_ext
    intro L
    rw [TypeCat.ofHom_apply, types_comp_apply, TypeCat.ofHom_apply, TypeCat.ofHom_apply]
    exact linesRestrict_comp ψ.unop φ.unop L

end FinalBraid
