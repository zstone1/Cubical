import CubeChains.Chains.BlockDecomp
import Mathlib.Order.RelClasses

/-!
# Salvetti/Lines — the chamber presheaf `Lines`

`Lines K : (Ch K)ᵒᵖ ⥤ Type` sends a cube chain `a` to the tuple of chambers of its
beads, `∏ᵢ Chamber (a.dims.get i)`, and a chain map to restriction (`linesRestrict`), pulling
each target bead's chamber back along the block data (`blockIdx`/`blockFace`/`faceEmb`,
`Chains/BlockDecomp`).  A `Chamber d` is a strict total order on the `d` directions of `□ᵈ`.
-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChains

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
def LinesObj (a : Ch K) : Type :=
  ∀ i : ChainCat.Bead a, Chamber (ChainCat.beadDim a i)

/-- Restriction of chambers along `f : a ⟶ b`: each `a`-bead `i` takes its target bead's
chamber `L (blockIdx f i)` restricted along the free-coordinate embedding of
`blockFace f i`. -/
noncomputable def linesRestrict {a b : Ch K} (f : a ⟶ b) (L : LinesObj b) :
    LinesObj a :=
  fun i => (L (blockIdx fᵂ i)).restrict
    (faceEmb (blockFace fᵂ i)) (faceEmb (blockFace fᵂ i)).injective

/-- Any block factorization `ι_i ≫ φ = g ≫ ι_r` computes the same restriction. -/
theorem restrict_factor {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length)
    (r : Fin cd.length) (g : ▫((ad.get i) : ℕ) ⟶ ▫((cd.get r) : ℕ))
    (h : ιᵂ ad i ≫ φ = yoneda.map g ≫ ιᵂ cd r)
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
theorem linesRestrict_id {a : Ch K} (L : LinesObj a) :
    linesRestrict (𝟙 a) L = L := by
  funext i
  have h : ιᵂ a.dims i ≫ 𝟙 ((⋁a.dims).toPsh)
      = yoneda.map (𝟙 ▫(ChainCat.beadDim a i)) ≫ ιᵂ a.dims i := by
    simp
  calc linesRestrict (𝟙 a) L i
      = (L i).restrict (faceEmb (𝟙 ▫(ChainCat.beadDim a i)))
          (faceEmb (𝟙 ▫(ChainCat.beadDim a i))).injective :=
        restrict_factor (𝟙 ((⋁a.dims).toPsh)) i i
          (𝟙 ▫(ChainCat.beadDim a i)) h L
    _ = L i := (L i).restrict_id_of _ (faceEmb_id _)

/-- `linesRestrict (p ≫ q) = linesRestrict p ∘ linesRestrict q`. -/
theorem linesRestrict_comp {a b c : Ch K} (p : a ⟶ b) (q : b ⟶ c)
    (L : LinesObj c) :
    linesRestrict (p ≫ q) L = linesRestrict p (linesRestrict q L) := by
  funext i
  have h : ιᵂ a.dims i ≫ (p ≫ q)ᵂ
      = yoneda.map (blockFace pᵂ i ≫ blockFace qᵂ (blockIdx pᵂ i))
        ≫ ιᵂ c.dims (blockIdx qᵂ (blockIdx pᵂ i)) :=
    blockFace_spec_comp pᵂ qᵂ i
  calc linesRestrict (p ≫ q) L i
      = (L (blockIdx qᵂ (blockIdx pᵂ i))).restrict
          (faceEmb (blockFace pᵂ i ≫ blockFace qᵂ (blockIdx pᵂ i)))
          (faceEmb (blockFace pᵂ i ≫ blockFace qᵂ (blockIdx pᵂ i))).injective :=
        restrict_factor (p ≫ q)ᵂ i (blockIdx qᵂ (blockIdx pᵂ i))
          (blockFace pᵂ i ≫ blockFace qᵂ (blockIdx pᵂ i)) h L
    _ = linesRestrict p (linesRestrict q L) i := by
        simp only [linesRestrict]
        rw [Chamber.restrict_restrict]
        exact Chamber.restrict_congr _ _ _
          (fun x => faceEmb_comp (blockFace pᵂ i) (blockFace qᵂ (blockIdx pᵂ i)) x)

/-- The chamber presheaf `Lines K : (Ch K)ᵒᵖ ⥤ Type`: chains ↦ their refining
chambers, chain maps ↦ restriction. -/
noncomputable def Lines (K : BPSet) : (Ch K)ᵒᵖ ⥤ Type where
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

end CubeChains
