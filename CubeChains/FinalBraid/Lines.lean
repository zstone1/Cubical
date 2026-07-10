import CubeChains.Chains.Category
import CubeChains.Chains.WedgeMap
import CubeChains.Chains.CubeNonSelfLinked
import Mathlib.Order.RelClasses

/-!
# FinalBraid/Lines — the chamber presheaf `Lines`

The **chamber presheaf** `Lines K : (ChainCat.Obj K)ᵒᵖ ⥤ Type` on the cube-chain category
(`Chains/Category.lean`). A **chamber** of the standard cube `□ᵈ` (`Chamber d`) is a finest
chain of the Boolean lattice `{0,1}ᵈ`, encoded as a strict total order on the `d` coordinate
directions; there are `d!` of them. `Lines K` sends a chain `a` to the tuple of chambers
`LinesObj a = ∏_{beads i} Chamber (a.dims.get i)` and a chain map to restriction
(`linesRestrict`), pulling each target bead's chamber back along the block data
(`blockIdx`/`blockFace`) of the wedge map.

**Layer:** FinalBraid.  **Imports:** `Chains/Category`, `Chains/WedgeMap`,
`Chains/CubeNonSelfLinked`, mathlib.
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

/-! ### The free-coordinate embedding of a cube face

A `k`-face `incl : □ᵏ ⟶ □ᵐ` has `k` free (`none`/star) coordinates;
`faceEmb incl : Fin k ↪o Fin m` enumerates them.  Chambers pull back along it. -/

/-- The order embedding of the free coordinates of a cube face `incl : □ᵏ ⟶ □ᵐ`. -/
noncomputable def faceEmb {k m : ℕ} (incl : Box.ob k ⟶ Box.ob m) : Fin k ↪o Fin m :=
  nones (ev incl)

/-- `nones` of the top cell is the identity embedding. -/
theorem nones_topCell (k : ℕ) (x : Fin k) : nones (topCell k) x = x := by
  have h : (id : Fin k → Fin k) = nones (topCell k) :=
    Finset.orderEmbOfFin_unique (topCell k).prop
      (fun y => by simp [mem_noneSet, topCell]) strictMono_id
  exact (congrFun h x).symm

/-- The free-coordinate embedding of the identity face is the identity. -/
theorem faceEmb_id (k : ℕ) (x : Fin k) : faceEmb (𝟙 (Box.ob k)) x = x := by
  have h1 : ev (𝟙 (Box.ob k)) = topCell k := by
    have e : (𝟙 (Box.ob k) : Box.ob k ⟶ Box.ob k) = canonicalMap (topCell k) :=
      (canonicalMap_topCell k).symm
    rw [e]; exact ev_canonicalMap _
  change nones (ev (𝟙 (Box.ob k))) x = x
  rw [h1]; exact nones_topCell k x

/-- `ev` of a composite of cube faces is the iterated-face map of the two sign vectors. -/
theorem ev_comp_app {k e m : ℕ} (p : Box.ob k ⟶ Box.ob e) (q : Box.ob e ⟶ Box.ob m) :
    ev (p ≫ q) = app (K := stdPre m) (ev q) (ev p) :=
  (ev_comp p q).trans (app_unique q rfl (ev p))

/-- `faceEmb (p ≫ q) = faceEmb q ∘ faceEmb p`. -/
theorem faceEmb_comp {k e m : ℕ} (p : Box.ob k ⟶ Box.ob e) (q : Box.ob e ⟶ Box.ob m)
    (x : Fin k) : faceEmb (p ≫ q) x = faceEmb q (faceEmb p x) := by
  change nones (ev (p ≫ q)) x
    = nones (ev q) (nones (ev p) x)
  rw [ev_comp_app p q]
  exact CubeChain.nones_app (ev q) (ev p) x

/-- `faceEmb` of the `eqToHom` of a dimension equality is the `Fin` cast: an `eqToHom` between
boxes has no free coordinates to permute. -/
theorem faceEmb_eqToHom {k k' : ℕ} (h : k = k') (x : Fin k) :
    faceEmb (eqToHom (congrArg Box.ob h)) x = Fin.cast h x := by
  subst h
  simp only [Fin.cast_eq_self]
  exact faceEmb_id k x

/-- Value form of `faceEmb_eqToHom`, for a box equality rather than a dimension equality. -/
theorem faceEmb_eqToHom_val {k k' : ℕ} (h : Box.ob k = Box.ob k') (x : Fin k) :
    (faceEmb (eqToHom h) x).1 = x.1 := by
  obtain rfl : k = k' := congrArg Box.dim h
  rw [eqToHom_refl, faceEmb_id]

/-! ### Block data of a wedge map

`wedgeMap_block` factors a source bead's inclusion `ι_i ≫ φ` through a unique target
block (`blockIdx φ i`) via a `Box`-face (`blockFace φ i`). -/

/-- The **target block index** of source bead `i` under a wedge map `φ`: the unique
`cd`-block `r` such that `ι_i ≫ φ` factors through block `r`. -/
noncomputable def blockIdx {ad cd : List ℕ+}
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh) (i : Fin ad.length) :
    Fin cd.length :=
  (wedgeMap_block φ i).choose

/-- The **face inclusion** of source bead `i` under a wedge map `φ`: the `Box`
morphism `□^{ad.get i} ⟶ □^{cd.get (blockIdx φ i)}` witnessing that `ι_i ≫ φ` lands
in a face of the target block. -/
noncomputable def blockFace {ad cd : List ℕ+}
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh) (i : Fin ad.length) :
    Box.ob ((ad.get i) : ℕ) ⟶ Box.ob ((cd.get (blockIdx φ i)) : ℕ) :=
  (wedgeMap_block φ i).choose_spec.choose

/-- Defining factorization of the block data (`r := blockIdx φ i`):

      □^{ad.get i}  --ι_i-->  □^∨(ad)
           |                     |
   blockFace φ i                 φ
           v                     v
      □^{cd.get r}  --ι_r-->  □^∨(cd)
-/
theorem blockFace_spec {ad cd : List ℕ+}
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh) (i : Fin ad.length) :
    BPSet.serialWedge.ι ad i ≫ φ
      = yoneda.map (blockFace φ i) ≫ BPSet.serialWedge.ι cd (blockIdx φ i) :=
  (wedgeMap_block φ i).choose_spec.choose_spec

/-- If `ι_i ≫ φ = g ≫ ι_r` for any face `g`, then `r = blockIdx φ i`. -/
theorem blockIdx_eq_of_factor {ad cd : List ℕ+}
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh) (i : Fin ad.length)
    (r : Fin cd.length) (g : Box.ob ((ad.get i) : ℕ) ⟶ Box.ob ((cd.get r) : ℕ))
    (h : BPSet.serialWedge.ι ad i ≫ φ = yoneda.map g ≫ BPSet.serialWedge.ι cd r) :
    r = blockIdx φ i := by
  refine serialWedge_block_unique cd (ad.get i).2 r (blockIdx φ i)
    (yonedaEquiv (BPSet.serialWedge.ι ad i ≫ φ))
    ⟨yonedaEquiv (yoneda.map g),
      (yonedaEquiv_comp (yoneda.map g) (BPSet.serialWedge.ι cd r)).symm.trans
        (congrArg yonedaEquiv h.symm)⟩
    ⟨yonedaEquiv (yoneda.map (blockFace φ i)),
      (yonedaEquiv_comp (yoneda.map (blockFace φ i))
        (BPSet.serialWedge.ι cd (blockIdx φ i))).symm.trans
        (congrArg yonedaEquiv (blockFace_spec φ i).symm)⟩

/-- The two-step block factorization of `ι_i ≫ (φ ≫ ψ)` (`r := blockIdx φ i`, `r' := blockIdx ψ r`):

      □^{ad.get i}   --ι-->  □^∨(ad)
           |                    |
   blockFace φ i                φ
           v                    v
      □^{bd.get r}   --ι-->  □^∨(bd)
           |                    |
   blockFace ψ r                ψ
           v                    v
      □^{cd.get r'}  --ι-->  □^∨(cd)
-/
theorem blockFace_spec_comp {ad bd cd : List ℕ+}
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge bd).toPsh)
    (ψ : (BPSet.serialWedge bd).toPsh ⟶ (BPSet.serialWedge cd).toPsh) (i : Fin ad.length) :
    BPSet.serialWedge.ι ad i ≫ (φ ≫ ψ)
      = yoneda.map (blockFace φ i ≫ blockFace ψ (blockIdx φ i))
        ≫ BPSet.serialWedge.ι cd (blockIdx ψ (blockIdx φ i)) :=
  calc BPSet.serialWedge.ι ad i ≫ (φ ≫ ψ)
      = (BPSet.serialWedge.ι ad i ≫ φ) ≫ ψ := (Category.assoc _ _ _).symm
    _ = (yoneda.map (blockFace φ i) ≫ BPSet.serialWedge.ι bd (blockIdx φ i)) ≫ ψ :=
        congrArg (· ≫ ψ) (blockFace_spec φ i)
    _ = yoneda.map (blockFace φ i) ≫ (BPSet.serialWedge.ι bd (blockIdx φ i) ≫ ψ) :=
        Category.assoc _ _ _
    _ = yoneda.map (blockFace φ i) ≫ (yoneda.map (blockFace ψ (blockIdx φ i))
          ≫ BPSet.serialWedge.ι cd (blockIdx ψ (blockIdx φ i))) :=
        congrArg (yoneda.map (blockFace φ i) ≫ ·) (blockFace_spec ψ (blockIdx φ i))
    _ = (yoneda.map (blockFace φ i) ≫ yoneda.map (blockFace ψ (blockIdx φ i)))
          ≫ BPSet.serialWedge.ι cd (blockIdx ψ (blockIdx φ i)) := (Category.assoc _ _ _).symm
    _ = yoneda.map (blockFace φ i ≫ blockFace ψ (blockIdx φ i))
          ≫ BPSet.serialWedge.ι cd (blockIdx ψ (blockIdx φ i)) :=
        congrArg (· ≫ BPSet.serialWedge.ι cd (blockIdx ψ (blockIdx φ i)))
          (yoneda.map_comp (blockFace φ i) (blockFace ψ (blockIdx φ i))).symm

/-- `blockIdx (φ ≫ ψ) i = blockIdx ψ (blockIdx φ i)`. -/
theorem blockIdx_comp {ad bd cd : List ℕ+}
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge bd).toPsh)
    (ψ : (BPSet.serialWedge bd).toPsh ⟶ (BPSet.serialWedge cd).toPsh) (i : Fin ad.length) :
    blockIdx (φ ≫ ψ) i = blockIdx ψ (blockIdx φ i) :=
  (blockIdx_eq_of_factor (φ ≫ ψ) i (blockIdx ψ (blockIdx φ i))
    (blockFace φ i ≫ blockFace ψ (blockIdx φ i)) (blockFace_spec_comp φ ψ i)).symm

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
