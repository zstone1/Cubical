import CubeChains.Chains.WedgeMonoidal
import CubeChains.Chains.SegalProd
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat

/-!
# Chains/WedgeLaxMonoidal — `chFunctor` is lax monoidal `(WedgeBP, ∨) ⥤ (Cat, ×)`

The tensorator is `chConcat` (unconditional); the unit comparison is `chUnit`.  Strong monoidal
(`chSegal`) holds only under `AdmitsAltitude`, so globally this is lax.
-/

open CategoryTheory MonoidalCategory ChainCat BPSet

namespace ChainCat

attribute [local instance] ChainCat.wedgeMonoidal

/-- Two chain morphisms are `HEq` when their objects agree and their underlying wedge maps do. -/
theorem chain_hom_hext {K : BPSet} {a a' b b' : Ch K} (ha : a = a') (hb : b = b')
    {f : a ⟶ b} {g : a' ⟶ b'} (hφ : HEq (Hom.φ f) (Hom.φ g)) : HEq f g := by
  subst ha; subst hb
  exact heq_of_eq (hom_ext' (eq_of_heq hφ))

/-- Concatenating on the left with the empty chain leaves a morphism's wedge map unchanged
(the left factor `□⁰` contributes no dimensions, so `[] ++ b.dims = b.dims`). -/
theorem concatHomφ_nil_left {K : BPSet} {b b' : Ch K} (g : b ⟶ b') :
    concatHomφ (𝟙 (default : Ch (□0))) g = Hom.φ g := by
  apply hom_ext
  change (Hom.φ g).hom ≫ wedgeInclR (default : Ch (□0)).dims b'.dims = (Hom.φ g).hom
  rw [show wedgeInclR (default : Ch (□0)).dims b'.dims = 𝟙 (⋁b'.dims).toPsh from rfl]
  erw [Category.comp_id]

/-- `.hom` of an `eqToHom` in `BPSet` is the `eqToHom` on underlying presheaves. -/
theorem bpset_eqToHom_hom' {K L : BPSet} (h : K = L) :
    (eqToHom h).hom = eqToHom (congrArg BPSet.toPsh h) := by subst h; rfl

/-- The final-vertex inclusion transports along an `⋁`-reindexing `eqToHom`. -/
theorem finalVertex_eqToHom {d d' : List ℕ+} (hd : d = d') :
    (⋁d).finalVertex ≫ eqToHom (congrArg (fun l => (⋁l).toPsh) hd) = (⋁d').finalVertex := by
  subst hd; simp

/-- Left inclusion commutes with the `⋁`-reindexing of the second wedge factor. -/
theorem inl_reindex (n : ℕ+) {d d' : List ℕ+} (hd : d = d') :
    Glue.inl (□(n : ℕ)).finalVertex (⋁d').initVertex
      = Glue.inl (□(n : ℕ)).finalVertex (⋁d).initVertex
        ≫ eqToHom (congrArg (fun l => (⋁(n :: l)).toPsh) hd) := by
  subst hd; exact (Category.comp_id _).symm

/-- Right inclusion commutes with the `⋁`-reindexing of the second wedge factor. -/
theorem inr_reindex (n : ℕ+) {d d' : List ℕ+} (hd : d = d') :
    eqToHom (congrArg (fun l => (⋁l).toPsh) hd)
        ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁d').initVertex
      = Glue.inr (□(n : ℕ)).finalVertex (⋁d).initVertex
        ≫ eqToHom (congrArg (fun l => (⋁(n :: l)).toPsh) hd) := by
  subst hd; exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- `wedgeInclR da []` is the final-vertex inclusion of `⋁(da ++ [])`. -/
theorem wedgeInclR_nil (da : List ℕ+) :
    wedgeInclR da ([] : List ℕ+) = (⋁(da ++ ([] : List ℕ+))).finalVertex := by
  have h := wedgeInclR_finalVertex da ([] : List ℕ+)
  rw [show (⋁([] : List ℕ+)).finalVertex = 𝟙 (⋁([] : List ℕ+)).toPsh from
    cube0_finalVertex_eq_id] at h
  erw [Category.id_comp] at h
  exact h

/-- `wedgeInclL da []` is the `append_nil` reindexing (the empty right factor adds no blocks). -/
theorem wedgeInclL_nil : ∀ da : List ℕ+,
    wedgeInclL da ([] : List ℕ+)
      = eqToHom (congrArg (fun l => (⋁l).toPsh) (List.append_nil da).symm)
  | [] => by
      rw [show wedgeInclL ([] : List ℕ+) ([] : List ℕ+) = (⋁([] : List ℕ+)).initVertex from rfl]
      erw [cube0_initVertex_eq_id]
      rfl
  | n :: da' => by
      rw [wedgeInclL_cons]
      refine Glue.hom_ext ?_ ?_
      · erw [Glue.inl_desc]
        exact inl_reindex n (List.append_nil da').symm
      · erw [Glue.inr_desc, wedgeInclL_nil da']
        exact inr_reindex n (List.append_nil da').symm

/-- Concatenating on the right with the empty chain leaves a morphism's wedge map unchanged, up to
the `append_nil` reindexing (`HEq` because the domain/codomain types differ). -/
theorem concatHomφ_nil_right {K : BPSet} {b b' : Ch K} (g : b ⟶ b') :
    HEq (Hom.φ g) (concatHomφ g (𝟙 (default : Ch (□0)))) := by
  refine HEq.symm ((conj_eqToHom_iff_heq (concatHomφ g (𝟙 (default : Ch (□0)))) (Hom.φ g)
    (congrArg BPSet.serialWedge (List.append_nil b.dims))
    (congrArg BPSet.serialWedge (List.append_nil b'.dims))).mp ?_)
  apply hom_ext
  rw [comp_hom, comp_hom, bpset_eqToHom_hom', bpset_eqToHom_hom']
  refine ChainCat.concat_hom_ext b.dims ([] : List ℕ+) _ _ ?_ ?_
  · erw [concatHomφ_inclL, wedgeInclL_nil b'.dims, wedgeInclL_nil b.dims]
    simp
  · erw [concatHomφ_inclR, wedgeInclR_nil b'.dims, wedgeInclR_nil b.dims]
    simp only [id_φ, id_hom, Category.id_comp]
    erw [← Category.assoc, finalVertex_eqToHom (List.append_nil b.dims), ← Category.assoc,
      finalVertex_comp_hom, finalVertex_eqToHom (List.append_nil b'.dims).symm]

/-! ### Associativity regrouping for the half-inclusions

The reindexing iso `⋁((da++db)++dc) ≅ ⋁(da++(db++dc))` sends each block-inclusion of the
left grouping to the corresponding one of the right grouping.  These `serialWedgeAssoc_*`
lemmas feed the `concatHomφ` associativity `HEq` in the lax-monoidal `associativity` field. -/

/-- The reindexing presheaf iso across `List.append_assoc`. -/
def serialWedgeAssoc (da db dc : List ℕ+) :
    (⋁((da ++ db) ++ dc)).toPsh ⟶ (⋁(da ++ (db ++ dc))).toPsh :=
  eqToHom (congrArg (fun l => (⋁l).toPsh) (List.append_assoc da db dc))

/-- `serialWedgeAssoc` commutes with the head-cube left inclusion. -/
theorem serialWedgeAssoc_inl (n : ℕ+) (da db dc : List ℕ+) :
    Glue.inl (□(n : ℕ)).finalVertex (⋁((da ++ db) ++ dc)).initVertex
        ≫ serialWedgeAssoc (n :: da) db dc
      = Glue.inl (□(n : ℕ)).finalVertex (⋁(da ++ (db ++ dc))).initVertex :=
  (inl_reindex n (List.append_assoc da db dc)).symm

/-- `serialWedgeAssoc` commutes with the head-cube right inclusion. -/
theorem serialWedgeAssoc_inr (n : ℕ+) (da db dc : List ℕ+) :
    Glue.inr (□(n : ℕ)).finalVertex (⋁((da ++ db) ++ dc)).initVertex
        ≫ serialWedgeAssoc (n :: da) db dc
      = serialWedgeAssoc da db dc
        ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁(da ++ (db ++ dc))).initVertex :=
  (inr_reindex n (List.append_assoc da db dc)).symm

/-- Regrouping (`a`-block): the left inclusion of `da` into `da++(db++dc)` factors through the
left grouping and the reindex. -/
theorem wedgeInclL_append_assoc : ∀ (da db dc : List ℕ+),
    wedgeInclL da db ≫ wedgeInclL (da ++ db) dc ≫ serialWedgeAssoc da db dc
      = wedgeInclL da (db ++ dc)
  | [], db, dc => by
      change (⋁db).initVertex ≫ wedgeInclL db dc ≫ serialWedgeAssoc ([] : List ℕ+) db dc
        = (⋁(db ++ dc)).initVertex
      rw [show serialWedgeAssoc ([] : List ℕ+) db dc = 𝟙 _ from rfl]
      erw [Category.comp_id]
      exact wedgeInclL_initVertex db dc
  | n :: da', db, dc => by
      change wedgeInclL (n :: da') db
          ≫ wedgeInclL (n :: (da' ++ db)) dc ≫ serialWedgeAssoc (n :: da') db dc
        = wedgeInclL (n :: da') (db ++ dc)
      have hIH := wedgeInclL_append_assoc da' db dc
      have hhead1 : Glue.inl (□(n : ℕ)).finalVertex (⋁da').initVertex
            ≫ wedgeInclL (n :: da') db
          = Glue.inl (□(n : ℕ)).finalVertex (⋁(da' ++ db)).initVertex := by
        rw [wedgeInclL_cons]; exact Glue.inl_desc _ _ _
      have htail1 : Glue.inr (□(n : ℕ)).finalVertex (⋁da').initVertex
            ≫ wedgeInclL (n :: da') db
          = wedgeInclL da' db ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁(da' ++ db)).initVertex := by
        rw [wedgeInclL_cons]; exact Glue.inr_desc _ _ _
      have hhead2 : Glue.inl (□(n : ℕ)).finalVertex (⋁(da' ++ db)).initVertex
            ≫ wedgeInclL (n :: (da' ++ db)) dc
          = Glue.inl (□(n : ℕ)).finalVertex (⋁((da' ++ db) ++ dc)).initVertex := by
        rw [wedgeInclL_cons]; exact Glue.inl_desc _ _ _
      have htail2 : Glue.inr (□(n : ℕ)).finalVertex (⋁(da' ++ db)).initVertex
            ≫ wedgeInclL (n :: (da' ++ db)) dc
          = wedgeInclL (da' ++ db) dc
            ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁((da' ++ db) ++ dc)).initVertex := by
        rw [wedgeInclL_cons]; exact Glue.inr_desc _ _ _
      have hheadR : Glue.inl (□(n : ℕ)).finalVertex (⋁da').initVertex
            ≫ wedgeInclL (n :: da') (db ++ dc)
          = Glue.inl (□(n : ℕ)).finalVertex (⋁(da' ++ (db ++ dc))).initVertex := by
        rw [wedgeInclL_cons]; exact Glue.inl_desc _ _ _
      have htailR : Glue.inr (□(n : ℕ)).finalVertex (⋁da').initVertex
            ≫ wedgeInclL (n :: da') (db ++ dc)
          = wedgeInclL da' (db ++ dc)
            ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁(da' ++ (db ++ dc))).initVertex := by
        rw [wedgeInclL_cons]; exact Glue.inr_desc _ _ _
      refine Glue.hom_ext ?_ ?_
      · erw [reassoc_of% hhead1, reassoc_of% hhead2, serialWedgeAssoc_inl]
        exact hheadR.symm
      · erw [reassoc_of% htail1, Category.assoc, reassoc_of% htail2, Category.assoc,
          serialWedgeAssoc_inr, reassoc_of% hIH]
        exact htailR.symm

/-- Regrouping (`b`-block): the right inclusion of `db` into `da++db`, pushed through the left
inclusion into `dc` and reindexed, is the middle-block inclusion of `da++(db++dc)`. -/
theorem wedgeInclR_wedgeInclL_append_assoc : ∀ (da db dc : List ℕ+),
    wedgeInclR da db ≫ wedgeInclL (da ++ db) dc ≫ serialWedgeAssoc da db dc
      = wedgeInclL db dc ≫ wedgeInclR da (db ++ dc)
  | [], db, dc => by
      change 𝟙 (⋁db).toPsh ≫ wedgeInclL db dc ≫ serialWedgeAssoc ([] : List ℕ+) db dc
        = wedgeInclL db dc ≫ 𝟙 (⋁(db ++ dc)).toPsh
      rw [show serialWedgeAssoc ([] : List ℕ+) db dc = 𝟙 _ from rfl]
      erw [Category.id_comp, Category.comp_id]
  | n :: da', db, dc => by
      change wedgeInclR (n :: da') db
          ≫ wedgeInclL (n :: (da' ++ db)) dc ≫ serialWedgeAssoc (n :: da') db dc
        = wedgeInclL db dc ≫ wedgeInclR (n :: da') (db ++ dc)
      have hIH := wedgeInclR_wedgeInclL_append_assoc da' db dc
      have hconsR : wedgeInclR (n :: da') db
          = wedgeInclR da' db ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁(da' ++ db)).initVertex := rfl
      have hconsR2 : wedgeInclR (n :: da') (db ++ dc)
          = wedgeInclR da' (db ++ dc)
            ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁(da' ++ (db ++ dc))).initVertex := rfl
      have hstep : Glue.inr (□(n : ℕ)).finalVertex (⋁(da' ++ db)).initVertex
            ≫ wedgeInclL (n :: (da' ++ db)) dc
          = wedgeInclL (da' ++ db) dc
            ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁((da' ++ db) ++ dc)).initVertex := by
        rw [wedgeInclL_cons]; exact Glue.inr_desc _ _ _
      rw [hconsR, hconsR2]
      erw [Category.assoc, reassoc_of% hstep, Category.assoc, serialWedgeAssoc_inr,
        reassoc_of% hIH]
      rfl

/-- Regrouping (`c`-block): the right inclusion of `dc` into `(da++db)++dc`, reindexed, is the
last-block inclusion of `da++(db++dc)`. -/
theorem wedgeInclR_append_assoc : ∀ (da db dc : List ℕ+),
    wedgeInclR (da ++ db) dc ≫ serialWedgeAssoc da db dc
      = wedgeInclR db dc ≫ wedgeInclR da (db ++ dc)
  | [], db, dc => by
      change wedgeInclR db dc ≫ serialWedgeAssoc ([] : List ℕ+) db dc
        = wedgeInclR db dc ≫ 𝟙 (⋁(db ++ dc)).toPsh
      rw [show serialWedgeAssoc ([] : List ℕ+) db dc = 𝟙 _ from rfl]
      erw [Category.comp_id]
  | n :: da', db, dc => by
      change wedgeInclR (n :: (da' ++ db)) dc ≫ serialWedgeAssoc (n :: da') db dc
        = wedgeInclR db dc ≫ wedgeInclR (n :: da') (db ++ dc)
      have hIH := wedgeInclR_append_assoc da' db dc
      have hcons1 : wedgeInclR (n :: (da' ++ db)) dc
          = wedgeInclR (da' ++ db) dc
            ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁((da' ++ db) ++ dc)).initVertex := rfl
      have hcons2 : wedgeInclR (n :: da') (db ++ dc)
          = wedgeInclR da' (db ++ dc)
            ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁(da' ++ (db ++ dc))).initVertex := rfl
      rw [hcons1, hcons2]
      erw [Category.assoc, serialWedgeAssoc_inr, reassoc_of% hIH]
      rfl

/-- `serialWedgeAssoc` cancels its inverse reindex. -/
theorem serialWedgeAssoc_comp_symm (da db dc : List ℕ+) :
    serialWedgeAssoc da db dc
        ≫ eqToHom (congrArg (fun l => (⋁l).toPsh) (List.append_assoc da db dc)).symm = 𝟙 _ := by
  unfold serialWedgeAssoc
  rw [eqToHom_trans, eqToHom_refl]

set_option maxHeartbeats 800000 in
-- Three block-legs, each a chain of `erw` over the sealed `Glue`/`serialWedge` maps against the
-- `wedgeInclL/R` regrouping lemmas; the defeq matching is heavy.
/-- **Associativity of the chain-morphism concatenation**, across the `List.append_assoc`
reindexing.  This is the morphism-level twin of the object associativity; the wedge associator
`wedge2AssocFwd` has already dropped out (`pushforward` preserves `.φ`), leaving pure
`concatHomφ` regrouping. -/
theorem concatHomφ_assoc {X Y Z : BPSet} {a a' : Ch X} {b b' : Ch Y} {c c' : Ch Z}
    (fa : a ⟶ a') (fb : b ⟶ b') (fc : c ⟶ c') :
    HEq (concatHomφ ((chConcat X Y).map ((fa, fb) : (a, b) ⟶ (a', b'))) fc)
        (concatHomφ fa ((chConcat Y Z).map ((fb, fc) : (b, c) ⟶ (b', c')))) := by
  refine (conj_eqToHom_iff_heq
    (concatHomφ ((chConcat X Y).map ((fa, fb) : (a, b) ⟶ (a', b'))) fc)
    (concatHomφ fa ((chConcat Y Z).map ((fb, fc) : (b, c) ⟶ (b', c'))))
    (congrArg BPSet.serialWedge (List.append_assoc a.dims b.dims c.dims))
    (congrArg BPSet.serialWedge (List.append_assoc a'.dims b'.dims c'.dims))).mp ?_
  apply hom_ext
  rw [comp_hom, comp_hom, bpset_eqToHom_hom', bpset_eqToHom_hom']
  -- Normalise the two `eqToHom`s to `serialWedgeAssoc` and its inverse (defeq, proof-irrelevant).
  change (concatHomφ ((chConcat X Y).map ((fa, fb) : (a, b) ⟶ (a', b'))) fc).hom
      = serialWedgeAssoc a.dims b.dims c.dims
        ≫ (concatHomφ fa ((chConcat Y Z).map ((fb, fc) : (b, c) ⟶ (b', c')))).hom
        ≫ eqToHom (congrArg (fun l => (⋁l).toPsh) (List.append_assoc a'.dims b'.dims c'.dims)).symm
  refine concat_hom_ext (a.dims ++ b.dims) c.dims _ _ ?_ ?_
  · refine concat_hom_ext a.dims b.dims _ _ ?_ ?_
    · -- `a`-block: both sides reduce to `faᵂ ≫ wedgeInclL a' b' ≫ wedgeInclL (a'++b') c'`
      trans faᵂ ≫ wedgeInclL a'.dims b'.dims ≫ wedgeInclL (a'.dims ++ b'.dims) c'.dims
      · erw [concatHomφ_inclL, reassoc_of% concatHomφ_inclL]; rfl
      · symm
        erw [reassoc_of% wedgeInclL_append_assoc, reassoc_of% concatHomφ_inclL,
          ← reassoc_of% wedgeInclL_append_assoc, serialWedgeAssoc_comp_symm, Category.comp_id]
    · -- `b`-block: both sides reduce to `fbᵂ ≫ wedgeInclR a' b' ≫ wedgeInclL (a'++b') c'`
      trans fbᵂ ≫ wedgeInclR a'.dims b'.dims ≫ wedgeInclL (a'.dims ++ b'.dims) c'.dims
      · erw [concatHomφ_inclL, reassoc_of% concatHomφ_inclR]; rfl
      · symm
        erw [reassoc_of% wedgeInclR_wedgeInclL_append_assoc, reassoc_of% concatHomφ_inclR,
          reassoc_of% concatHomφ_inclL, ← reassoc_of% wedgeInclR_wedgeInclL_append_assoc,
          serialWedgeAssoc_comp_symm, Category.comp_id]
  · -- `c`-block: both sides reduce to `fcᵂ ≫ wedgeInclR (a'++b') c'`
    trans fcᵂ ≫ wedgeInclR (a'.dims ++ b'.dims) c'.dims
    · erw [concatHomφ_inclR]; rfl
    · symm
      erw [reassoc_of% wedgeInclR_append_assoc, reassoc_of% concatHomφ_inclR,
        reassoc_of% concatHomφ_inclR, ← reassoc_of% wedgeInclR_append_assoc,
        serialWedgeAssoc_comp_symm, Category.comp_id]

end ChainCat

/-- `chFunctor`, re-sourced to the wedge-monoidal alias. -/
def chFunctorW : WedgeBP ⥤ Cat := chFunctor

/-! ### Lax-monoidal coherence laws for `chFunctorW`

The fields of the `LaxMonoidal` instance below, each extracted so the instance is a thin assembly.
The tensorator is `μ X Y = chConcat X Y`, the unit `ε` is the terminal chain; the squares are
checked object-wise (`Cat.ext` + `Functor.hext`), the associativity via `concatHomφ_assoc`. -/

/-- Tensorator naturality in the left factor. -/
theorem chConcat_μ_natural_left {X Y : WedgeBP} (f : X ⟶ Y) (X' : WedgeBP) :
    chFunctorW.map f ▷ chFunctorW.obj X' ≫ (chConcat Y X').toCatHom
      = (chConcat X X').toCatHom ≫ chFunctorW.map (f ▷ X') := by
  apply Cat.ext
  have hob : ∀ ax : Ch X × Ch X',
      (chConcat Y X').obj (⟨ax.1.dims, ax.1.map ≫ f⟩, ax.2)
        = (pushforward (f ▷ X')).obj ((chConcat X X').obj ax) := by
    intro ⟨a, x⟩
    refine congrArg (ChainCat.Obj.mk (a.dims ++ x.dims)) ?_
    apply hom_ext
    change (concatChainMap Y X' ⟨a.dims, a.map ≫ f⟩ x).hom
      = (concatChainMap X X' a x).hom ≫ ChainCat.wedge2MapPsh f (𝟙 X')
    refine ChainCat.concat_hom_ext a.dims x.dims _ _ ?_ ?_
    · rw [ChainCat.concatChainMap_inclL Y X' ⟨a.dims, a.map ≫ f⟩ x]
      erw [← Category.assoc]
      rw [ChainCat.concatChainMap_inclL X X' a x]
      change (a.map ≫ f).hom ≫ Glue.inl Y.finalVertex X'.initVertex
        = (a.map.hom ≫ Glue.inl X.finalVertex X'.initVertex) ≫ ChainCat.wedge2MapPsh f (𝟙 X')
      rw [comp_hom]
      erw [Category.assoc, Category.assoc, ChainCat.wedge2MapPsh_inl]
      rfl
    · rw [ChainCat.concatChainMap_inclR Y X' ⟨a.dims, a.map ≫ f⟩ x]
      erw [← Category.assoc]
      rw [ChainCat.concatChainMap_inclR X X' a x]
      change x.map.hom ≫ Glue.inr Y.finalVertex X'.initVertex
        = (x.map.hom ≫ Glue.inr X.finalVertex X'.initVertex) ≫ ChainCat.wedge2MapPsh f (𝟙 X')
      erw [Category.assoc, ChainCat.wedge2MapPsh_inr, id_hom, Category.id_comp]
      rfl
  exact Functor.hext hob (fun ax ax' g => chain_hom_hext (hob ax) (hob ax') HEq.rfl)

/-- Tensorator naturality in the right factor. -/
theorem chConcat_μ_natural_right {X Y : WedgeBP} (X' : WedgeBP) (f : X ⟶ Y) :
    chFunctorW.obj X' ◁ chFunctorW.map f ≫ (chConcat X' Y).toCatHom
      = (chConcat X' X).toCatHom ≫ chFunctorW.map (X' ◁ f) := by
  apply Cat.ext
  have hob : ∀ xa : Ch X' × Ch X,
      (chConcat X' Y).obj (xa.1, ⟨xa.2.dims, xa.2.map ≫ f⟩)
        = (pushforward (X' ◁ f)).obj ((chConcat X' X).obj xa) := by
    intro ⟨x, a⟩
    refine congrArg (ChainCat.Obj.mk (x.dims ++ a.dims)) ?_
    apply hom_ext
    change (concatChainMap X' Y x ⟨a.dims, a.map ≫ f⟩).hom
      = (concatChainMap X' X x a).hom ≫ ChainCat.wedge2MapPsh (𝟙 X') f
    refine ChainCat.concat_hom_ext x.dims a.dims _ _ ?_ ?_
    · rw [ChainCat.concatChainMap_inclL X' Y x ⟨a.dims, a.map ≫ f⟩]
      erw [← Category.assoc]
      rw [ChainCat.concatChainMap_inclL X' X x a]
      change x.map.hom ≫ Glue.inl X'.finalVertex Y.initVertex
        = (x.map.hom ≫ Glue.inl X'.finalVertex X.initVertex) ≫ ChainCat.wedge2MapPsh (𝟙 X') f
      erw [Category.assoc, ChainCat.wedge2MapPsh_inl, id_hom, Category.id_comp]
      rfl
    · rw [ChainCat.concatChainMap_inclR X' Y x ⟨a.dims, a.map ≫ f⟩]
      erw [← Category.assoc]
      rw [ChainCat.concatChainMap_inclR X' X x a]
      change (a.map ≫ f).hom ≫ Glue.inr X'.finalVertex Y.initVertex
        = (a.map.hom ≫ Glue.inr X'.finalVertex X.initVertex) ≫ ChainCat.wedge2MapPsh (𝟙 X') f
      rw [comp_hom]
      erw [Category.assoc, Category.assoc, ChainCat.wedge2MapPsh_inr]
      rfl
  exact Functor.hext hob (fun xa xa' g => chain_hom_hext (hob xa) (hob xa') HEq.rfl)

/-- Associativity of the tensorator. -/
theorem chConcat_associativity (X Y Z : WedgeBP) :
    (chConcat X Y).toCatHom ▷ chFunctorW.obj Z ≫ (chConcat (wedge2 X Y) Z).toCatHom
        ≫ chFunctorW.map (α_ X Y Z).hom
      = (α_ (chFunctorW.obj X) (chFunctorW.obj Y) (chFunctorW.obj Z)).hom
        ≫ chFunctorW.obj X ◁ (chConcat Y Z).toCatHom ≫ (chConcat X (wedge2 Y Z)).toCatHom := by
  apply Cat.ext
  have hob : ∀ (a : Ch X) (b : Ch Y) (c : Ch Z),
      (ChainCat.Obj.mk ((a.dims ++ b.dims) ++ c.dims)
          (concatChainMap (wedge2 X Y) Z ⟨a.dims ++ b.dims, concatChainMap X Y a b⟩ c
            ≫ (α_ X Y Z).hom) : Ch (wedge2 X (wedge2 Y Z)))
        = ChainCat.Obj.mk (a.dims ++ (b.dims ++ c.dims))
            (concatChainMap X (wedge2 Y Z) a ⟨b.dims ++ c.dims, concatChainMap Y Z b c⟩) := by
    intro a b c
    apply ChainCat.Obj.eq_of_wedgeToCubes
    change CubeChain.wedgeToCubes ⟨(a.dims ++ b.dims) ++ c.dims,
        (concatChainMap (wedge2 X Y) Z ⟨a.dims ++ b.dims, concatChainMap X Y a b⟩ c).hom
          ≫ wedge2AssocFwd X Y Z⟩
      = CubeChain.wedgeToCubes ⟨a.dims ++ (b.dims ++ c.dims),
          (concatChainMap X (wedge2 Y Z) a ⟨b.dims ++ c.dims, concatChainMap Y Z b c⟩).hom⟩
    rw [ChainCat.wedgeToCubes_comp,
      ChainCat.wedgeToCubes_concatChainMap (wedge2 X Y) Z
        ⟨a.dims ++ b.dims, concatChainMap X Y a b⟩ c,
      ChainCat.wedgeToCubes_concatChainMap X Y a b,
      ChainCat.wedgeToCubes_concatChainMap X (wedge2 Y Z) a
        ⟨b.dims ++ c.dims, concatChainMap Y Z b c⟩,
      ChainCat.wedgeToCubes_concatChainMap Y Z b c]
    simp only [List.map_append, List.map_map, List.append_assoc]
    refine congr_arg₂ (· ++ ·) ?_ (congr_arg₂ (· ++ ·) ?_ ?_)
    · refine List.map_congr_left fun cube _ => ?_
      obtain ⟨n, v⟩ := cube
      refine Sigma.ext rfl (heq_of_eq ?_)
      have key := congrArg
        (fun m : (X : BPSet).toPsh ⟶ (wedge2 X (wedge2 Y Z)).toPsh => m⟪(n : ℕ)⟫ v)
        (wedge2AssocFwd_inl_inl X Y Z)
      simpa only [NatTrans.comp_app, types_comp_apply, Function.comp_apply,
        ChainCat.inlPush, ChainCat.inrPush] using key
    · refine List.map_congr_left fun cube _ => ?_
      obtain ⟨n, v⟩ := cube
      refine Sigma.ext rfl (heq_of_eq ?_)
      have key := congrArg
        (fun m : (Y : BPSet).toPsh ⟶ (wedge2 X (wedge2 Y Z)).toPsh => m⟪(n : ℕ)⟫ v)
        (wedge2AssocFwd_inr_inl X Y Z)
      simpa only [NatTrans.comp_app, types_comp_apply, Function.comp_apply,
        ChainCat.inlPush, ChainCat.inrPush] using key
    · refine List.map_congr_left fun cube _ => ?_
      obtain ⟨n, v⟩ := cube
      refine Sigma.ext rfl (heq_of_eq ?_)
      have key := congrArg
        (fun m : (Z : BPSet).toPsh ⟶ (wedge2 X (wedge2 Y Z)).toPsh => m⟪(n : ℕ)⟫ v)
        (wedge2AssocFwd_inr X Y Z)
      simpa only [NatTrans.comp_app, types_comp_apply, Function.comp_apply,
        ChainCat.inlPush, ChainCat.inrPush] using key
  refine Functor.hext (fun o => ?_) (fun o o' g => ?_)
  · obtain ⟨⟨a, b⟩, c⟩ := o
    exact hob a b c
  · obtain ⟨⟨a, b⟩, c⟩ := o
    obtain ⟨⟨a', b'⟩, c'⟩ := o'
    obtain ⟨⟨fa, fb⟩, fc⟩ := g
    exact chain_hom_hext (hob a b c) (hob a' b' c') (ChainCat.concatHomφ_assoc fa fb fc)

/-- Left unitality. -/
theorem chConcat_left_unitality (X : WedgeBP) :
    (λ_ (chFunctorW.obj X)).hom
      = (Cat.fromChosenTerminalEquiv.symm (default : Ch (□0))).toCatHom ▷ chFunctorW.obj X
        ≫ (chConcat (𝟙_ WedgeBP) X).toCatHom ≫ chFunctorW.map (λ_ X).hom := by
  apply Cat.ext
  have hob : ∀ tx : ↥(𝟙_ Cat) × Ch X, tx.2
      = (pushforward (λ_ X).hom).obj ((chConcat (□0) X).obj (default, tx.2)) := by
    intro ⟨t, x⟩
    refine congrArg (ChainCat.Obj.mk x.dims) ?_
    apply hom_ext
    rw [comp_hom]
    change x.map.hom
      = (x.map.hom ≫ Glue.inr (□0).finalVertex X.initVertex) ≫ ChainCat.wedge2LeftUnitPsh X
    erw [Category.assoc, ChainCat.wedge2LeftUnitPsh_inr, Category.comp_id]
  refine Functor.hext hob (fun o o' g => chain_hom_hext (hob o) (hob o') ?_)
  exact heq_of_eq (concatHomφ_nil_left g.2).symm

/-- Right unitality. -/
theorem chConcat_right_unitality (X : WedgeBP) :
    (ρ_ (chFunctorW.obj X)).hom
      = chFunctorW.obj X ◁ (Cat.fromChosenTerminalEquiv.symm (default : Ch (□0))).toCatHom
        ≫ (chConcat X (𝟙_ WedgeBP)).toCatHom ≫ chFunctorW.map (ρ_ X).hom := by
  apply Cat.ext
  have hob : ∀ xt : Ch X × ↥(𝟙_ Cat), xt.1
      = (pushforward (ρ_ X).hom).obj ((chConcat X (□0)).obj (xt.1, default)) := by
    intro ⟨x, t⟩
    apply ChainCat.Obj.eq_of_wedgeToCubes
    change CubeChain.wedgeToCubes ⟨x.dims, x.map.hom⟩
      = CubeChain.wedgeToCubes ⟨x.dims ++ (default : Ch (□0)).dims,
          (concatChainMap X (□0) x default).hom ≫ ChainCat.wedge2RightUnitPsh X⟩
    have hnil : CubeChain.wedgeToCubes ⟨(default : Ch (□0)).dims, (default : Ch (□0)).map.hom⟩
        = ([] : List (Σ n : ℕ+, (□0).cells (n : ℕ))) :=
      List.map_eq_nil_iff.mp
        ((CubeChain.wedgeToCubes_dims _ _).trans (obj_cube0_dims_nil default))
    rw [ChainCat.wedgeToCubes_comp, ChainCat.wedgeToCubes_concatChainMap X (□0) x default,
      hnil, List.map_nil, List.append_nil, List.map_map]
    have hid : ∀ c : Σ n : ℕ+, X.cells (n : ℕ),
        ((fun c => ⟨c.1, (ChainCat.wedge2RightUnitPsh X)⟪(c.1 : ℕ)⟫ c.2⟩)
            (ChainCat.inlPush X (□0) c) : Σ n : ℕ+, X.cells (n : ℕ)) = c := by
      intro ⟨n, v⟩
      refine Sigma.ext rfl (heq_of_eq ?_)
      change (ChainCat.wedge2RightUnitPsh X)⟪(n : ℕ)⟫
        ((Glue.inl X.finalVertex (□0).initVertex)⟪(n : ℕ)⟫ v) = v
      have hc : (Glue.inl X.finalVertex (□0).initVertex
            ≫ ChainCat.wedge2RightUnitPsh X)⟪(n : ℕ)⟫ v = (𝟙 X.toPsh)⟪(n : ℕ)⟫ v := by
        erw [ChainCat.wedge2RightUnitPsh_inl]
      simp only [NatTrans.comp_app, types_comp_apply, NatTrans.id_app, types_id_apply] at hc
      exact hc
    exact ((List.map_congr_left fun c _ => hid c).trans (List.map_id _)).symm
  refine Functor.hext hob (fun o o' g => chain_hom_hext (hob o) (hob o') ?_)
  exact ChainCat.concatHomφ_nil_right g.1

instance : chFunctorW.LaxMonoidal where
  ε := (Cat.fromChosenTerminalEquiv.symm (default : Ch (□0))).toCatHom
  μ X Y := (chConcat X Y).toCatHom
  μ_natural_left := chConcat_μ_natural_left
  μ_natural_right := chConcat_μ_natural_right
  associativity := chConcat_associativity
  left_unitality := chConcat_left_unitality
  right_unitality := chConcat_right_unitality
