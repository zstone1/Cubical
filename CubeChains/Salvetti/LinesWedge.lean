import CubeChains.Salvetti.Lines
import CubeChains.Salvetti.Elements
import CubeChains.Chains.SegalProd
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Salvetti/LinesWedge — the wedge → product theorem for `Lines`

For bi-pointed precubical sets `P Q` admitting altitudes, the category of elements of the
chamber presheaf on the wedge splits as a product:

    linesWedgeEquiv : (Lines (wedge2 P Q)).Elements ≌ (Lines P).Elements × (Lines Q).Elements

Built from: the external product `extProd` and its category-of-elements equivalence
`extProdEquiv`; the multiplicativity nat-iso `multIso` (`chConcat.op ⋙ Lines W ≅ Lines P ⊠ Lines Q`,
chambers on a concatenated chain split via `linesSplitEquiv`); base transport along the Segal
equivalence `chSegal` and `prodOpEquiv`.

-/

open CategoryTheory Opposite CubeChain

namespace CategoryTheory.CategoryOfElements

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-! ## The external product of presheaves and its category of elements -/

/-- The **external product** of `F : Cᵒᵖ ⥤ Type` and `G : Dᵒᵖ ⥤ Type`, a functor on `Cᵒᵖ × Dᵒᵖ`
with `(F ⊠ G)(c,d) = F c × G d`. -/
def extProd (F : Cᵒᵖ ⥤ Type w) (G : Dᵒᵖ ⥤ Type w) : Cᵒᵖ × Dᵒᵖ ⥤ Type w where
  obj cd := F.obj cd.1 × G.obj cd.2
  map {X Y} f := TypeCat.ofHom (fun p => (F.map f.1 p.1, G.map f.2 p.2))
  map_id X := by
    apply ConcreteCategory.hom_ext; intro p
    rw [TypeCat.ofHom_apply, types_id_apply]
    exact Prod.ext (by simp) (by simp)
  map_comp {X Y Z} f g := by
    apply ConcreteCategory.hom_ext; intro p
    rw [TypeCat.ofHom_apply, types_comp_apply, TypeCat.ofHom_apply, TypeCat.ofHom_apply]
    exact Prod.ext (by simp) (by simp)

@[simp] theorem extProd_map_apply (F : Cᵒᵖ ⥤ Type w) (G : Dᵒᵖ ⥤ Type w) {X Y : Cᵒᵖ × Dᵒᵖ}
    (f : X ⟶ Y) (p : (extProd F G).obj X) :
    (extProd F G).map f p = (F.map f.1 p.1, G.map f.2 p.2) := rfl

/-- Forward functor of the external-product-of-elements equivalence: split an element of
`(F ⊠ G).Elements` into its two coordinates. -/
@[reducible] def extProdToProd (F : Cᵒᵖ ⥤ Type w) (G : Dᵒᵖ ⥤ Type w) :
    (extProd F G).Elements ⥤ F.Elements × G.Elements where
  obj Z := (⟨Z.1.1, Z.2.1⟩, ⟨Z.1.2, Z.2.2⟩)
  map {Z W} m :=
    (⟨m.1.1, by have h := m.2; rw [extProd_map_apply] at h; exact congrArg (·.1) h⟩,
     ⟨m.1.2, by have h := m.2; rw [extProd_map_apply] at h; exact congrArg (·.2) h⟩)
  map_id Z := by apply Prod.ext <;> · apply CategoryOfElements.ext; rfl
  map_comp {Z W V} m n := by apply Prod.ext <;> · apply CategoryOfElements.ext; rfl

/-- Backward functor of the external-product-of-elements equivalence: merge two coordinates. -/
@[reducible] def extProdOfProd (F : Cᵒᵖ ⥤ Type w) (G : Dᵒᵖ ⥤ Type w) :
    F.Elements × G.Elements ⥤ (extProd F G).Elements where
  obj Z := ⟨(Z.1.1, Z.2.1), (Z.1.2, Z.2.2)⟩
  map {Z W} m := ⟨(m.1.1, m.2.1), by
    rw [extProd_map_apply]; exact Prod.ext m.1.2 m.2.2⟩
  map_id Z := by apply CategoryOfElements.ext; rfl
  map_comp {Z W V} m n := by apply CategoryOfElements.ext; rfl

theorem extProdToProd_obj_ofProd_obj (F : Cᵒᵖ ⥤ Type w) (G : Dᵒᵖ ⥤ Type w)
    (x : F.Elements × G.Elements) :
    (extProdToProd F G).obj ((extProdOfProd F G).obj x) = x := by
  obtain ⟨⟨c, u⟩, ⟨d, v⟩⟩ := x; rfl

instance extProdToProd_faithful (F : Cᵒᵖ ⥤ Type w) (G : Dᵒᵖ ⥤ Type w) :
    (extProdToProd F G).Faithful where
  map_injective {Z W} {m m'} h := by
    have h1 : m.1.1 = m'.1.1 := congrArg (fun p => p.1.val) h
    have h2 : m.1.2 = m'.1.2 := congrArg (fun p => p.2.val) h
    exact Subtype.ext (Prod.ext h1 h2)

instance extProdToProd_full (F : Cᵒᵖ ⥤ Type w) (G : Dᵒᵖ ⥤ Type w) :
    (extProdToProd F G).Full where
  map_surjective {Z W} k :=
    ⟨⟨(k.1.val, k.2.val), by rw [extProd_map_apply]; exact Prod.ext k.1.2 k.2.2⟩,
     by apply Prod.ext <;> · apply CategoryOfElements.ext; rfl⟩

instance extProdToProd_essSurj (F : Cᵒᵖ ⥤ Type w) (G : Dᵒᵖ ⥤ Type w) :
    (extProdToProd F G).EssSurj where
  mem_essImage x :=
    ⟨(extProdOfProd F G).obj x, ⟨eqToIso (extProdToProd_obj_ofProd_obj F G x)⟩⟩

/-- **External product of categories of elements:**
`(F ⊠ G).Elements ≌ F.Elements × G.Elements`. -/
noncomputable def extProdEquiv (F : Cᵒᵖ ⥤ Type w) (G : Dᵒᵖ ⥤ Type w) :
    (extProd F G).Elements ≌ F.Elements × G.Elements :=
  haveI : (extProdToProd F G).IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  (extProdToProd F G).asEquivalence

end CategoryTheory.CategoryOfElements

namespace FinalBraid

open ChainCat BPSet CubeChain

/-! ## The object-level split of chambers over an appended dimension sequence -/

/-- The left inclusion `Fin da.length ↪ Fin (da ++ db).length` (identity on values). -/
def leftEmbed (da db : List ℕ+) (i : Fin da.length) : Fin (da ++ db).length :=
  ⟨i.1, by rw [List.length_append]; omega⟩

/-- The right inclusion `Fin db.length ↪ Fin (da ++ db).length` (shift by `da.length`). -/
def rightEmbed (da db : List ℕ+) (j : Fin db.length) : Fin (da ++ db).length :=
  ⟨j.1 + da.length, by rw [List.length_append]; omega⟩

theorem get_leftEmbed (da db : List ℕ+) (i : Fin da.length) :
    (da ++ db).get (leftEmbed da db i) = da.get i := by
  simp only [List.get_eq_getElem]
  exact (List.getElem_append_left' i.2 db).symm

theorem get_rightEmbed (da db : List ℕ+) (j : Fin db.length) :
    (da ++ db).get (rightEmbed da db j) = db.get j := by
  simp only [List.get_eq_getElem]
  exact (List.getElem_append_right' da j.2).symm

/-- Dimension equality across the left inclusion. -/
theorem dimLeft (da db : List ℕ+) (i : Fin da.length) :
    ((da ++ db).get (leftEmbed da db i) : ℕ) = (da.get i : ℕ) :=
  congrArg (fun p : ℕ+ => (p : ℕ)) (get_leftEmbed da db i)

theorem dimRight (da db : List ℕ+) (j : Fin db.length) :
    ((da ++ db).get (rightEmbed da db j) : ℕ) = (db.get j : ℕ) :=
  congrArg (fun p : ℕ+ => (p : ℕ)) (get_rightEmbed da db j)

theorem dimLeft' (da db : List ℕ+) (i : Fin (da ++ db).length) (h : i.1 < da.length) :
    ((da ++ db).get i : ℕ) = (da.get ⟨i.1, h⟩ : ℕ) := by
  have e : (da ++ db).get i = da.get ⟨i.1, h⟩ := by
    simp only [List.get_eq_getElem]; exact List.getElem_append_left h
  exact congrArg (fun p : ℕ+ => (p : ℕ)) e

theorem mergeIdxLt (da db : List ℕ+) (i : Fin (da ++ db).length) (h : ¬ i.1 < da.length) :
    i.1 - da.length < db.length := by
  have h2 := i.2
  have hlen : (da ++ db).length = da.length + db.length := List.length_append
  omega

theorem dimRight' (da db : List ℕ+) (i : Fin (da ++ db).length) (h : ¬ i.1 < da.length) :
    ((da ++ db).get i : ℕ) = (db.get ⟨i.1 - da.length, mergeIdxLt da db i h⟩ : ℕ) := by
  have e : (da ++ db).get i = db.get ⟨i.1 - da.length, mergeIdxLt da db i h⟩ := by
    simp only [List.get_eq_getElem]; exact List.getElem_append_right (by omega)
  exact congrArg (fun p : ℕ+ => (p : ℕ)) e

/-- The forward split map: a chamber tuple on `da ++ db` restricts to a pair of tuples. -/
def linesSplit (da db : List ℕ+)
    (L : ∀ i : Fin (da ++ db).length, Chamber ((da ++ db).get i : ℕ)) :
    (∀ i : Fin da.length, Chamber ((da.get i : ℕ))) ×
      (∀ j : Fin db.length, Chamber ((db.get j : ℕ))) :=
  (fun i => (L (leftEmbed da db i)).restrict (finCongr (dimLeft da db i).symm)
      (finCongr (dimLeft da db i).symm).injective,
   fun j => (L (rightEmbed da db j)).restrict (finCongr (dimRight da db j).symm)
      (finCongr (dimRight da db j).symm).injective)

/-- The backward merge map. -/
def linesMerge (da db : List ℕ+)
    (LR : (∀ i : Fin da.length, Chamber ((da.get i : ℕ))) ×
      (∀ j : Fin db.length, Chamber ((db.get j : ℕ)))) :
    ∀ i : Fin (da ++ db).length, Chamber ((da ++ db).get i : ℕ) :=
  fun i =>
    if h : i.1 < da.length then
      (LR.1 ⟨i.1, h⟩).restrict (finCongr (dimLeft' da db i h))
        (finCongr (dimLeft' da db i h)).injective
    else
      (LR.2 ⟨i.1 - da.length, mergeIdxLt da db i h⟩).restrict (finCongr (dimRight' da db i h))
        (finCongr (dimRight' da db i h)).injective

/-- Restricting `L k` along a value-preserving reindexing recovers `L i` when `k = i`. -/
theorem restrict_reindex_id {N : ℕ} {φ : Fin N → ℕ} (L : ∀ i, Chamber (φ i))
    {i k : Fin N} (hik : k = i) {g : Fin (φ i) → Fin (φ k)} (hg : Function.Injective g)
    (hgv : ∀ x, (g x).1 = x.1) : (L k).restrict g hg = L i := by
  cases hik
  exact Chamber.restrict_id_of _ _ (fun x => Fin.ext (hgv x))

/-- The object-level chamber split as an equivalence. -/
def linesSplitEquiv (da db : List ℕ+) :
    (∀ i : Fin (da ++ db).length, Chamber ((da ++ db).get i : ℕ)) ≃
      (∀ i : Fin da.length, Chamber ((da.get i : ℕ))) ×
        (∀ j : Fin db.length, Chamber ((db.get j : ℕ))) where
  toFun := linesSplit da db
  invFun := linesMerge da db
  left_inv L := by
    funext i
    by_cases h : i.1 < da.length
    · simp only [linesMerge, dif_pos h, linesSplit, Chamber.restrict_restrict]
      exact Chamber.restrict_id_of _ _ (fun x => Fin.ext (by simp))
    · simp only [linesMerge, dif_neg h, linesSplit, Chamber.restrict_restrict]
      exact restrict_reindex_id L (Fin.ext (by simp only [rightEmbed]; omega)) _
        (fun x => by simp)
  right_inv LR := by
    apply Prod.ext
    · funext i
      have hi : (leftEmbed da db i).1 < da.length := i.2
      simp only [linesSplit, linesMerge, dif_pos hi, Chamber.restrict_restrict]
      exact Chamber.restrict_id_of _ _ (fun x => Fin.ext (by simp))
    · funext j
      have hj : ¬ (rightEmbed da db j).1 < da.length := by
        have : (rightEmbed da db j).1 = j.1 + da.length := rfl
        rw [this]; omega
      simp only [linesSplit, linesMerge, dif_neg hj, Chamber.restrict_restrict]
      exact restrict_reindex_id LR.2 (Fin.ext (by simp only [rightEmbed]; omega)) _
        (fun x => by simp)

open CategoryTheory.Limits

/-- Reindexing a block inclusion along an index equality is a value-preserving `eqToHom`. -/
theorem serialWedge_ι_cast (l : List ℕ+) {i i' : Fin l.length} (h : i = i') :
    BPSet.serialWedge.ι l i
      = yoneda.map (eqToHom (congrArg (fun j => Box.ob ((l.get j : ℕ))) h))
        ≫ BPSet.serialWedge.ι l i' := by
  subst h; simp

/-- `yoneda.map` of a reflexive box `eqToHom` is the identity. -/
@[simp] theorem yoneda_map_eqToHom_self {k : ℕ} (h : Box.ob k = Box.ob k) :
    yoneda.map (eqToHom h) = 𝟙 (yoneda.obj (Box.ob k)) := by
  rw [eqToHom_refl]; exact CategoryTheory.Functor.map_id yoneda (Box.ob k)

/-- A box `eqToHom` (dimensions equal via `hAB`) composes away against `HEq`-equal maps. -/
theorem yoneda_eqToHom_comp_heq {A B : ℕ} (hAB : A = B) (h : Box.ob A = Box.ob B)
    {Z : PrecubicalSet} (f : yoneda.obj (Box.ob B) ⟶ Z) (g : yoneda.obj (Box.ob A) ⟶ Z)
    (hfg : HEq f g) : g = yoneda.map (eqToHom h) ≫ f := by
  subst hAB
  obtain rfl := eq_of_heq hfg
  rw [yoneda_map_eqToHom_self, Category.id_comp]

/-- **Block inclusion across the left append.** -/
theorem ι_wedgeInclL : ∀ (da db : List ℕ+) (i : Fin da.length),
    BPSet.serialWedge.ι da i ≫ wedgeInclL da db
      = yoneda.map (eqToHom (congrArg Box.ob (dimLeft da db i).symm))
        ≫ BPSet.serialWedge.ι (da ++ db) (leftEmbed da db i)
  | [], _, i => i.elim0
  | n :: da', db, i => by
      induction i using Fin.cases with
      | zero =>
          erw [serialWedge_ι_zero, wedgeInclL_cons, pushout.inl_desc]
          rw [show serialWedge.ι ((n :: da') ++ db) (leftEmbed (n :: da') db 0)
                = pushout.inl (BPSet.cube (n : ℕ)).finalVertex
                    (BPSet.serialWedge (da' ++ db)).initVertex
              from serialWedge_ι_zero n (da' ++ db)]
          exact yoneda_eqToHom_comp_heq rfl _ _ _ HEq.rfl
      | succ j =>
          erw [serialWedge_ι_succ, Category.assoc, wedgeInclL_cons, pushout.inr_desc,
            ← Category.assoc, ι_wedgeInclL da' db j, Category.assoc,
            ← serialWedge_ι_succ n (da' ++ db) (leftEmbed da' db j),
            serialWedge_ι_cast ((n :: da') ++ db)
              (show (leftEmbed da' db j).succ = leftEmbed (n :: da') db j.succ by
                apply Fin.ext; simp [leftEmbed, Fin.val_succ])]

/-- **Block inclusion across the right append.** -/
theorem ι_wedgeInclR : ∀ (da db : List ℕ+) (j : Fin db.length),
    BPSet.serialWedge.ι db j ≫ wedgeInclR da db
      = yoneda.map (eqToHom (congrArg Box.ob (dimRight da db j).symm))
        ≫ BPSet.serialWedge.ι (da ++ db) (rightEmbed da db j)
  | [], db, j => by
      erw [show wedgeInclR ([] : List ℕ+) db = 𝟙 _ from rfl, Category.comp_id]
  | n :: da', db, j => by
      erw [show wedgeInclR (n :: da') db = wedgeInclR da' db
            ≫ pushout.inr (BPSet.cube (n : ℕ)).finalVertex
              (BPSet.serialWedge (da' ++ db)).initVertex from rfl,
        ← Category.assoc, ι_wedgeInclR da' db j, Category.assoc,
        ← serialWedge_ι_succ n (da' ++ db) (rightEmbed da' db j),
        serialWedge_ι_cast ((n :: da') ++ db)
          (show (rightEmbed da' db j).succ = rightEmbed (n :: da') db j by
            apply Fin.ext; simp only [rightEmbed, Fin.val_succ, List.length_cons]; omega)]

/-- Naturality of the left-half split: restrict-then-split (left) = split-then-restrict. -/
theorem linesSplit_natL {X Y : BPSet} {a a' : ChainCat.Obj X} {b b' : ChainCat.Obj Y}
    (f : a ⟶ a') (g : b ⟶ b')
    (L : ∀ i : Fin (a'.dims ++ b'.dims).length, Chamber ((a'.dims ++ b'.dims).get i : ℕ)) :
    (linesSplit a.dims b.dims
        (linesRestrict ((chConcat X Y).map ((f, g) : (a, b) ⟶ (a', b'))) L)).1
      = linesRestrict f (linesSplit a'.dims b'.dims L).1 := by
  funext i
  have factEqL : BPSet.serialWedge.ι (a.dims ++ b.dims) (leftEmbed a.dims b.dims i)
        ≫ (concatHomφ f g).hom
      = yoneda.map (eqToHom (congrArg Box.ob (dimLeft a.dims b.dims i)) ≫ blockFace f.φ.hom i
          ≫ eqToHom (congrArg Box.ob (dimLeft a'.dims b'.dims (blockIdx f.φ.hom i)).symm))
        ≫ BPSet.serialWedge.ι (a'.dims ++ b'.dims)
            (leftEmbed a'.dims b'.dims (blockIdx f.φ.hom i)) := by
    rw [Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [← ι_wedgeInclL a'.dims b'.dims (blockIdx f.φ.hom i)]
    erw [← Category.assoc (yoneda.map (blockFace f.φ.hom i))]
    rw [← blockFace_spec f.φ.hom i]
    erw [Category.assoc (BPSet.serialWedge.ι a.dims i)]
    rw [← concatHomφ_inclL f g]
    erw [← Category.assoc (BPSet.serialWedge.ι a.dims i)]
    rw [ι_wedgeInclL a.dims b.dims i]
    erw [Category.assoc, ← Category.assoc]
    rw [← Functor.map_comp, eqToHom_trans, eqToHom_refl]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  simp only [linesSplit, linesRestrict, chConcat_map_φ]
  erw [restrict_factor (concatHomφ f g).hom (leftEmbed a.dims b.dims i)
        (leftEmbed a'.dims b'.dims (blockIdx f.φ.hom i)) _ factEqL L]
  rw [Chamber.restrict_restrict, Chamber.restrict_restrict]
  refine Chamber.restrict_congr _ _ _ (fun x => ?_)
  simp only [Function.comp_apply]
  apply Fin.ext
  rw [faceEmb_comp, faceEmb_comp, faceEmb_eqToHom_val]
  have hx : faceEmb (eqToHom (congrArg Box.ob (dimLeft a.dims b.dims i)))
      (finCongr (dimLeft a.dims b.dims i).symm x) = x := by
    apply Fin.ext; rw [faceEmb_eqToHom_val]; simp
  rw [hx]; simp

/-- Naturality of the right-half split: restrict-then-split (right) = split-then-restrict. -/
theorem linesSplit_natR {X Y : BPSet} {a a' : ChainCat.Obj X} {b b' : ChainCat.Obj Y}
    (f : a ⟶ a') (g : b ⟶ b')
    (L : ∀ i : Fin (a'.dims ++ b'.dims).length, Chamber ((a'.dims ++ b'.dims).get i : ℕ)) :
    (linesSplit a.dims b.dims
        (linesRestrict ((chConcat X Y).map ((f, g) : (a, b) ⟶ (a', b'))) L)).2
      = linesRestrict g (linesSplit a'.dims b'.dims L).2 := by
  funext j
  have factEqR : BPSet.serialWedge.ι (a.dims ++ b.dims) (rightEmbed a.dims b.dims j)
        ≫ (concatHomφ f g).hom
      = yoneda.map (eqToHom (congrArg Box.ob (dimRight a.dims b.dims j)) ≫ blockFace g.φ.hom j
          ≫ eqToHom (congrArg Box.ob (dimRight a'.dims b'.dims (blockIdx g.φ.hom j)).symm))
        ≫ BPSet.serialWedge.ι (a'.dims ++ b'.dims)
            (rightEmbed a'.dims b'.dims (blockIdx g.φ.hom j)) := by
    rw [Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [← ι_wedgeInclR a'.dims b'.dims (blockIdx g.φ.hom j)]
    erw [← Category.assoc (yoneda.map (blockFace g.φ.hom j))]
    rw [← blockFace_spec g.φ.hom j]
    erw [Category.assoc (BPSet.serialWedge.ι b.dims j)]
    rw [← concatHomφ_inclR f g]
    erw [← Category.assoc (BPSet.serialWedge.ι b.dims j)]
    rw [ι_wedgeInclR a.dims b.dims j]
    erw [Category.assoc, ← Category.assoc]
    rw [← Functor.map_comp, eqToHom_trans, eqToHom_refl]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  simp only [linesSplit, linesRestrict, chConcat_map_φ]
  erw [restrict_factor (concatHomφ f g).hom (rightEmbed a.dims b.dims j)
        (rightEmbed a'.dims b'.dims (blockIdx g.φ.hom j)) _ factEqR L]
  rw [Chamber.restrict_restrict, Chamber.restrict_restrict]
  refine Chamber.restrict_congr _ _ _ (fun x => ?_)
  simp only [Function.comp_apply]
  apply Fin.ext
  rw [faceEmb_comp, faceEmb_comp, faceEmb_eqToHom_val]
  have hx : faceEmb (eqToHom (congrArg Box.ob (dimRight a.dims b.dims j)))
      (finCongr (dimRight a.dims b.dims j).symm x) = x := by
    apply Fin.ext; rw [faceEmb_eqToHom_val]; simp
  rw [hx]; simp

/-! ## The multiplicativity natural isomorphism and the wedge → product theorem -/

variable (P Q : BPSet)

/-- **Multiplicativity.**  Restricting the chamber presheaf of the wedge along the concatenation
functor is the external product of the two chamber presheaves (`chConcat.op ⋙ Lines W ≅
Lines P ⊠ Lines Q`); on objects it is the list-append split `linesSplitEquiv`. -/
noncomputable def multIso :
    (chConcat P Q).op ⋙ Lines (wedge2 P Q) ≅
      (prodOpEquiv (C := ChainCat.Obj P) (D := ChainCat.Obj Q)).functor ⋙
        CategoryOfElements.extProd (Lines P) (Lines Q) :=
  NatIso.ofComponents
    (fun X => (linesSplitEquiv X.unop.1.dims X.unop.2.dims).toIso)
    (by
      intro X Y F
      apply ConcreteCategory.hom_ext
      intro L
      refine Prod.ext ?_ ?_
      · exact linesSplit_natL F.unop.1 F.unop.2 L
      · exact linesSplit_natR F.unop.1 F.unop.2 L)

/-- **The wedge → product theorem.**  For bi-pointed precubical sets `P Q` admitting altitudes,
the category of elements of `Lines (wedge2 P Q)` splits as the product of those of `Lines P`
and `Lines Q`. -/
noncomputable def linesWedgeEquiv (hP : P.AdmitsAltitude) (hQ : Q.AdmitsAltitude) :
    (Lines (wedge2 P Q)).Elements ≌ (Lines P).Elements × (Lines Q).Elements :=
  (CategoryOfElements.preEquivalence (Lines (wedge2 P Q))
        (ChainCat.chSegal P Q (wedge2_admitsAltitude hP hQ)).op).symm.trans
    ((CategoryOfElements.mapEquivalence (multIso P Q)).trans
      ((CategoryOfElements.preEquivalence (CategoryOfElements.extProd (Lines P) (Lines Q))
            (prodOpEquiv (C := ChainCat.Obj P) (D := ChainCat.Obj Q))).trans
        (CategoryOfElements.extProdEquiv (Lines P) (Lines Q))))

end FinalBraid
