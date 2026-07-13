import CubeChains.Salvetti.Lines
import CubeChains.Salvetti.Elements
import CubeChains.Arrangements.ElementsProd
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

namespace CubeChains

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
    ιᵂ l i
      = yoneda.map (eqToHom (congrArg (fun j => ▫((l.get j : ℕ))) h))
        ≫ ιᵂ l i' := by
  subst h; simp

/-- `yoneda.map` of a reflexive box `eqToHom` is the identity. -/
@[simp] theorem yoneda_map_eqToHom_self {k : ℕ} (h : ▫k = ▫k) :
    yoneda.map (eqToHom h) = 𝟙 (yoneda.obj ▫k) := by
  rw [eqToHom_refl]; exact CategoryTheory.Functor.map_id yoneda ▫k

/-- A box `eqToHom` (dimensions equal via `hAB`) composes away against `HEq`-equal maps. -/
theorem yoneda_eqToHom_comp_heq {A B : ℕ} (hAB : A = B) (h : ▫A = ▫B)
    {Z : PrecubicalSet} (f : yoneda.obj ▫B ⟶ Z) (g : yoneda.obj ▫A ⟶ Z)
    (hfg : HEq f g) : g = yoneda.map (eqToHom h) ≫ f := by
  subst hAB
  obtain rfl := eq_of_heq hfg
  rw [yoneda_map_eqToHom_self, Category.id_comp]

/-- **Block inclusion across the left append.** -/
theorem ι_wedgeInclL : ∀ (da db : List ℕ+) (i : Fin da.length),
    ιᵂ da i ≫ wedgeInclL da db
      = yoneda.map (eqToHom (congrArg Box.ob (dimLeft da db i).symm))
        ≫ ιᵂ (da ++ db) (leftEmbed da db i)
  | [], _, i => i.elim0
  | n :: da', db, i => by
      induction i using Fin.cases with
      | zero =>
          erw [serialWedge_ι_zero, wedgeInclL_cons, pushout.inl_desc]
          rw [show serialWedge.ι ((n :: da') ++ db) (leftEmbed (n :: da') db 0)
                = pushout.inl (□(n : ℕ)).finalVertex
                    (⋁(da' ++ db)).initVertex
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
    ιᵂ db j ≫ wedgeInclR da db
      = yoneda.map (eqToHom (congrArg Box.ob (dimRight da db j).symm))
        ≫ ιᵂ (da ++ db) (rightEmbed da db j)
  | [], db, j => by
      erw [show wedgeInclR ([] : List ℕ+) db = 𝟙 _ from rfl, Category.comp_id]
  | n :: da', db, j => by
      erw [show wedgeInclR (n :: da') db = wedgeInclR da' db
            ≫ pushout.inr (□(n : ℕ)).finalVertex
              (⋁(da' ++ db)).initVertex from rfl,
        ← Category.assoc, ι_wedgeInclR da' db j, Category.assoc,
        ← serialWedge_ι_succ n (da' ++ db) (rightEmbed da' db j),
        serialWedge_ι_cast ((n :: da') ++ db)
          (show (rightEmbed da' db j).succ = rightEmbed (n :: da') db j by
            apply Fin.ext; simp only [rightEmbed, Fin.val_succ, List.length_cons]; omega)]

/-- Naturality of the left-half split: restrict-then-split (left) = split-then-restrict. -/
theorem linesSplit_natL {X Y : BPSet} {a a' : Ch X} {b b' : Ch Y}
    (f : a ⟶ a') (g : b ⟶ b')
    (L : ∀ i : Fin (a'.dims ++ b'.dims).length, Chamber ((a'.dims ++ b'.dims).get i : ℕ)) :
    (linesSplit a.dims b.dims
        (linesRestrict ((chConcat X Y).map ((f, g) : (a, b) ⟶ (a', b'))) L)).1
      = linesRestrict f (linesSplit a'.dims b'.dims L).1 := by
  funext i
  have factEqL : ιᵂ (a.dims ++ b.dims) (leftEmbed a.dims b.dims i)
        ≫ (concatHomφ f g).hom
      = yoneda.map (eqToHom (congrArg Box.ob (dimLeft a.dims b.dims i)) ≫ blockFace fᵂ i
          ≫ eqToHom (congrArg Box.ob (dimLeft a'.dims b'.dims (blockIdx fᵂ i)).symm))
        ≫ ιᵂ (a'.dims ++ b'.dims)
            (leftEmbed a'.dims b'.dims (blockIdx fᵂ i)) := by
    rw [Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [← ι_wedgeInclL a'.dims b'.dims (blockIdx fᵂ i)]
    erw [← Category.assoc (yoneda.map (blockFace fᵂ i))]
    rw [← blockFace_spec fᵂ i]
    erw [Category.assoc (ιᵂ a.dims i)]
    rw [← concatHomφ_inclL f g]
    erw [← Category.assoc (ιᵂ a.dims i)]
    rw [ι_wedgeInclL a.dims b.dims i]
    erw [Category.assoc, ← Category.assoc]
    rw [← Functor.map_comp, eqToHom_trans, eqToHom_refl]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  simp only [linesSplit, linesRestrict, chConcat_map_φ]
  erw [restrict_factor (concatHomφ f g).hom (leftEmbed a.dims b.dims i)
        (leftEmbed a'.dims b'.dims (blockIdx fᵂ i)) _ factEqL L]
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
theorem linesSplit_natR {X Y : BPSet} {a a' : Ch X} {b b' : Ch Y}
    (f : a ⟶ a') (g : b ⟶ b')
    (L : ∀ i : Fin (a'.dims ++ b'.dims).length, Chamber ((a'.dims ++ b'.dims).get i : ℕ)) :
    (linesSplit a.dims b.dims
        (linesRestrict ((chConcat X Y).map ((f, g) : (a, b) ⟶ (a', b'))) L)).2
      = linesRestrict g (linesSplit a'.dims b'.dims L).2 := by
  funext j
  have factEqR : ιᵂ (a.dims ++ b.dims) (rightEmbed a.dims b.dims j)
        ≫ (concatHomφ f g).hom
      = yoneda.map (eqToHom (congrArg Box.ob (dimRight a.dims b.dims j)) ≫ blockFace gᵂ j
          ≫ eqToHom (congrArg Box.ob (dimRight a'.dims b'.dims (blockIdx gᵂ j)).symm))
        ≫ ιᵂ (a'.dims ++ b'.dims)
            (rightEmbed a'.dims b'.dims (blockIdx gᵂ j)) := by
    rw [Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [← ι_wedgeInclR a'.dims b'.dims (blockIdx gᵂ j)]
    erw [← Category.assoc (yoneda.map (blockFace gᵂ j))]
    rw [← blockFace_spec gᵂ j]
    erw [Category.assoc (ιᵂ b.dims j)]
    rw [← concatHomφ_inclR f g]
    erw [← Category.assoc (ιᵂ b.dims j)]
    rw [ι_wedgeInclR a.dims b.dims j]
    erw [Category.assoc, ← Category.assoc]
    rw [← Functor.map_comp, eqToHom_trans, eqToHom_refl]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  simp only [linesSplit, linesRestrict, chConcat_map_φ]
  erw [restrict_factor (concatHomφ f g).hom (rightEmbed a.dims b.dims j)
        (rightEmbed a'.dims b'.dims (blockIdx gᵂ j)) _ factEqR L]
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
      (prodOpEquiv (C := Ch P) (D := Ch Q)).functor ⋙
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
            (prodOpEquiv (C := Ch P) (D := Ch Q))).trans
        (CategoryOfElements.extProdEquiv (Lines P) (Lines Q))))

end CubeChains
