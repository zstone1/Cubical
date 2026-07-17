import CubeChains.Braid.CubeLegOne

/-!
# Braid/CubeTerminalDescent — the descent functor `Ψ : ConcCat Zbp ⥤ QuotCat (Sal) Sₙ`

`FZ = braidSalEquiv.functor ⋙ concToZ` is star-bijective (`FZ_star_bijective`), so every outgoing
terminal refinement of `(FZ n).obj a` lifts uniquely to a Salvetti morphism out of `a`.  Post-
composing that lift with the `Sₙ`-quotient functor gives a functor `Ψ` on the terminal concurrency
category with `FZ ⋙ Ψ ≅ quotFunctor`.  Hence `coverZ ⋙ map Ψ ≅ quotCover`, and since `quotCover`
is faithful (a covering is `π₁`-injective), `coverZ` is faithful — the `Pₙ ↪ Bₙ` injection,
axiom-free.
-/

open CategoryTheory OrderQuotient Quiver

namespace CubeChains

variable {n : ℕ}

/-! ## Object map: chosen Salvetti preimage -/

open Classical in
/-- The chosen Salvetti preimage of a terminal execution: `hX.choose` on the `n`-event stratum,
the junk cell `defaultCell` off it. -/
noncomputable def preIm (n : ℕ) (y : ConcCat Zbp) : Sal (braidCOM n) :=
  if h : ∃ a : Sal (braidCOM n), (FZ n).obj a = y then h.choose else defaultCell n

theorem FZ_preIm {n : ℕ} {y : ConcCat Zbp}
    (h : ∃ a : Sal (braidCOM n), (FZ n).obj a = y) : (FZ n).obj (preIm n y) = y := by
  rw [preIm, dif_pos h]; exact h.choose_spec

theorem preIm_junk {n : ℕ} {y : ConcCat Zbp}
    (h : ¬ ∃ a : Sal (braidCOM n), (FZ n).obj a = y) : preIm n y = defaultCell n := by
  rw [preIm, dif_neg h]

theorem psiObj_eq_mk_preIm (n : ℕ) (y : ConcCat Zbp) :
    psiObj n y = Quotient.mk'' (preIm n y) := by
  rw [psiObj, preIm]; split <;> rfl

/-- Two Salvetti cells with the same terminal execution have the same `Sₙ`-orbit. -/
theorem orbit_eq_of_FZ_eq {n : ℕ} {a a' : Sal (braidCOM n)}
    (h : (FZ n).obj a = (FZ n).obj a') :
    (Quotient.mk'' a : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) = Quotient.mk'' a' := by
  obtain ⟨σ, hσ⟩ := braidSal_concToZ_fiber h
  rw [← hσ]; exact mk_smul_eq σ a'

/-- Being in the image of `FZ n` is transported along `ConcCat Zbp` morphisms (event count is
preserved). -/
theorem exists_FZ_of_hom {n : ℕ} {X Y : ConcCat Zbp} (e : X ⟶ Y)
    (hX : ∃ a : Sal (braidCOM n), (FZ n).obj a = X) :
    ∃ a : Sal (braidCOM n), (FZ n).obj a = Y :=
  (exists_FZ_preimage_iff n Y).mpr ((nEvents_eq e).symm.trans ((exists_FZ_preimage_iff n X).mp hX))

/-! ## The morphism map -/

open Classical in
/-- The morphism map of `Ψ`: on the `n`-event stratum, lift `e` uniquely to a Salvetti morphism out
of `preIm X` (`FZstarInv`) and push through `quotFunctor`; off it, the forced junk identity. -/
noncomputable def psiMap (n : ℕ) {X Y : ConcCat Zbp} (e : X ⟶ Y) :
    (Quotient.mk'' (preIm n X) : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))
      ⟶ Quotient.mk'' (preIm n Y) :=
  dite (∃ a : Sal (braidCOM n), (FZ n).obj a = X)
    (fun hX =>
      quotHom (leOfHom (FZstarInv n (preIm n X)
          ⟨Y, eqToHom (FZ_preIm hX) ≫ e⟩).2)
        ≫ eqToHom (orbit_eq_of_FZ_eq (by
            rw [FZstarInv_obj]
            exact (FZ_preIm (exists_FZ_of_hom e hX)).symm)))
    (fun hX =>
      eqToHom (by rw [preIm_junk hX, preIm_junk (fun hY => hX (by
        rw [exists_FZ_preimage_iff] at hY ⊢; exact (nEvents_eq e).trans hY))]))

/-- `psiMap` on the image stratum: the pushed star-lift, up to the codomain orbit `eqToHom`. -/
theorem psiMap_image {n : ℕ} {X Y : ConcCat Zbp} (e : X ⟶ Y)
    (hX : ∃ a : Sal (braidCOM n), (FZ n).obj a = X)
    (h : (Quotient.mk''
          (FZstarInv n (preIm n X) ⟨Y, eqToHom (FZ_preIm hX) ≫ e⟩).1
          : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))
        = Quotient.mk'' (preIm n Y)) :
    psiMap n e
      = quotHom (leOfHom (FZstarInv n (preIm n X) ⟨Y, eqToHom (FZ_preIm hX) ≫ e⟩).2)
        ≫ eqToHom h := by
  rw [psiMap, dif_pos hX]

/-- `psiMap` off the image stratum is the junk identity. -/
theorem psiMap_junk {n : ℕ} {X Y : ConcCat Zbp} (e : X ⟶ Y)
    (hX : ¬ ∃ a : Sal (braidCOM n), (FZ n).obj a = X)
    (h : (Quotient.mk'' (preIm n X) : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))
        = Quotient.mk'' (preIm n Y)) :
    psiMap n e = eqToHom h := by
  rw [psiMap, dif_neg hX]

/-! ## Up-set representative helpers for `QuotCat` morphism equality

`homEquivUpSet` presents a hom `⟦a⟧ ⟶ Y` by the unique `b ≥ a` with `⟦b⟧ = Y`; equalities of
`QuotCat` morphisms are proved by comparing these representatives, sidestepping `eqToHom`. -/

/-- Two `QuotCat` morphisms out of `⟦a⟧` agree once their up-set representatives agree. -/
theorem quot_hom_ext {a : Sal (braidCOM n)}
    {Y : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))}
    {f g : (Quotient.mk'' a : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) ⟶ Y}
    (h : ((QuotCat.homEquivUpSet a Y) f).val = ((QuotCat.homEquivUpSet a Y) g).val) : f = g :=
  (QuotCat.homEquivUpSet a Y).injective (Subtype.ext h)

/-- The up-set representative of `quotHom hab ≫ eqToHom hbY` is `b`. -/
theorem upRep_quotHom_eqToHom {a b : Sal (braidCOM n)} (hab : a ≤ b)
    {Y : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))}
    (hbY : (Quotient.mk'' b : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) = Y) :
    ((QuotCat.homEquivUpSet a Y) (quotHom hab ≫ eqToHom hbY)).val = b := by
  have hs := homEquivUpSet_symm_eq (⟨b, hab, hbY⟩ :
    {c : Sal (braidCOM n) // a ≤ c
      ∧ (Quotient.mk'' c : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) = Y})
  have h2 : (QuotCat.homEquivUpSet a Y) (quotHom hab ≫ eqToHom hbY) = ⟨b, hab, hbY⟩ := by
    rw [← hs]; exact Equiv.apply_symm_apply _ _
  rw [h2]

/-- The up-set representative of the identity is the base point. -/
theorem upRep_id (a : Sal (braidCOM n)) :
    ((QuotCat.homEquivUpSet a (Quotient.mk'' a : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))))
        (𝟙 _)).val = a := by
  have hid : (𝟙 (Quotient.mk'' a : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))))
      = quotHom (le_refl a) ≫ eqToHom rfl := by
    rw [eqToHom_refl, Category.comp_id, quotHom_id]
  rw [hid, upRep_quotHom_eqToHom]

/-- Up-set representative of a composite: peel off the first `quotHom … ≫ eqToHom` and continue
from its representative. -/
theorem upRep_comp {a b m p : Sal (braidCOM n)} (hab : a ≤ b)
    (hbm : (Quotient.mk'' b : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) = Quotient.mk'' m)
    (g : (Quotient.mk'' m : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))
        ⟶ Quotient.mk'' p) :
    (QuotCat.homEquivUpSet a (Quotient.mk'' p) ((quotHom hab ≫ eqToHom hbm) ≫ g)).val
      = (QuotCat.homEquivUpSet b (Quotient.mk'' p) (eqToHom hbm ≫ g)).val := by
  have hg : eqToHom hbm ≫ g
      = quotHom (QuotCat.homEquivUpSet b (Quotient.mk'' p) (eqToHom hbm ≫ g)).property.1
        ≫ eqToHom (QuotCat.homEquivUpSet b (Quotient.mk'' p) (eqToHom hbm ≫ g)).property.2 := by
    conv_lhs => rw [← Equiv.symm_apply_apply (QuotCat.homEquivUpSet b (Quotient.mk'' p))
      (eqToHom hbm ≫ g)]
    rw [homEquivUpSet_symm_eq]
  conv_lhs => rw [Category.assoc, hg, ← Category.assoc, quotHom_comp]
  rw [upRep_quotHom_eqToHom]

/-- The up-set representative is unchanged by a trailing `eqToHom`. -/
theorem upRep_comp_eqToHom {a m p : Sal (braidCOM n)}
    (f : (Quotient.mk'' a : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) ⟶ Quotient.mk'' m)
    (hmp : (Quotient.mk'' m : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) = Quotient.mk'' p) :
    (QuotCat.homEquivUpSet a (Quotient.mk'' p) (f ≫ eqToHom hmp)).val
      = (QuotCat.homEquivUpSet a (Quotient.mk'' m) f).val := by
  have hf : f = quotHom (QuotCat.homEquivUpSet a (Quotient.mk'' m) f).property.1
      ≫ eqToHom (QuotCat.homEquivUpSet a (Quotient.mk'' m) f).property.2 := by
    conv_lhs => rw [← Equiv.symm_apply_apply (QuotCat.homEquivUpSet a (Quotient.mk'' m)) f]
    rw [homEquivUpSet_symm_eq]
  conv_lhs => rw [hf, Category.assoc, eqToHom_trans]
  rw [upRep_quotHom_eqToHom]

/-- The up-set rep of a span-morphism out of `⟦a⟧` is the `align`-translated upper endpoint. -/
theorem homToUpSet_val_mk (a : Sal (braidCOM n))
    {Y : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))}
    (p : QuotCat.Span (Quotient.mk'' a) Y) :
    (QuotCat.homToUpSet a Y (Quotient.mk'' p)).val
      = align a p.val.1 p.property.2.1.symm • p.val.2 := rfl

/-- Base `align`-collapse: the up-set rep of `eqToHom ≫ quotHom` out of `v` is `align v u • w`. -/
theorem upRep_eqToHom_quotHom_base {v u w : Sal (braidCOM n)}
    (hvu : (Quotient.mk'' v : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) = Quotient.mk'' u)
    (huw : u ≤ w) :
    (QuotCat.homEquivUpSet v (Quotient.mk'' w) (eqToHom hvu ≫ quotHom huw)).val
      = align v u hvu • w := by
  have hcomp : eqToHom hvu ≫ quotHom huw
      = Quotient.mk'' (QuotCat.compSpan
          (⟨(v, v), le_refl v, rfl, hvu⟩ : QuotCat.Span (Quotient.mk'' v) (Quotient.mk'' u))
          (⟨(u, w), huw, rfl, rfl⟩ : QuotCat.Span (Quotient.mk'' u) (Quotient.mk'' w))) := by
    rw [eqToHom_quotMk hvu]; rfl
  rw [hcomp]
  change (QuotCat.homToUpSet v (Quotient.mk'' w) (Quotient.mk'' _)).val = align v u hvu • w
  rw [homToUpSet_val_mk]
  simp only [QuotCat.compSpan_val_fst, QuotCat.compSpan_val_snd, QuotCat.alignPair]
  rw [align_self, one_smul]

/-- The `align`-collapse: the up-set rep of `eqToHom ≫ quotHom ≫ eqToHom` out of `v` is the
`align`-translate of `w`. -/
theorem upRep_eqToHom_quotHom {v u w p : Sal (braidCOM n)}
    (hvu : (Quotient.mk'' v : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) = Quotient.mk'' u)
    (huw : u ≤ w)
    (hwp : (Quotient.mk'' w : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) = Quotient.mk'' p) :
    (QuotCat.homEquivUpSet v (Quotient.mk'' p)
        (eqToHom hvu ≫ quotHom huw ≫ eqToHom hwp)).val
      = align v u hvu • w := by
  rw [show eqToHom hvu ≫ quotHom huw ≫ eqToHom hwp
      = (eqToHom hvu ≫ quotHom huw) ≫ eqToHom hwp from (Category.assoc _ _ _).symm,
    upRep_comp_eqToHom, upRep_eqToHom_quotHom_base]

/-! ## The morphism map is functorial -/

/-- A star-vertex built from an `eqToHom` is the star-vertex of an identity. -/
theorem star_mk_eqToHom {C : Type*} [Category C] {a b : C} (h : a = b) :
    (Quiver.Star.mk (eqToHom h) : Quiver.Star a) = Quiver.Star.mk (𝟙 a) := by
  subst h; simp

/-- The `FZ`-star-lift of an identity is trivial: the lift target of `𝟙 X` out of `preIm X`
is `preIm X`. -/
theorem FZstarInv_id {n : ℕ} {X : ConcCat Zbp}
    (hX : ∃ a : Sal (braidCOM n), (FZ n).obj a = X) :
    (FZstarInv n (preIm n X) ⟨X, eqToHom (FZ_preIm hX) ≫ 𝟙 X⟩).1 = preIm n X := by
  have hEq : FZstarInv n (preIm n X) ⟨X, eqToHom (FZ_preIm hX) ≫ 𝟙 X⟩
      = ⟨preIm n X, 𝟙 (preIm n X)⟩ := by
    rw [FZstarInv, Equiv.symm_apply_eq]
    change (⟨X, eqToHom (FZ_preIm hX) ≫ 𝟙 X⟩ : Quiver.Star ((FZ n).obj (preIm n X)))
        = Quiver.Star.mk ((FZ n).map (𝟙 (preIm n X)))
    rw [(FZ n).map_id, Category.comp_id]
    exact star_mk_eqToHom (FZ_preIm hX)
  rw [hEq]

/-- **Identity law for `psiMap`.** -/
theorem psiMap_id {n : ℕ} (X : ConcCat Zbp) :
    psiMap n (𝟙 X) = 𝟙 (Quotient.mk'' (preIm n X)) := by
  by_cases hX : ∃ a : Sal (braidCOM n), (FZ n).obj a = X
  · rw [psiMap_image (𝟙 X) hX
      (h := orbit_eq_of_FZ_eq (by rw [FZstarInv_obj]; exact (FZ_preIm hX).symm))]
    apply quot_hom_ext
    rw [upRep_quotHom_eqToHom, upRep_id]
    exact FZstarInv_id hX
  · rw [psiMap_junk (𝟙 X) hX rfl, eqToHom_refl]

/-- **Composition law for `psiMap`, reduced to the star-lift reindex crux.**  The up-set machinery
collapses `map_comp` to a single Salvetti-cell equality: the lift of `e ≫ e'` out of `preIm X`
equals the aligner-translate of the lift of `e'` out of `preIm Y`.  The remaining `hcrux` is the
`Sₙ`-equivariance of `FZstarInv` (the wedge-map σ-invariance of `FZ`, plus the codomain
symmetry-propagation `FZ.obj (σ • b) = FZ.obj b`). -/
theorem psiMap_comp_of_crux {n : ℕ} {X Y Z : ConcCat Zbp} (e : X ⟶ Y) (e' : Y ⟶ Z)
    (hX : ∃ a : Sal (braidCOM n), (FZ n).obj a = X)
    (hcrux :
      (FZstarInv n (preIm n X) ⟨Z, eqToHom (FZ_preIm hX) ≫ e ≫ e'⟩).1
        = align (FZstarInv n (preIm n X) ⟨Y, eqToHom (FZ_preIm hX) ≫ e⟩).1 (preIm n Y)
            (orbit_eq_of_FZ_eq (by
              rw [FZstarInv_obj]; exact (FZ_preIm (exists_FZ_of_hom e hX)).symm))
          • (FZstarInv n (preIm n Y)
              ⟨Z, eqToHom (FZ_preIm (exists_FZ_of_hom e hX)) ≫ e'⟩).1) :
    psiMap n (e ≫ e') = psiMap n e ≫ psiMap n e' := by
  have hY : ∃ a : Sal (braidCOM n), (FZ n).obj a = Y := exists_FZ_of_hom e hX
  have hZ : ∃ a : Sal (braidCOM n), (FZ n).obj a = Z := exists_FZ_of_hom e' hY
  rw [psiMap_image (e ≫ e') hX
      (h := orbit_eq_of_FZ_eq (by rw [FZstarInv_obj]; exact (FZ_preIm hZ).symm)),
    psiMap_image e hX
      (h := orbit_eq_of_FZ_eq (by rw [FZstarInv_obj]; exact (FZ_preIm hY).symm)),
    psiMap_image e' hY
      (h := orbit_eq_of_FZ_eq (by rw [FZstarInv_obj]; exact (FZ_preIm hZ).symm))]
  apply quot_hom_ext
  rw [upRep_quotHom_eqToHom, upRep_comp, upRep_eqToHom_quotHom]
  exact hcrux

/-- Off the `n`-event stratum `psiMap` is functorial for free (both sides are junk identities). -/
theorem psiMap_comp_junk {n : ℕ} {X Y Z : ConcCat Zbp} (e : X ⟶ Y) (e' : Y ⟶ Z)
    (hX : ¬ ∃ a : Sal (braidCOM n), (FZ n).obj a = X) :
    psiMap n (e ≫ e') = psiMap n e ≫ psiMap n e' := by
  have hXn : nEvents X ≠ n := fun h => hX ((exists_FZ_preimage_iff n X).mpr h)
  have hY : ¬ ∃ a : Sal (braidCOM n), (FZ n).obj a = Y := fun h =>
    hXn (by rw [nEvents_eq e]; exact (exists_FZ_preimage_iff n Y).mp h)
  have hZ : ¬ ∃ a : Sal (braidCOM n), (FZ n).obj a = Z := fun h =>
    hXn (by rw [nEvents_eq (e ≫ e')]; exact (exists_FZ_preimage_iff n Z).mp h)
  rw [psiMap_junk (e ≫ e') hX (by rw [preIm_junk hX, preIm_junk hZ]),
    psiMap_junk e hX (by rw [preIm_junk hX, preIm_junk hY]),
    psiMap_junk e' hY (by rw [preIm_junk hY, preIm_junk hZ]), eqToHom_trans]

/-! ## Discharging the crux — the star-lift is a valid preimage

The unique `FZ`-star-lift of a terminal morphism `⟨T, m⟩` is identified whenever a concrete
Salvetti morphism `g : A ⟶ B` maps to it (`FZ.obj B = T`, `FZ.map g ≍ m`).  The reindex `HEq`
(`FZ_map_salReindex_heq`) supplies exactly the `g`'s for `hcrux` and for the transport iso. -/

/-- **Uniqueness of the star-lift.**  A concrete Salvetti morphism `g : A ⟶ B` whose `FZ`-image
matches `⟨T, m⟩` *is* the star-lift. -/
theorem FZstarInv_eq_of_map_heq {n : ℕ} {A B : Sal (braidCOM n)} {T : ConcCat Zbp}
    (g : A ⟶ B) (m : (FZ n).obj A ⟶ T)
    (hobj : (FZ n).obj B = T) (hmap : HEq m ((FZ n).map g)) :
    FZstarInv n A ⟨T, m⟩ = ⟨B, g⟩ := by
  rw [FZstarInv, Equiv.symm_apply_eq]
  show (⟨T, m⟩ : Quiver.Star ((FZ n).obj A)) = Quiver.Star.mk ((FZ n).map g)
  exact Sigma.ext hobj.symm hmap

/-- **Star-lift of `FZ.map f`.**  For `f : a ⟶ b` and a same-orbit preimage `A` of `FZ.obj a`, the
lift of `FZ.map f` out of `A` is the `align`-translate of `b`. -/
theorem starLift_FZmap_align {n : ℕ} {A a b : Sal (braidCOM n)} (f : a ⟶ b)
    (ho : (Quotient.mk'' A : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) = Quotient.mk'' a)
    (hAfix : (FZ n).obj A = (FZ n).obj a) :
    (FZstarInv n A ⟨(FZ n).obj b, eqToHom hAfix ≫ (FZ n).map f⟩).1 = align A a ho • b := by
  set ρ := align A a ho with hρ
  have hAρ : A = (salReindex ρ).obj a := (align_smul A a ho).symm
  have hfix : (FZ n).obj (salReindexObj ρ a) = (FZ n).obj a := by
    rw [show salReindexObj ρ a = A from align_smul A a ho]; exact hAfix
  have hobj : (FZ n).obj ((salReindex ρ).obj b) = (FZ n).obj b :=
    FZ_obj_reindex_propagate ρ (leOfHom f) hfix
  have hmap : HEq (eqToHom hAfix ≫ (FZ n).map f)
      ((FZ n).map (eqToHom hAρ ≫ (salReindex ρ).map f)) := by
    rw [(FZ n).map_comp, eqToHom_map]
    exact (eqToHom_comp_heq _ _).trans
      ((FZ_map_salReindex_heq ρ f hfix).symm.trans (eqToHom_comp_heq _ _).symm)
  exact congrArg Sigma.fst
    (FZstarInv_eq_of_map_heq (eqToHom hAρ ≫ (salReindex ρ).map f) _ hobj hmap)

/-- **Composition law for `psiMap`.** -/
theorem psiMap_comp {n : ℕ} {X Y Z : ConcCat Zbp} (e : X ⟶ Y) (e' : Y ⟶ Z) :
    psiMap n (e ≫ e') = psiMap n e ≫ psiMap n e' := by
  by_cases hX : ∃ a : Sal (braidCOM n), (FZ n).obj a = X
  · refine psiMap_comp_of_crux e e' hX ?_
    have hY : ∃ a : Sal (braidCOM n), (FZ n).obj a = Y := exists_FZ_of_hom e hX
    set A := preIm n X with hAdef
    set A_Y := preIm n Y with hAYdef
    set m_XY : (FZ n).obj A ⟶ Y := eqToHom (FZ_preIm hX) ≫ e with hmXY
    set m_YZ : (FZ n).obj A_Y ⟶ Z := eqToHom (FZ_preIm hY) ≫ e' with hmYZ
    set B_Y := (FZstarInv n A ⟨Y, m_XY⟩).1 with hBY
    set f_XY := (FZstarInv n A ⟨Y, m_XY⟩).2 with hfXY
    set B_YZ := (FZstarInv n A_Y ⟨Z, m_YZ⟩).1 with hBYZ
    set f_YZ := (FZstarInv n A_Y ⟨Z, m_YZ⟩).2 with hfYZ
    have hBY_obj : (FZ n).obj B_Y = Y := FZstarInv_obj n A ⟨Y, m_XY⟩
    have hAY_obj : (FZ n).obj A_Y = Y := FZ_preIm hY
    have h_orbit : (Quotient.mk'' B_Y : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))
        = Quotient.mk'' A_Y := orbit_eq_of_FZ_eq (by rw [hBY_obj, hAY_obj])
    set τ := align B_Y A_Y h_orbit with hτ
    have hb : B_Y = (salReindex τ).obj A_Y := (align_smul B_Y A_Y h_orbit).symm
    have hfix : (FZ n).obj (salReindexObj τ A_Y) = (FZ n).obj A_Y := by
      rw [show salReindexObj τ A_Y = B_Y from align_smul B_Y A_Y h_orbit, hBY_obj, hAY_obj]
    have hBYZ_obj : (FZ n).obj B_YZ = Z := FZstarInv_obj n A_Y ⟨Z, m_YZ⟩
    have hobj : (FZ n).obj ((salReindex τ).obj B_YZ) = Z := by
      rw [show (salReindex τ).obj B_YZ = salReindexObj τ B_YZ from rfl,
        FZ_obj_reindex_propagate τ (leOfHom f_YZ) hfix, hBYZ_obj]
    have h1 : HEq ((FZ n).map ((salReindex τ).map f_YZ)) ((FZ n).map f_YZ) :=
      FZ_map_salReindex_heq τ f_YZ hfix
    have h2 : HEq ((FZ n).map f_YZ) m_YZ := FZstarInv_map_heq n A_Y ⟨Z, m_YZ⟩
    have h3 : HEq m_YZ e' := eqToHom_comp_heq e' (FZ_preIm hY)
    have hf : HEq m_XY ((FZ n).map f_XY) := (FZstarInv_map_heq n A ⟨Y, m_XY⟩).symm
    have hg : HEq e' ((FZ n).map (eqToHom hb ≫ (salReindex τ).map f_YZ)) := by
      rw [(FZ n).map_comp, eqToHom_map]
      exact h3.symm.trans (h2.symm.trans (h1.symm.trans (eqToHom_comp_heq _ _).symm))
    have hmap : HEq (eqToHom (FZ_preIm hX) ≫ e ≫ e')
        ((FZ n).map (f_XY ≫ eqToHom hb ≫ (salReindex τ).map f_YZ)) := by
      rw [(FZ n).map_comp, ← Category.assoc]
      exact comp_heq_comp rfl hBY_obj.symm hobj.symm hf hg
    exact congrArg Sigma.fst
      (FZstarInv_eq_of_map_heq (f_XY ≫ eqToHom hb ≫ (salReindex τ).map f_YZ) _ hobj hmap)
  · exact psiMap_comp_junk e e' hX

/-! ## The descent functor and the transport isomorphism -/

/-- **The descent functor** `Ψ : ConcCat Zbp ⥤ QuotCat (Sal) Sₙ`. -/
noncomputable def Psi (n : ℕ) : ConcCat Zbp ⥤ QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)) where
  obj y := Quotient.mk'' (preIm n y)
  map {_ _} e := psiMap n e
  map_id X := psiMap_id X
  map_comp e e' := psiMap_comp e e'

/-- **The transport equation.**  `FZ ⋙ Ψ ≅ quotFunctor`: on `FZ.obj a` the descent recovers the
orbit `⟦a⟧` (`psiObj_FZ`), and its morphism map is the `Sₙ`-quotient of the star-lift, which is the
`align`-translate matching `quotHom` (`starLift_FZmap_align`). -/
noncomputable def FZ_comp_Psi_iso (n : ℕ) :
    FZ n ⋙ Psi n ≅ OrderQuotient.quotFunctor (G := Equiv.Perm (Fin n)) (P := Sal (braidCOM n)) :=
  NatIso.ofComponents
    (fun a => eqToIso ((psiObj_eq_mk_preIm n ((FZ n).obj a)).symm.trans (psiObj_FZ n a)))
    (fun {a b} f => by
      have hX_a : ∃ c : Sal (braidCOM n), (FZ n).obj c = (FZ n).obj a := ⟨a, rfl⟩
      have ho_a : (Quotient.mk'' (preIm n ((FZ n).obj a))
          : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) = Quotient.mk'' a :=
        (psiObj_eq_mk_preIm n _).symm.trans (psiObj_FZ n a)
      have ho_b : (Quotient.mk'' (preIm n ((FZ n).obj b))
          : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) = Quotient.mk'' b :=
        (psiObj_eq_mk_preIm n _).symm.trans (psiObj_FZ n b)
      show psiMap n ((FZ n).map f) ≫ eqToHom ho_b
        = eqToHom ho_a ≫ quotHom (leOfHom f)
      rw [psiMap_image ((FZ n).map f) hX_a
        (h := orbit_eq_of_FZ_eq (by rw [FZstarInv_obj]; exact (FZ_preIm
          (exists_FZ_of_hom ((FZ n).map f) hX_a)).symm))]
      apply quot_hom_ext
      rw [Category.assoc, eqToHom_trans, upRep_quotHom_eqToHom, upRep_eqToHom_quotHom_base]
      exact starLift_FZmap_align f ho_a (FZ_preIm hX_a))

/-! ## The endgame — `coverZ` is faithful, hence `Pₙ ↪ Bₙ` -/

/-- **`coverZ` is faithful.**  `FreeGroupoid.map Ψ` descends `coverZ = FreeGroupoid.map FZ` to
`quotCover` (`FZ ⋙ Ψ ≅ quotFunctor`), which is `π₁`-injective. -/
theorem coverZ_faithful (n : ℕ) : (coverZ n).Faithful := by
  haveI := quotCover_faithful n
  have hiso : FreeGroupoid.map (FZ n) ⋙ FreeGroupoid.map (Psi n) ≅ quotCover n :=
    eqToIso (FreeGroupoid.map_comp (FZ n) (Psi n)).symm ≪≫ FreeGroupoid.mapIso (FZ_comp_Psi_iso n)
  haveI : (FreeGroupoid.map (FZ n)).Faithful := Functor.Faithful.of_comp_iso hiso
  rw [show coverZ n = FreeGroupoid.map (FZ n) from coverZ_eq n]
  infer_instance

/-- **`φ_x` injectivity, axiom-free.**  The `Pₙ ↪ Bₙ` injection from `coverZ` faithfulness. -/
theorem concToZAut_injective (n : ℕ) (x : ConcCat (□n)) :
    Function.Injective (concToZAut n x) :=
  concToZAut_injective_of_coverZ_faithful n (coverZ_faithful n) x

end CubeChains
