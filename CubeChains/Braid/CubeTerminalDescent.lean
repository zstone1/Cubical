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

end CubeChains
