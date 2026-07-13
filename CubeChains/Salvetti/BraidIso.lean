import CubeChains.Salvetti.WallCrossing
import CubeChains.Salvetti.BraidFaceEquiv

/-!
# Salvetti/BraidIso — the headline theorem `Sal(braidCOM n) ≌ Int(Lines(□ⁿ))`

**The main theorem of the braid/Salvetti program.**  The Salvetti face poset of the braid oriented
matroid `braidCOM n` is equivalent to the category of elements of the chamber presheaf `Lines` on
the cube-chain category of `□ⁿ`:

> `braidSalEquiv n : Sal (braidCOM n) ≌ (Lines (□n)).Elements`.

Both sides are categories of elements; we never match cells by hand.  Instead we assemble four
equivalences (`STRUCTURE.md` §5.4):

```
Sal (braidCOM n)
  ≌ (salFunctor (braidCOM n)).Elements                    -- salElementsEquiv     (SalElements)
  ≌ (refineOpToFace n ⋙ salFunctor (braidCOM n)).Elements -- (preEquivalence).symm (Elements)
  ≌ (RefineLines n).Elements                                  -- mapEquivalence salLinesIso.symm
  ≌ (Lines (□n)).Elements                           -- refineLinesEquiv     (Partition)
```

The only genuinely new content is the natural isomorphism
`salLinesIso n : RefineLines n ≅ refineOpToFace n ⋙ salFunctor (braidCOM n)`
of presheaves on `(RefineObj □ⁿ)ᵒᵖ`.  Its object component at `op x` is the bijection between
chamber tuples on the chain `x` and topes of `braidCOM n` above `x`'s covector; the two directions
are `heightOf`/`chambersOf` from `SalBraidTope`, and *naturality is exactly the wall-crossing law*
`wall_crossing` from `WallCrossing`.

We route the base transport through `refineOpToFace n` (whose object map is definitional) rather
than through the choice-opaque `braidFaceEquiv n = (refineOpToFace n).asEquivalence.symm`, so that
`salFunctor` composes along a computable object map.

-/

open CategoryTheory Opposite CubeChain StdCube SignType

namespace CubeChains

open SignVec

variable {n : ℕ}

/-! ## STEP 1 — `chambersOf` depends on the height only through its covector -/

/-- **`chambersOf` is a `braidSign` invariant.**  Two injective heights with the same braid
covector induce the same chamber tuple, because a chamber's strict order is read off `σ` through
strict comparisons, which `braidSign` reflects (`lt_iff_of_braidSign_eq`). -/
theorem chambersOf_congr (x : RefineObj (□n).init (□n).final)
    {σ σ' : Fin n → ℤ} (hσ : Function.Injective σ) (hσ' : Function.Injective σ')
    (h : braidSign σ = braidSign σ') :
    chambersOf x σ hσ = chambersOf x σ' hσ' := by
  funext j
  apply Chamber.ext
  funext a b
  exact propext (lt_iff_of_braidSign_eq h
    (nones (toStar (x.cubes.get (j.cast (dseqLen x))).2)
      (Fin.cast (dseqGetNat x (j.cast (dseqLen x))) a))
    (nones (toStar (x.cubes.get (j.cast (dseqLen x))).2)
      (Fin.cast (dseqGetNat x (j.cast (dseqLen x))) b)))

/-! ## STEP 2 — the two maps `topes above X_a ↔ chambers on a` -/

/-- **Chambers from a tope.**  A tope `T` above `x`'s covector is `braidSign σ` for some injective
`σ` (`braidCOM_isTope_iff_injective`); read the chamber tuple off `σ`.  Well-defined by
`chambersOf_congr`, since a different `σ` with the same covector gives the same chambers. -/
noncomputable def toLines (x : RefineObj (□n).init (□n).final)
    (T : {T : SignVec (BraidGround n) //
      (braidCOM n).IsTope T ∧ braidSign (covectorHeight x) ⊑ T}) :
    (RefineLines n).obj (op x) :=
  chambersOf x ((braidCOM_isTope_iff_injective T.1).mp T.2.1).choose
              ((braidCOM_isTope_iff_injective T.1).mp T.2.1).choose_spec.1

/-- `toLines` is computed by *any* injective realiser of the tope. -/
theorem toLines_eq (x : RefineObj (□n).init (□n).final)
    (T : {T : SignVec (BraidGround n) //
      (braidCOM n).IsTope T ∧ braidSign (covectorHeight x) ⊑ T})
    {σ : Fin n → ℤ} (hσ : Function.Injective σ) (hTσ : T.1 = braidSign σ) :
    toLines x T = chambersOf x σ hσ :=
  chambersOf_congr x ((braidCOM_isTope_iff_injective T.1).mp T.2.1).choose_spec.1 hσ
    ((((braidCOM_isTope_iff_injective T.1).mp T.2.1).choose_spec.2).symm.trans hTσ)

/-- **Tope from chambers.**  The height covector `braidSign (heightOf x L)`; it is a tope
(`isTope_braidSign_heightOf`) above `x`'s covector (`faceLE_covectorHeight_heightOf`). -/
noncomputable def ofLines (x : RefineObj (□n).init (□n).final)
    (L : (RefineLines n).obj (op x)) :
    {T : SignVec (BraidGround n) //
      (braidCOM n).IsTope T ∧ braidSign (covectorHeight x) ⊑ T} :=
  ⟨braidSign (heightOf x L), isTope_braidSign_heightOf x L, faceLE_covectorHeight_heightOf x L⟩

/-- Round trip: chambers → tope → chambers is the identity (`chambersOf_heightOf`). -/
theorem toLines_ofLines (x : RefineObj (□n).init (□n).final)
    (L : (RefineLines n).obj (op x)) : toLines x (ofLines x L) = L := by
  rw [toLines_eq x (ofLines x L) (heightOf_injective x L) rfl]
  exact chambersOf_heightOf x L

/-- Round trip: tope → chambers → tope is the identity (`braidSign_heightOf_chambersOf`, whose
`faceLE` hypothesis is `T`'s own, transported along `T = braidSign σ`). -/
theorem ofLines_toLines (x : RefineObj (□n).init (□n).final)
    (T : {T : SignVec (BraidGround n) //
      (braidCOM n).IsTope T ∧ braidSign (covectorHeight x) ⊑ T}) :
    ofLines x (toLines x T) = T := by
  apply Subtype.ext
  have hσ := ((braidCOM_isTope_iff_injective T.1).mp T.2.1).choose_spec.1
  have hTσ : T.1 = braidSign ((braidCOM_isTope_iff_injective T.1).mp T.2.1).choose :=
    ((braidCOM_isTope_iff_injective T.1).mp T.2.1).choose_spec.2
  change braidSign (heightOf x (toLines x T)) = T.1
  rw [toLines_eq x T hσ hTσ, braidSign_heightOf_chambersOf x _ hσ (hTσ ▸ T.2.2)]
  exact hTσ.symm

/-! ## STEP 3 — the objectwise iso and naturality (the wall-crossing law) -/

/-- **The objectwise chamber↔tope iso.**  On the chain `x`, chamber tuples are isomorphic (in
`Type`) to the topes above `x`'s covector. -/
noncomputable def salLinesComponent (n : ℕ)
    (x : RefineObj (□n).init (□n).final) :
    (RefineLines n).obj (op x)
      ≅ (refineOpToFace n ⋙ COM.salFunctor (braidCOM n)).obj (op x) where
  hom := TypeCat.ofHom (ofLines x)
  inv := TypeCat.ofHom (toLines x)
  hom_inv_id := by
    apply ConcreteCategory.hom_ext
    intro L
    simp only [types_comp_apply, TypeCat.ofHom_apply, types_id_apply]
    exact toLines_ofLines x L
  inv_hom_id := by
    apply ConcreteCategory.hom_ext
    intro T
    simp only [types_comp_apply, TypeCat.ofHom_apply, types_id_apply]
    exact ofLines_toLines x T

/-- **The chamber presheaf is the Salvetti presheaf (transported).**  The natural isomorphism
`RefineLines n ≅ refineOpToFace n ⋙ salFunctor (braidCOM n)` of presheaves on
`(RefineObj □ⁿ)ᵒᵖ`.
Naturality is the wall-crossing law: the tope of a restricted chamber tuple is the Salvetti
composite `covectorHeight y ⊙ heightOf x L` (`wall_crossing`). -/
noncomputable def salLinesIso (n : ℕ) :
    RefineLines n ≅ refineOpToFace n ⋙ COM.salFunctor (braidCOM n) :=
  NatIso.ofComponents (fun X => salLinesComponent n X.unop) (by
    intro X Y f
    apply ConcreteCategory.hom_ext
    intro L
    change ofLines Y.unop ((RefineLines n).map f L)
        = (COM.salFunctor (braidCOM n)).map ((refineOpToFace n).map f)
            (ofLines X.unop L)
    rw [COM.salFunctor_map_apply]
    apply Subtype.ext
    change braidSign (heightOf Y.unop ((RefineLines n).map f L))
        = braidSign (covectorHeight Y.unop) ⊙ braidSign (heightOf X.unop L)
    have hw := wall_crossing f.unop L
    rwa [Quiver.Hom.op_unop] at hw)

/-! ## STEP 4 — assembly -/

/-- **THE MAIN THEOREM.**  The Salvetti face poset of the braid oriented matroid `braidCOM n` is
equivalent to the category of elements of the chamber presheaf `Lines` on the cube-chain category
of `□ⁿ` — i.e. to `Int(Lines(□ⁿ))`.  This identifies the Salvetti complex of the braid arrangement
with the retraction model of directed lines in the `n`-cube. -/
noncomputable def braidSalEquiv (n : ℕ) :
    Sal (braidCOM n) ≌ (CubeChains.Lines (□n)).Elements :=
  haveI : (refineOpToFace n).IsEquivalence := { }
  (COM.salElementsEquiv (braidCOM n)).trans <|
    (CategoryOfElements.preEquivalence (COM.salFunctor (braidCOM n))
        (refineOpToFace n).asEquivalence).symm.trans <|
      (CategoryOfElements.mapEquivalence (salLinesIso n).symm).trans (refineLinesEquiv n)

end CubeChains
