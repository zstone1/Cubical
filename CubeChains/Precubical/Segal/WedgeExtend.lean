import CubeChains.Precubical.Segal.Segal

/-!
# Precubical/Segal/WedgeExtend — lifting a presheaf on `Box` to serial wedges

`F↑ X := (X.toPsh ⟶ F)` is precomposition, so it turns the wedge colimit into a *limit*: with a
single vertex in `F ▫0`, `F↑ (⋁a)` is the product `∏ᵢ F ▫aᵢ` — `pshExtWedge2` binary, `pshExtProd`
iterated.  That descent is the *monoidal* content, the general form of "`Run` is monoidal"; `F↑`
being a hom-set, the functor itself needs no carrier and is `pshExtFunctor`
(`Precubical/Segal/PshExtMonoidal`).
-/

open CategoryTheory Opposite BPSet

namespace ChainCat

/-- **`F↑` sends a wedge to a product of bead values** — the wedge pushout read as a pullback, its
glue condition discharged by single-vertexness. -/
def pshExtWedge2 (F : PrecubicalSet) (hF : ∀ p q : (□0).toPsh ⟶ F, p = q) (X Y : BPSet) :
    ((X ∨ Y).toPsh ⟶ F) ≃ (X.toPsh ⟶ F) × (Y.toPsh ⟶ F) where
  toFun φ := (Glue.inl X.finalVertex Y.initVertex ≫ φ, Glue.inr X.finalVertex Y.initVertex ≫ φ)
  invFun p := Glue.desc (f := X.finalVertex) (g := Y.initVertex) p.1 p.2 (hF _ _)
  left_inv φ := Glue.hom_ext (by rw [Glue.inl_desc]) (by rw [Glue.inr_desc])
  right_inv p := by
    refine Prod.ext ?_ ?_
    · exact Glue.inl_desc _ _ _
    · exact Glue.inr_desc _ _ _

/-- The iterated product a wedge decomposes to: one bead value per bead. -/
def pshExtProdType (F : PrecubicalSet) : List ℕ+ → Type
  | [] => PUnit
  | c :: rest => ((□(c : ℕ)).toPsh ⟶ F) × pshExtProdType F rest

/-- **`F↑` sends a serial wedge to the iterated product of bead values** — the general
`runSegalProd`.  `pt` inhabits the empty-wedge value, `hF` collapses it. -/
def pshExtProd (F : PrecubicalSet) (pt : (□0).toPsh ⟶ F) (hF : ∀ p q : (□0).toPsh ⟶ F, p = q) :
    (a : List ℕ+) → ((⋁a).toPsh ⟶ F) ≃ pshExtProdType F a
  | [] =>
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => pt
      left_inv := fun φ => hF pt φ
      right_inv := fun _ => rfl }
  | c :: rest =>
    (pshExtWedge2 F hF (□(c : ℕ)) (⋁rest)).trans
      ((Equiv.refl ((□(c : ℕ)).toPsh ⟶ F)).prodCongr (pshExtProd F pt hF rest))

end ChainCat
