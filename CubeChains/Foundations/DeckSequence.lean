import CubeChains.Foundations.QuotientCovering

/-!
# Foundations/DeckSequence — the deck-transformation sequence of a regular groupoid covering

For an order-free action `G ↷ P`, `quotFunctor : P ⥤ QuotCat P G` is a covering
(`QuotientCovering`), and `FreeGroupoid.map quotFunctor` is the induced covering of groupoids.
This file reads off the **monodromy** of a downstairs loop at `⟦x⟧`: lift it (uniquely, `liftPS`)
to a path out of `x`, whose endpoint `endpt` lands in the fibre `G • x`.

The load-bearing output is **middle exactness** (`mem_range_mapAut_iff`): a loop at `⟦x⟧` is the
image of an upstairs loop **iff** its lift returns to `x` (trivial monodromy).  Combined with
`quotFunctor_freeMap_faithful` (injectivity, the "a covering is π₁-injective"), this is the
covering content of the deck sequence

```
1 → π₁(FreeGroupoid P, x) → π₁(FreeGroupoid (QuotCat P G), ⟦x⟧) → G → 1.
```

The engine is unique lifting of zigzag words (`liftPS`, `pathLiftEquiv`) plus reflection of the
word relation (`reflectPS`), both from `QuotientCovering`.
-/

open CategoryTheory CategoryTheory.FreeGroupoid Quiver Relation

namespace OrderQuotient

open MulAction QuotCat

variable {G P : Type*} [Group G] [PartialOrder P] [MulAction G P] [OrderFreeAction G P]

/-! ## The lift endpoint of a word

`endptW x w` is the endpoint of the unique upstairs lift, based at `x`, of a downstairs word `w`
out of `⟦x⟧`.  The word need not be a loop; for a loop it lands in the fibre `G • x`. -/

/-- The endpoint of the unique upstairs lift of a downstairs word `w` out of `⟦x⟧`, based at `x`. -/
noncomputable def endptW (x : P)
    {D : Quiver.Symmetrify (QuotCat P G)}
    (w : Quiver.Path ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x) D) : P :=
  (liftPS x ⟨D, w⟩).1

/-- **Endpoint recovers the lift of a `mapPath`.**  Lifting the `φ`-image of an upstairs word `wt`
based at `x` returns `wt` itself, so the endpoint is `wt`'s — covering uniqueness. -/
theorem endptW_mapPath (x v : P)
    (wt : Quiver.Path (V := Quiver.Symmetrify P) x v) :
    endptW x ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath wt) = v := by
  have key := liftPS_pathLiftEquiv (G := G) (P := P) x ⟨v, wt⟩
  have himg : pathLiftEquiv (G := G) (P := P) x ⟨v, wt⟩
      = (⟨_, (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath wt⟩ :
          Quiver.PathStar ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x)) :=
    pathLiftEquiv_apply x ⟨v, wt⟩
  change (liftPS x ⟨_, (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath wt⟩).1 = v
  rw [← himg, key]

/-- `mapPath` commutes with endpoint recasting. -/
theorem mapPath_cast {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W)
    {a b b' : V} (hb : b = b') (p : Quiver.Path a b) :
    F.mapPath (p.cast rfl hb) = (F.mapPath p).cast rfl (congrArg F.obj hb) := by
  subst hb
  rw [Quiver.Path.cast_rfl_rfl, Quiver.Path.cast_rfl_rfl]

/-- The lift endpoint of a loop-word stays in the fibre over `⟦x⟧`. -/
theorem mk_endptW (x : P)
    (w : Quiver.Path ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x)
      ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x)) :
    (Quotient.mk'' (endptW x w) : QuotCat P G) = Quotient.mk'' x :=
  liftPS_obj (G := G) (P := P) x ⟨_, w⟩

/-- **Endpoint is a homotopy invariant.**  Two loop-words representing the same free-groupoid arrow
have the same lift endpoint — the reflection of the word relation shares the endpoint. -/
theorem endptW_congr (x : P)
    {w₁ w₂ : Quiver.Path ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x)
      ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x)}
    (h : (wordFunctor (QuotCat P G)).map w₁ = (wordFunctor (QuotCat P G)).map w₂) :
    endptW x w₁ = endptW x w₂ := by
  have hEqv := eqvGen_totalRel_of_wordFunctor_map_eq h
  obtain ⟨v, p, q, hS, hT, _⟩ := reflectPS (G := G) (P := P) x hEqv
  change (liftPS x ⟨_, w₁⟩).1 = (liftPS x ⟨_, w₂⟩).1
  rw [hS, hT]

/-! ## The monodromy endpoint of a free-groupoid loop -/

/-- The lift endpoint of a free-groupoid loop `γ` at `⟦x⟧`: choose a representing word and read off
where its lift, based at `x`, lands.  Well-defined by `endptW_congr`. -/
noncomputable def endpt (x : P)
    (γ : (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G)) ⟶ mk (Quotient.mk'' x)) : P :=
  endptW x ((wordFunctor (QuotCat P G)).preimage γ)

/-- **Defining property of `endpt`.**  For any word `w` representing `γ`, `endpt x γ` is the lift
endpoint of `w`. -/
theorem endpt_spec (x : P)
    (γ : (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G)) ⟶ mk (Quotient.mk'' x))
    {w : Quiver.Path ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x)
      ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x)}
    (hw : (wordFunctor (QuotCat P G)).map w = γ) :
    endpt x γ = endptW x w :=
  endptW_congr x (((wordFunctor (QuotCat P G)).map_preimage γ).trans hw.symm)

/-- `endpt x γ` lands in the fibre over `⟦x⟧`. -/
theorem mk_endpt (x : P)
    (γ : (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G)) ⟶ mk (Quotient.mk'' x)) :
    (Quotient.mk'' (endpt x γ) : QuotCat P G) = Quotient.mk'' x :=
  mk_endptW x _

/-! ## Middle exactness of the deck sequence

A loop at `⟦x⟧` is the image of an upstairs loop iff its lift returns to `x`.  This is the
covering content that, in applications, identifies the image of `π₁(cover)` with the kernel of the
monodromy — replacing an ad-hoc surjectivity computation. -/

/-- **Middle exactness (endpoint form).**  `γ` lies in the image of `FreeGroupoid.map quotFunctor`
on the vertex group at `x` iff its lift, based at `x`, is a loop (`endpt x γ = x`). -/
theorem mem_range_mapAut_iff (x : P)
    (γ : (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G)) ⟶ mk (Quotient.mk'' x)) :
    (∃ a : (mk x : FreeGroupoid P) ⟶ mk x,
        (CategoryTheory.FreeGroupoid.map (quotFunctor (G := G) (P := P))).map a = γ)
      ↔ endpt x γ = x := by
  constructor
  · rintro ⟨a, rfl⟩
    exact (endpt_spec x _
      ((map_quotFunctor_wordFunctor ((wordFunctor P).preimage a)).symm.trans
        (congrArg _ ((wordFunctor P).map_preimage a)))).trans (endptW_mapPath x x _)
  · intro hendpt
    have hw : (wordFunctor (QuotCat P G)).map ((wordFunctor (QuotCat P G)).preimage γ) = γ :=
      (wordFunctor (QuotCat P G)).map_preimage γ
    set L := liftPS (G := G) (P := P) x ⟨_, (wordFunctor (QuotCat P G)).preimage γ⟩ with hLdef
    have hend : L.1 = x := by
      have h := endpt_spec x γ hw
      rw [hendpt] at h
      exact h.symm
    have hsym : pathLiftEquiv (G := G) (P := P) x L
        = ⟨_, (wordFunctor (QuotCat P G)).preimage γ⟩ := by
      rw [hLdef]; exact (pathLiftEquiv (G := G) (P := P) x).apply_symm_apply _
    rw [pathLiftEquiv_apply] at hsym
    have hheq : HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath L.2)
        ((wordFunctor (QuotCat P G)).preimage γ) := (Sigma.ext_iff.mp hsym).2
    -- the lift `L.2 : Path x L.1` is a loop after recasting its endpoint by `hend`
    refine ⟨(wordFunctor P).map (L.2.cast rfl hend),
      (map_quotFunctor_wordFunctor (L.2.cast rfl hend)).trans ?_⟩
    rw [mapPath_cast, (Quiver.Path.cast_eq_iff_heq rfl (congrArg _ hend) _ _).mpr hheq]
    exact hw

/-- **Injectivity of the deck sequence's left map** — "a covering is π₁-injective".  The vertex-group
map of `FreeGroupoid.map quotFunctor` is injective, packaged from `quotFunctor_freeMap_faithful`. -/
theorem mapAut_injective (x : P) :
    Function.Injective
      ((CategoryTheory.FreeGroupoid.map (quotFunctor (G := G) (P := P))).mapAut (mk x)) := by
  haveI := quotFunctor_freeMap_faithful (G := G) (P := P)
  intro a b h
  apply Aut.ext
  exact (CategoryTheory.FreeGroupoid.map (quotFunctor (G := G) (P := P))).map_injective
    (congrArg Iso.hom h)

end OrderQuotient
