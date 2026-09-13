import CubeChains.Concurrency.Presentation.BeadOrder
import CubeChains.Concurrency.Merge.CubeWeakEquiv
import CubeChains.Machinery.Presentation.Taut

/-!
# Concurrency/Presentation/Dehornoy — the Garside germ of a shape, and what it presents

`dehornoyPoly n` is the **Dehornoy germ** of the braid monoid on `n` strands: 0-cells the
permutations, 1-cells the simples crossed length-additively, 2-cells `σ·τ ↦ στ` and `1 ↦ ε`.  It is
`taut (WeakOrder n)` — the germ of the right weak Bruhat order — so that it presents that order is
`tautPresents`, the collapse of a word to its composite.

`garsidePolyList l` is the same germ one bead at a time: `taut (wedgeOrder l)`, on bead tuples.
`wedgeOrder (n :: rest)` *is* a product of categories, so the splitting of the polygraph over a
junction is `tautProdIso` and nothing else (`garsidePolyListCons`), and the recursion below happens
in the **orders**: `Ch(⋁l)[W⁻¹]` read backwards is `wedgeOrder l` (`wedgeLocOrder`), bead by bead,
by `locCubeWeakOrder` and `locChConsEquiv`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits

namespace ChainCat

instance isThin_weakOrder (n : ℕ) : Quiver.IsThin (WeakOrder n) := fun _ _ => inferInstance

/-! ## The germ -/

/-- **The Garside germ of the braid monoid on `n` strands** — the weak order's own arrows as
generators, composition and identity as relations. -/
def dehornoyPoly (n : ℕ) : Polygraph.{0, 0, 0} := taut (WeakOrder n)

/-- **…presenting the right weak Bruhat order on `Sₙ`.** -/
def dehornoyPresents (n : ℕ) : Presents (dehornoyPoly n) (WeakOrder n) := tautPresents (WeakOrder n)

/-- **One Dehornoy germ per bead**, multiplied — the Garside polygraph of a shape. -/
def garsidePolyList (l : List ℕ+) : Polygraph.{0, 0, 0} := taut (wedgeOrder l)

/-- **…presenting the beads' orders.** -/
def garsidePolyListPresents (l : List ℕ+) : Presents (garsidePolyList l) (wedgeOrder l) :=
  tautPresents (wedgeOrder l)

/-! ## The 1-cells are the simples

A 1-cell is a rise in the weak order, and a rise *is* a germ step at the simple it crosses — the gap
`x⁻¹y`, crossed length-additively.  That is the dictionary between the germ's cells and the braid
monoid's generators; nothing below reads a 1-cell any other way. -/

/-- **A germ step rises in the weak order.** -/
theorem le_of_germStep {n : ℕ} {β : PosBraid n} {σ τ : Equiv.Perm (Fin n)}
    (h : CubeChains.GermStep β σ τ) : WeakOrder.of σ ≤ WeakOrder.of τ := by
  rw [h.mul_eq]
  exact WeakOrder.le_of_mul (by rw [← h.mul_eq]; exact h.permLen_add)

/-- **…and every rise is one**, at the simple that names the gap. -/
theorem germStep_of_le {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (h : WeakOrder.of σ ≤ WeakOrder.of τ) :
    CubeChains.GermStep (posPerm (σ⁻¹ * τ)) σ τ :=
  (germStep_posPerm_iff _ σ τ).mpr ⟨(mul_inv_cancel_left σ τ).symm, WeakOrder.le_def.mp h⟩

/-- **A 1-cell of the Dehornoy germ crosses its own gap.** -/
theorem germStep_of_dehornoyGen {n : ℕ} {x y : WeakOrder n} (e : (dehornoyPoly n).Gen x y) :
    CubeChains.GermStep (posPerm ((WeakOrder.perm x)⁻¹ * WeakOrder.perm y)) (WeakOrder.perm x)
      (WeakOrder.perm y) :=
  germStep_of_le (leOfHom e)

/-- …and every length-additive crossing is a 1-cell. -/
def dehornoyGen_of_germStep {n : ℕ} {β : PosBraid n} {x y : WeakOrder n}
    (h : CubeChains.GermStep β (WeakOrder.perm x) (WeakOrder.perm y)) : (dehornoyPoly n).Gen x y :=
  homOfLE (le_of_germStep h)

/-! ## The splitting over a junction

`wedgeOrder (n :: rest)` is a product of categories on the nose, so the germ of a junction splits
with no comparison of its own: a 2-cell is a word, a word of a product is a pair of words, and the
identity relation pads the shorter one. -/

/-- **The head bead splits off the Garside polygraph.** -/
noncomputable def garsidePolyListCons (n : ℕ+) (rest : List ℕ+) :
    garsidePolyList (n :: rest) ≅ dehornoyPoly (n : ℕ) ⨯ garsidePolyList rest :=
  tautProdIso (WeakOrder (n : ℕ)) (wedgeOrder rest)

/-- **The beads of a concatenation are the beads of its halves** — the cons recursion, one junction
at a time, with no permutation in it.  The base case is the unit: the empty shape carries one tuple,
so adjoining it is `Functor.prod'` against a constant and dropping it is `Prod.snd`. -/
noncomputable def garsidePolyListAppend : ∀ (l l' : List ℕ+),
    garsidePolyList (l ++ l') ≅ garsidePolyList l ⨯ garsidePolyList l'
  | [], l' =>
      tautMapIso (((CategoryTheory.Functor.const (wedgeOrder l')).obj (WeakOrder.of 1)).prod' (𝟭 _))
          (CategoryTheory.Prod.snd (wedgeOrder []) (wedgeOrder l'))
          (CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => wedgeOrder_hom_eq _ _)
          (CategoryTheory.Functor.ext (fun _ => Prod.ext (wedgeOrder_nil_eq _ _) rfl)
            fun _ _ _ => CategoryTheory.Prod.hom_ext (Subsingleton.elim _ _)
              (wedgeOrder_hom_eq _ _)) ≪≫
        tautProdIso (wedgeOrder []) (wedgeOrder l')
  | n :: rest, l' =>
      garsidePolyListCons n (rest ++ l') ≪≫
        prod.mapIso (Iso.refl _) (garsidePolyListAppend rest l') ≪≫
        (Limits.prod.associator _ _ _).symm ≪≫
        prod.mapIso (garsidePolyListCons n rest).symm (Iso.refl _)

/-! ## What the localized chains of a wedge are

`Ch(□n)[W⁻¹]` read backwards is the weak order (`locCubeWeakOrder`), the head bead splits off
(`locChConsEquiv`), and the recursion happens in the orders: `wedgeOrder (n :: rest)` is already the
product the splitting produces. -/

/-- **`Ch(□ⁿ)[W⁻¹]` read backwards is the right weak Bruhat order on `Sₙ`.** -/
noncomputable def cubeLocOrder (n : ℕ) : WeakOrder n ≌ ((W (□n)).Localization)ᵒᵖ :=
  ((locCubeWeakOrder n).op.trans (opOpEquivalence (WeakOrder n))).symm

/-- **…so the Dehornoy germ of `Sₙ` presents it.** -/
noncomputable def dehornoyCube (n : ℕ) :
    Presents (dehornoyPoly n) (((W (□n)).Localization)ᵒᵖ) :=
  (dehornoyPresents n).transport (cubeLocOrder n)

/-- **The first bead splits off the localized wedge**, read backwards. -/
noncomputable def consLocOrder (n : ℕ+) (rest : List ℕ+) :
    ((W (□(n : ℕ))).Localization)ᵒᵖ × ((W (⋁rest)).Localization)ᵒᵖ
      ≌ ((W (⋁(n :: rest))).Localization)ᵒᵖ :=
  (prodOpEquiv _).symm.trans (locChConsEquiv n rest).op

/-- **The localized chains of a wedge are the beads' orders**, read backwards — one junction at a
time, with nothing to collect: the tuples are already the product. -/
noncomputable def wedgeLocOrder : (l : List ℕ+) → (wedgeOrder l ≌ ((W (⋁l)).Localization)ᵒᵖ)
  | [] => cubeLocOrder 0
  | n :: rest => ((cubeLocOrder (n : ℕ)).prod (wedgeLocOrder rest)).trans (consLocOrder n rest)

/-- **…and the beads' Dehornoy germs, multiplied, present them.** -/
noncomputable def garsideWedgePresents (l : List ℕ+) :
    Presents (garsidePolyList l) (((W (⋁l)).Localization)ᵒᵖ) :=
  (garsidePolyListPresents l).transport (wedgeLocOrder l)

/-- **The localized slice over a chain is presented by the Dehornoy germs of its beads.** -/
noncomputable def garsideSlicePresents (d : Ch Zbp) :
    Presents (garsidePolyList d.dims) ((((W Zbp).over (X := d)).Localization)ᵒᵖ) :=
  (garsideWedgePresents d.dims).transport (locOverEquivWedge d).op.symm

/-! ## What a 0-cell names

Every step above is read *forwards* on a `Q`-image, so the object a tuple names is the chain it is:
the beads' runs, concatenated. -/

/-- **The wedge splitting names the concatenated runs.** -/
theorem wedgeLocOrder_functor_obj : ∀ (l : List ℕ+) (x : wedgeOrder l),
    (wedgeLocOrder l).functor.obj x = op ((W (⋁l)).Q.obj (wedgeRunChain l x))
  | [], _ => rfl
  | n :: rest, x =>
      congrArg (fun y : ((W (⋁rest)).Localization)ᵒᵖ =>
          (consLocOrder n rest).functor.obj
            (op ((W (□(n : ℕ))).Q.obj (wordRun (WeakOrder.perm x.1)).chain), y))
        (wedgeLocOrder_functor_obj rest x.2)

/-- **A 0-cell of the slice polygraph names the run it is.** -/
theorem garsideSlicePresents_at (d : Ch Zbp) (x : wedgeOrder d.dims) :
    (garsideSlicePresents d).at' ⟨x⟩
      = op (((W Zbp).over (X := d)).Q.obj (wedgeRunOver d x).1) :=
  congrArg ((locOverEquivWedge d).op.symm).functor.obj (wedgeLocOrder_functor_obj d.dims x)

end ChainCat
