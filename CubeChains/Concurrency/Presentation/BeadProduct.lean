import CubeChains.Concurrency.Presentation.ChartFibre
import CubeChains.Concurrency.Presentation.BasePresentation
import CubeChains.Concurrency.Merge.CubeWeakEquiv
import CubeChains.Concurrency.Merge.WedgeLocalize
import CubeChains.Machinery.Presentation.Product
import CubeChains.Machinery.Presentation.Opposite

/-!
# Concurrency/Presentation/BeadProduct — a localized slice is a product over its beads

`⋁(n :: rest)` *is* `□n ∨ ⋁rest`, so the slice over a shape is the product of the slices over its
one-bead shapes (`locChConsEquiv`), and `Presents.prod` builds the presentation from the factors'
with no reindexing and no `eqToHom`.

The one-bead factor is the **whole** symmetric group acting: over `[n]` every permutation is a run,
so the only partiality left is length-additivity, and the defined part of that action is the weak
order entire (`chartsWeakEquiv`).  So the strand-count gluing plays no part here — a bead pins its
own count — but the `Option` layer does not go away: it *is* the length-additivity.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Equiv

namespace ChainCat

/-! ## The one bead

`weakActionOn` at the unrestricted set: `PosBraid n` acting on all of `Perm (Fin n)` by
length-additive right multiplication. -/

/-- **The braid monoid acting on every permutation**, by length-additive right multiplication. -/
noncomputable def beadAction (N : ℕ) : PosBraid N →* (strictEnd (Equiv.Perm (Fin N)))ᵐᵒᵖ :=
  weakActionOn _ ((Equiv.refl (Equiv.Perm (Fin N))).trans (weakSetUniv N).symm) weakDown_univ

/-- The defined part of that action: one 0-cell per permutation, one arrow per rise. -/
abbrev BeadCharts (n : ℕ) : Type := ChartsAt beadAction n

/-- **The defined charts of one bead are the right weak order.** -/
noncomputable def beadChartsWeak (n : ℕ) : BeadCharts n ≌ WeakOrder n :=
  chartsWeakEquiv beadAction (Equiv.refl _) rfl

/-- **The one-bead slice polygraph**: the base's cells at `n` strands, taken where they act. -/
noncomputable def beadPoly (p : BraidPresentation) (n : ℕ) : Polygraph.{0, 0, 0} :=
  (((p.comp n).elements (partialActionFunctor (beadAction n))).restrictPoly
    (Presents.defined _ (chartBot beadAction n))).op

/-- **…presenting `Ch(□n)[W⁻¹]`**, the slice over the one-bead shape.  Nothing but the bead's own
strand count enters, so no strand decomposition is spent. -/
noncomputable def beadPresents (p : BraidPresentation) (n : ℕ) :
    Presents (beadPoly p n) ((W (□n)).Localization) :=
  ((Presents.partialElements (partialActionFunctor (beadAction n)) (chartBot beadAction n)
      (fun g => partialActionFunctor_map_none _ g) (p.comp n)).op).transport
    ((beadChartsWeak n).op.trans (locCubeWeakOrder n).symm)

/-! ## The product over the beads -/

/-- **The slice polygraph of a shape**: one copy of the bead polygraph per bead. -/
noncomputable def wedgePoly (p : BraidPresentation) : List ℕ+ → Polygraph.{0, 0, 0}
  | [] => beadPoly p 0
  | n :: rest => Polygraph.prod (beadPoly p (n : ℕ)) (wedgePoly p rest)

/-- **…presenting `Ch(⋁d)[W⁻¹]`.**  `serialWedge_cons` is `rfl`, so the recursion carries no
transport; the interchange 2-cells of `Polygraph.prod` are what stop the beads' words from
presenting a free product. -/
noncomputable def wedgePresents (p : BraidPresentation) :
    ∀ d : List ℕ+, Presents (wedgePoly p d) ((W (⋁d)).Localization)
  | [] => beadPresents p 0
  | n :: rest =>
      (Presents.prod (beadPresents p (n : ℕ)) (wedgePresents p rest)).transport
        (locChConsEquiv n rest)

/-! ## The bead's cells, without the `Option`

The germ reading of `beadPoly`: 0-cells the simples, and a 1-cell `σ ⟶ τ` a generator of `p` that
**is** a simple and multiplies `τ` up to `σ`, adding every crossing it names.  The `Option` layer
carries the partiality of that product; a presheaf on a *one-object* category has a total action,
so the base being one object per strand count is what forces it. -/

namespace BraidPresentation

variable (p : BraidPresentation) {n : ℕ}

/-- **A generator acts exactly at a germ step.** -/
theorem beadAction_iff (s : p.S n) (τ σ : Equiv.Perm (Fin n)) :
    (beadAction n (p.braid s)).unop.val (some τ) = some σ ↔ p.GermStep s τ σ :=
  weakActionOn_eq_some_iff_germStep _ _ weakDown_univ (p.braid s) τ σ

/-- The 0-cell a simple names. -/
def beadPt (σ : Equiv.Perm (Fin n)) : (beadPoly p n).V := ⟨⟨p.v n, some σ⟩, Option.some_ne_none σ⟩

/-- …and the simple a 0-cell names. -/
noncomputable def beadRun (a : (beadPoly p n).V) : Equiv.Perm (Fin n) :=
  a.1.2.get (Option.ne_none_iff_isSome.mp a.2)

/-- **The 0-cells of the bead polygraph are the simples.** -/
noncomputable def beadV (n : ℕ) : (beadPoly p n).V ≃ Equiv.Perm (Fin n) where
  toFun := p.beadRun
  invFun := p.beadPt
  left_inv a := by
    obtain ⟨⟨x, o⟩, ho⟩ := a
    obtain rfl : x = p.v n := p.eq_v x
    obtain ⟨σ, rfl⟩ := Option.ne_none_iff_exists'.mp ho
    rfl
  right_inv _ := rfl

/-- **The 1-cells of the bead polygraph are the germ steps** — one per generator of `p` that acts,
so the bead's presentation moves when `p` does. -/
def beadGenEquiv (σ τ : Equiv.Perm (Fin n)) :
    ((⟨p.beadPt σ⟩ : GenObj (beadPoly p n).Gen) ⟶ ⟨p.beadPt τ⟩)
      ≃ {s : p.S n // p.GermStep s τ σ} :=
  Equiv.subtypeEquivRight fun s => p.beadAction_iff s τ σ

end BraidPresentation

/-! ## Functoriality in the shape

An arrow of `Ch Zbp` merges beads, so a family indexed by shapes must carry
`(bead a) × (bead b) ⟶ (bead (a+b))`: a **lax monoidal** structure for the block sum.

At the level of the *categories* that structure is free — `weakOrderSum`, below, because
`permLen_permSum` says the two blocks never interact.  At the level of the *cells* it is not: a
1-cell of the product polygraph is labelled by a generator of `p` at its own bead's strand count,
and the merge changes that count, so the family needs `p`'s generators to include with the blocks
(`BraidPresentation.Blocks`).  `dimSum` is constant along an arrow of `Ch Zbp`, which is exactly why
the *un-split* slice family needs no such datum: there every 1-cell is labelled at the one strand
count `dimSum d`, and only the 0-cells move.

**The gluing obligation is a different matter.**  `presentsSliceColimit` asks its family for an
*equality* of functors, so the 0-cells must name their slice objects on the nose.  `wedgePresents`
transports along `locChConsEquiv`, which is `Localization.uniq`, and that carries only a natural
iso (`Localization.compUniqFunctor`) — a localized slice is thin but never skeletal, so an iso of
objects is not an equality of them.  This is why the splitting describes the *category* and not the
presentation. -/

/-- **The block sum is monotone for the weak order** — `permSum` is a monoid map and
`permLen_permSum` adds, so the difference of two block sums is the block sum of the differences and
its length splits. -/
theorem weakOrder_permSum_le {a b : ℕ} {σ σ' : Equiv.Perm (Fin a)} {τ τ' : Equiv.Perm (Fin b)}
    (hσ : WeakOrder.of σ ≤ WeakOrder.of σ') (hτ : WeakOrder.of τ ≤ WeakOrder.of τ') :
    WeakOrder.of (permSum a b (σ, τ)) ≤ WeakOrder.of (permSum a b (σ', τ')) := by
  simp only [WeakOrder.le_def, WeakOrder.perm_of] at hσ hτ ⊢
  have hdiff : (permSum a b (σ, τ))⁻¹ * permSum a b (σ', τ')
      = permSum a b (σ⁻¹ * σ', τ⁻¹ * τ') := by
    rw [← map_inv, ← map_mul]; rfl
  rw [hdiff]
  simp only [permLen_permSum] at hσ hτ ⊢
  omega

/-- **The weak orders are lax monoidal for the block sum** — the comparison a merge of beads
performs, read on the categories the beads present. -/
def weakOrderSum (a b : ℕ) : WeakOrder a × WeakOrder b ⥤ WeakOrder (a + b) where
  obj x := WeakOrder.of (permSum a b (WeakOrder.perm x.1, WeakOrder.perm x.2))
  map f := homOfLE (weakOrder_permSum_le (leOfHom f.1) (leOfHom f.2))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **What a product family asks of the base presentation**: a generator at a bead's own strand
count, read as one at the strand count of the block that bead merges into.  `BraidPresentation`
does not carry this, and the un-split slice family never needs it. -/
structure BraidPresentation.Blocks (p : BraidPresentation) where
  /-- a generator of the left block -/
  left : ∀ a b : ℕ, p.S a → p.S (a + b)
  /-- …performing its own simple, block-summed with the identity -/
  left_braid : ∀ (a b : ℕ) (s : p.S a),
    p.braid (left a b s) = posPerm (permSum a b (p.perm s, 1))
  /-- a generator of the right block -/
  right : ∀ a b : ℕ, p.S b → p.S (a + b)
  /-- …likewise -/
  right_braid : ∀ (a b : ℕ) (s : p.S b),
    p.braid (right a b s) = posPerm (permSum a b (1, p.perm s))

end ChainCat
