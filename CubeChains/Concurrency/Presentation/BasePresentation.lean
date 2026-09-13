import CubeChains.Concurrency.Presentation.BaseDecomposition
import CubeChains.Machinery.SigmaComponents
import CubeChains.Machinery.Presentation.Restrict
import CubeChains.Machinery.Presentation.Coproduct
import CubeChains.Machinery.Presentation.Monoid
import CubeChains.Machinery.Presentation.Comparison

/-!
# Concurrency/Presentation/BasePresentation — `Ch Zbp[W⁻¹]` as a single polygraph

The localized base *is* the graded positive braid monoid (`fullBaseEquiv`): one object per strand
count, its endomorphisms the braids on that many strands.  A `BraidPresentation` presents that
category, in one polygraph — the **coproduct of one-object polygraphs**, one per strand count — so
there is no vertex to declare unique.

`pt` names the 0-cell at a strand count and `count` reads it back, bijectively.  Both compute, and
the base is read through `zLocSigma` rather than through `FullPosBraid`, so `base_at'` — "the
strand-`N` 0-cell names the run" — is `rfl` and nothing a generator names carries a transport.

`zLocComponent` runs the other way, by `Presents.restrict`: an *arbitrary* presentation of the
localized base restricts to one of each strand component.

At strand count `N` the 1-cells are `Perm (Fin N)` — the maps `1ᴺ ⟶ [N]`, by `onesTopEquiv` — and
the 2-cells are `PosGermRel N`: two simples compose when their crossing lengths add.
-/

open CategoryTheory Opposite CubeChains

namespace ChainCat

/-- The germ presentation of `PosBraid n`; the ascription is the point, `PosBraid` being a `def`. -/
def germPresentation (n : ℕ) : Presents (monoidPoly (PosGermRel n)) ((SingleObj (PosBraid n))ᵒᵖ) :=
  presentedMonoidPresentation (PosGermRel n)

/-- The Artin presentation of `ArtinPosBraid n`. -/
def artinPresentation (n : ℕ) :
    Presents (monoidPoly (ArtinRel n)) ((SingleObj (ArtinPosBraid n))ᵒᵖ) :=
  presentedMonoidPresentation (ArtinRel n)

/-- **…read on the positive braids**, along Artin-from-Garside — the Artin spelling of the same
component, in the shape the lift consumes. -/
noncomputable def artinComponent (n : ℕ) :
    Presents (monoidPoly (ArtinRel n)) ((SingleObj (PosBraid n))ᵒᵖ) :=
  (artinPresentation n).transport ((MulEquiv.toSingleObjEquiv (posBraid_equiv_artinPos n)).op).symm

/-- No arrow enters or leaves a strand component, so a word between two of its objects stays
inside — the one hypothesis `Presents.restrict` takes. -/
theorem convex_atStrands (N : ℕ) : (AtStrands N).Convex := fun ha _ f _ =>
  (ObjectProperty.prop_iff_of_hom AtStrands exists_atStrands
    (fun hX hY g => atStrands_eq_of_hom hX hY g) f).mp ha

/-- **…and every presentation of the localized base restricts to one of each strand component** —
`Presents.restrict` at a strand component, read through `strandComponentGarside`. -/
noncomputable def zLocComponent {P : Polygraph} (p : Presents P (((W Zbp).op).Localization))
    (N : ℕ) : Presents (p.restrictPoly (AtStrands N)) ((SingleObj (PosBraid N))ᵒᵖ) :=
  (p.restrict (AtStrands N) (convex_atStrands N)).transport (strandComponentGarside N).symm

/-! ## The input, bundled

The 0-cells are named by the strand counts and the 1-cells at one of them are the generators there,
so a `BraidPresentation` is a monoid presentation of each braid monoid *plus* the way the blocks
juxtapose.  Everything downstream is a lift of that. -/

/-- The braid a generator of a one-object presentation performs; the 0-cells are explicit because
there is exactly one and the generator does not name it. -/
def loopBraid {A R : Type} {sr tr : R → Quiver.Path (Polygraph.loopPt A) (Polygraph.loopPt A)}
    {N : ℕ} (q : Presents (Polygraph.loopPoly A R sr tr) ((SingleObj (PosBraid N))ᵒᵖ)) (s : A) :
    PosBraid N :=
  (q.arrow (x := Polygraph.loopPt A) (y := Polygraph.loopPt A) s).unop

/-- The one-object polygraph a braid presentation carries at one strand count. -/
abbrev strandFibre (Gen Rel : ℕ → Type)
    (src tgt : ∀ N : ℕ, Rel N → Quiver.Path (Polygraph.loopPt (Gen N)) (Polygraph.loopPt (Gen N)))
    (N : ℕ) : Polygraph.{0, 0, 0} :=
  Polygraph.loopPoly (Gen N) (Rel N) (src N) (tgt N)

/-- **A presentation of the graded positive braid monoid**: generators and relations at each strand
count, read as a single polygraph — the coproduct over the strand counts. -/
structure BraidPresentation where
  /-- the generators at each strand count -/
  Gen : ℕ → Type
  /-- the relations there -/
  Rel : ℕ → Type
  /-- a relation's source word -/
  src : ∀ N : ℕ, Rel N → Quiver.Path (Polygraph.loopPt (Gen N)) (Polygraph.loopPt (Gen N))
  /-- …and its target -/
  tgt : ∀ N : ℕ, Rel N → Quiver.Path (Polygraph.loopPt (Gen N)) (Polygraph.loopPt (Gen N))
  /-- …presenting the braid monoid on that many strands -/
  part : ∀ N : ℕ, Presents (strandFibre Gen Rel src tgt N) ((SingleObj (PosBraid N))ᵒᵖ)

namespace BraidPresentation

variable (p : BraidPresentation)

/-- The polygraph at one strand count: `p`'s generators and relations there, at a single 0-cell. -/
abbrev P (N : ℕ) : Polygraph.{0, 0, 0} := strandFibre p.Gen p.Rel p.src p.tgt N

/-- The 0-cell at strand count `N`; there is exactly one, by construction. -/
def v (N : ℕ) : (p.P N).V := ()

theorem eq_v {N : ℕ} (x : (p.P N).V) : x = p.v N := rfl

/-- The generators at strand count `N`: the 1-cells at its 0-cell. -/
def S (N : ℕ) : Type := (p.P N).Gen (p.v N) (p.v N)


/-- **The polygraph**: one copy of `p`'s one-object polygraph per strand count. -/
def poly : Polygraph.{0, 0, 0} := Polygraph.coprod p.P

/-- The strand-`N` polygraph, included in the whole. -/
def incl (N : ℕ) : p.P N ⟶ p.poly := Polygraph.coprodι p.P N

/-- …on the generating quivers. -/
def pre (N : ℕ) : GenObj (p.P N).Gen ⥤q GenObj p.poly.Gen := (p.incl N).pre

@[simp] theorem incl_pre (N : ℕ) : (p.incl N).pre = p.pre N := rfl

instance pre_faithful (N : ℕ) : (p.pre N).pathsFunctor.Faithful :=
  Polygraph.coprod_pathsFunctor_faithful p.P N

/-- **…presenting the graded positive braid monoid** — one object per strand count, its
endomorphisms the braids on that many strands. -/
noncomputable def braids : Presents p.poly (FullPosBraid)ᵒᵖ :=
  (Presents.coproduct p.part).transport Graded.sigmaEquiv

/-- **…and hence `Ch Zbp[W⁻¹]`**, read through `zLocSigma` so that a leg of the coproduct names its
own run and performs its own braids, with nothing in between. -/
noncomputable def base : Presents p.poly (((W Zbp).op).Localization) :=
  (Presents.coproduct p.part).transport zLocEquiv

/-- The 0-cell at strand count `N`.  A leg has exactly one, so `Unit`'s eta makes every 0-cell of
the strand-`N` copy this one. -/
noncomputable def pt (N : ℕ) : GenObj p.poly.Gen := (p.pre N).obj (Polygraph.loopPt (p.Gen N))

/-- A generator, as a 1-cell. -/
noncomputable def gen {N : ℕ} (s : p.S N) : p.pt N ⟶ p.pt N := (p.pre N).map s

/-- **A 1-cell at one strand count is a generator there** — the legs of a coproduct are
star-bijective. -/
theorem exists_gen {N : ℕ} (e : p.pt N ⟶ p.pt N) : ∃ s : p.S N, p.gen s = e := by
  obtain ⟨⟨z, s⟩, hs⟩ :=
    Polygraph.coprod_star_surjective p.P N (Polygraph.loopPt (p.Gen N)) ⟨p.pt N, e⟩
  exact ⟨s, eq_of_heq (Sigma.mk.inj_iff.mp hs).2⟩

/-- **A 1-cell of `p.poly` joins one strand count to itself.** -/
theorem pt_eq_of_hom {M N : ℕ} (e : p.pt M ⟶ p.pt N) : M = N :=
  (Polygraph.coprodFibre_ι p.P M _).symm.trans
    ((Polygraph.coprodFibre_eq_of_hom p.P e).trans (Polygraph.coprodFibre_ι p.P N _))

/-- **Every 0-cell of `p.poly` is a strand count's.** -/
theorem exists_pt (x : GenObj p.poly.Gen) : ∃ N : ℕ, p.pt N = x := by
  obtain ⟨N, y, rfl⟩ := Polygraph.exists_coprod_obj p.P x
  exact ⟨N, rfl⟩

theorem pt_injective : Function.Injective p.pt := fun _ _ h =>
  Polygraph.coprod_index_eq p.P h

/-- The strand count a 0-cell names — the leg it lies in. -/
noncomputable def count (x : GenObj p.poly.Gen) : ℕ := Polygraph.coprodFibre p.P x

@[simp] theorem count_pt (N : ℕ) : p.count (p.pt N) = N := Polygraph.coprodFibre_ι p.P N _

@[simp] theorem pt_count (x : GenObj p.poly.Gen) : p.pt (p.count x) = x := by
  obtain ⟨N, rfl⟩ := p.exists_pt x
  rw [p.count_pt]

/-- The braid a generator names — the strand count has one 0-cell, so its loops *are* the
braids. -/
def braid {N : ℕ} (s : p.S N) : PosBraid N := loopBraid (p.part N) s

/-- …and its permutation. -/
def perm {N : ℕ} (s : p.S N) : Equiv.Perm (Fin N) := posPermHom N (p.braid s)

def BySimples : Prop := ∀ (N : ℕ) (s : p.S N), p.braid s = posPerm (p.perm s)

/-- **A generator of `p` carries `u` to `v` length-additively** — the germ condition at one
generator: `s` is a simple, and every pair it names is crossed anew.  This is the only relation the
inherited cells ever carry, and `Ch Zbp[W⁻¹]`'s partiality is exactly its failure. -/
def GermStep {N : ℕ} (s : p.S N) (u v : Equiv.Perm (Fin N)) : Prop :=
  CubeChains.GermStep (p.braid s) u v

/-- **The 0-cell at strand count `N` names the run** — a leg of `coprod` is definitional and
`zLocSigma` reads it at `runBase N`, so there is nothing between the two spellings. -/
theorem base_at' (N : ℕ) : p.base.at' (p.pt N) = ((W Zbp).op).Q.obj (op (zObj (𝟙^N))) := rfl

/-- **A whole word of one strand count names the loop that word's braid is** — the strand-`N`
component, included. -/
theorem base_eval_pre {N : ℕ} {x y : GenObj (p.P N).Gen} (w : Quiver.Path x y) :
    p.base.eval.map ((p.pre N).mapPath w) = (runBase N).map ((p.part N).eval.map w) :=
  congrArg zLocSigma.map (Presents.lift_coproductEval_mapPath p.part N w)

/-- **A generator names the loop at the run its braid is.** -/
theorem base_arrow {N : ℕ} (s : p.S N) :
    p.base.arrow (p.gen s) = (runBase N).map (posArrow N (p.braid s)) :=
  p.base_eval_pre (Quiver.Hom.toPath s)

/-- **A simple generator names the loop its permutation spells.** -/
theorem base_arrow_of_simple (hp : p.BySimples) {N : ℕ} (s : p.S N) :
    p.base.arrow (p.gen s) = runLoop N (p.perm s) :=
  (p.base_arrow s).trans (congrArg (fun β => (runBase N).map (posArrow N β)) (hp N s))

/-- **A monoid presentation of every braid monoid is one** — the constructor the two spellings
below use, and the only place `PresentedMonoid` enters. -/
noncomputable def ofMonoids {S : ℕ → Type}
    (rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop)
    (e : ∀ N, PresentedMonoid (rels N) ≃* PosBraid N) :
    BraidPresentation where
  Gen := S
  Rel := fun N => monoidRel (rels N) (monoidPt (rels N)) (monoidPt (rels N))
  src := fun _ α => α.1.1
  tgt := fun _ α => α.1.2
  part := fun N =>
    (presentedMonoidPresentation (rels N)).transport (MulEquiv.toSingleObjEquiv (e N)).op

@[simp] theorem ofMonoids_braid {S : ℕ → Type}
    {rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop}
    {e : ∀ N, PresentedMonoid (rels N) ≃* PosBraid N} {N : ℕ}
    (s : (ofMonoids rels e).S N) :
    (ofMonoids rels e).braid s
      = e N (PresentedMonoid.mk (rels N) (FreeMonoid.of s)) := rfl

end BraidPresentation

/-- **`Ch Zbp[W⁻¹]`, presented**: one copy of the Garside germ per strand count — `PosBraid N` is
the presented monoid of `PosGermRel N` on the nose. -/
noncomputable def germBP : BraidPresentation :=
  BraidPresentation.ofMonoids PosGermRel (fun _ => MulEquiv.refl _)

/-- **…and the Artin spelling**, on `N−1` generators with the commutation and braid relations: the
same input, handed Artin-from-Garside instead of the identity. -/
noncomputable def artinBP : BraidPresentation :=
  BraidPresentation.ofMonoids ArtinRel (fun N => (posBraid_equiv_artinPos N).symm)

/-- **A germ generator is its own simple.** -/
@[simp] theorem germBP_braid {N : ℕ} (σ : germBP.S N) :
    germBP.braid σ = posPerm σ := rfl

theorem germBP_bySimples : germBP.BySimples := fun _ _ => rfl

/-- **…and it is its own permutation.** -/
@[simp] theorem germBP_perm {N : ℕ} (σ : germBP.S N) :
    germBP.perm σ = σ := posPermHom_posPerm σ

/-- **An Artin generator is the simple of its adjacent transposition** — `posOfArtinPos` is the
inverse's underlying map, and it sends a generator to its atom on the nose. -/
@[simp] theorem artinBP_braid {N : ℕ} (k : artinBP.S N) :
    artinBP.braid k = posPerm (adjT k) := rfl

@[simp] theorem artinBP_perm {N : ℕ} (k : artinBP.S N) :
    artinBP.perm k = adjT k := by
  rw [BraidPresentation.perm, artinBP_braid, posPermHom_posPerm]

theorem artinBP_bySimples : artinBP.BySimples := fun _ k => by
  rw [artinBP_braid k, artinBP_perm k]

/-- **A Garside generator's germ step is the length equation alone** — the generator *is* its
simple, so `Br germBP` sees every length-additive pair. -/
theorem germBP_germStep_iff {N : ℕ} (σ : germBP.S N)
    (u v : Equiv.Perm (Fin N)) :
    germBP.GermStep σ u v ↔ v = u * germBP.perm σ ∧
      permLen u + permLen (germBP.perm σ) = permLen v :=
  germStep_posPerm_iff _ u v

/-- …and an Artin generator's is a covering: exactly one new crossing. -/
theorem artinBP_germStep_iff {N : ℕ} (k : artinBP.S N)
    (u v : Equiv.Perm (Fin N)) :
    artinBP.GermStep k u v ↔ v = u * adjT k ∧ permLen u + 1 = permLen v :=
  germStep_adjT_iff k u v

/-- **The `k`-th Artin generator is the `k`-th atom.** -/
theorem artinBase_arrow_atom (N : ℕ) (k : Fin (N - 1)) :
    artinBP.base.arrow (artinBP.gen k) = atomLoop N k :=
  (artinBP.base_arrow_of_simple artinBP_bySimples k).trans
    (by rw [artinBP_perm, runLoop_adjT])

end ChainCat
