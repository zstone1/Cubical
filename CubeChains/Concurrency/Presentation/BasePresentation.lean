import CubeChains.Concurrency.Presentation.BaseDecomposition
import CubeChains.Machinery.Presentation.Partial
import CubeChains.Machinery.Presentation.Coproduct
import CubeChains.Machinery.Presentation.Monoid
import CubeChains.Machinery.Presentation.Comparison

/-!
# Concurrency/Presentation/BasePresentation — `Ch Zbp[W⁻¹]` as a single polygraph

The localized base is the disjoint union of its strand components (`strandDecomposition`) and each
component is one object carrying the braid monoid, so the whole of it is the coproduct of those
one-object polygraphs.  A `BraidPresentation` is that data: a presentation of
`SingleObj (PosBraid N)` for each `N`, with one 0-cell there.

`zLocComponent` runs the other way, by `Presents.restrict`: an *arbitrary* presentation of the
localized base restricts to one of each strand component — the shape the lift consumes.

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

/-- **A presentation of every strand component is a presentation of the localized base.** -/
noncomputable def zLocOfComponents {P : ℕ → Polygraph}
    (p : ∀ N, Presents (P N) ((AtStrands N).FullSubcategory)) :
    Presents (Polygraph.coproduct P) (((W Zbp).op).Localization) :=
  (Presents.coproduct p).transport strandDecomposition.symm

/-- No arrow enters or leaves a strand component, so a word between two of its objects stays
inside — the one hypothesis `Presents.restrict` takes. -/
theorem convex_atStrands (N : ℕ) : (AtStrands N).Convex :=
  ObjectProperty.convex_of_absorbing fun hx f hy =>
    hx ((ObjectProperty.prop_iff_of_hom AtStrands exists_atStrands
      (fun hX hY g => atStrands_eq_of_hom hX hY g) f).mpr hy)

/-- **…and every presentation of the localized base restricts to one of each strand component** —
`Presents.restrict` at a strand component, read through `strandComponentGarside`. -/
noncomputable def zLocComponent {P : Polygraph} (p : Presents P (((W Zbp).op).Localization))
    (N : ℕ) : Presents (p.restrictPoly (AtStrands N)) ((SingleObj (PosBraid N))ᵒᵖ) :=
  (p.restrict (AtStrands N) (convex_atStrands N)).transport (strandComponentGarside N).symm

/-! ## The input, bundled

A strand component *is* the braid monoid on that many strands (`strandComponentGarside`), so
presenting `SingleObj (PosBraid N)` presents the component, and the coproduct over the strand
counts is the whole of `Ch Zbp[W⁻¹]`.  Everything downstream is a lift of that. -/

/-- **A presentation of the braid monoids, one per strand count.**  `vertex` is not decoration: it
is what names `pt N` and `S N` at all, and a second 0-cell at a strand count would name every run
twice, so that `runPtEquiv` would be a surjection and not a bijection. -/
structure BraidPresentation where
  /-- the polygraph at each strand count -/
  P : ℕ → Polygraph.{0, 0, 0}
  /-- …presenting the braid monoid, as a one-object category -/
  comp : ∀ N, Presents (P N) ((SingleObj (PosBraid N))ᵒᵖ)
  /-- one 0-cell per strand count -/
  vertex : ∀ N, Unique (P N).V

namespace BraidPresentation

variable (p : BraidPresentation)

/-- The 0-cell at strand count `N`. -/
def v (N : ℕ) : (p.P N).V := (p.vertex N).default

theorem eq_v {N : ℕ} (x : (p.P N).V) : x = p.v N := (p.vertex N).uniq x

/-- The generators at strand count `N`: the 1-cells at its 0-cell. -/
def S (N : ℕ) : Type := (p.P N).Gen (p.v N) (p.v N)

/-- A 1-cell, read at the 0-cell.  The transport is between two terms of a subsingleton, so it
disappears the moment either is substituted. -/
def toS {N : ℕ} {x y : (p.P N).V} (s : (p.P N).Gen x y) : p.S N :=
  cast (congrArg₂ (p.P N).Gen (p.eq_v x) (p.eq_v y)) s

def poly : Polygraph.{0, 0, 0} := Polygraph.coproduct p.P

/-- The strand-`N` component, read where it sits in the localized base. -/
noncomputable def component (N : ℕ) : Presents (p.P N) ((AtStrands N).FullSubcategory) :=
  (p.comp N).transport (strandComponentGarside N)

/-- **…presenting `Ch Zbp[W⁻¹]`.** -/
noncomputable def base : Presents p.poly (((W Zbp).op).Localization) :=
  zLocOfComponents p.component

/-- The 0-cell at strand count `N`. -/
def pt (N : ℕ) : GenObj p.poly.Gen := p.poly.pt ⟨N, p.v N⟩

/-- A generator, as a 1-cell. -/
def gen {N : ℕ} (s : p.S N) : p.pt N ⟶ p.pt N := Polygraph.CoproductGen.mk s

/-- The braid a generator names — the component has one object, so its arrows *are* the braids. -/
def braid {N : ℕ} {x y : (p.P N).V} (s : (p.P N).Gen x y) : PosBraid N :=
  ((p.comp N).arrow (show (⟨x⟩ : GenObj (p.P N).Gen) ⟶ ⟨y⟩ from s)).unop

/-- …and its permutation. -/
def perm {N : ℕ} {x y : (p.P N).V} (s : (p.P N).Gen x y) : Equiv.Perm (Fin N) :=
  posPermHom N (p.braid s)

def BySimples : Prop :=
  ∀ (N : ℕ) {x y : (p.P N).V} (s : (p.P N).Gen x y), p.braid s = posPerm (p.perm s)

/-- **A generator of `p` carries `u` to `v` length-additively** — the germ condition at one
generator: `s` is a simple, and every pair it names is crossed anew.  This is the only relation the
inherited cells ever carry, and `Ch Zbp[W⁻¹]`'s partiality is exactly its failure. -/
def GermStep {N : ℕ} {x y : (p.P N).V} (s : (p.P N).Gen x y) (u v : Equiv.Perm (Fin N)) : Prop :=
  CubeChains.GermStep (p.braid s) u v

/-- …spelled out. -/
theorem germStep_iff {N : ℕ} {x y : (p.P N).V} (s : (p.P N).Gen x y)
    (u v : Equiv.Perm (Fin N)) :
    p.GermStep s u v ↔ p.braid s = posPerm (p.perm s) ∧ v = u * p.perm s ∧
      permLen u + permLen (p.perm s) = permLen v := Iff.rfl

theorem GermStep.mul_eq {q : BraidPresentation} {N : ℕ} {x y : (q.P N).V} {s : (q.P N).Gen x y}
    {u v : Equiv.Perm (Fin N)} (h : q.GermStep s u v) : v = u * q.perm s :=
  CubeChains.GermStep.mul_eq h

theorem GermStep.permLen_add {q : BraidPresentation} {N : ℕ} {x y : (q.P N).V}
    {s : (q.P N).Gen x y} {u v : Equiv.Perm (Fin N)} (h : q.GermStep s u v) :
    permLen u + permLen (q.perm s) = permLen v := CubeChains.GermStep.permLen_add h

/-- **The 0-cell at strand count `N` names the run.** -/
theorem base_at' (N : ℕ) (x : (p.P N).V) :
    p.base.at' (p.poly.pt ⟨N, x⟩) = ((W Zbp).op).Q.obj (op (zObj (𝟙^N))) := rfl

/-- **A generator names the loop at the run its braid is.** -/
theorem base_arrow {N : ℕ} {x y : (p.P N).V} (s : (p.P N).Gen x y) :
    p.base.arrow (Polygraph.CoproductGen.mk s :
        (p.poly.pt ⟨N, x⟩ : GenObj p.poly.Gen) ⟶ p.poly.pt ⟨N, y⟩)
      = (runBase N).map (posArrow N (p.braid s)) :=
  congrArg (ObjectProperty.sigmaι AtStrands).map (Presents.coproduct_arrow p.component N s)

/-- **…and a whole word of one component names the loop that word's braid is** — `base_arrow`,
read on words rather than letters. -/
theorem base_eval_coproductPre {N : ℕ} {x y : GenObj (p.P N).Gen} (w : Quiver.Path x y) :
    p.base.eval.map ((Polygraph.coproductPre p.P N).mapPath w)
      = (runBase N).map ((p.comp N).eval.map w) := by
  induction w with
  | nil =>
      exact ((p.base.eval.map_id ((Polygraph.coproductPre p.P N).obj x)).trans
          ((runBase N).map_id ((p.comp N).at' x)).symm).trans
        (congrArg (runBase N).map (Presents.eval_nil (p.comp N) x).symm)
  | cons w' g ih =>
      have hg : p.base.arrow ((Polygraph.coproductPre p.P N).map g)
          = (runBase N).map ((p.comp N).arrow g) := p.base_arrow g
      calc p.base.eval.map ((Polygraph.coproductPre p.P N).mapPath (w'.cons g))
          = p.base.eval.map ((Polygraph.coproductPre p.P N).mapPath w')
              ≫ p.base.arrow ((Polygraph.coproductPre p.P N).map g) :=
            Presents.eval_cons p.base _ _
        _ = (runBase N).map ((p.comp N).eval.map w')
              ≫ (runBase N).map ((p.comp N).arrow g) := by rw [ih, hg]; rfl
        _ = (runBase N).map ((p.comp N).eval.map (w'.cons g)) :=
            ((runBase N).map_comp _ _).symm.trans
              (congrArg (runBase N).map (Presents.eval_cons (p.comp N) w' g).symm)

/-- **A simple generator names the loop its permutation spells.** -/
theorem base_arrow_of_simple (hp : p.BySimples) {N : ℕ} {x y : (p.P N).V}
    (s : (p.P N).Gen x y) :
    p.base.arrow (Polygraph.CoproductGen.mk s :
        (p.poly.pt ⟨N, x⟩ : GenObj p.poly.Gen) ⟶ p.poly.pt ⟨N, y⟩)
      = runLoop N (p.perm s) :=
  (p.base_arrow s).trans (congrArg (fun β => (runBase N).map (posArrow N β)) (hp N s))

/-- **A monoid presentation of every braid monoid is one** — the constructor the two spellings
below use, and the only place `PresentedMonoid` enters. -/
noncomputable def ofMonoids {S : ℕ → Type}
    (rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop)
    (e : ∀ N, PresentedMonoid (rels N) ≃* PosBraid N) : BraidPresentation where
  P N := monoidPoly (rels N)
  comp N := (presentedMonoidPresentation (rels N)).transport (MulEquiv.toSingleObjEquiv (e N)).op
  vertex _ := inferInstanceAs (Unique Unit)

@[simp] theorem ofMonoids_braid {S : ℕ → Type}
    (rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop)
    (e : ∀ N, PresentedMonoid (rels N) ≃* PosBraid N) {N : ℕ} (s : (ofMonoids rels e).S N) :
    (ofMonoids rels e).braid s = e N (PresentedMonoid.mk (rels N) (FreeMonoid.of s)) := rfl

/-! ### Maps

A map is a comparison at each strand count.  A comparison is a *spelling*, so a generator goes to a
**word** — that is where a germ simple resolves into a product of atoms — and `PosBraid N` has no
non-trivial units, so the comparison's own isomorphisms are identities and the word performs the
generator's braid on the nose. -/

/-- **An isomorphism of a braid component is the identity** — `posLen` is additive and vanishes only
at `1`, so `PosBraid N` has no non-trivial units. -/
theorem hom_unop_eq_one {N : ℕ} {X Y : (SingleObj (PosBraid N))ᵒᵖ} (α : X ≅ Y) :
    α.hom.unop = (1 : PosBraid N) := by
  have h := congrArg Quiver.Hom.unop α.hom_inv_id
  rw [unop_comp, unop_id, SingleObj.comp_as_mul, SingleObj.id_as_one] at h
  exact eq_one_of_mul_eq_one h

/-- **…so conjugating by isomorphisms changes nothing**, which is all a comparison's `iso` can do
to a word. -/
theorem unop_conj {N : ℕ} {W X Y Z : (SingleObj (PosBraid N))ᵒᵖ} (f : W ⟶ X) (g : X ⟶ Y)
    (k : Y ⟶ Z) (hf : f.unop = (1 : PosBraid N)) (hk : k.unop = (1 : PosBraid N)) :
    (f ≫ g ≫ k).unop = g.unop :=
  have key : ∀ a b c : PosBraid N, a = 1 → c = 1 → a * (b * c) = b :=
    fun a b c ha hc => by rw [ha, hc, mul_one, one_mul]
  key f.unop g.unop k.unop hf hk

end BraidPresentation

/-- **A map of braid presentations**: a comparison of the two spellings of each braid monoid. -/
structure BraidPresentation.Map (p q : BraidPresentation) where
  /-- the comparison at each strand count -/
  comp : ∀ N, Polygraph.Presents.Map (p.comp N) (q.comp N)

namespace BraidPresentation.Map

variable {p q r : BraidPresentation}

/-- **A braid presentation compares with itself, letter by letter.** -/
def refl (p : BraidPresentation) : BraidPresentation.Map p p :=
  ⟨fun _ => Polygraph.Presents.Map.refl _⟩

/-- **…and comparisons compose**, by substituting the second spelling into the first's words. -/
def trans (m : BraidPresentation.Map p q) (n : BraidPresentation.Map q r) :
    BraidPresentation.Map p r :=
  ⟨fun N => (m.comp N).trans (n.comp N)⟩

/-- The word a map spells a generator by. -/
def word (m : BraidPresentation.Map p q) {N : ℕ} {x y : (p.P N).V} (s : (p.P N).Gen x y) :
    (m.comp N).hom.cells.obj ⟨x⟩ ⟶ (m.comp N).hom.cells.obj ⟨y⟩ :=
  (m.comp N).hom.cells.map (show (⟨x⟩ : GenObj (p.P N).Gen) ⟶ ⟨y⟩ from s)

/-- **…and it performs the generator's own braid.** -/
theorem braid_word (m : BraidPresentation.Map p q) {N : ℕ} {x y : (p.P N).V}
    (s : (p.P N).Gen x y) : ((q.comp N).eval.map (m.word s)).unop = p.braid s :=
  (congrArg Quiver.Hom.unop
      ((m.comp N).eval_cells (show (⟨x⟩ : GenObj (p.P N).Gen) ⟶ ⟨y⟩ from s))).trans
    (BraidPresentation.unop_conj _ _ _
      (BraidPresentation.hom_unop_eq_one ((m.comp N).iso.app (⟨⟨x⟩⟩ : (p.P N).presented)))
      (BraidPresentation.hom_unop_eq_one ((m.comp N).iso.app (⟨⟨y⟩⟩ : (p.P N).presented)).symm))

end BraidPresentation.Map

/-- **`Ch Zbp[W⁻¹]`, presented**: one copy of the Garside germ per strand count — `PosBraid N` is
the presented monoid of `PosGermRel N` on the nose. -/
noncomputable def germBP : BraidPresentation :=
  BraidPresentation.ofMonoids PosGermRel fun _ => MulEquiv.refl _

/-- **…and the Artin spelling**, on `N−1` generators with the commutation and braid relations: the
same input, handed Artin-from-Garside instead of the identity. -/
noncomputable def artinBP : BraidPresentation :=
  BraidPresentation.ofMonoids ArtinRel fun N => (posBraid_equiv_artinPos N).symm

/-- **A germ generator is its own simple.** -/
@[simp] theorem germBP_braid {N : ℕ} {x y : (germBP.P N).V} (σ : (germBP.P N).Gen x y) :
    germBP.braid σ = posPerm σ := rfl

theorem germBP_bySimples : germBP.BySimples := fun _ {_ _} _ => rfl

/-- **…and it is its own permutation.** -/
@[simp] theorem germBP_perm {N : ℕ} {x y : (germBP.P N).V} (σ : (germBP.P N).Gen x y) :
    germBP.perm σ = σ := posPermHom_posPerm σ

/-- **An Artin generator is the simple of its adjacent transposition** — `posOfArtinPos` is the
inverse's underlying map, and it sends a generator to its atom on the nose. -/
@[simp] theorem artinBP_braid {N : ℕ} {x y : (artinBP.P N).V} (k : (artinBP.P N).Gen x y) :
    artinBP.braid k = posPerm (adjT k) := rfl

@[simp] theorem artinBP_perm {N : ℕ} {x y : (artinBP.P N).V} (k : (artinBP.P N).Gen x y) :
    artinBP.perm k = adjT k := by
  rw [BraidPresentation.perm, artinBP_braid, posPermHom_posPerm]

theorem artinBP_bySimples : artinBP.BySimples := fun _ {_ _} k => by
  rw [artinBP_braid k, artinBP_perm k]

/-- **A Garside generator's germ step is the length equation alone** — the generator *is* its
simple, so `Br germBP` sees every length-additive pair. -/
theorem germBP_germStep_iff {N : ℕ} {x y : (germBP.P N).V} (σ : (germBP.P N).Gen x y)
    (u v : Equiv.Perm (Fin N)) :
    germBP.GermStep σ u v ↔ v = u * germBP.perm σ ∧
      permLen u + permLen (germBP.perm σ) = permLen v :=
  germStep_posPerm_iff _ u v

/-- …and an Artin generator's is a covering: exactly one new crossing. -/
theorem artinBP_germStep_iff {N : ℕ} {x y : (artinBP.P N).V} (k : (artinBP.P N).Gen x y)
    (u v : Equiv.Perm (Fin N)) :
    artinBP.GermStep k u v ↔ v = u * adjT k ∧ permLen u + 1 = permLen v :=
  germStep_adjT_iff k u v

/-- **The `k`-th Artin generator is the `k`-th atom.** -/
theorem artinBase_arrow_atom (N : ℕ) (k : Fin (N - 1)) :
    artinBP.base.arrow (artinBP.gen k) = atomLoop N k :=
  (artinBP.base_arrow_of_simple artinBP_bySimples k).trans (by rw [artinBP_perm, runLoop_adjT])

end ChainCat
