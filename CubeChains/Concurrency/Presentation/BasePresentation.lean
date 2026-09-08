import CubeChains.Concurrency.Presentation.BaseDecomposition
import CubeChains.Machinery.Presentation.Partial
import CubeChains.Machinery.Presentation.Coproduct
import CubeChains.Machinery.Presentation.Strand
import CubeChains.Machinery.Presentation.Monoid
import CubeChains.Machinery.Presentation.Comparison

/-!
# Concurrency/Presentation/BasePresentation — `Ch Zbp[W⁻¹]` as a single polygraph

The localized base *is* the graded positive braid monoid (`fullBaseEquiv`): one object per strand
count, its endomorphisms the braids on that many strands.  A `BraidPresentation` presents that
category, in one polygraph whose **0-cells are the strand counts** — so there is no vertex to
declare unique, and the block inclusion of generators (`sumR`, `sumL`) is the tensor rather than
extra data at each use site.

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

The 0-cells are the strand counts and the 1-cells at one of them are the generators there, so a
`BraidPresentation` is a monoid presentation of each braid monoid *plus* the way the blocks
juxtapose.  Everything downstream is a lift of that. -/

/-- The braid a generator of a one-object presentation performs; the 0-cells are explicit because
there is exactly one and the generator does not name it. -/
def loopBraid {A R : Type} {sr tr : R → Quiver.Path (Polygraph.loopPt A) (Polygraph.loopPt A)}
    {N : ℕ} (q : Presents (Polygraph.loopPoly A R sr tr) ((SingleObj (PosBraid N))ᵒᵖ)) (s : A) :
    PosBraid N :=
  (q.arrow (x := Polygraph.loopPt A) (y := Polygraph.loopPt A) s).unop

/-- **A presentation of the graded positive braid monoid**: generators and relations at each strand
count, read as a single polygraph whose 0-cells *are* the strand counts, together with the block
inclusions that make it monoidal over the addition of strand counts. -/
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
  part : ∀ N : ℕ,
    Presents (Polygraph.strandFibre Gen Rel src tgt N) ((SingleObj (PosBraid N))ᵒᵖ)
  /-- **the block inclusion**: a generator, with `c` idle strands added on the right -/
  sumR : ∀ {a : ℕ}, Gen a → (c : ℕ) → Gen (a + c)
  /-- …and on the left -/
  sumL : ∀ (c : ℕ) {a : ℕ}, Gen a → Gen (c + a)
  /-- …performing the juxtaposed braid -/
  braid_sumR : ∀ {a : ℕ} (s : Gen a) (c : ℕ),
    loopBraid (part (a + c)) (sumR s c) = posSumL a c (loopBraid (part a) s)
  /-- …on either side -/
  braid_sumL : ∀ (c : ℕ) {a : ℕ} (s : Gen a),
    loopBraid (part (c + a)) (sumL c s) = posSumR c a (loopBraid (part a) s)

namespace BraidPresentation

variable (p : BraidPresentation)

/-- The polygraph at one strand count: `p`'s generators and relations there, at a single 0-cell. -/
abbrev P (N : ℕ) : Polygraph.{0, 0, 0} := Polygraph.strandFibre p.Gen p.Rel p.src p.tgt N

/-- …presenting the braid monoid, as a one-object category. -/
def comp (N : ℕ) : Presents (p.P N) ((SingleObj (PosBraid N))ᵒᵖ) := p.part N

/-- The 0-cell at strand count `N`; there is exactly one, by construction. -/
def v (N : ℕ) : (p.P N).V := ()

theorem eq_v {N : ℕ} (x : (p.P N).V) : x = p.v N := rfl

/-- The generators at strand count `N`: the 1-cells at its 0-cell. -/
def S (N : ℕ) : Type := (p.P N).Gen (p.v N) (p.v N)


/-- **The polygraph**: 0-cells the strand counts, 1-cells the generators there. -/
def poly : Polygraph.{0, 0, 0} := Polygraph.strandPoly p.Gen p.Rel p.src p.tgt

/-- The strand-`N` polygraph, included in the whole. -/
def incl (N : ℕ) : p.P N ⟶ p.poly := Polygraph.strandIncl p.Gen p.Rel p.src p.tgt N

/-- …on the generating quivers. -/
def pre (N : ℕ) : GenObj (p.P N).Gen ⥤q GenObj p.poly.Gen := Polygraph.strandPre p.Gen N

@[simp] theorem incl_pre (N : ℕ) : (p.incl N).pre = p.pre N := rfl

instance pre_faithful (N : ℕ) : (p.pre N).pathsFunctor.Faithful :=
  Polygraph.strandPre_pathsFunctor_faithful N

/-- **…presenting the graded positive braid monoid** — one object per strand count, its
endomorphisms the braids on that many strands. -/
noncomputable def braids : Presents p.poly (FullPosBraid)ᵒᵖ :=
  (Presents.strand p.comp).transport Graded.sigmaEquiv

/-- **…and hence `Ch Zbp[W⁻¹]`.** -/
noncomputable def base : Presents p.poly (((W Zbp).op).Localization) :=
  p.braids.transport fullBaseEquiv

/-- The 0-cell at strand count `N`. -/
def pt (N : ℕ) : GenObj p.poly.Gen := ⟨N⟩

/-- A generator, as a 1-cell. -/
def gen {N : ℕ} (s : p.S N) : p.pt N ⟶ p.pt N := Polygraph.StrandGen.mk s

/-- The braid a generator names — the strand count has one 0-cell, so its loops *are* the
braids. -/
def braid {N : ℕ} (s : p.S N) : PosBraid N := loopBraid (p.part N) s

/-- …and its permutation. -/
def perm {N : ℕ} (s : p.S N) : Equiv.Perm (Fin N) := posPermHom N (p.braid s)

/-- **The block inclusion juxtaposes the braids** — `braid_sumR`, in the derived vocabulary. -/
@[simp] theorem braid_sumR' {a : ℕ} (s : p.S a) (c : ℕ) :
    p.braid (p.sumR s c) = posSumL a c (p.braid s) := p.braid_sumR s c

@[simp] theorem braid_sumL' (c : ℕ) {a : ℕ} (s : p.S a) :
    p.braid (p.sumL c s) = posSumR c a (p.braid s) := p.braid_sumL c s

open CategoryTheory.MonoidalCategory in
/-- **The block inclusion *is* the tensor of `FullPosBraid`, on generators** — a generator with `c`
idle strands beside it is that generator whiskered by `c`. -/
theorem loop_braid_sumR {a : ℕ} (s : p.S a) (c : ℕ) :
    Graded.loop (p.braid (p.sumR s c)) = Graded.loop (p.braid s) ▷ (c : FullPosBraid) :=
  GradedHom.ext ((p.braid_sumR' s c).trans (posSum_left _).symm)

open CategoryTheory.MonoidalCategory in
theorem loop_braid_sumL (c : ℕ) {a : ℕ} (s : p.S a) :
    Graded.loop (p.braid (p.sumL c s))
      = whiskerLeft (C := FullPosBraid) c (Graded.loop (p.braid s)) :=
  GradedHom.ext ((p.braid_sumL' c s).trans (posSum_right _).symm)

def BySimples : Prop := ∀ (N : ℕ) (s : p.S N), p.braid s = posPerm (p.perm s)

/-- **A generator of `p` carries `u` to `v` length-additively** — the germ condition at one
generator: `s` is a simple, and every pair it names is crossed anew.  This is the only relation the
inherited cells ever carry, and `Ch Zbp[W⁻¹]`'s partiality is exactly its failure. -/
def GermStep {N : ℕ} (s : p.S N) (u v : Equiv.Perm (Fin N)) : Prop :=
  CubeChains.GermStep (p.braid s) u v

/-- …spelled out. -/
theorem germStep_iff {N : ℕ} (s : p.S N)
    (u v : Equiv.Perm (Fin N)) :
    p.GermStep s u v ↔ p.braid s = posPerm (p.perm s) ∧ v = u * p.perm s ∧
      permLen u + permLen (p.perm s) = permLen v := Iff.rfl

theorem GermStep.mul_eq {q : BraidPresentation} {N : ℕ} {s : q.S N}
    {u v : Equiv.Perm (Fin N)} (h : q.GermStep s u v) : v = u * q.perm s :=
  CubeChains.GermStep.mul_eq h

theorem GermStep.permLen_add {q : BraidPresentation} {N : ℕ}
    {s : q.S N} {u v : Equiv.Perm (Fin N)} (h : q.GermStep s u v) :
    permLen u + permLen (q.perm s) = permLen v := CubeChains.GermStep.permLen_add h

/-- **The 0-cell at strand count `N` names the run.** -/
theorem base_at' (N : ℕ) : p.base.at' (p.pt N) = ((W Zbp).op).Q.obj (op (zObj (𝟙^N))) := rfl

/-- **A generator names the loop at the run its braid is.** -/
theorem base_arrow {N : ℕ} (s : p.S N) :
    p.base.arrow (Polygraph.StrandGen.mk s : p.pt N ⟶ p.pt N)
      = (runBase N).map (posArrow N (p.braid s)) := by
  change runFullBase.map (Graded.sigmaDesc.map ((Presents.strand p.comp).arrow _)) = _
  refine Eq.trans (congrArg (fun t => runFullBase.map (Graded.sigmaDesc.map t))
    (Presents.strand_arrow p.comp N s)) ?_
  exact runFullBase_braidLoop N (p.braid s)

/-- **…and a whole word of one strand count names the loop that word's braid is** — `base_arrow`,
read on words rather than letters. -/
theorem base_eval_strandPre {N : ℕ} {x y : GenObj (p.P N).Gen} (w : Quiver.Path x y) :
    p.base.eval.map ((p.pre N).mapPath w)
      = (runBase N).map ((p.comp N).eval.map w) := by
  induction w with
  | nil =>
      exact ((p.base.eval.map_id ((p.pre N).obj x)).trans
          ((runBase N).map_id ((p.comp N).at' x)).symm).trans
        (congrArg (runBase N).map (Presents.eval_nil (p.comp N) x).symm)
  | cons w' g ih =>
      have hg : p.base.arrow ((p.pre N).map g)
          = (runBase N).map ((p.comp N).arrow g) := p.base_arrow g
      calc p.base.eval.map ((p.pre N).mapPath (w'.cons g))
          = p.base.eval.map ((p.pre N).mapPath w')
              ≫ p.base.arrow ((p.pre N).map g) :=
            Presents.eval_cons p.base _ _
        _ = (runBase N).map ((p.comp N).eval.map w')
              ≫ (runBase N).map ((p.comp N).arrow g) := by rw [ih, hg]; rfl
        _ = (runBase N).map ((p.comp N).eval.map (w'.cons g)) :=
            ((runBase N).map_comp _ _).symm.trans
              (congrArg (runBase N).map (Presents.eval_cons (p.comp N) w' g).symm)

/-- **A simple generator names the loop its permutation spells.** -/
theorem base_arrow_of_simple (hp : p.BySimples) {N : ℕ} (s : p.S N) :
    p.base.arrow (Polygraph.StrandGen.mk s : p.pt N ⟶ p.pt N) = runLoop N (p.perm s) :=
  (p.base_arrow s).trans (congrArg (fun β => (runBase N).map (posArrow N β)) (hp N s))

/-- **A monoid presentation of every braid monoid is one**, once the blocks are told how to
juxtapose — the constructor the two spellings below use, and the only place `PresentedMonoid`
enters. -/
noncomputable def ofMonoids {S : ℕ → Type}
    (rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop)
    (e : ∀ N, PresentedMonoid (rels N) ≃* PosBraid N)
    (sumR : ∀ {a : ℕ}, S a → (c : ℕ) → S (a + c))
    (sumL : ∀ (c : ℕ) {a : ℕ}, S a → S (c + a))
    (hR : ∀ {a : ℕ} (s : S a) (c : ℕ),
      e (a + c) (PresentedMonoid.mk (rels (a + c)) (FreeMonoid.of (sumR s c)))
        = posSumL a c (e a (PresentedMonoid.mk (rels a) (FreeMonoid.of s))))
    (hL : ∀ (c : ℕ) {a : ℕ} (s : S a),
      e (c + a) (PresentedMonoid.mk (rels (c + a)) (FreeMonoid.of (sumL c s)))
        = posSumR c a (e a (PresentedMonoid.mk (rels a) (FreeMonoid.of s)))) :
    BraidPresentation where
  Gen := S
  Rel := fun N => monoidRel (rels N) (monoidPt (rels N)) (monoidPt (rels N))
  src := fun _ α => α.1.1
  tgt := fun _ α => α.1.2
  part := fun N =>
    (presentedMonoidPresentation (rels N)).transport (MulEquiv.toSingleObjEquiv (e N)).op
  sumR := sumR
  sumL := sumL
  braid_sumR := hR
  braid_sumL := hL

@[simp] theorem ofMonoids_braid {S : ℕ → Type}
    {rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop}
    {e : ∀ N, PresentedMonoid (rels N) ≃* PosBraid N} {sumR sumL hR hL} {N : ℕ}
    (s : (ofMonoids rels e sumR sumL hR hL).S N) :
    (ofMonoids rels e sumR sumL hR hL).braid s
      = e N (PresentedMonoid.mk (rels N) (FreeMonoid.of s)) := rfl

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
def word (m : BraidPresentation.Map p q) {N : ℕ} (s : p.S N) :
    (m.comp N).hom.cells.obj ⟨p.v N⟩ ⟶ (m.comp N).hom.cells.obj ⟨p.v N⟩ :=
  (m.comp N).hom.cells.map (show (⟨p.v N⟩ : GenObj (p.P N).Gen) ⟶ ⟨p.v N⟩ from s)

/-- **…and it performs the generator's own braid.** -/
theorem braid_word (m : BraidPresentation.Map p q) {N : ℕ}
    (s : p.S N) : ((q.comp N).eval.map (m.word s)).unop = p.braid s :=
  (congrArg Quiver.Hom.unop
      ((m.comp N).eval_cells (show (⟨p.v N⟩ : GenObj (p.P N).Gen) ⟶ ⟨p.v N⟩ from s))).trans
    (BraidPresentation.unop_conj _ _ _
      (BraidPresentation.hom_unop_eq_one ((m.comp N).iso.app (⟨⟨p.v N⟩⟩ : (p.P N).presented)))
      (BraidPresentation.hom_unop_eq_one ((m.comp N).iso.app (⟨⟨p.v N⟩⟩ : (p.P N).presented)).symm))

end BraidPresentation.Map

/-- **`Ch Zbp[W⁻¹]`, presented**: one copy of the Garside germ per strand count — `PosBraid N` is
the presented monoid of `PosGermRel N` on the nose, and a simple set beside idle strands is the
block-diagonal simple. -/
noncomputable def germBP : BraidPresentation :=
  BraidPresentation.ofMonoids PosGermRel (fun _ => MulEquiv.refl _)
    (fun {a} σ c => permSum a c (σ, 1)) (fun c {a} σ => permSum c a (1, σ))
    (fun {_} _ _ => rfl) (fun _ {_} _ => rfl)

/-- **…and the Artin spelling**, on `N−1` generators with the commutation and braid relations: the
same input, handed Artin-from-Garside instead of the identity.  An atom of a block is an atom
(`permSum_adjT_left`), so the blocks juxtapose on the generators themselves. -/
noncomputable def artinBP : BraidPresentation :=
  BraidPresentation.ofMonoids ArtinRel (fun N => (posBraid_equiv_artinPos N).symm)
    (fun {a} k c => ⟨(k : ℕ), by have := k.2; omega⟩)
    (fun c {a} k => ⟨c + (k : ℕ), by have := k.2; omega⟩)
    (fun {a} k c => by
      change posPerm (adjT _) = posSumL a c (posPerm (adjT k))
      rw [posSumL_posPerm]
      exact congrArg posPerm (permSum_adjT_left k _ rfl).symm)
    (fun c {a} k => by
      change posPerm (adjT _) = posSumR c a (posPerm (adjT k))
      rw [posSumR_posPerm]
      exact congrArg posPerm (permSum_adjT_right k _ rfl).symm)

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
