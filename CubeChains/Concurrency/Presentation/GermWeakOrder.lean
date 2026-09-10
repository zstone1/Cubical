import CubeChains.Concurrency.Presentation.BasePresentation
import CubeChains.Concurrency.Merge.CubeWeakOrder

/-!
# Concurrency/Presentation/GermWeakOrder — a braid presentation presents a down-set

A **`WeakDownset n`** is a set of permutations on `n` strands, named injectively by a carrier and
closed downwards in the right weak order.  `germPoly p C` is the **germ** of a `BraidPresentation`
there: 0-cells its points, 1-cells the generators of `p` making a germ step between two of
them, 2-cells the relations of `p` holding there.  `dehornoy p C` says it presents the
down-set's own order.

This is Dehornoy–Digne–Michel's germ presentation theorem (*Garside families and Garside germs*,
J. Algebra 2013) for the braid germ.  The content is `GermStep.factor`: a braid word whose braid
makes a germ step lifts prefix by prefix, and down-closure supplies each intermediate.
The germ's product stays partial — nothing here encodes the partiality as a total action.

    a ──⟨s, h⟩──▶ b        h : p.braid s = posPerm (p.perm s), C.perm b = C.perm a · p.perm s,
    │                          |C.perm a| + |p.perm s| = |C.perm b|
    └── germWord ──▶ s     one 0-cell downstairs, so words there are braid words
-/

open CategoryTheory Opposite CubeChains Polygraph

namespace ChainCat

/-! ## Down-sets -/

/-- **A down-set on `n` strands**: permutations named injectively by `carrier`, closed downwards
in the right weak order.  Down-closure is what makes a braid word lift step by step — every prefix
of a germ step lands in the down-set again. -/
structure WeakDownset (n : ℕ) where
  /-- the points -/
  carrier : Type
  /-- …each naming a permutation -/
  perm : carrier → Equiv.Perm (Fin n)
  /-- …injectively -/
  perm_injective : Function.Injective perm
  /-- …and the named set is a down-set -/
  mem_of_le : ∀ {x : carrier} {τ : Equiv.Perm (Fin n)},
    WeakOrder.of τ ≤ WeakOrder.of (perm x) → ∃ y, perm y = τ

/-- **A germ step rises in the weak order.** -/
theorem le_of_germStep {n : ℕ} {β : PosBraid n} {σ τ : Equiv.Perm (Fin n)}
    (h : CubeChains.GermStep β σ τ) : WeakOrder.of σ ≤ WeakOrder.of τ := by
  rw [h.mul_eq]
  exact WeakOrder.le_of_mul (by rw [← h.mul_eq]; exact h.permLen_add)

/-- **…and every rise is one**, at the simple that names the gap. -/
theorem germStep_of_le {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (h : WeakOrder.of σ ≤ WeakOrder.of τ) :
    CubeChains.GermStep (posPerm (σ⁻¹ * τ)) σ τ :=
  (germStep_posPerm_iff _ σ τ).mpr ⟨(mul_inv_cancel_left σ τ).symm, WeakOrder.le_def.mp h⟩

namespace WeakDownset

variable {n : ℕ} (C : WeakDownset n)

/-- **A factorised germ step passes through the down-set** — the middle permutation is below the
upper end, so the down-closure names it. -/
theorem exists_mid {β γ : PosBraid n} {a b : C.carrier}
    (h : CubeChains.GermStep (β * γ) (C.perm a) (C.perm b)) :
    ∃ c : C.carrier, CubeChains.GermStep β (C.perm a) (C.perm c) ∧
      CubeChains.GermStep γ (C.perm c) (C.perm b) := by
  obtain ⟨h₁, h₂⟩ := h.factor
  obtain ⟨c, hc⟩ := C.mem_of_le (le_of_germStep h₂)
  exact ⟨c, hc ▸ h₁, hc ▸ h₂⟩

/-- **The down-set's own order**: its points, ordered by their permutations. -/
def Order : Type := C.carrier

instance : PartialOrder C.Order :=
  PartialOrder.lift (fun a : C.carrier => WeakOrder.of (C.perm a))
    fun _ _ h => C.perm_injective (congrArg WeakOrder.perm h)

theorem le_iff {a b : C.Order} :
    a ≤ b ↔ WeakOrder.of (C.perm a) ≤ WeakOrder.of (C.perm b) := Iff.rfl

/-- **The whole weak order is a down-set** — every permutation, named by itself. -/
def top (n : ℕ) : WeakDownset n where
  carrier := Equiv.Perm (Fin n)
  perm := id
  perm_injective := Function.injective_id
  mem_of_le := fun {_ τ} _ => ⟨τ, rfl⟩

/-- …and its order **is** the right weak Bruhat order. -/
def orderTop (n : ℕ) : (WeakDownset.top n).Order ≌ WeakOrder n where
  functor := { obj := WeakOrder.of, map := fun h => h }
  inverse := { obj := WeakOrder.perm, map := fun h => h }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => Subsingleton.elim _ _
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => Subsingleton.elim _ _
  functor_unitIso_comp _ := Subsingleton.elim _ _

end WeakDownset

/-! ## Maps of down-sets

A renaming and a merge's left translation are both maps of points carrying germ steps to germ
steps, and that is all the germ polygraph reads of either. -/

/-- **A map of down-sets**: a map of points carrying every germ step to a germ step. -/
structure WeakDownset.Map {n : ℕ} (C D : WeakDownset n) where
  /-- the map of points -/
  toFun : C.carrier → D.carrier
  /-- …carrying germ steps to germ steps -/
  germStep : ∀ {β : PosBraid n} {a b : C.carrier},
    CubeChains.GermStep β (C.perm a) (C.perm b) →
      CubeChains.GermStep β (D.perm (toFun a)) (D.perm (toFun b))

namespace WeakDownset

variable {n : ℕ} {C D E : WeakDownset n}

theorem Map.ext {m m' : C.Map D} (h : m.toFun = m'.toFun) : m = m' := by
  cases m; cases m'; cases h; rfl

/-- The identity. -/
def Map.id (C : WeakDownset n) : C.Map C where
  toFun x := x
  germStep h := h

/-- The composite. -/
def Map.comp (m : C.Map D) (m' : D.Map E) : C.Map E where
  toFun x := m'.toFun (m.toFun x)
  germStep h := m'.germStep (m.germStep h)

/-- **Down-sets naming the same permutations name each other's points** — `perm` is injective, so
the naming is a bijection. -/
noncomputable def equivOfRangeEq (h : Set.range C.perm = Set.range D.perm) :
    C.carrier ≃ D.carrier :=
  (Equiv.ofInjective _ C.perm_injective).trans
    ((Equiv.setCongr h).trans (Equiv.ofInjective _ D.perm_injective).symm)

theorem perm_equivOfRangeEq (h : Set.range C.perm = Set.range D.perm) (x : C.carrier) :
    D.perm (equivOfRangeEq h x) = C.perm x :=
  Equiv.apply_ofInjective_symm D.perm_injective _

/-- …hence a map of down-sets — a germ step reads the permutations and nothing else — inverted by
the same construction backwards. -/
noncomputable def mapOfRangeEq (h : Set.range C.perm = Set.range D.perm) : C.Map D where
  toFun := equivOfRangeEq h
  germStep e := by rw [perm_equivOfRangeEq, perm_equivOfRangeEq]; exact e

theorem mapOfRangeEq_comp (h : Set.range C.perm = Set.range D.perm) :
    (mapOfRangeEq h).comp (mapOfRangeEq h.symm) = Map.id C :=
  Map.ext (funext fun x => C.perm_injective
    ((perm_equivOfRangeEq h.symm _).trans (perm_equivOfRangeEq h x)))

end WeakDownset

namespace BraidPresentation

variable (p : BraidPresentation)

/-! ## The braid a word performs -/

/-- The one 0-cell of `p`'s words at `n` strands. -/
abbrev germBase (n : ℕ) : (p.P n).Word := ⟨p.v n⟩

/-- The braid a word of `p` at `n` strands performs — one 0-cell downstairs, so its arrows *are*
the braids. -/
def wordBraid {n : ℕ} {x y : (p.P n).Word} (w : x ⟶ y) : PosBraid n :=
  ((p.comp n).eval.map w).unop

@[simp] theorem wordBraid_id {n : ℕ} (x : (p.P n).Word) : p.wordBraid (𝟙 x) = 1 :=
  congrArg Quiver.Hom.unop (Presents.eval_nil (p.comp n) x)

/-- …at the spelling a path induction leaves behind: `𝟙` in `Paths` *is* `nil`, but `rw` matches
syntactically. -/
@[simp] theorem wordBraid_nil {n : ℕ} (x : GenObj (p.P n).Gen) :
    p.wordBraid (Quiver.Path.nil (a := x)) = 1 := p.wordBraid_id x

theorem wordBraid_cons {n : ℕ} {x y z : GenObj (p.P n).Gen} (w : Quiver.Path x y)
    (e : (p.P n).Gen y.as z.as) :
    p.wordBraid (Quiver.Path.cons w e) = p.wordBraid w * p.braid e :=
  congrArg Quiver.Hom.unop (Presents.eval_cons (p.comp n) w e)

theorem wordBraid_comp {n : ℕ} {x y z : (p.P n).Word} (u : x ⟶ y) (v : y ⟶ z) :
    p.wordBraid (u ≫ v) = p.wordBraid u * p.wordBraid v :=
  congrArg Quiver.Hom.unop ((p.comp n).eval.map_comp u v)

/-- **Related words perform the same braid** — the 2-cells of `p` are sound. -/
theorem wordBraid_eq_of_homRel {n : ℕ} {x y : (p.P n).Word} {u v : x ⟶ y}
    (h : (p.P n).homRel u v) : p.wordBraid u = p.wordBraid v :=
  congrArg Quiver.Hom.unop ((p.comp n).sound' h)

/-- **…and so do congruent words** — `p` presents the monoid, so nothing but its 2-cells separates
them. -/
theorem wordBraid_eq_of_gen {n : ℕ} {x y : (p.P n).Word} {u v : x ⟶ y}
    (h : HomRel.Gen (p.P n).homRel u v) : p.wordBraid u = p.wordBraid v :=
  congrArg Quiver.Hom.unop
    (congrArg (p.comp n).E.map ((HomRel.gen_iff_functor_map_eq (p.P n).homRel u v).mp h))

/-! ## The germ polygraph -/

variable {n : ℕ} (C : WeakDownset n)

/-- **The 1-cells of the germ**: a generator of `p` carrying one down-set point to another
length-additively. -/
def GermGen (a b : C.carrier) : Type := {s : p.S n // p.GermStep s (C.perm a) (C.perm b)}

/-- …lying over the generators of `p`, which is where the 2-cells come from. -/
def germProj : GenObj (p.GermGen C) ⥤q GenObj (p.P n).Gen where
  obj _ := ⟨p.v n⟩
  map e := e.1

/-- **The germ polygraph of `p` on a down-set**: 0-cells its points, 1-cells the generators
of `p` making a germ step, 2-cells the relations of `p` holding there. -/
def germPoly : Polygraph.{0, 0, 0} := (p.P n).comap (p.GermGen C) (p.germProj C)

/-- The 0-cell a down-set point names. -/
abbrev germPt (a : C.carrier) : Paths (GenObj (p.GermGen C)) := ⟨a⟩

/-- The braid word a germ word spells.  The target type is the point: `germProj` is constant on
0-cells, so every germ word spells a word in the *same* hom-set, and no endpoint travels. -/
def germWord {x y : GenObj (p.GermGen C)} (w : Quiver.Path x y) :
    p.germBase n ⟶ p.germBase n := (p.germProj C).mapPath w

@[simp] theorem germWord_nil (x : GenObj (p.GermGen C)) :
    p.germWord C (Quiver.Path.nil (a := x)) = 𝟙 (p.germBase n) := rfl

theorem wordBraid_germWord_cons {x y z : GenObj (p.GermGen C)} (w : Quiver.Path x y)
    (e : y ⟶ z) : p.wordBraid (p.germWord C (Quiver.Path.cons w e))
      = p.wordBraid (p.germWord C w) * p.braid e.1 :=
  p.wordBraid_cons _ _

theorem germWord_comp {x y z : Paths (GenObj (p.GermGen C))} (u : x ⟶ y) (v : y ⟶ z) :
    p.germWord C (u ≫ v) = p.germWord C u ≫ p.germWord C v :=
  Prefunctor.mapPath_comp (p.germProj C) u v

/-- **A word of the germ makes a germ step** — the steps compose, and their braids multiply. -/
theorem germStep_germWord_aux {a : C.carrier} :
    ∀ {y : GenObj (p.GermGen C)} (w : Quiver.Path (⟨a⟩ : GenObj (p.GermGen C)) y),
      CubeChains.GermStep (p.wordBraid (p.germWord C w)) (C.perm a) (C.perm y.as) := by
  intro y w
  induction w with
  | nil =>
      rw [p.germWord_nil, p.wordBraid_id]
      exact germStep_one _
  | @cons b c w e ih =>
      rw [p.wordBraid_germWord_cons]
      exact ih.trans e.2

theorem germStep_germWord {a b : C.carrier} (w : p.germPt C a ⟶ p.germPt C b) :
    CubeChains.GermStep (p.wordBraid (p.germWord C w)) (C.perm a) (C.perm b) :=
  p.germStep_germWord_aux C w

/-- **A 1-cell is pinned by the generator it names**: a germ step's target is its source times that
generator's permutation. -/
theorem germProj_star_injective (x : GenObj (p.GermGen C)) :
    Function.Injective ((p.germProj C).star x) := by
  rintro ⟨⟨τ₁⟩, s₁, h₁⟩ ⟨⟨τ₂⟩, s₂, h₂⟩ hh
  obtain ⟨-, he⟩ := Sigma.mk.inj_iff.mp hh
  obtain rfl : s₁ = s₂ := eq_of_heq he
  obtain rfl : τ₁ = τ₂ := C.perm_injective (h₁.mul_eq.trans h₂.mul_eq.symm)
  rfl

instance germProj_faithful : (p.germProj C).pathsFunctor.Faithful :=
  Prefunctor.pathsFunctor_faithful _ (p.germProj_star_injective C)

/-- **A word of the germ is its braid word** — the covering is faithful. -/
theorem germWord_injective {a b : C.carrier} {w w' : p.germPt C a ⟶ p.germPt C b}
    (h : p.germWord C w = p.germWord C w') : w = w' :=
  (p.germProj_faithful C).map_injective h

/-- **A braid word whose braid makes a germ step lifts** — `WeakDownset.exists_mid` supplies each
intermediate.  No endpoint bookkeeping: `p` has one 0-cell per strand count, so `Unit`'s eta makes
every word's ends `germBase` *on the nose*. -/
theorem exists_germPath {a : C.carrier} :
    ∀ {y : GenObj (p.P n).Gen} (w : Quiver.Path (⟨p.v n⟩ : GenObj (p.P n).Gen) y)
      {b : C.carrier}, CubeChains.GermStep (p.wordBraid w) (C.perm a) (C.perm b) →
      ∃ w' : p.germPt C a ⟶ p.germPt C b,
        p.germWord C w' = (w : p.germBase n ⟶ p.germBase n) := by
  intro y w
  induction w with
  | nil =>
      intro b h
      obtain rfl : a = b := by
        refine C.perm_injective ?_
        have hm := h.mul_eq
        simpa only [p.wordBraid_nil, map_one, mul_one, eq_comm] using hm
      exact ⟨Quiver.Path.nil, rfl⟩
  | @cons b c w e ih =>
      intro t h
      rw [p.wordBraid_cons] at h
      obtain ⟨m, h₁, h₂⟩ := C.exists_mid h
      obtain ⟨w', hw'⟩ := ih h₁
      exact ⟨Quiver.Path.cons w' ⟨e, h₂⟩, congrArg (fun u => Quiver.Path.cons u e) hw'⟩

/-! ## What the germ presents -/

/-- The cells of the germ, interpreted in the down-set's order. -/
def germInterp : GenObj (p.GermGen C) ⥤q C.Order where
  obj x := (x.as : C.Order)
  map e := homOfLE (le_of_germStep (β := p.braid e.1) e.2)

/-- **The generators span**: `p` spells the simple that names the gap, and that word lifts. -/
theorem germInterp_full : (Paths.lift (p.germInterp C)).Full where
  map_surjective {x y} h := by
    obtain ⟨w, hw⟩ := (p.comp n).eval.map_surjective (X := p.germBase n) (Y := p.germBase n)
      (Quiver.Hom.op (X := SingleObj.star (PosBraid n)) (Y := SingleObj.star (PosBraid n))
        (posPerm ((C.perm x.as)⁻¹ * C.perm y.as)))
    have hb : p.wordBraid w = posPerm ((C.perm x.as)⁻¹ * C.perm y.as) :=
      congrArg Quiver.Hom.unop hw
    have hstep : CubeChains.GermStep (p.wordBraid w) (C.perm x.as) (C.perm y.as) := by
      rw [hb]; exact germStep_of_le (C.le_iff.mp (leOfHom h))
    obtain ⟨w', -⟩ := p.exists_germPath C w hstep
    exact ⟨w', Subsingleton.elim _ _⟩

/-- **The 0-cells cover**: they are the down-set's points. -/
theorem germInterp_essSurj : (Paths.lift (p.germInterp C)).EssSurj where
  mem_essImage c := ⟨⟨c⟩, ⟨Iso.refl _⟩⟩

/-! ### Completeness

Two germ words with the same ends spell braid words performing the same braid, hence congruent
ones.  That congruence lifts: every word in the chain performs that braid, hence makes the same
germ step, hence lifts; and a relation of `p` applied inside a lifting word is applied between
lifting words. -/

private theorem gen_germ_aux {a : C.carrier} :
    ∀ {u v : p.germBase n ⟶ p.germBase n}, HomRel.Gen (p.P n).homRel u v →
      ∀ {b : C.carrier} (f g : p.germPt C a ⟶ p.germPt C b),
        p.germWord C f = u → p.germWord C g = v →
        HomRel.Gen ((p.germProj C).pathsFunctor.pullbackRel (p.P n).homRel) f g := by
  intro u v h
  induction h with
  | rel _ _ huv =>
      obtain ⟨X, Y, x, m₁, m₂, y, hm⟩ := huv
      obtain rfl : X = p.germBase n :=
        congrArg (fun a => (⟨a⟩ : GenObj (p.P n).Gen)) (p.eq_v X.as)
      obtain rfl : Y = p.germBase n :=
        congrArg (fun a => (⟨a⟩ : GenObj (p.P n).Gen)) (p.eq_v Y.as)
      intro b f g hf hg
      have hstep := p.germStep_germWord C f
      rw [hf, p.wordBraid_comp, p.wordBraid_comp] at hstep
      obtain ⟨c₁, hx, hmy⟩ := C.exists_mid hstep
      obtain ⟨c₂, hm₁, hy⟩ := C.exists_mid hmy
      obtain ⟨x', hx'⟩ := p.exists_germPath C x hx
      obtain ⟨m₁', hm₁'⟩ := p.exists_germPath C m₁ hm₁
      obtain ⟨y', hy'⟩ := p.exists_germPath C y hy
      obtain ⟨m₂', hm₂'⟩ := p.exists_germPath C m₂ (by
        rw [← p.wordBraid_eq_of_homRel hm]; exact hm₁)
      obtain rfl : f = x' ≫ m₁' ≫ y' :=
        p.germWord_injective C (by
          rw [hf, p.germWord_comp, p.germWord_comp, hx', hm₁', hy'])
      obtain rfl : g = x' ≫ m₂' ≫ y' :=
        p.germWord_injective C (by
          rw [hg, p.germWord_comp, p.germWord_comp, hx', hm₂', hy'])
      refine Relation.EqvGen.rel _ _ (HomRel.CompClosure.intro _ _ x' m₁' m₂' y' ?_)
      change (p.P n).homRel (p.germWord C m₁') (p.germWord C m₂')
      rw [hm₁', hm₂']
      exact hm
  | refl _ =>
      intro b f g hf hg
      exact p.germWord_injective C (hf.trans hg.symm) ▸ Relation.EqvGen.refl _
  | symm _ _ _ ih => intro b f g hf hg; exact (ih g f hg hf).symm
  | @trans _ v _ huv _ ih₁ ih₂ =>
      intro b f g hf hg
      have hstep := p.germStep_germWord C f
      rw [hf, p.wordBraid_eq_of_gen huv] at hstep
      obtain ⟨m, hm⟩ := p.exists_germPath C v hstep
      exact Relation.EqvGen.trans _ _ _ (ih₁ f m hf hm) (ih₂ m g hm hg)

/-- **Two germ words with the same ends are one arrow** — completeness, inherited from `p`'s. -/
theorem germ_quot_map_eq {a b : C.carrier} (f g : p.germPt C a ⟶ p.germPt C b) :
    (p.germPoly C).quot.map f = (p.germPoly C).quot.map g := by
  refine Polygraph.comap_quot_map_eq_of_gen (p.germProj C) (p.gen_germ_aux C ?_ f g rfl rfl)
  exact (p.comp n).gen_of_eval_eq
    (Quiver.Hom.unop_inj ((p.germStep_germWord C f).eq_of_eq (p.germStep_germWord C g)))

/-- **`p`'s germ presents the down-set's order** — 0-cells the down-set's points, 1-cells `p`'s
generators where they make a germ step, 2-cells `p`'s relations holding there.
Dehornoy–Digne–Michel's germ presentation, for the braid germ. -/
noncomputable def dehornoy : Presents (p.germPoly C) C.Order :=
  Presents.ofDesc (p.germInterp C) (fun _ => Subsingleton.elim _ _)
    (fun {_ _ _ _} _ => p.germ_quot_map_eq C _ _) (p.germInterp_full C) (p.germInterp_essSurj C)

/-- **…and on the whole weak order it is the right weak Bruhat order on `Sₙ`.** -/
noncomputable def dehornoyTop (n : ℕ) :
    Presents (p.germPoly (WeakDownset.top n)) (WeakOrder n) :=
  (p.dehornoy (WeakDownset.top n)).transport (WeakDownset.orderTop n)

end BraidPresentation

/-! ## …transported along a map of down-sets

A map of points moves no generator, so the transport is `comapOver` on it — for every
`BraidPresentation`, since nothing here reads a germ 1-cell. -/

namespace BraidPresentation

variable (p : BraidPresentation) {n : ℕ} {C D E : WeakDownset n}

/-- The map, on the germ's generating quiver. -/
def germPre (m : C.Map D) : GenObj (p.GermGen C) ⥤q GenObj (p.GermGen D) where
  obj x := ⟨m.toFun x.as⟩
  map e := ⟨e.1, m.germStep e.2⟩

/-- …hence on the germ polygraph, with the 2-cells untouched. -/
def germPolyMap (m : C.Map D) : p.germPoly C ⟶ p.germPoly D :=
  Polygraph.comapOver (p.germProj D) (p.germPre m)

@[simp] theorem germPolyMap_id : p.germPolyMap (WeakDownset.Map.id C) = 𝟙 (p.germPoly C) :=
  Polygraph.comapOver_id (p.germProj C)

theorem germPolyMap_comp (m : C.Map D) (m' : D.Map E) :
    p.germPolyMap (m.comp m') = p.germPolyMap m ≫ p.germPolyMap m' :=
  Polygraph.comapOver_comp (p.germProj E) (p.germPre m) (p.germPre m')

/-- **A map of down-sets leaves the braid word a germ word spells alone** — it moves the points,
never the generators. -/
theorem germWord_germPre (m : C.Map D) {x y : GenObj (p.GermGen C)} (w : Quiver.Path x y) :
    p.germWord D ((p.germPre m).mapPath w) = p.germWord C w := by
  induction w with
  | nil => rfl
  | cons w e ih =>
      change Quiver.Path.cons (p.germWord D ((p.germPre m).mapPath w)) _
        = Quiver.Path.cons (p.germWord C w) _
      rw [ih]
      rfl

/-- **Down-sets naming the same permutations have the same germ.** -/
noncomputable def germPolyCongr (h : Set.range C.perm = Set.range D.perm) :
    p.germPoly C ≅ p.germPoly D where
  hom := p.germPolyMap (WeakDownset.mapOfRangeEq h)
  inv := p.germPolyMap (WeakDownset.mapOfRangeEq h.symm)
  hom_inv_id := by rw [← p.germPolyMap_comp, WeakDownset.mapOfRangeEq_comp, p.germPolyMap_id]
  inv_hom_id := by rw [← p.germPolyMap_comp, WeakDownset.mapOfRangeEq_comp, p.germPolyMap_id]

end BraidPresentation

end ChainCat
