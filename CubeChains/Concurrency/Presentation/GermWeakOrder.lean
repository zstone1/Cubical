import CubeChains.Concurrency.Presentation.BasePresentation
import CubeChains.Concurrency.Merge.CubeWeakOrder

/-!
# Concurrency/Presentation/GermWeakOrder — a braid presentation presents the weak order

`germPoly p n` is the **germ** of a `BraidPresentation` at `n` strands: 0-cells the permutations,
1-cells the generators of `p` making a germ step (a simple, crossing anew every pair it names),
2-cells the relations of `p` holding there.  `dehornoy p n` says it presents the right weak Bruhat
order.

This is Dehornoy–Digne–Michel's germ presentation theorem (*Garside families and Garside germs*,
J. Algebra 2013) for the braid germ.  The content is `GermStep.factor`: a braid word whose braid
makes a germ step lifts prefix by prefix, so a congruence downstairs is one upstairs.  The germ's
product stays partial — nothing here encodes the partiality as a total action.

    σ ──⟨s, h⟩──▶ τ        h : p.braid s = posPerm (p.perm s), τ = σ · p.perm s,
    │                          |σ| + |p.perm s| = |τ|
    └── germWord ──▶ s     one 0-cell downstairs, so words there are braid words
-/

open CategoryTheory Opposite CubeChains Polygraph

namespace ChainCat

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

theorem wordBraid_cons {n : ℕ} {x y z : GenObj (p.P n).Gen} (w : Quiver.Path x y)
    (e : (p.P n).Gen y.as z.as) :
    p.wordBraid (Quiver.Path.cons w e) = p.wordBraid w * p.braid e :=
  congrArg Quiver.Hom.unop (Presents.eval_cons (p.comp n) w e)

theorem wordBraid_comp {n : ℕ} {x y z : (p.P n).Word} (u : x ⟶ y) (v : y ⟶ z) :
    p.wordBraid (u ≫ v) = p.wordBraid u * p.wordBraid v :=
  congrArg Quiver.Hom.unop ((p.comp n).eval.map_comp u v)

theorem wordBraid_eqToHom {n : ℕ} {x y : (p.P n).Word} (h : x = y) : p.wordBraid (eqToHom h) = 1 :=
  by subst h; exact p.wordBraid_id x

/-- Any word of `p` at `n` strands, read at the strand count's own 0-cell — `p` has one there, so
the two ends move with no braid spent. -/
def rebase {n : ℕ} {x y : (p.P n).Word} (w : x ⟶ y) : p.germBase n ⟶ p.germBase n :=
  eqToHom (congrArg (fun a => (⟨a⟩ : GenObj (p.P n).Gen)) (p.eq_v x.as)).symm ≫ w ≫
    eqToHom (congrArg (fun a => (⟨a⟩ : GenObj (p.P n).Gen)) (p.eq_v y.as))

@[simp] theorem wordBraid_rebase {n : ℕ} {x y : (p.P n).Word} (w : x ⟶ y) :
    p.wordBraid (p.rebase w) = p.wordBraid w := by
  rw [rebase, p.wordBraid_comp, p.wordBraid_comp, p.wordBraid_eqToHom, p.wordBraid_eqToHom,
    one_mul, mul_one]
  exact rfl

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

/-- **The 1-cells of the germ**: a generator of `p` carrying `σ` to `τ` length-additively. -/
def GermGen (n : ℕ) (σ τ : Equiv.Perm (Fin n)) : Type := {s : p.S n // p.GermStep s σ τ}

/-- …lying over the generators of `p`, which is where the 2-cells come from. -/
def germProj (n : ℕ) : GenObj (p.GermGen n) ⥤q GenObj (p.P n).Gen where
  obj _ := ⟨p.v n⟩
  map e := e.1

/-- **The germ polygraph of `p` at `n` strands**: 0-cells the permutations, 1-cells the generators
of `p` making a germ step, 2-cells the relations of `p` holding there. -/
def germPoly (n : ℕ) : Polygraph.{0, 0, 0} := (p.P n).comap (p.GermGen n) (p.germProj n)

/-- The 0-cell a permutation names. -/
abbrev germPt {n : ℕ} (σ : Equiv.Perm (Fin n)) : Paths (GenObj (p.GermGen n)) := ⟨σ⟩

/-- The braid word a germ word spells.  The target type is the point: `germProj` is constant on
0-cells, so every germ word spells a word in the *same* hom-set, and no endpoint travels. -/
def germWord {n : ℕ} {x y : GenObj (p.GermGen n)} (w : Quiver.Path x y) :
    p.germBase n ⟶ p.germBase n := (p.germProj n).mapPath w

@[simp] theorem germWord_nil {n : ℕ} (x : GenObj (p.GermGen n)) :
    p.germWord (Quiver.Path.nil (a := x)) = 𝟙 (p.germBase n) := rfl

theorem wordBraid_germWord_cons {n : ℕ} {x y z : GenObj (p.GermGen n)} (w : Quiver.Path x y)
    (e : y ⟶ z) : p.wordBraid (p.germWord (Quiver.Path.cons w e))
      = p.wordBraid (p.germWord w) * p.braid e.1 :=
  p.wordBraid_cons _ _

theorem germWord_comp {n : ℕ} {x y z : Paths (GenObj (p.GermGen n))} (u : x ⟶ y) (v : y ⟶ z) :
    p.germWord (u ≫ v) = p.germWord u ≫ p.germWord v :=
  Prefunctor.mapPath_comp (p.germProj n) u v

/-- **A word of the germ makes a germ step** — the steps compose, and their braids multiply. -/
theorem germStep_germWord_aux {n : ℕ} {σ : Equiv.Perm (Fin n)} :
    ∀ {y : GenObj (p.GermGen n)} (w : Quiver.Path (⟨σ⟩ : GenObj (p.GermGen n)) y),
      CubeChains.GermStep (p.wordBraid (p.germWord w)) σ y.as := by
  intro y w
  induction w with
  | nil =>
      rw [p.germWord_nil, p.wordBraid_id]
      exact germStep_one σ
  | @cons b c w e ih =>
      rw [p.wordBraid_germWord_cons]
      exact ih.trans e.2

theorem germStep_germWord {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (w : p.germPt σ ⟶ p.germPt τ) :
    CubeChains.GermStep (p.wordBraid (p.germWord w)) σ τ := p.germStep_germWord_aux w

/-- **A 1-cell is pinned by the generator it names**: a germ step's target is its source times that
generator's permutation. -/
theorem germProj_star_injective {n : ℕ} (x : GenObj (p.GermGen n)) :
    Function.Injective ((p.germProj n).star x) := by
  rintro ⟨⟨τ₁⟩, s₁, h₁⟩ ⟨⟨τ₂⟩, s₂, h₂⟩ hh
  obtain ⟨-, he⟩ := Sigma.mk.inj_iff.mp hh
  obtain rfl : s₁ = s₂ := eq_of_heq he
  obtain rfl : τ₁ = τ₂ := h₁.mul_eq.trans h₂.mul_eq.symm
  rfl

instance germProj_faithful (n : ℕ) : (p.germProj n).pathsFunctor.Faithful :=
  Prefunctor.pathsFunctor_faithful _ p.germProj_star_injective

/-- **A word of the germ is its braid word** — the covering is faithful. -/
theorem germWord_injective {n : ℕ} {σ τ : Equiv.Perm (Fin n)} {w w' : p.germPt σ ⟶ p.germPt τ}
    (h : p.germWord w = p.germWord w') : w = w' :=
  (p.germProj_faithful n).map_injective h

/-- **A braid word whose braid makes a germ step lifts** — `GermStep.factor` supplies each
intermediate.  The `≍` is endpoint bookkeeping: `p` has one 0-cell per strand count, so a word's
target is `germBase` propositionally, not on the nose. -/
theorem exists_germPath_aux {n : ℕ} {σ : Equiv.Perm (Fin n)} :
    ∀ {y : GenObj (p.P n).Gen} (w : Quiver.Path (⟨p.v n⟩ : GenObj (p.P n).Gen) y)
      {τ : Equiv.Perm (Fin n)}, CubeChains.GermStep (p.wordBraid w) σ τ →
      ∃ w' : p.germPt σ ⟶ p.germPt τ, p.germWord w' ≍ w := by
  intro y w
  induction w with
  | nil =>
      intro τ h
      obtain rfl : σ = τ := by
        have hm := h.mul_eq
        rwa [show p.wordBraid (Quiver.Path.nil
            (a := (⟨p.v n⟩ : GenObj (p.P n).Gen))) = 1 from p.wordBraid_id _,
          map_one, mul_one, eq_comm] at hm
      exact ⟨Quiver.Path.nil, HEq.rfl⟩
  | @cons b c w e ih =>
      intro τ h
      obtain rfl : b = (⟨p.v n⟩ : GenObj (p.P n).Gen) :=
        congrArg (fun a => (⟨a⟩ : GenObj (p.P n).Gen)) (p.eq_v b.as)
      obtain rfl : c = (⟨p.v n⟩ : GenObj (p.P n).Gen) :=
        congrArg (fun a => (⟨a⟩ : GenObj (p.P n).Gen)) (p.eq_v c.as)
      rw [p.wordBraid_cons] at h
      obtain ⟨h₁, h₂⟩ := h.factor
      obtain ⟨w', hw'⟩ := ih h₁
      refine ⟨Quiver.Path.cons w' ⟨e, h₂⟩, heq_of_eq ?_⟩
      change Quiver.Path.cons (p.germWord w') e = Quiver.Path.cons w e
      rw [eq_of_heq hw']

/-- …at the strand count's own 0-cell, where no transport is left. -/
theorem exists_germPath {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (w : p.germBase n ⟶ p.germBase n)
    (h : CubeChains.GermStep (p.wordBraid w) σ τ) :
    ∃ w' : p.germPt σ ⟶ p.germPt τ, p.germWord w' = w :=
  (p.exists_germPath_aux w h).imp fun _ hw => eq_of_heq hw

/-! ## What the germ presents -/

/-- **A germ step rises in the weak order.** -/
theorem le_of_germStep {n : ℕ} {β : PosBraid n} {σ τ : Equiv.Perm (Fin n)}
    (h : CubeChains.GermStep β σ τ) : WeakOrder.of σ ≤ WeakOrder.of τ := by
  rw [h.mul_eq]
  exact WeakOrder.le_of_mul (by rw [← h.mul_eq]; exact h.permLen_add)

/-- **…and every rise is one**, at the simple that names the gap. -/
theorem germStep_of_le {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (h : WeakOrder.of σ ≤ WeakOrder.of τ) :
    CubeChains.GermStep (posPerm (σ⁻¹ * τ)) σ τ :=
  (germStep_posPerm_iff _ σ τ).mpr ⟨(mul_inv_cancel_left σ τ).symm, WeakOrder.le_def.mp h⟩

/-- The cells of the germ, interpreted in the weak order. -/
def germInterp (n : ℕ) : GenObj (p.GermGen n) ⥤q WeakOrder n where
  obj x := WeakOrder.of x.as
  map e := homOfLE (le_of_germStep (β := p.braid e.1) e.2)

/-- **The generators span**: `p` spells the simple that names the gap, and that word lifts. -/
theorem germInterp_full (n : ℕ) : (Paths.lift (p.germInterp n)).Full where
  map_surjective {x y} h := by
    obtain ⟨w, hw⟩ := (p.comp n).eval.map_surjective (X := p.germBase n) (Y := p.germBase n)
      (Quiver.Hom.op (X := SingleObj.star (PosBraid n)) (Y := SingleObj.star (PosBraid n))
        (posPerm (x.as⁻¹ * y.as)))
    have hb : p.wordBraid w = posPerm (x.as⁻¹ * y.as) := congrArg Quiver.Hom.unop hw
    have hstep : CubeChains.GermStep (p.wordBraid w) x.as y.as := by
      rw [hb]; exact germStep_of_le (leOfHom h)
    obtain ⟨w', -⟩ := p.exists_germPath w hstep
    exact ⟨w', Subsingleton.elim _ _⟩

/-- **The 0-cells cover**: they are the permutations. -/
theorem germInterp_essSurj (n : ℕ) : (Paths.lift (p.germInterp n)).EssSurj where
  mem_essImage c := ⟨⟨WeakOrder.perm c⟩, ⟨Iso.refl _⟩⟩

/-! ### Completeness

Two germ words with the same ends spell braid words performing the same braid, hence congruent
ones.  That congruence lifts: every word in the chain performs that braid, hence makes the same
germ step, hence lifts; and a relation of `p` applied inside a lifting word is applied between
lifting words. -/

private theorem gen_germ_aux {n : ℕ} {σ : Equiv.Perm (Fin n)} :
    ∀ {u v : p.germBase n ⟶ p.germBase n}, HomRel.Gen (p.P n).homRel u v →
      ∀ {τ : Equiv.Perm (Fin n)} (f g : p.germPt σ ⟶ p.germPt τ),
        p.germWord f = u → p.germWord g = v →
        HomRel.Gen ((p.germProj n).pathsFunctor.pullbackRel (p.P n).homRel) f g := by
  intro u v h
  induction h with
  | rel _ _ huv =>
      obtain ⟨X, Y, x, m₁, m₂, y, hm⟩ := huv
      obtain rfl : X = p.germBase n :=
        congrArg (fun a => (⟨a⟩ : GenObj (p.P n).Gen)) (p.eq_v X.as)
      obtain rfl : Y = p.germBase n :=
        congrArg (fun a => (⟨a⟩ : GenObj (p.P n).Gen)) (p.eq_v Y.as)
      intro τ f g hf hg
      have hstep := p.germStep_germWord f
      rw [hf, p.wordBraid_comp, p.wordBraid_comp] at hstep
      obtain ⟨hx, hmy⟩ := hstep.factor
      obtain ⟨hm₁, hy⟩ := hmy.factor
      obtain ⟨x', hx'⟩ := p.exists_germPath x hx
      obtain ⟨m₁', hm₁'⟩ := p.exists_germPath m₁ hm₁
      obtain ⟨y', hy'⟩ := p.exists_germPath y hy
      obtain ⟨m₂', hm₂'⟩ := p.exists_germPath m₂ (by
        rw [← p.wordBraid_eq_of_homRel hm]; exact hm₁)
      obtain rfl : f = x' ≫ m₁' ≫ y' :=
        p.germWord_injective (by rw [hf, p.germWord_comp, p.germWord_comp, hx', hm₁', hy'])
      obtain rfl : g = x' ≫ m₂' ≫ y' :=
        p.germWord_injective (by rw [hg, p.germWord_comp, p.germWord_comp, hx', hm₂', hy'])
      refine Relation.EqvGen.rel _ _ (HomRel.CompClosure.intro _ _ x' m₁' m₂' y' ?_)
      change (p.P n).homRel (p.germWord m₁') (p.germWord m₂')
      rw [hm₁', hm₂']
      exact hm
  | refl _ =>
      intro τ f g hf hg
      exact p.germWord_injective (hf.trans hg.symm) ▸ Relation.EqvGen.refl _
  | symm _ _ _ ih => intro τ f g hf hg; exact (ih g f hg hf).symm
  | @trans _ v _ huv _ ih₁ ih₂ =>
      intro τ f g hf hg
      have hstep := p.germStep_germWord f
      rw [hf, p.wordBraid_eq_of_gen huv] at hstep
      obtain ⟨m, hm⟩ := p.exists_germPath v hstep
      exact Relation.EqvGen.trans _ _ _ (ih₁ f m hf hm) (ih₂ m g hm hg)

/-- **Two germ words with the same ends are one arrow** — completeness, inherited from `p`'s. -/
theorem germ_quot_map_eq {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (f g : p.germPt σ ⟶ p.germPt τ) :
    (p.germPoly n).quot.map f = (p.germPoly n).quot.map g := by
  refine Polygraph.comap_quot_map_eq_of_gen (p.germProj n) (p.gen_germ_aux ?_ f g rfl rfl)
  exact (p.comp n).gen_of_eval_eq
    (Quiver.Hom.unop_inj ((p.germStep_germWord f).eq_of_eq (p.germStep_germWord g)))

/-- **`p`'s germ presents the right weak Bruhat order on `Sₙ`** — 0-cells the permutations,
1-cells `p`'s generators where they make a germ step, 2-cells `p`'s relations holding there.
Dehornoy–Digne–Michel's germ presentation, for the braid germ. -/
noncomputable def dehornoy (n : ℕ) : Presents (p.germPoly n) (WeakOrder n) :=
  Presents.ofDesc (p.germInterp n) (fun _ => Subsingleton.elim _ _)
    (fun {_ _ _ _} _ => p.germ_quot_map_eq _ _) (p.germInterp_full n) (p.germInterp_essSurj n)

end BraidPresentation

/-! ## …functorially in the braid presentation

A comparison of braid presentations spells each generator of `p` by a word of `q`; that word
performs the generator's own braid, so it lifts at the germ step's source and spells the germ
1-cell.  Soundness and the comparison iso are both thinness of the weak order. -/

namespace BraidPresentation.Map

variable {p q : BraidPresentation} (m : BraidPresentation.Map p q)

/-- **A comparison's word performs the generator's braid** — `braid_word`, in germ vocabulary. -/
theorem wordBraid_word {n : ℕ} {x y : (p.P n).V} (s : (p.P n).Gen x y) :
    q.wordBraid (m.word s) = p.braid s := m.braid_word s

/-- The germ word a comparison spells a germ 1-cell by. -/
noncomputable def germWordOf {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (e : p.GermGen n σ τ) :
    q.germPt σ ⟶ q.germPt τ :=
  (q.exists_germPath (q.rebase (m.word e.1))
    (by rw [q.wordBraid_rebase, m.wordBraid_word]; exact e.2)).choose

/-- **A comparison of braid presentations is one of their germs.** -/
noncomputable def germSpelling (n : ℕ) : Polygraph.Spelling (p.germPoly n) (q.germPoly n) where
  cells := { obj := fun x => ⟨x.as⟩, map := fun {_ _} e => m.germWordOf e }
  sound _ := q.germ_quot_map_eq _ _

/-- **…and the germ presentation is functorial in the braid presentation** — the comparison iso is
the identity, because the weak order is a poset and both readings name the same permutation. -/
noncomputable def dehornoy (n : ℕ) :
    Polygraph.Presents.Map (p.dehornoy n) (q.dehornoy n) where
  hom := m.germSpelling n
  iso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => Subsingleton.elim _ _

end BraidPresentation.Map

end ChainCat
