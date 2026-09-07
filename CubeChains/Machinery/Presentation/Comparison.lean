import CubeChains.Machinery.Presentation.Basic
import Mathlib.CategoryTheory.HomCongr

/-!
# Machinery/Presentation/Comparison — two presentations of one category

Two presentations of one category are abstractly equivalent for free (`p.equiv.trans q.equiv.symm`),
which says nothing.  The content is that the comparison is *spelled by the generators*: a
`Presents.Map` is a `Polygraph.Spelling` whose induced functor commutes with the two comparisons,
and it is then automatically an equivalence (`isEquivalence`).

A spelling sends a 1-cell to a *word*, so one exists whenever each generator of `P` can be spelled
in `Q` at all — a mere *choice* of word makes the statement vacuous.  The comparisons worth building
are those whose generators go to generators.
-/

universe v w w' w'' u u' u'' u''' w₂ w₂' w₂''

namespace CategoryTheory.Polygraph

variable {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}} {C : Type u} [Category.{v} C]

/-- **An arrow read at objects its endpoints are equal to** — `Quiver.homOfEq`, as `eqToHom`s. -/
theorem _root_.CategoryTheory.Functor.map_homOfEq {D : Type*} [Category* D] {E : Type*}
    [Category* E] (F : D ⥤ E) {X Y X' Y' : D} (f : X ⟶ Y) (hX : X = X') (hY : Y = Y') :
    F.map (Quiver.homOfEq f hX hY)
      = eqToHom (congrArg F.obj hX).symm ≫ F.map f ≫ eqToHom (congrArg F.obj hY) := by
  subst hX; subst hY; simp

/-- **An `eqToHom`-conjugate is pinned by the arrow it conjugates** — proof irrelevance, once the
two composites are flattened.  Stated at the nesting a comparison of two glued presentations
produces, because `rw`/`simp` cannot reassociate there: the object slots of `≫` carry two spellings
of one object, which defeats `kabstract`, while `exact` unifies them. -/
theorem eqToHom_sandwich {D : Type*} [Category* D] {A Z X Y W B Z' W' : D} (f : X ⟶ Y)
    (h₁ : A = Z) (h₂ : Z = X) (h₃ : Y = W) (h₄ : W = B)
    (h₁' : A = Z') (h₂' : Z' = X) (h₃' : Y = W') (h₄' : W' = B) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ f ≫ eqToHom h₃) ≫ eqToHom h₄
      = eqToHom h₁' ≫ (eqToHom h₂' ≫ f ≫ eqToHom h₃') ≫ eqToHom h₄' := by
  subst h₂; subst h₄; subst h₂'; subst h₄'; simp

/-- **A 1-cell read at 0-cells its endpoints are equal to**: the transport a comparison of two
polygraphs leaves behind. -/
theorem Presents.arrow_homOfEq (p : Presents P C) {a b a' b' : GenObj P.Gen} (f : a ⟶ b)
    (ha : a = a') (hb : b = b') :
    p.arrow (Quiver.homOfEq f ha hb)
      = eqToHom (congrArg p.at' ha).symm ≫ p.arrow f ≫ eqToHom (congrArg p.at' hb) := by
  subst ha; subst hb; simp [Quiver.homOfEq]

/-- **A comparison of presentations**: a spelling naming the same arrows. -/
structure Presents.Map (p : Presents P C) (q : Presents Q C) where
  /-- the word each generator spells -/
  hom : Spelling P Q
  /-- …naming the same arrow of `C` -/
  iso : hom.functor ⋙ q.E ≅ p.E

namespace Presents.Map

variable {p : Presents P C} {q : Presents Q C} (m : Presents.Map p q)

/-- **A comparison names the same arrow, on whole words** — the naturality of `iso`, which is the
only thing the `iso` field is ever used for. -/
theorem eval_words {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    q.eval.map (m.hom.words.map u) = m.iso.hom.app ⟨x⟩ ≫ p.eval.map u ≫ m.iso.inv.app ⟨y⟩ :=
  have hnat : q.eval.map (m.hom.words.map u) ≫ (m.iso.app ⟨y⟩).hom
      = m.iso.hom.app ⟨x⟩ ≫ p.eval.map u := m.iso.hom.naturality (P.quot.map u)
  ((Iso.eq_comp_inv (m.iso.app ⟨y⟩)).mpr hnat).trans (Category.assoc _ _ _)

/-- **A spelling reads a generator's word off its own `cells`.** -/
theorem _root_.CategoryTheory.Polygraph.Spelling.words_toPath (F : Spelling P Q)
    {x y : GenObj P.Gen} (e : x ⟶ y) : F.words.map e.toPath = F.cells.map e := by
  rw [show e.toPath = Quiver.Path.nil.cons e from rfl, Paths.lift_cons, Paths.lift_nil]
  exact Category.id_comp _

/-- …and on a generator, whose word is one letter. -/
theorem eval_cells {x y : GenObj P.Gen} (e : x ⟶ y) :
    q.eval.map (m.hom.cells.map e) = m.iso.hom.app ⟨x⟩ ≫ p.arrow e ≫ m.iso.inv.app ⟨y⟩ :=
  (congrArg q.eval.map (m.hom.words_toPath e).symm).trans (m.eval_words e.toPath)

/-- **A comparison of presentations of one category is an equivalence.**  Neither polygraph is
assumed finite, small or related to the other: only that one spells the other's arrows. -/
instance isEquivalence : m.hom.functor.IsEquivalence :=
  haveI : (m.hom.functor ⋙ q.E).IsEquivalence := Functor.isEquivalence_of_iso m.iso.symm
  Functor.isEquivalence_of_comp_right _ q.E

/-- The two polygraphs present the same category, compatibly. -/
noncomputable def equiv : P.presented ≌ Q.presented := m.hom.functor.asEquivalence

end Presents.Map

/-! ## Comparisons compose

A polygraph spelling itself letter by letter is the identity, and two spellings compose by
substituting the second into the first's words (`Paths.lift_comp_map`).  So the presentations of a
fixed category carry an identity and a composition, and every arrow is invertible up to the
equivalence `isEquivalence` supplies. -/

theorem _root_.CategoryTheory.Paths.lift_of (V : Type u') [Quiver.{w} V] :
    Paths.lift (Paths.of V) = 𝟭 (Paths V) :=
  (Paths.lift_unique (Paths.of V) (𝟭 (Paths V)) rfl).symm

namespace Spelling

variable {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}}
  {R : Polygraph.{w'', u''', w₂''}}

/-- **A polygraph spells itself, letter by letter.** -/
def refl (P : Polygraph.{w, u', w₂}) : Spelling P P where
  cells := Paths.of _
  sound α := by rw [Paths.lift_of]; exact P.quot_src_tgt α

@[simp] theorem functor_refl : (Spelling.refl P).functor = 𝟭 P.presented :=
  descWords_id (by
    rw [show (Spelling.refl P).words = 𝟭 P.Word from Paths.lift_of _, Functor.id_comp])

/-- **Substituting one spelling into another.** -/
def trans (F : Spelling P Q) (G : Spelling Q R) : Spelling P R where
  cells := F.cells ⋙q (Paths.lift G.cells).toPrefunctor
  sound α := by
    rw [← Paths.lift_comp_map F.cells (Paths.lift G.cells),
      ← Paths.lift_comp_map F.cells (Paths.lift G.cells)]
    exact congrArg G.functor.map (F.sound α)

theorem words_trans (F : Spelling P Q) (G : Spelling Q R) :
    (F.trans G).words = F.words ⋙ G.words :=
  (Paths.lift_unique (F.cells ⋙q (Paths.lift G.cells).toPrefunctor) (F.words ⋙ G.words)
    (congrArg (fun π => π ⋙q G.words.toPrefunctor) (Paths.lift_spec F.cells))).symm

theorem functor_trans (F : Spelling P Q) (G : Spelling Q R) :
    (F.trans G).functor = F.functor ⋙ G.functor :=
  descWords_comp G.functor (by
    rw [words_trans, Functor.assoc, ← Spelling.quot_comp_functor G, ← Functor.assoc])

end Spelling

namespace Presents.Map

variable {p : Presents P C} {q : Presents Q C}

/-- **The identity comparison.** -/
def refl (p : Presents P C) : Presents.Map p p where
  hom := Spelling.refl P
  iso := eqToIso (by rw [Spelling.functor_refl, Functor.id_comp])

/-- **Comparisons compose** — substitute the second spelling into the first's words. -/
def trans {R : Polygraph.{w'', u''', w₂''}} {r : Presents R C}
    (m : Presents.Map p q) (n : Presents.Map q r) : Presents.Map p r where
  hom := m.hom.trans n.hom
  iso := eqToIso (congrArg (fun U => U ⋙ r.E) (Spelling.functor_trans m.hom n.hom)) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft m.hom.functor n.iso ≪≫ m.iso

end Presents.Map

/-! ## Building one

The 2-cells never have to be checked: a spelling that names the same arrow kills them, `q.E` being
faithful.  So a comparison *is* its generator data. -/

section OfSpelling

private theorem conj_comp_hom {A B A' B' : C} (α : A' ≅ A) (β : B' ≅ B) (f : A ⟶ B) :
    (α.hom ≫ f ≫ β.inv) ≫ β.hom = α.hom ≫ f := by simp

/-- **A prefunctor conjugate to `p`'s own interpretation lifts to one** — the induction every
comparison runs, stated where composition is the target category's, not `Paths`'. -/
theorem lift_conj {p : Presents P C} {ψ : GenObj P.Gen ⥤q C}
    (θ : ∀ x : GenObj P.Gen, ψ.obj x ≅ p.at' x)
    (hψ : ∀ {x y : GenObj P.Gen} (e : x ⟶ y), ψ.map e = (θ x).hom ≫ p.arrow e ≫ (θ y).inv)
    {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (Paths.lift ψ).map u = (θ x).hom ≫ p.eval.map u ≫ (θ y).inv := by
  induction u with
  | nil => rw [Paths.lift_nil, p.eval_nil, Category.id_comp, (θ x).hom_inv_id]
  | @cons b c u e ih =>
      rw [Paths.lift_cons, ih, hψ e, p.eval_cons]
      -- `Category.assoc` cannot fire: the outer `≫` spells its objects `(Paths.lift ψ).obj`
      -- where the inner spells them `ψ.obj`, so the step runs through `exact`.
      exact (Iso.homCongr_comp (θ x).symm (θ b).symm (θ c).symm (p.eval.map u) (p.arrow e)).symm

variable {p : Presents P C} {q : Presents Q C} (φ : GenObj P.Gen ⥤q Q.Word)
  (θ : ∀ x : GenObj P.Gen, q.eval.obj (φ.obj x) ≅ p.at' x)
  (hφ : ∀ {x y : GenObj P.Gen} (e : x ⟶ y),
    q.eval.map (φ.map e) = (θ x).hom ≫ p.arrow e ≫ (θ y).inv)

include hφ in
/-- **A spelling names the same arrow on whole words**, not only on generators. -/
theorem eval_lift_map {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    q.eval.map ((Paths.lift φ).map u) = (θ x).hom ≫ p.eval.map u ≫ (θ y).inv :=
  (Paths.lift_comp_map φ q.eval u).trans
    (lift_conj (ψ := φ ⋙q q.eval.toPrefunctor) θ (fun e => hφ e) u)

include hφ in
/-- **`Spelling`'s obligation, for free**: `q.E` is faithful, so a 2-cell of `P` whose two sides
name one arrow of `C` is spelled by two equal arrows of `Q.presented`. -/
theorem spelling_sound {x y : GenObj P.Gen} (α : P.Rel x y) :
    Q.quot.map ((Paths.lift φ).map (P.src α)) = Q.quot.map ((Paths.lift φ).map (P.tgt α)) :=
  q.E.map_injective
    (((eval_lift_map φ θ hφ _).trans (by rw [p.sound α])).trans (eval_lift_map φ θ hφ _).symm)

/-- **A comparison of presentations, from a spelling of the generators.**  `θ` names the 0-cells,
`hφ` says a 1-cell spells the same arrow; that is the whole of the data. -/
def Presents.Map.ofSpelling : Presents.Map p q where
  hom := ⟨φ, fun α => spelling_sound φ θ hφ α⟩
  iso := NatIso.ofComponents (fun X => θ X.as) (by
    rintro ⟨x⟩ ⟨y⟩ f
    obtain ⟨u, rfl⟩ := P.quot.map_surjective f
    change q.eval.map ((Paths.lift φ).map u) ≫ (θ y).hom = (θ x).hom ≫ p.eval.map u
    rw [eval_lift_map φ θ hφ]
    exact conj_comp_hom (θ x) (θ y) (p.eval.map u))

end OfSpelling

/-! A comparison whose generators go to *generators* — the form worth having, and the only one that
says anything: the words are single letters, so the two generating families biject onto each other's
arrows. -/

section OfGenerators

variable {p : Presents P C} {q : Presents Q C} (ob : GenObj P.Gen → GenObj Q.Gen)
  (gen : ∀ {x y : GenObj P.Gen}, (x ⟶ y) → (ob x ⟶ ob y))
  (θ : ∀ x : GenObj P.Gen, q.at' (ob x) ≅ p.at' x)
  (hgen : ∀ {x y : GenObj P.Gen} (e : x ⟶ y),
    q.arrow (gen e) = (θ x).hom ≫ p.arrow e ≫ (θ y).inv)

include hgen in
/-- **…generator by generator.** -/
def Presents.Map.ofGenerators : Presents.Map p q :=
  Presents.Map.ofSpelling ⟨ob, fun e => (gen e).toPath⟩ θ hgen

end OfGenerators

end CategoryTheory.Polygraph
