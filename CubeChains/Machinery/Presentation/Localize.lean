import CubeChains.Machinery.Presentation.Basic
import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Machinery/Presentation/Localize — formal inverses for some of the generators

`invPoly P S` adjoins to `P` one formal-inverse 1-cell per 1-cell `S` picks out, together with the
two cancellation 2-cells; `presentsLocalization` says it presents the localization of what `P`
presents at the class the picked cells generate.

The proof compares universal properties: a functor out of `(invPoly P S).presented` is a functor out
of `P.presented` sending each picked cell to an *isomorphism* (`invDesc`, `invIncl_comp_injective`),
which is `IsInvertedBy` once the class is the multiplicative closure.

Everything is spelled on `GenObj (InvGen P S)`, never on `GenObj (invPoly P S).Gen`: the two differ
by a projection, so mixing them blocks `rw` on the `Paths.lift` lemmas.
-/

universe w u' w₂ v u v₂ u₂ v₃ u₃

namespace CategoryTheory

/-! ## A multiplicative closure, reversed -/

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] (G : MorphismProperty C)

/-- **Generating a class commutes with reversal** — the closure is the least multiplicative class
above `G`, and reversal preserves `IsMultiplicative`. -/
theorem multiplicativeClosure_op :
    G.multiplicativeClosure.op = G.op.multiplicativeClosure := by
  refine le_antisymm (fun _ _ f hf => ?_) (fun _ _ f hf => ?_)
  · exact (multiplicativeClosure_le_iff G G.op.multiplicativeClosure.unop).mpr
      (fun _ _ g hg => le_multiplicativeClosure G.op g.op hg) f.unop hf
  · exact (multiplicativeClosure_le_iff G.op G.multiplicativeClosure.op).mpr
      (fun _ _ g hg => le_multiplicativeClosure G g.unop hg) f hf

/-! ## A functor between localizations

A functor carrying one class into another descends, and `Localization.Construction.fac` makes the
square an *equality*; so the two functor laws are `uniq`, and nothing is transported. -/

section LocalizedMap

variable {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]

/-- **A functor carrying one class into another, localized.** -/
noncomputable def localizedMap (W₁ : MorphismProperty C) (W₂ : MorphismProperty D) (F : C ⥤ D)
    (hF : ∀ {X Y : C} (f : X ⟶ Y), W₁ f → W₂ (F.map f)) :
    W₁.Localization ⥤ W₂.Localization :=
  Localization.Construction.lift (F ⋙ W₂.Q) fun _ _ f hf =>
    Localization.inverts W₂.Q W₂ _ (hF f hf)

theorem Q_comp_localizedMap (W₁ : MorphismProperty C) (W₂ : MorphismProperty D) (F : C ⥤ D)
    (hF : ∀ {X Y : C} (f : X ⟶ Y), W₁ f → W₂ (F.map f)) :
    W₁.Q ⋙ localizedMap W₁ W₂ F hF = F ⋙ W₂.Q :=
  Localization.Construction.fac _ _

/-- **Two functors out of a localization agree as soon as they agree upstairs** — the uniqueness
every functor law below is. -/
theorem eq_of_Q_comp_eq {W₁ : MorphismProperty C} {W₂ : MorphismProperty D}
    {Φ Ψ : W₁.Localization ⥤ W₂.Localization} (h : W₁.Q ⋙ Φ = W₁.Q ⋙ Ψ) : Φ = Ψ :=
  Localization.Construction.uniq _ _ h

theorem localizedMap_id (W₁ : MorphismProperty C)
    (hF : ∀ {X Y : C} (f : X ⟶ Y), W₁ f → W₁ ((𝟭 C).map f)) :
    localizedMap W₁ W₁ (𝟭 C) hF = 𝟭 _ :=
  eq_of_Q_comp_eq ((Q_comp_localizedMap W₁ W₁ (𝟭 C) hF).trans rfl)

theorem localizedMap_comp (W₁ : MorphismProperty C) (W₂ : MorphismProperty D)
    (W₃ : MorphismProperty E) (F : C ⥤ D) (G : D ⥤ E)
    (hF : ∀ {X Y : C} (f : X ⟶ Y), W₁ f → W₂ (F.map f))
    (hG : ∀ {X Y : D} (g : X ⟶ Y), W₂ g → W₃ (G.map g))
    (hFG : ∀ {X Y : C} (f : X ⟶ Y), W₁ f → W₃ ((F ⋙ G).map f)) :
    localizedMap W₁ W₃ (F ⋙ G) hFG = localizedMap W₁ W₂ F hF ⋙ localizedMap W₂ W₃ G hG :=
  eq_of_Q_comp_eq ((Q_comp_localizedMap W₁ W₃ (F ⋙ G) hFG).trans
    ((congrArg (fun H => F ⋙ H) (Q_comp_localizedMap W₂ W₃ G hG)).symm.trans
      (congrArg (fun H => H ⋙ localizedMap W₂ W₃ G hG)
        (Q_comp_localizedMap W₁ W₂ F hF)).symm))

end LocalizedMap

end MorphismProperty

/-! ## A localization localizes at every class with the same localization

`V ≤ W` together with `W` inverted by `V.Q` says exactly that `V` and `W` have the same
localization; `Equivalence.refl` turns that into the source-transport lemma. -/

/-- **A localization at `V` localizes at every bigger class its localization already inverts.** -/
theorem Functor.IsLocalization.of_le {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {V W : MorphismProperty C} [L.IsLocalization V] (hle : V ≤ W)
    (hinv : W.IsInvertedBy V.Q) : L.IsLocalization W :=
  Functor.IsLocalization.of_equivalence_source L V L W (Equivalence.refl)
    (fun _ _ f hf => MorphismProperty.le_isoClosure W _ (hle f hf))
    ((MorphismProperty.IsInvertedBy.iff_of_iso W
        (Localization.qCompEquivalenceFromModelFunctorIso L V)).mp
      (MorphismProperty.IsInvertedBy.of_comp W V.Q hinv _))
    (Functor.leftUnitor L)

/-! ## A transformation out of a localization is pinned by its restriction

`Localization.liftNatTrans` lifts; these say the lift is the only one, which is what makes a
comparison built that way canonical — and what reduces a coherence upstairs to one downstairs. -/

namespace Localization

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E] (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] {F₁ F₂ : D ⥤ E}

include W in
theorem natTrans_ext_whiskerLeft {σ σ' : F₁ ⟶ F₂}
    (h : Functor.whiskerLeft L σ = Functor.whiskerLeft L σ') : σ = σ' :=
  natTrans_ext L W fun X => congr_app h X

include W in
theorem iso_ext_isoWhiskerLeft {e e' : F₁ ≅ F₂}
    (h : Functor.isoWhiskerLeft L e = Functor.isoWhiskerLeft L e') : e = e' :=
  Iso.ext (natTrans_ext_whiskerLeft L W (congrArg Iso.hom h))

@[simp] theorem whiskerLeft_liftNatTrans (τ : L ⋙ F₁ ⟶ L ⋙ F₂) :
    Functor.whiskerLeft L (liftNatTrans L W (L ⋙ F₁) (L ⋙ F₂) F₁ F₂ τ) = τ := by
  ext X; simp

@[simp] theorem isoWhiskerLeft_liftNatIso (e : L ⋙ F₁ ≅ L ⋙ F₂) :
    Functor.isoWhiskerLeft L (liftNatIso L W (L ⋙ F₁) (L ⋙ F₂) F₁ F₂ e) = e :=
  Iso.ext (whiskerLeft_liftNatTrans L W e.hom)

end Localization

/-! ## The arrows a family of 1-cells names -/

namespace Presents

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C] (p : Presents P C)
  (S : ∀ {a b : P.V}, P.Gen a b → Prop)

/-- The arrow of `C` a picked 1-cell evaluates to. -/
inductive Picked : ∀ {A B : C}, (A ⟶ B) → Prop
  | mk {a b : P.V} (e : P.Gen a b) (he : S e) : Picked (p.arrow (Polygraph.cell e))

/-- **The arrows the picked 1-cells evaluate to.** -/
def pickedArrows : MorphismProperty C := fun _ _ f => p.Picked S f

end Presents

namespace Polygraph

/-! ## The extension -/

section Invert

variable (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)

/-- **1-cells**: those of `P`, and a formal inverse for each the predicate picks out.  A `Sum` and
not an inductive: a constructor argument in `P.V` would raise the 1-cell universe. -/
abbrev InvGen (a b : P.V) : Type w := P.Gen a b ⊕ {e : P.Gen b a // S e}

/-- A 1-cell of `P`, in the extension. -/
def fwdCell {a b : P.V} (e : P.Gen a b) : (⟨a⟩ : GenObj (InvGen P S)) ⟶ ⟨b⟩ := .inl e

/-- …and the formal inverse of a picked one. -/
def bwdCell {a b : P.V} (e : P.Gen a b) (he : S e) :
    (⟨b⟩ : GenObj (InvGen P S)) ⟶ ⟨a⟩ := .inr ⟨e, he⟩

/-- `P`'s generating quiver, inside the extension's. -/
def fwdPre : GenObj P.Gen ⥤q GenObj (InvGen P S) where
  obj x := ⟨x.as⟩
  map e := .inl e

/-- **2-cells**: those of `P`, and the two cancellations. -/
inductive InvRel : GenObj (InvGen P S) → GenObj (InvGen P S) → Type (max u' w w₂)
  | keep {x y : GenObj P.Gen} (α : P.Rel x y) : InvRel ⟨x.as⟩ ⟨y.as⟩
  | cancel {a b : P.V} (e : P.Gen a b) (he : S e) : InvRel ⟨a⟩ ⟨a⟩
  | cancel' {a b : P.V} (e : P.Gen a b) (he : S e) : InvRel ⟨b⟩ ⟨b⟩

/-- The source word of a 2-cell. -/
def invSrc : ∀ {x y : GenObj (InvGen P S)}, InvRel P S x y → Quiver.Path x y
  | _, _, .keep α => (fwdPre P S).mapPath (P.src α)
  | _, _, .cancel e he => (fwdCell P S e).toPath.comp (bwdCell P S e he).toPath
  | _, _, .cancel' e he => (bwdCell P S e he).toPath.comp (fwdCell P S e).toPath

/-- …and the target word. -/
def invTgt : ∀ {x y : GenObj (InvGen P S)}, InvRel P S x y → Quiver.Path x y
  | _, _, .keep α => (fwdPre P S).mapPath (P.tgt α)
  | _, _, .cancel _ _ => Quiver.Path.nil
  | _, _, .cancel' _ _ => Quiver.Path.nil

/-- **`P` with a formal inverse adjoined for each picked 1-cell.** -/
def invPoly : Polygraph.{w, u', max u' w w₂} where
  V := P.V
  Gen := InvGen P S
  Rel := InvRel P S
  src := invSrc P S
  tgt := invTgt P S

/-- **The extension, as a morphism of polygraphs.** -/
def invIncl : Hom P (invPoly P S) where
  pre := fwdPre P S
  two α := .keep α
  src_two _ := rfl
  tgt_two _ := rfl

/-! ## The picked cells, and their inverses in the extension -/

/-- The arrow a 1-cell names in `P.presented`. -/
def genArrow {a b : P.V} (e : P.Gen a b) : (⟨⟨a⟩⟩ : P.presented) ⟶ ⟨⟨b⟩⟩ :=
  P.quot.map (cell e).toPath

/-- The arrow a 1-cell names in the extension. -/
def fwdArrow {a b : P.V} (e : P.Gen a b) :
    (⟨⟨a⟩⟩ : (invPoly P S).presented) ⟶ ⟨⟨b⟩⟩ :=
  (invPoly P S).quot.map (fwdCell P S e).toPath

/-- …and the one its formal inverse names. -/
def bwdArrow {a b : P.V} (e : P.Gen a b) (he : S e) :
    (⟨⟨b⟩⟩ : (invPoly P S).presented) ⟶ ⟨⟨a⟩⟩ :=
  (invPoly P S).quot.map (bwdCell P S e he).toPath

theorem fwdArrow_bwdArrow {a b : P.V} (e : P.Gen a b) (he : S e) :
    fwdArrow P S e ≫ bwdArrow P S e he = 𝟙 _ :=
  ((invPoly P S).quot.map_comp _ _).symm.trans
    ((invPoly P S).quot_src_tgt (InvRel.cancel e he))

theorem bwdArrow_fwdArrow {a b : P.V} (e : P.Gen a b) (he : S e) :
    bwdArrow P S e he ≫ fwdArrow P S e = 𝟙 _ :=
  ((invPoly P S).quot.map_comp _ _).symm.trans
    ((invPoly P S).quot_src_tgt (InvRel.cancel' e he))

/-- **The cancellation 2-cells, as an isomorphism.** -/
def fwdIso {a b : P.V} (e : P.Gen a b) (he : S e) :
    (⟨⟨a⟩⟩ : (invPoly P S).presented) ≅ ⟨⟨b⟩⟩ where
  hom := fwdArrow P S e
  inv := bwdArrow P S e he
  hom_inv_id := fwdArrow_bwdArrow P S e he
  inv_hom_id := bwdArrow_fwdArrow P S e he

theorem isIso_fwdArrow {a b : P.V} (e : P.Gen a b) (he : S e) : IsIso (fwdArrow P S e) :=
  (fwdIso P S e he).isIso_hom

/-- **The extension reads a 1-cell of `P` as that 1-cell.** -/
theorem invIncl_functor_genArrow {a b : P.V} (e : P.Gen a b) :
    (invIncl P S).functor.map (genArrow P e) = fwdArrow P S e := rfl

/-! ## The class to invert, read upstairs

A 1-cell of `P` names an arrow of `P.presented` through the tautological presentation, so the class
upstairs is `Presents.pickedArrows` there and needs no second definition. -/

/-- **The class the picked 1-cells generate in `P.presented`.** -/
def pickedClosure : MorphismProperty P.presented :=
  ((Presents.self P).pickedArrows S).multiplicativeClosure

theorem pickedCells_le_pickedClosure :
    (Presents.self P).pickedArrows S ≤ pickedClosure P S :=
  MorphismProperty.le_multiplicativeClosure _

instance : (pickedClosure P S).IsMultiplicative :=
  inferInstanceAs ((Presents.self P).pickedArrows S).multiplicativeClosure.IsMultiplicative

/-- **The extension inverts the class** — the cancellation 2-cells do it one generator at a time. -/
theorem inverts_pickedClosure :
    (pickedClosure P S).IsInvertedBy (invIncl P S).functor := by
  have h : pickedClosure P S
      ≤ (MorphismProperty.isomorphisms _).inverseImage (invIncl P S).functor :=
    (MorphismProperty.multiplicativeClosure_le_iff _ _).mpr (by
      rintro X Y f ⟨e, he⟩
      exact isIso_fwdArrow P S e he)
  exact fun _ _ f hf => h f hf

/-! ## Reading the extension in a target

A functor out of `P.presented` inverting the picked cells is exactly a functor out of the extension:
the formal inverse has nowhere to go but the inverse. -/

section Desc

variable {E : Type*} [Category E] (F : P.presented ⥤ E)
  (hF : ((Presents.self P).pickedArrows S).IsInvertedBy F)

/-- The arrow a picked 1-cell names downstairs, as an isomorphism. -/
private noncomputable def descIso {a b : P.V} (e : P.Gen a b) (he : S e) :
    F.obj ⟨⟨a⟩⟩ ≅ F.obj ⟨⟨b⟩⟩ :=
  @asIso _ _ _ _ (F.map (genArrow P e)) (hF _ (Presents.Picked.mk e he))

private noncomputable def invMap :
    ∀ {a b : P.V}, InvGen P S a b → (F.obj ⟨⟨a⟩⟩ ⟶ F.obj ⟨⟨b⟩⟩)
  | _, _, .inl e => F.map (genArrow P e)
  | _, _, .inr ⟨e, he⟩ => (descIso P S F hF e he).inv

/-- The cells, read in `E`. -/
private noncomputable def invInterp : GenObj (InvGen P S) ⥤q E where
  obj x := F.obj ⟨⟨x.as⟩⟩
  map {x y} e := invMap P S F hF (e : InvGen P S x.as y.as)

/-- **A word of `P`, read through the extension.** -/
private theorem lift_invInterp_fwd {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (Paths.lift (invInterp P S F hF)).map ((fwdPre P S).mapPath u) = F.map (P.quot.map u) := by
  induction u with
  | nil =>
      rw [Prefunctor.mapPath_nil, Paths.lift_nil]
      exact ((congrArg F.map (P.quot.map_id _)).trans (F.map_id _)).symm
  | cons u e ih =>
      rw [Prefunctor.mapPath_cons, Paths.lift_cons, ih,
        show P.quot.map (u.cons e) = P.quot.map u ≫ P.quot.map (Quiver.Hom.toPath e) from
          P.quot.map_comp u (Quiver.Hom.toPath e),
        F.map_comp]
      rfl

private theorem invSound {x y : GenObj (InvGen P S)} (α : InvRel P S x y) :
    (Paths.lift (invInterp P S F hF)).map (invSrc P S α)
      = (Paths.lift (invInterp P S F hF)).map (invTgt P S α) := by
  cases α with
  | keep α =>
      exact (lift_invInterp_fwd P S F hF (P.src α)).trans
        ((congrArg F.map (P.quot_src_tgt α)).trans (lift_invInterp_fwd P S F hF (P.tgt α)).symm)
  | cancel e he =>
      change (Paths.lift (invInterp P S F hF)).map
            ((fwdCell P S e).toPath.comp (bwdCell P S e he).toPath)
          = (Paths.lift (invInterp P S F hF)).map Quiver.Path.nil
      rw [Paths.lift_map_comp, Paths.lift_toPath, Paths.lift_toPath, Paths.lift_nil]
      exact (descIso P S F hF e he).hom_inv_id
  | cancel' e he =>
      change (Paths.lift (invInterp P S F hF)).map
            ((bwdCell P S e he).toPath.comp (fwdCell P S e).toPath)
          = (Paths.lift (invInterp P S F hF)).map Quiver.Path.nil
      rw [Paths.lift_map_comp, Paths.lift_toPath, Paths.lift_toPath, Paths.lift_nil]
      exact (descIso P S F hF e he).inv_hom_id

/-- **The functor a reading of `P` with invertible picked cells descends to.** -/
noncomputable def invDesc : (invPoly P S).presented ⥤ E :=
  Polygraph.desc (P := invPoly P S) (invInterp P S F hF) (invSound P S F hF)

/-- **…and it restricts to the reading it came from.** -/
theorem invIncl_comp_invDesc : (invIncl P S).functor ⋙ invDesc P S F hF = F :=
  Quotient.lift_unique' P.homRel _ F
    (Functor.ext (fun _ => rfl) fun _ _ u =>
      (lift_invInterp_fwd P S F hF u).trans
        ((Category.comp_id _).symm.trans (Category.id_comp _).symm))

end Desc

/-- **A functor out of the extension is pinned by its restriction to `P`** — the formal inverse has
no choice but the inverse, and the 1-cells of `P` span the rest. -/
theorem invIncl_comp_injective {E : Type*} [Category E]
    {F₁ F₂ : (invPoly P S).presented ⥤ E}
    (h : (invIncl P S).functor ⋙ F₁ = (invIncl P S).functor ⋙ F₂) : F₁ = F₂ := by
  have hobj : ∀ x : GenObj (invPoly P S).Gen, F₁.obj ⟨x⟩ = F₂.obj ⟨x⟩ :=
    fun x => Functor.congr_obj h (⟨⟨x.as⟩⟩ : P.presented)
  have hφ : Paths.of (GenObj (invPoly P S).Gen) ⋙q ((invPoly P S).quot ⋙ F₁).toPrefunctor
      = Paths.of (GenObj (invPoly P S).Gen) ⋙q ((invPoly P S).quot ⋙ F₂).toPrefunctor := by
    refine Prefunctor.ext_homOfEq hobj fun x y e => ?_
    refine Eq.trans ?_ (homOfEq_eq_eqToHom_conj _ (hobj x) (hobj y)).symm
    rcases e with e' | ⟨e', he⟩
    · exact Functor.congr_hom h (genArrow P e')
    · have hfwd : F₁.map (fwdArrow P S e')
          = eqToHom (hobj y) ≫ F₂.map (fwdArrow P S e') ≫ eqToHom (hobj x).symm := by
        rw [← invIncl_functor_genArrow P S e']
        exact Functor.congr_hom h (genArrow P e')
      -- a functor reads a picked 1-cell as an isomorphism, the formal inverse as its inverse
      exact Iso.inv_eqToHom_conj (F₁.mapIso (fwdIso P S e' he)) (F₂.mapIso (fwdIso P S e' he))
        (hobj y) (hobj x) hfwd
  exact Quotient.lift_unique' (invPoly P S).homRel F₁ F₂
    ((Paths.lift_unique _ ((invPoly P S).quot ⋙ F₁) rfl).trans
      ((congrArg Paths.lift hφ).trans
        (Paths.lift_unique _ ((invPoly P S).quot ⋙ F₂) rfl).symm))

/-! ## The extension is a localization -/

/-- **The strict universal property of the localization**, at every target. -/
noncomputable def invStrict (E : Type*) [Category E] :
    Localization.StrictUniversalPropertyFixedTarget (invIncl P S).functor
      (pickedClosure P S) E where
  inverts := inverts_pickedClosure P S
  lift F hF := invDesc P S F
    (MorphismProperty.IsInvertedBy.of_le _ _ F hF (pickedCells_le_pickedClosure P S))
  fac F _ := invIncl_comp_invDesc P S F _
  uniq _ _ h := invIncl_comp_injective P S h

/-- **The extension localizes at the class the picked 1-cells generate.** -/
theorem isLocalization_invIncl :
    (invIncl P S).functor.IsLocalization (pickedClosure P S) :=
  Functor.IsLocalization.mk' _ _ (invStrict P S _) (invStrict P S _)

end Invert

/-! ## The formal inverse of a word -/

section InvWord

/-- **The formal inverse of a word all of whose letters are picked** — each letter's inverse, read
against the word. -/
def invWord (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {x y : GenObj P.Gen} (u : Quiver.Path x y)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u) :
    Quiver.Path ((fwdPre P S).obj y) ((fwdPre P S).obj x) :=
  Quiver.Path.All.foldRev (fun z : GenObj P.Gen => (fwdPre P S).obj z)
    (fun _ _ e he => (bwdCell P S e he).toPath) u h

theorem invWord_cons (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {x y z : GenObj P.Gen} (u : Quiver.Path x y) (e : y ⟶ z) (he : S e)
    (h₀ : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) (u.cons e)) :
    invWord P S (u.cons e) h = (bwdCell P S e he).toPath.comp (invWord P S u h₀) := rfl

/-- **A formal inverse is spelled out of formal inverses** — the `All` predicate a contraction of
the adjoined cells needs. -/
theorem all_invWord (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {T : ∀ ⦃x y : GenObj (InvGen P S)⦄, (x ⟶ y) → Prop}
    (hT : ∀ {a b : P.V} (e : P.Gen a b) (he : S e), T (bwdCell P S e he)) :
    ∀ {x y : GenObj P.Gen} (u : Quiver.Path x y)
      (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u), Quiver.Path.All T (invWord P S u h) := by
  intro x y u
  induction u with
  | nil => exact fun _ => Quiver.Path.all_nil _
  | cons u e ih =>
      intro h
      obtain ⟨h₀, he⟩ := (Quiver.Path.all_cons_iff u e).mp h
      rw [invWord_cons P S u e he h₀ h]
      exact (Quiver.Path.all_toPath.mpr (hT e he)).comp (ih h₀)

private theorem quot_invWord_aux (P : Polygraph.{w, u', w₂})
    (S : ∀ {a b : P.V}, P.Gen a b → Prop) :
    ∀ {x y : GenObj P.Gen} (u : Quiver.Path x y)
      (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u),
      ((invPoly P S).quot.map ((fwdPre P S).mapPath u)
            ≫ (invPoly P S).quot.map (invWord P S u h)
          = 𝟙 ((invPoly P S).quot.obj ((fwdPre P S).obj x)))
        ∧ ((invPoly P S).quot.map (invWord P S u h)
            ≫ (invPoly P S).quot.map ((fwdPre P S).mapPath u)
          = 𝟙 ((invPoly P S).quot.obj ((fwdPre P S).obj y))) := by
  intro x y u
  induction u with
  | nil =>
      refine fun h => ⟨?_, ?_⟩ <;>
        exact ((invPoly P S).quot.map_comp _ _).symm.trans
          ((invPoly P S).quot.map_id ((fwdPre P S).obj x))
  | cons u e ih =>
      intro h
      obtain ⟨h₀, he⟩ := (Quiver.Path.all_cons_iff u e).mp h
      obtain ⟨ih₁, ih₂⟩ := ih h₀
      have hfw : (invPoly P S).quot.map ((fwdPre P S).mapPath u) ≫ fwdArrow P S e
          = (invPoly P S).quot.map ((fwdPre P S).mapPath (u.cons e)) :=
        ((invPoly P S).quot.map_comp ((fwdPre P S).mapPath u) (fwdCell P S e).toPath).symm
      have hbw : bwdArrow P S e he ≫ (invPoly P S).quot.map (invWord P S u h₀)
          = (invPoly P S).quot.map (invWord P S (u.cons e) h) :=
        ((invPoly P S).quot.map_comp (bwdCell P S e he).toPath (invWord P S u h₀)).symm
      rw [← hfw, ← hbw]
      let iso := Iso.mk ((invPoly P S).quot.map ((fwdPre P S).mapPath u))
        ((invPoly P S).quot.map (invWord P S u h₀)) ih₁ ih₂ ≪≫ fwdIso P S e he
      exact ⟨iso.hom_inv_id, iso.inv_hom_id⟩

/-- **A word of picked 1-cells cancels its formal inverse.** -/
theorem quot_fwd_invWord (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {x y : GenObj P.Gen} (u : Quiver.Path x y)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u) :
    (invPoly P S).quot.map ((fwdPre P S).mapPath u)
        ≫ (invPoly P S).quot.map (invWord P S u h) = 𝟙 _ :=
  (quot_invWord_aux P S u h).1

/-- **…and is cancelled by it.** -/
theorem quot_invWord_fwd (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {x y : GenObj P.Gen} (u : Quiver.Path x y)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u) :
    (invPoly P S).quot.map (invWord P S u h)
        ≫ (invPoly P S).quot.map ((fwdPre P S).mapPath u) = 𝟙 _ :=
  (quot_invWord_aux P S u h).2

theorem invWord_congr (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {x y : GenObj P.Gen} {u v : Quiver.Path x y} (h : u = v)
    (hu : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u)
    (hv : Quiver.Path.All (fun ⦃_ _⦄ e => S e) v) :
    invWord P S u hu = invWord P S v hv := by subst h; rfl

/-- **A transported word's formal inverse is its formal inverse, transported** — reading a word at
another name for its far endpoint renames the near endpoint of the inverse. -/
theorem invWord_cellCongr (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {x y y' : GenObj P.Gen} (h : y = y') (u : Quiver.Path x y)
    (hu : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u)
    (hu' : Quiver.Path.All (fun ⦃_ _⦄ e => S e) (cellCongr Quiver.Path rfl h u)) :
    invWord P S (cellCongr Quiver.Path rfl h u) hu'
      = cellCongr Quiver.Path (congrArg (fwdPre P S).obj h) rfl (invWord P S u hu) := by
  subst h; rfl

end InvWord

/-! ## The extension along a map of polygraphs -/

universe w' u'' w₂'

section Map

variable {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}}
  (S : ∀ {a b : P.V}, P.Gen a b → Prop) (T : ∀ {a b : Q.V}, Q.Gen a b → Prop)
  (f : Hom P Q) (hf : ∀ {a b : P.V} (e : P.Gen a b), S e → T (f.pre.map (cell e)))

private def invPre : GenObj (InvGen P S) ⥤q GenObj (InvGen Q T) where
  obj x := ⟨(f.pre.obj ⟨x.as⟩).as⟩
  map {x y} e := match (e : InvGen P S x.as y.as) with
    | .inl e' => Sum.inl (f.pre.map (cell e'))
    | .inr ⟨e', he⟩ => Sum.inr ⟨f.pre.map (cell e'), hf e' he⟩

private theorem fwdPre_comp_invPre : fwdPre P S ⋙q invPre S T f hf = f.pre ⋙q fwdPre Q T := rfl

/-- The extension's square on words; both boundary conditions of `invPolyMap` are this. -/
private theorem invPre_mapPath_fwd {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (invPre S T f hf).mapPath ((fwdPre P S).mapPath u) = (fwdPre Q T).mapPath (f.pre.mapPath u) :=
  (Prefunctor.mapPath_comp_apply (fwdPre P S) (invPre S T f hf) u).symm.trans
    ((eq_of_heq (Prefunctor.mapPath_heq_of_eq (fwdPre_comp_invPre S T f hf) u)).trans
      (Prefunctor.mapPath_comp_apply f.pre (fwdPre Q T) u))

/-- **A map carrying picked 1-cells to picked 1-cells extends to the formal inverses.** -/
def invPolyMap : Hom (invPoly P S) (invPoly Q T) where
  pre := invPre S T f hf
  two {x y} α := match α with
    | .keep α => .keep (f.two α)
    | .cancel e he => .cancel (f.pre.map (cell e)) (hf e he)
    | .cancel' e he => .cancel' (f.pre.map (cell e)) (hf e he)
  src_two α := by
    cases α with
    | keep α =>
        exact (congrArg (fwdPre Q T).mapPath (f.src_two α)).trans
          (invPre_mapPath_fwd S T f hf (P.src α)).symm
    | cancel e he => rfl
    | cancel' e he => rfl
  tgt_two α := by
    cases α with
    | keep α =>
        exact (congrArg (fwdPre Q T).mapPath (f.tgt_two α)).trans
          (invPre_mapPath_fwd S T f hf (P.tgt α)).symm
    | cancel e he => rfl
    | cancel' e he => rfl

/-- **…carrying a word of picked 1-cells to the pushed-forward word.** -/
theorem invPolyMap_mapPath_fwd {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (invPolyMap S T f hf).pre.mapPath ((fwdPre P S).mapPath u)
      = (fwdPre Q T).mapPath (f.pre.mapPath u) :=
  invPre_mapPath_fwd S T f hf u

/-- **…and the formal inverse of a word to the formal inverse of the pushed-forward word.** -/
theorem invPolyMap_mapPath_invWord {x y : GenObj P.Gen} (u : Quiver.Path x y)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u)
    (h' : Quiver.Path.All (fun ⦃_ _⦄ e => T e) (f.pre.mapPath u)) :
    (invPolyMap S T f hf).pre.mapPath (invWord P S u h)
      = invWord Q T (f.pre.mapPath u) h' := by
  revert h h'
  induction u with
  | nil => intro h h'; rfl
  | cons u e ih =>
      intro h h'
      obtain ⟨h₀, he⟩ := (Quiver.Path.all_cons_iff u e).mp h
      obtain ⟨h₀', -⟩ := (Quiver.Path.all_cons_iff _ _).mp h'
      refine Eq.trans (congrArg (invPre S T f hf).mapPath
        (invWord_cons P S u e he h₀ h)) ?_
      refine Eq.trans (Prefunctor.mapPath_comp (invPre S T f hf)
        (bwdCell P S e he).toPath (invWord P S u h₀)) ?_
      refine Eq.trans ?_ (invWord_cons Q T (f.pre.mapPath u) (f.pre.map (cell e))
        (hf e he) h₀' h').symm
      exact congrArg (Quiver.Path.comp (bwdCell Q T (f.pre.map (cell e)) (hf e he)).toPath)
        (ih h₀ h₀')

/-! ### Reading the pushed-forward word at another name for its far endpoint

A contraction of the extension takes its words from the base, so a map of such contractions asks for
the two statements above with the pushed-forward word only *renamed* into the target's chosen word.
Both transports are `cellCongr`, and the formal inverse moves it to the other end. -/

/-- **A word of picked 1-cells, pushed forward and renamed at its far endpoint.** -/
theorem invPolyMap_mapPath_fwd_cellCongr {x y : GenObj P.Gen} {y' : GenObj Q.Gen}
    (u : Quiver.Path x y) (v : Quiver.Path (f.pre.obj x) y') (h : y' = f.pre.obj y)
    (hv : f.pre.mapPath u = cellCongr Quiver.Path rfl h v) :
    (invPolyMap S T f hf).pre.mapPath ((fwdPre P S).mapPath u)
      = cellCongr Quiver.Path rfl (congrArg (fwdPre Q T).obj h) ((fwdPre Q T).mapPath v) :=
  (invPolyMap_mapPath_fwd S T f hf u).trans
    ((congrArg (fwdPre Q T).mapPath hv).trans
      (Prefunctor.mapPath_cellCongr (fwdPre Q T) rfl h v))

/-- **…and its formal inverse**, the renaming now at the near endpoint. -/
theorem invPolyMap_mapPath_invWord_cellCongr {x y : GenObj P.Gen} {y' : GenObj Q.Gen}
    (u : Quiver.Path x y) (hu : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u)
    (v : Quiver.Path (f.pre.obj x) y') (h : y' = f.pre.obj y)
    (hv : f.pre.mapPath u = cellCongr Quiver.Path rfl h v)
    (hv' : Quiver.Path.All (fun ⦃_ _⦄ e => T e) v) :
    (invPolyMap S T f hf).pre.mapPath (invWord P S u hu)
      = cellCongr Quiver.Path (congrArg (fwdPre Q T).obj h) rfl (invWord Q T v hv') :=
  have hall : Quiver.Path.All (fun ⦃_ _⦄ e => T e) (f.pre.mapPath u) :=
    Quiver.Path.All.mapPath f.pre (fun e he => hf e he) hu
  (invPolyMap_mapPath_invWord S T f hf u hu hall).trans
    ((invWord_congr Q T hv hall (hv ▸ hall)).trans
      (invWord_cellCongr Q T h v hv' (hv ▸ hall)))

/-! ### …and the extension is natural for it

The square is an equality of *prefunctors* (`fwdPre_comp_invPre`), so it needs no transport; it is
stated on the presented categories because `Hom.comp` does not typecheck into an extension, which
raises the 2-cell universe. -/

theorem invIncl_functor_map_quot {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (invPolyMap S T f hf).functor.map ((invIncl P S).functor.map (P.quot.map u))
      = (invIncl Q T).functor.map (f.functor.map (P.quot.map u)) :=
  show (invPoly Q T).quot.map ((invPre S T f hf).mapPath ((fwdPre P S).mapPath u))
      = (invPoly Q T).quot.map ((fwdPre Q T).mapPath (f.pre.mapPath u)) from
  congrArg (invPoly Q T).quot.map (invPolyMap_mapPath_fwd S T f hf u)

/-- **Adjoining the formal inverses is natural in the map of polygraphs** — on the nose. -/
theorem invIncl_functor_naturality :
    (invIncl P S).functor ⋙ (invPolyMap S T f hf).functor
      = f.functor ⋙ (invIncl Q T).functor :=
  Polygraph.presented_ext_of_gen (fun _ => rfl) fun e =>
    heq_of_eq (invIncl_functor_map_quot S T f hf e.toPath)

end Map

section MapLaws

theorem invPolyMap_congr {P Q : Polygraph.{w, u', w₂}}
    (S : ∀ {a b : P.V}, P.Gen a b → Prop) (T : ∀ {a b : Q.V}, Q.Gen a b → Prop)
    {f g : Hom P Q} (h : f = g)
    (hf : ∀ {a b : P.V} (e : P.Gen a b), S e → T (f.pre.map (cell e)))
    (hg : ∀ {a b : P.V} (e : P.Gen a b), S e → T (g.pre.map (cell e))) :
    invPolyMap S T f hf = invPolyMap S T g hg := by subst h; rfl

theorem invPolyMap_id {P : Polygraph.{w, u', w₂}} (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    (hS : ∀ {a b : P.V} (e : P.Gen a b), S e → S ((𝟙 P : Hom P P).pre.map (cell e))) :
    invPolyMap S S (𝟙 P) hS = 𝟙 (invPoly P S) :=
  Hom.ext' (Prefunctor.ext' (fun _ => rfl) fun _ _ e => by rcases e with e | ⟨e, he⟩ <;> rfl)
    fun α => by cases α <;> rfl

theorem invPolyMap_comp {P Q R : Polygraph.{w, u', w₂}}
    (S : ∀ {a b : P.V}, P.Gen a b → Prop) (T : ∀ {a b : Q.V}, Q.Gen a b → Prop)
    (U : ∀ {a b : R.V}, R.Gen a b → Prop) (f : P ⟶ Q) (g : Q ⟶ R)
    (hf : ∀ {a b : P.V} (e : P.Gen a b), S e → T (f.pre.map (cell e)))
    (hg : ∀ {a b : Q.V} (e : Q.Gen a b), T e → U (g.pre.map (cell e)))
    (hfg : ∀ {a b : P.V} (e : P.Gen a b), S e → U ((f ≫ g).pre.map (cell e))) :
    invPolyMap S U (f ≫ g) hfg
      = (invPolyMap S T f hf ≫ invPolyMap T U g hg : invPoly P S ⟶ invPoly R U) :=
  Hom.ext' (Prefunctor.ext' (fun _ => rfl) fun _ _ e => by rcases e with e | ⟨e, he⟩ <;> rfl)
    fun α => by cases α <;> rfl

end MapLaws

section Fun

variable {D : Type*} [Category D] (G : D ⥤ Polygraph.{w, u', w₂})
  (S : ∀ (d : D) {a b : (G.obj d).V}, (G.obj d).Gen a b → Prop)
  (hS : ∀ {d d' : D} (u : d ⟶ d') {a b : (G.obj d).V} (e : (G.obj d).Gen a b),
    S d e → S d' ((G.map u).pre.map (cell e)))

/-- **A functor into `Polygraph` whose picked 1-cells are carried along, with the picked 1-cells
formally inverted.** -/
def invFunctor : D ⥤ Polygraph.{w, u', max u' w w₂} where
  obj d := invPoly (G.obj d) (S d)
  map {d d'} u := invPolyMap (S d) (S d') (G.map u) (hS u)
  map_id d := (invPolyMap_congr (S d) (S d) (G.map_id d) (hS (𝟙 d)) fun _ he => he).trans
    (invPolyMap_id (S d) fun _ he => he)
  map_comp {d d' d''} u v :=
    (invPolyMap_congr (S d) (S d'') (G.map_comp u v) (hS (u ≫ v))
        fun e he => hS v _ (hS u e he)).trans
      (invPolyMap_comp (S d) (S d') (S d'') (G.map u) (G.map v) (hS u) (hS v)
        fun e he => hS v _ (hS u e he))

end Fun

/-! ## A spelling, on the formal inverses -/

section Spell

variable {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}}
  (S : ∀ {a b : P.V}, P.Gen a b → Prop) (T : ∀ {a b : Q.V}, Q.Gen a b → Prop)

/-- **The words a picked-respecting spelling of the 1-cells spells, on the formal inverses.** -/
def invCells (X : GenObj P.Gen ⥤q Q.Word)
    (hX : ∀ {a b : P.V} (e : P.Gen a b), S e →
      Quiver.Path.All (fun ⦃_ _⦄ e' => T e') (X.map (cell e))) :
    GenObj (InvGen P S) ⥤q (invPoly Q T).Word where
  obj x := (fwdPre Q T).obj (X.obj ⟨x.as⟩)
  map {x y} e := match (e : InvGen P S x.as y.as) with
    | .inl e' => (fwdPre Q T).mapPath (X.map (cell e'))
    | .inr ⟨e', he⟩ => invWord Q T (X.map (cell e')) (hX e' he)

private theorem lift_invCells_fwd (X : GenObj P.Gen ⥤q Q.Word) (hX) {x y : GenObj P.Gen}
    (u : Quiver.Path x y) :
    (Paths.lift (invCells S T X hX)).map ((fwdPre P S).mapPath u)
      = (fwdPre Q T).mapPath ((Paths.lift X).map u) :=
  (Paths.lift_mapPath (fwdPre P S) (invCells S T X hX) u).trans
    (Paths.lift_comp_map X (fwdPre Q T).pathsFunctor u).symm

variable (ψ : Spelling P Q)
  (hψ : ∀ {a b : P.V} (e : P.Gen a b), S e →
    Quiver.Path.All (fun ⦃_ _⦄ e' => T e') (ψ.cells.map (cell e)))

/-- **A spelling whose picked 1-cells spell words of picked 1-cells extends to the formal
inverses** — the inverse of a word is the reversed word of inverses. -/
def invSpelling : Spelling (invPoly P S) (invPoly Q T) where
  cells := invCells S T ψ.cells hψ
  sound α := by
    cases α with
    | keep α =>
        change (invPoly Q T).quot.map ((Paths.lift (invCells S T ψ.cells hψ)).map
              ((fwdPre P S).mapPath (P.src α)))
            = (invPoly Q T).quot.map ((Paths.lift (invCells S T ψ.cells hψ)).map
              ((fwdPre P S).mapPath (P.tgt α)))
        rw [lift_invCells_fwd S T ψ.cells hψ, lift_invCells_fwd S T ψ.cells hψ]
        exact Hom.quot_map_congr (invIncl Q T) (ψ.sound α)
    | cancel e he =>
        change (invPoly Q T).quot.map ((Paths.lift (invCells S T ψ.cells hψ)).map
              ((fwdCell P S e).toPath.comp (bwdCell P S e he).toPath))
            = (invPoly Q T).quot.map ((Paths.lift (invCells S T ψ.cells hψ)).map Quiver.Path.nil)
        rw [Paths.lift_map_comp, Paths.lift_toPath, Paths.lift_toPath]
        exact (((invPoly Q T).quot.map_comp _ _).trans
          (quot_fwd_invWord Q T (ψ.cells.map (cell e)) (hψ e he))).trans
          ((invPoly Q T).quot.map_id _).symm
    | cancel' e he =>
        change (invPoly Q T).quot.map ((Paths.lift (invCells S T ψ.cells hψ)).map
              ((bwdCell P S e he).toPath.comp (fwdCell P S e).toPath))
            = (invPoly Q T).quot.map ((Paths.lift (invCells S T ψ.cells hψ)).map Quiver.Path.nil)
        rw [Paths.lift_map_comp, Paths.lift_toPath, Paths.lift_toPath]
        exact (((invPoly Q T).quot.map_comp _ _).trans
          (quot_invWord_fwd Q T (ψ.cells.map (cell e)) (hψ e he))).trans
          ((invPoly Q T).quot.map_id _).symm

end Spell

end Polygraph

/-! ## The presentation of a localization -/

namespace Presents

open Polygraph

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C] (p : Presents P C)
  (S : ∀ {a b : P.V}, P.Gen a b → Prop)

/-- **A picked arrow is the image of the arrow the cell names upstairs.** -/
theorem arrow_eq_E_map_genArrow {a b : P.V} (e : P.Gen a b) :
    p.arrow (cell e) = p.E.map (genArrow P e) := rfl

variable {W : MorphismProperty C} (hW : W = (p.pickedArrows S).multiplicativeClosure)

/-- The extension, read in `C` through a chosen inverse of the presentation. -/
private noncomputable def locLeg : C ⥤ (invPoly P S).presented :=
  p.equiv.inverse ⋙ (invIncl P S).functor

/-- …and that reading agrees with the extension along the presentation. -/
private noncomputable def locLegIso :
    p.equiv.functor ⋙ p.locLeg S ≅ (invIncl P S).functor :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight p.equiv.unitIso.symm _
    ≪≫ Functor.leftUnitor _

private theorem inverts_locLeg :
    (p.pickedArrows S).multiplicativeClosure.IsInvertedBy (p.locLeg S) := by
  have hiso : (pickedClosure P S).IsInvertedBy (p.equiv.functor ⋙ p.locLeg S) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _ (p.locLegIso S)).mpr
      (inverts_pickedClosure P S)
  have h : (p.pickedArrows S).multiplicativeClosure
      ≤ (MorphismProperty.isomorphisms _).inverseImage (p.locLeg S) :=
    (MorphismProperty.multiplicativeClosure_le_iff _ _).mpr (by
      rintro A B f ⟨e, he⟩
      rw [p.arrow_eq_E_map_genArrow e]
      exact hiso (genArrow P e) (pickedCells_le_pickedClosure P S _ (Picked.mk e he)))
  exact fun _ _ f hf => h f hf

private theorem pickedClosure_le :
    pickedClosure P S
      ≤ (p.pickedArrows S).multiplicativeClosure.isoClosure.inverseImage p.equiv.functor := by
  refine le_trans ((MorphismProperty.multiplicativeClosure_le_iff _ _).mpr ?_)
    (MorphismProperty.monotone_inverseImage _
      (MorphismProperty.le_isoClosure (p.pickedArrows S).multiplicativeClosure))
  rintro X Y f ⟨e, he⟩
  exact MorphismProperty.le_multiplicativeClosure _ _ (Picked.mk e he)

/-- **The extension localizes at the class the picked 1-cells evaluate to.** -/
private theorem isLocalization_locLeg_closure :
    (p.locLeg S).IsLocalization (p.pickedArrows S).multiplicativeClosure :=
  haveI : (invIncl P S).functor.IsLocalization (pickedClosure P S) :=
    isLocalization_invIncl P S
  Functor.IsLocalization.of_equivalence_source (invIncl P S).functor (pickedClosure P S)
    (p.locLeg S) _ p.equiv (p.pickedClosure_le S) (p.inverts_locLeg S) (p.locLegIso S)

/-- **Adjoining a formal inverse to some of the generators presents the localization** at any class
with the same localization as the one those generators generate. -/
noncomputable def presentsLocalizationOfLe
    (hle : (p.pickedArrows S).multiplicativeClosure ≤ W)
    (hinv : W.IsInvertedBy (p.pickedArrows S).multiplicativeClosure.Q) :
    Presents (invPoly P S) W.Localization :=
  haveI := p.isLocalization_locLeg_closure S
  haveI : (p.locLeg S).IsLocalization W := Functor.IsLocalization.of_le hle hinv
  ⟨(Localization.equivalenceFromModel (p.locLeg S) W).inverse, inferInstance⟩

include hW in
/-- **…and at the class those generators generate.** -/
noncomputable def presentsLocalization : Presents (invPoly P S) W.Localization :=
  p.presentsLocalizationOfLe S (le_of_eq hW.symm)
    fun _ _ f hf => MorphismProperty.Q_inverts _ f (le_of_eq hW f hf)

/-! ### …compatibly with `Q`

What the extension presents is read through `Q`: a 1-cell of `P` names, in the localization, the
arrow `P` named, and a formal inverse names its inverse.  Nothing abstract gives this — two
localization functors with the same target differ by an automorphism — so it is proved where the
construction is. -/

include hW in
/-- **The comparison**: the extension, read in the localization, is `P`'s reading then `Q`. -/
noncomputable def locComparison :
    (invIncl P S).functor ⋙ (p.presentsLocalization S hW).E ≅ p.E ⋙ W.Q :=
  haveI : (p.locLeg S).IsLocalization W := by subst hW; exact p.isLocalization_locLeg_closure S
  Functor.isoWhiskerRight (p.locLegIso S).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft p.equiv.functor
      (Localization.compEquivalenceFromModelInverseIso (p.locLeg S) W)

include hW in
/-- **A word of `P`, read in the localization.** -/
theorem eval_fwd_mapPath {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (p.presentsLocalization S hW).eval.map ((fwdPre P S).mapPath u)
      = ((p.locComparison S hW).app ⟨x⟩).hom ≫ W.Q.map (p.eval.map u)
        ≫ ((p.locComparison S hW).app ⟨y⟩).inv :=
  have hnat : ((invIncl P S).functor ⋙ (p.presentsLocalization S hW).E).map (P.quot.map u)
      ≫ ((p.locComparison S hW).app ⟨y⟩).hom
    = ((p.locComparison S hW).app ⟨x⟩).hom ≫ (p.E ⋙ W.Q).map (P.quot.map u) :=
    (p.locComparison S hW).hom.naturality (P.quot.map u)
  ((Iso.eq_comp_inv ((p.locComparison S hW).app ⟨y⟩)).mpr hnat).trans (Category.assoc _ _ _)

/-- **A pair of words inverse in `presented` is inverse wherever the presentation reads it.** -/
theorem eval_comp_eq_id {Q : Polygraph.{w', u'', w₂'}} {D : Type*} [Category D] (q : Presents Q D)
    {x y : GenObj Q.Gen} {u : Quiver.Path x y} {v : Quiver.Path y x}
    (h : Q.quot.map u ≫ Q.quot.map v = 𝟙 (Q.quot.obj x)) :
    q.eval.map u ≫ q.eval.map v = 𝟙 (q.at' x) :=
  (q.E.map_comp _ _).symm.trans ((congrArg q.E.map h).trans (q.E.map_id _))

end Presents

end CategoryTheory
