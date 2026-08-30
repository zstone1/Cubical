import CubeChains.Foundations.MonoidPresentation
import CubeChains.Foundations.SigmaPresentation

/-!
# Foundations/WordQuiver — an indexed family of monoid presentations, as one quiver

One vertex per index, one loop per letter, no morphisms between indices: a loop **is** a word
(`wordOf`/`wordPath`), and the imposed relation **is** the family's relation on those words
(`wordPathRel_iff`).  Transporting it to a category of elements keeps both readings — the
generators are a letter acting on a fibre element, and the relation is still the family's
(`totalRel_word_iff`).
-/

universe w v u

open CategoryTheory Quiver

namespace CategoryTheory.Sigma

variable {I : Type u} {α : I → Type v}

/-- One vertex per index, a loop for each letter. -/
abbrev WordQuiver (α : I → Type v) : Type u := Quiv fun i => SingleObj (α i)

/-- The vertex at index `i`, as an object of the path category. -/
def wordVtx (i : I) : Paths (WordQuiver α) := ⟨i, SingleObj.star (α i)⟩

/-- The `a`-th edge at index `i`. -/
def wordEdge (i : I) (a : α i) : @Quiver.Hom (WordQuiver α) _ (wordVtx i) (wordVtx i) :=
  Quiv.Hom.mk a

/-! ## A loop is a word -/

/-- The word a summand path spells. -/
def summandWord : ∀ {X Y : Σ i, Paths (SingleObj (α i))}, (X ⟶ Y) → FreeMonoid (α X.1)
  | _, _, SigmaHom.mk p => SingleObj.pathWord p

/-- The word a loop at index `i` spells. -/
def wordOf {i : I} (P : wordVtx (α := α) i ⟶ wordVtx i) : FreeMonoid (α i) :=
  summandWord (toSigmaPaths.map P)

/-- …and the loop spelling a word. -/
def wordPath {i : I} (w : FreeMonoid (α i)) : wordVtx (α := α) i ⟶ wordVtx i :=
  descPaths.map (SigmaHom.mk (SingleObj.pathOfWord w))

theorem wordPath_of {i : I} (a : α i) :
    wordPath (FreeMonoid.of a) = Quiver.Hom.toPath (wordEdge i a) := rfl

theorem wordPath_mul {i : I} (w₁ w₂ : FreeMonoid (α i)) :
    wordPath (α := α) (w₁ * w₂) = wordPath w₁ ≫ wordPath w₂ := by
  refine Eq.trans (congrArg descPaths.map (congrArg SigmaHom.mk
    (SingleObj.pathOfWord_mul w₁ w₂))) ?_
  exact descPaths.map_comp
    (SigmaHom.mk (C := fun j => Paths (SingleObj (α j))) (i := i) (SingleObj.pathOfWord w₁))
    (SigmaHom.mk (C := fun j => Paths (SingleObj (α j))) (i := i) (SingleObj.pathOfWord w₂))

@[simp] theorem wordOf_wordPath {i : I} (w : FreeMonoid (α i)) : wordOf (wordPath w) = w :=
  (congrArg summandWord (toSigmaPaths_map_descPaths_map _)).trans
    (SingleObj.pathWord_pathOfWord w)

private theorem mk_pathOfWord_summandWord {i : I}
    (f : toSigmaPaths.obj (wordVtx (α := α) i) ⟶ toSigmaPaths.obj (wordVtx (α := α) i)) :
    SigmaHom.mk (SingleObj.pathOfWord (summandWord f)) = f := by
  cases f with
  | mk p => exact congrArg SigmaHom.mk (SingleObj.pathOfWord_pathWord p)

@[simp] theorem wordPath_wordOf {i : I} (P : wordVtx (α := α) i ⟶ wordVtx i) :
    wordPath (wordOf P) = P := by
  refine Eq.trans ?_ (descPaths_map_toSigmaPaths_map P)
  exact congrArg (fun f : toSigmaPaths.obj (wordVtx (α := α) i) ⟶
    toSigmaPaths.obj (wordVtx (α := α) i) => descPaths.map f) (mk_pathOfWord_summandWord _)

/-! ## …and the relation is the family's -/

/-- The family's relations, read on paths. -/
def wordPathRel (rel : ∀ i, FreeMonoid (α i) → FreeMonoid (α i) → Prop) :
    HomRel (Paths (WordQuiver α)) :=
  pathRel fun i => SingleObj.pathRel (rel i)

/-- **The relation is the family's, letter for letter.** -/
theorem wordPathRel_iff (rel : ∀ i, FreeMonoid (α i) → FreeMonoid (α i) → Prop) {i : I}
    (P Q : wordVtx (α := α) i ⟶ wordVtx i) :
    wordPathRel rel P Q ↔ rel i (wordOf P) (wordOf Q) := by
  change homRel (fun i => SingleObj.pathRel (rel i)) (toSigmaPaths.map P) (toSigmaPaths.map Q)
    ↔ rel i (summandWord (toSigmaPaths.map P)) (summandWord (toSigmaPaths.map Q))
  generalize toSigmaPaths.map P = f
  generalize toSigmaPaths.map Q = g
  cases f with
  | mk p => cases g with
    | mk q => exact Iff.rfl

/-! ## The transported presentation

`elementsPresentation` builds its quiver from the base's *edges* acting on the fibre; here that is
a letter acting on a fibre element, and its relation is still the family's, on the spelled words. -/

section Total

variable {rel : ∀ i, FreeMonoid (α i) → FreeMonoid (α i) → Prop}
  {Pd : Quotient (wordPathRel rel) ⥤ Type w}

/-- The fibre at index `i`. -/
abbrev wordFibre (Pd : Quotient (wordPathRel rel) ⥤ Type w) (i : I) : Type w :=
  (basePsh (wordPathRel rel) Pd).obj (wordVtx i)

/-- **A word's action on the fibre** — at a single letter, the arrow the transported presentation
adds. -/
def wordAct (Pd : Quotient (wordPathRel rel) ⥤ Type w) {i : I} (w : FreeMonoid (α i))
    (c : wordFibre Pd i) : wordFibre Pd i :=
  (basePsh (wordPathRel rel) Pd).map (wordPath w) c

theorem wordAct_mul {i : I} (w₁ w₂ : FreeMonoid (α i)) (c : wordFibre Pd i) :
    wordAct Pd (w₁ * w₂) c = wordAct Pd w₂ (wordAct Pd w₁ c) := by
  rw [wordAct, wordPath_mul, Functor.map_comp_apply]
  rfl

/-- **A relation of the family acts trivially** — the fibre presheaf factors through the
quotient. -/
theorem wordAct_congr {i : I} {w₁ w₂ : FreeMonoid (α i)} (h : rel i w₁ w₂)
    (c : wordFibre Pd i) : wordAct Pd w₁ c = wordAct Pd w₂ c :=
  basePsh_respects _ Pd ((wordPathRel_iff rel _ _).mpr (by rwa [wordOf_wordPath,
    wordOf_wordPath])) c

/-- A fibre element at index `i`, as a vertex of the total quiver. -/
def wordTotalVtx {i : I} (c : wordFibre Pd i) : Total (basePsh (wordPathRel rel) Pd) :=
  ⟨wordVtx i, c⟩

/-- …and as an object of its path category. -/
def wordTotalObj {i : I} (c : wordFibre Pd i) : Paths (Total (basePsh (wordPathRel rel) Pd)) :=
  wordTotalVtx c

/-- **A generator of the total quiver is a letter acting on a fibre element.** -/
def totalEdgeEquiv {i : I} (c c' : wordFibre Pd i) :
    (wordTotalVtx c ⟶ wordTotalVtx c') ≃ {a : α i // wordAct Pd (FreeMonoid.of a) c = c'} where
  toFun e := ⟨match e with | ⟨Quiv.Hom.mk a, _⟩ => a,
    match e with | ⟨Quiv.Hom.mk _, h⟩ => h⟩
  invFun a := ⟨wordEdge i a.1, a.2⟩
  left_inv e := by obtain ⟨⟨a⟩, h⟩ := e; rfl
  right_inv _ := rfl

/-- **The transported relation is still the family's, letter for letter.** -/
theorem totalRel_word_iff {i : I} {c c' : wordFibre Pd i}
    (P₁ P₂ : wordTotalObj c ⟶ wordTotalObj c') :
    totalRel (wordPathRel rel) Pd P₁ P₂ ↔
      rel i (wordOf ((totalProj _).mapPath P₁)) (wordOf ((totalProj _).mapPath P₂)) :=
  (totalRel_iff (wordPathRel rel) Pd P₁ P₂).trans (wordPathRel_iff rel _ _)

/-! ### The path a word spells

`totalToElements` is fully faithful, so a word and a landing place name a unique generator path.
`totalRel_totalPath` says the family's relation holds between the paths spelling its two words, and
`totalRel_word_iff` says nothing else is imposed. -/

/-- The generator path spelling `w` out of `c`, landing at `c'`. -/
noncomputable def totalPath {i : I} (w : FreeMonoid (α i)) {c c' : wordFibre Pd i}
    (h : wordAct Pd w c = c') : wordTotalObj c ⟶ wordTotalObj c' :=
  (totalToElements _).preimage ⟨wordPath w, h⟩

@[simp] theorem mapPath_totalPath {i : I} (w : FreeMonoid (α i)) {c c' : wordFibre Pd i}
    (h : wordAct Pd w c = c') : (totalProj _).mapPath (totalPath w h) = wordPath w :=
  congrArg Subtype.val ((totalToElements (basePsh (wordPathRel rel) Pd)).map_preimage _)

/-- **The family's relation, between the two paths spelling its two words.** -/
theorem totalRel_totalPath {i : I} {w₁ w₂ : FreeMonoid (α i)} {c c' : wordFibre Pd i}
    (hrel : rel i w₁ w₂) (h₁ : wordAct Pd w₁ c = c') (h₂ : wordAct Pd w₂ c = c') :
    totalRel (wordPathRel rel) Pd (totalPath w₁ h₁) (totalPath w₂ h₂) := by
  rw [totalRel_word_iff, mapPath_totalPath, mapPath_totalPath, wordOf_wordPath, wordOf_wordPath]
  exact hrel

/-- **A generator path names the cartesian lift of the base path spelling its word** — so the
generator's invariants are the base's. -/
theorem val_elementsPresentation_totalPath {i : I} (w : FreeMonoid (α i))
    {c c' : wordFibre Pd i} (h : wordAct Pd w c = c') :
    ((elementsPresentation (wordPathRel rel) Pd).functor.map
        ((Quotient.functor (totalRel (wordPathRel rel) Pd)).map (totalPath w h))).val
      = (Quotient.functor (wordPathRel rel)).map (wordPath w) :=
  (val_elementsPresentation_map _ _ _).trans (congrArg _ (mapPath_totalPath w h))

/-- …so they are one arrow of the presented category. -/
theorem quotient_map_totalPath {i : I} {w₁ w₂ : FreeMonoid (α i)} {c c' : wordFibre Pd i}
    (hrel : rel i w₁ w₂) (h₁ : wordAct Pd w₁ c = c') (h₂ : wordAct Pd w₂ c = c') :
    (Quotient.functor (totalRel (wordPathRel rel) Pd)).map (totalPath w₁ h₁)
      = (Quotient.functor (totalRel (wordPathRel rel) Pd)).map (totalPath w₂ h₂) :=
  Quotient.sound _ (totalRel_totalPath hrel h₁ h₂)

end Total

end CategoryTheory.Sigma
