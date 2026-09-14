import CubeChains.Machinery.Presentation.Basic

/-!
# Machinery/Presentation/Reduce — spelling every 1-cell in a kept family

`T₁` keeps a sub-quiver of `P`'s 1-cells; a substitution rewrites each 1-cell into a word of kept
ones, and a word already spelled out of `T₁` is rewritten to itself.

                    word g          (every letter kept by `T₁`)
          a ═══════════════════════▸ b
          └─────────── g ───────────┘

The inclusion of the kept letters is a covering, hence faithful on words, so a substituted word is
pinned by the word of `P` it reads back as.
-/

universe w u' w₂ v u

namespace CategoryTheory

/-! ## A `T₁`-word, read on the kept 1-cells

The kept 1-cells form a sub-quiver of `P`'s; a word lands in it exactly when every letter is kept,
and that passage is inverse to the inclusion in both directions. -/

section Kept

variable {P : Polygraph.{w, u', w₂}} (T : ∀ {a b : P.V}, P.Gen a b → Prop)

/-- The 1-cells `T` keeps. -/
abbrev keptGen (a b : P.V) : Type w := {g : P.Gen a b // T g}

/-- A kept 1-cell, as a 1-cell of the sub-quiver. -/
def keptCell {a b : P.V} (g : P.Gen a b) (hg : T g) :
    (⟨a⟩ : GenObj (keptGen T)) ⟶ ⟨b⟩ := ⟨g, hg⟩

/-- The sub-quiver, included in `P`'s. -/
def keptPre : GenObj (keptGen T) ⥤q GenObj P.Gen where
  obj x := ⟨x.as⟩
  map e := e.1

/-- **A word every letter of which is kept, read on the kept 1-cells** — each letter spelling
itself, in the word's own order. -/
def keptWord {x y : GenObj P.Gen} (u : Quiver.Path x y)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => T e) u) :
    Quiver.Path (⟨x.as⟩ : GenObj (keptGen T)) ⟨y.as⟩ :=
  Quiver.Path.All.fold (fun z : GenObj P.Gen => (⟨z.as⟩ : GenObj (keptGen T)))
    (fun _ _ e he => (keptCell T e he).toPath) u h

theorem keptWord_cons {x y z : GenObj P.Gen} (u : Quiver.Path x y) (e : y ⟶ z) (he : T e)
    (h₀ : Quiver.Path.All (fun ⦃_ _⦄ e => T e) u)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => T e) (u.cons e)) :
    keptWord T (u.cons e) h = (keptWord T u h₀).cons ⟨e, he⟩ := rfl

/-- Which word it reads matters, which proof does not. -/
theorem keptWord_congr {x y : GenObj P.Gen} {u v : Quiver.Path x y} (h : u = v)
    (hu : Quiver.Path.All (fun ⦃_ _⦄ e => T e) u)
    (hv : Quiver.Path.All (fun ⦃_ _⦄ e => T e) v) : keptWord T u hu = keptWord T v hv := by
  subst h; rfl

theorem keptWord_toPath {a b : P.V} (g : P.Gen a b) (hg : T g)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => T e) (Polygraph.cell g).toPath) :
    keptWord T (Polygraph.cell g).toPath h = (keptCell T g hg).toPath := rfl

/-- **Reading a `T`-word back is the word itself.** -/
theorem keptPre_mapPath_keptWord : ∀ {x y : GenObj P.Gen} (u : Quiver.Path x y)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => T e) u), (keptPre T).mapPath (keptWord T u h) = u := by
  intro x y u
  induction u with
  | nil => intro _; rfl
  | cons u e ih =>
      intro h
      obtain ⟨h₀, he⟩ := (Quiver.Path.all_cons_iff u e).mp h
      rw [keptWord_cons T u e he h₀ h, Prefunctor.mapPath_cons, ih h₀]
      rfl

/-- The sub-quiver is a covering of its image: a kept letter is the letter it reads as. -/
theorem keptPre_star_injective (x : GenObj (keptGen T)) :
    Function.Injective ((keptPre T).star x) := by
  rintro ⟨⟨b₁⟩, g₁⟩ ⟨⟨b₂⟩, g₂⟩ h
  obtain ⟨hb, hg⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : b₁ = b₂ := congrArg GenObj.as hb
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext (eq_of_heq hg)))

/-- **…so the inclusion is faithful on words**: a word of the sub-quiver is pinned by the word of
`P` it reads as. -/
theorem keptPre_mapPath_injective {x y : GenObj (keptGen T)} {w w' : Quiver.Path x y}
    (h : (keptPre T).mapPath w = (keptPre T).mapPath w') : w = w' :=
  haveI := Prefunctor.pathsFunctor_faithful (keptPre T) (keptPre_star_injective T)
  (keptPre T).pathsFunctor.map_injective h

end Kept

/-! ## The substitution -/

section Sub

variable {P : Polygraph.{w, u', w₂}} (T₁ : ∀ {a b : P.V}, P.Gen a b → Prop)

/-- The substitution, on a letter. -/
def subPre (word : ∀ {a b : P.V}, P.Gen a b → Quiver.Path (P.pt a) (P.pt b))
    (word_all : ∀ {a b : P.V} (g : P.Gen a b), Quiver.Path.All (fun ⦃_ _⦄ e => T₁ e) (word g)) :
    GenObj P.Gen ⥤q Paths (GenObj (keptGen T₁)) where
  obj x := ⟨x.as⟩
  map g := keptWord T₁ (word g) (word_all g)

/-- **A word of kept letters substitutes to itself**, read on the kept 1-cells. -/
theorem subWords_of_all
    {word : ∀ {a b : P.V}, P.Gen a b → Quiver.Path (P.pt a) (P.pt b)}
    {word_all : ∀ {a b : P.V} (g : P.Gen a b), Quiver.Path.All (fun ⦃_ _⦄ e => T₁ e) (word g)}
    (word_self : ∀ {a b : P.V} (g : P.Gen a b), T₁ g → word g = (Polygraph.cell g).toPath) :
    ∀ {x y : GenObj P.Gen} (u : Quiver.Path x y)
      (h : Quiver.Path.All (fun ⦃_ _⦄ e => T₁ e) u),
      (Paths.lift (subPre T₁ word word_all)).map u = keptWord T₁ u h := by
  intro x y u
  induction u with
  | nil => intro _; rfl
  | cons u e ih =>
      intro h
      obtain ⟨h₀, he⟩ := (Quiver.Path.all_cons_iff u e).mp h
      rw [keptWord_cons T₁ u e he h₀ h, Paths.lift_cons, ih h₀]
      exact congrArg (fun t => Quiver.Path.comp (keptWord T₁ u h₀) t)
        ((keptWord_congr T₁ (word_self e he) _ (Quiver.Path.all_toPath.mpr he)).trans
          (keptWord_toPath T₁ e he _))

/-- **A kept letter substituted is that letter.** -/
theorem subPre_map_kept
    (word : ∀ {a b : P.V}, P.Gen a b → Quiver.Path (P.pt a) (P.pt b))
    (word_all : ∀ {a b : P.V} (g : P.Gen a b), Quiver.Path.All (fun ⦃_ _⦄ e => T₁ e) (word g))
    (word_self : ∀ {a b : P.V} (g : P.Gen a b), T₁ g → word g = (Polygraph.cell g).toPath)
    {x y : GenObj (keptGen T₁)} (e : x ⟶ y) :
    (subPre T₁ word word_all).map ((keptPre T₁).map e) = e.toPath :=
  (keptWord_congr T₁ (word_self e.1 e.2) _ (Quiver.Path.all_toPath.mpr e.2)).trans
    (keptWord_toPath T₁ e.1 e.2 _)

end Sub

end CategoryTheory
