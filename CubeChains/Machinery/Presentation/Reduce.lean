import CubeChains.Machinery.Presentation.Comparison

/-!
# Machinery/Presentation/Reduce — the cells that suffice, in both dimensions

A `Spans` says a sub-polygraph carries all of `P`, one pair of fields per dimension: each 1-cell is
a word in the kept 1-cells (`word`), and each 2-cell holds modulo the kept 2-cells once its letters
are substituted (`cell_derivable`).  `P.sub` drops the rest, `equivalence` says nothing is lost.

                    word g          (every letter kept by `T₁`)
          a ═══════════════════════▸ b
          └─────────── g ───────────┘          (equal in `P.presented`)

`sub` takes the substitution as an argument rather than deriving it: the kept 2-cells' boundaries
are words of `P`, so they only become words of the sub-polygraph once the letters are substituted.
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

@[simp] theorem keptPre_map {x y : GenObj (keptGen T)} (e : x ⟶ y) : (keptPre T).map e = e.1 := rfl

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

/-! ## The sub-polygraph -/

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

/-- **The sub-polygraph**: the kept 0-cells, the 1-cells `T₁` keeps, and the 2-cells `T₂` keeps with
every letter substituted. -/
def Polygraph.sub (T₂ : ∀ {x y : GenObj P.Gen}, P.Rel x y → Prop)
    (word : ∀ {a b : P.V}, P.Gen a b → Quiver.Path (P.pt a) (P.pt b))
    (word_all : ∀ {a b : P.V} (g : P.Gen a b), Quiver.Path.All (fun ⦃_ _⦄ e => T₁ e) (word g)) :
    Polygraph.{w, u', w₂} where
  V := P.V
  Gen := keptGen T₁
  Rel x y := {α : P.Rel ⟨x.as⟩ ⟨y.as⟩ // T₂ α}
  src α := (Paths.lift (subPre T₁ word word_all)).map (P.src α.1)
  tgt α := (Paths.lift (subPre T₁ word word_all)).map (P.tgt α.1)

end Sub

/-- **Data spanning `P` by a sub-polygraph**, one pair of fields per dimension: a `T₁`-word for
every 1-cell, and derivability from the `T₂`-cells for every 2-cell. -/
structure Spans (P : Polygraph.{w, u', w₂}) (T₁ : ∀ {a b : P.V}, P.Gen a b → Prop)
    (T₂ : ∀ {x y : GenObj P.Gen}, P.Rel x y → Prop) where
  /-- a `T₁`-word spelling each 1-cell -/
  word : ∀ {a b : P.V} (_g : P.Gen a b), Quiver.Path (P.pt a) (P.pt b)
  /-- …spelled out of `T₁` -/
  word_all : ∀ {a b : P.V} (g : P.Gen a b), Quiver.Path.All (fun ⦃_ _⦄ e => T₁ e) (word g)
  /-- …equal to it -/
  word_eq : ∀ {a b : P.V} (g : P.Gen a b),
    P.quot.map (word g) = P.quot.map (Polygraph.cell g).toPath
  /-- a kept 1-cell spells itself -/
  word_self : ∀ {a b : P.V} (g : P.Gen a b), T₁ g → word g = (Polygraph.cell g).toPath
  /-- every 2-cell, substituted, holds modulo the kept ones -/
  cell_derivable : ∀ {x y : GenObj P.Gen} (α : P.Rel x y),
    (Polygraph.sub T₁ T₂ word word_all).quot.map
        ((Paths.lift (subPre T₁ word word_all)).map (P.src α))
      = (Polygraph.sub T₁ T₂ word word_all).quot.map
        ((Paths.lift (subPre T₁ word word_all)).map (P.tgt α))

namespace Spans

variable {P : Polygraph.{w, u', w₂}} {T₁ : ∀ {a b : P.V}, P.Gen a b → Prop}
  {T₂ : ∀ {x y : GenObj P.Gen}, P.Rel x y → Prop} (s : Spans P T₁ T₂)

/-- The substitution, on a letter. -/
abbrev pre : GenObj P.Gen ⥤q Paths (GenObj (keptGen T₁)) := subPre T₁ s.word s.word_all

/-- …and on whole words. -/
abbrev subWords : P.Word ⥤ Paths (GenObj (keptGen T₁)) := Paths.lift s.pre

/-- **The sub-polygraph `s` spans.** -/
def poly : Polygraph.{w, u', w₂} := Polygraph.sub T₁ T₂ s.word s.word_all

/-- The substitution, as a spelling — its soundness is `cell_derivable`. -/
def sub : Polygraph.Spelling P s.poly where
  cells := s.pre
  sound α := s.cell_derivable α

/-- **A letter substituted and read back is that letter.** -/
theorem quot_keptPre_subWords : ∀ {x y : GenObj P.Gen} (u : Quiver.Path x y),
    P.quot.map ((keptPre T₁).mapPath (s.subWords.map u)) = P.quot.map u := by
  intro x y u
  induction u with
  | nil => rw [Paths.lift_nil]; rfl
  | cons u e ih =>
      refine Eq.trans (congrArg P.quot.map
        ((congrArg (keptPre T₁).mapPath (Paths.lift_cons s.pre u e)).trans
          (Prefunctor.mapPath_comp (keptPre T₁) _ _))) ?_
      refine ((P.quot_map_comp _ _).trans (congrArg (fun t => t ≫ _) ih)).trans ?_
      refine Eq.trans (congrArg (fun t => P.quot.map u ≫ t) ?_) (P.quot_map_cons u e).symm
      exact (congrArg P.quot.map (keptPre_mapPath_keptWord T₁ (s.word e) (s.word_all e))).trans
        (s.word_eq e)

/-- The inclusion, as a spelling: a kept 1-cell spells itself. -/
def incl : Polygraph.Spelling s.poly P where
  cells := keptPre T₁ ⋙q Paths.of (GenObj P.Gen)
  sound {x y} α := by
    rw [Paths.lift_comp_of_map, Paths.lift_comp_of_map]
    exact (s.quot_keptPre_subWords (P.src α.1)).trans
      ((P.quot_src_tgt α.1).trans (s.quot_keptPre_subWords (P.tgt α.1)).symm)

/-- **A kept letter substituted is that letter.** -/
theorem pre_map_kept {x y : GenObj s.poly.Gen} (e : x ⟶ y) :
    s.pre.map ((keptPre T₁).map e) = e.toPath :=
  (keptWord_congr T₁ (s.word_self e.1 e.2) _ (Quiver.Path.all_toPath.mpr e.2)).trans
    (keptWord_toPath T₁ e.1 e.2 _)

/-- …and so is a kept word. -/
theorem subWords_keptPre_mapPath : ∀ {x y : GenObj s.poly.Gen} (w : Quiver.Path x y),
    s.subWords.map ((keptPre T₁).mapPath w) = w := by
  intro x y w
  induction w with
  | nil => rfl
  | cons w e ih =>
      exact ((Paths.lift_cons s.pre _ _).trans
        (congrArg (fun t => Quiver.Path.comp t (s.pre.map ((keptPre T₁).map e))) ih)).trans
        (congrArg (fun t => Quiver.Path.comp w t) (s.pre_map_kept e))

/-! ## The two spellings are mutually inverse

Both composites are the identity already on *words*, so the unit and the counit have identity
components and `naturality` is all that is left. -/

theorem sub_functor_quot {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    s.sub.functor.map (P.quot.map u) = s.poly.quot.map (s.subWords.map u) := rfl

theorem incl_functor_quot {x y : GenObj s.poly.Gen} (w : Quiver.Path x y) :
    s.incl.functor.map (s.poly.quot.map w) = P.quot.map ((keptPre T₁).mapPath w) :=
  congrArg P.quot.map (Paths.lift_comp_of_map (keptPre T₁) w)

theorem map_sub_incl {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (s.sub.functor ⋙ s.incl.functor).map (P.quot.map u) = P.quot.map u :=
  ((congrArg s.incl.functor.map (s.sub_functor_quot u)).trans
    (s.incl_functor_quot _)).trans (s.quot_keptPre_subWords u)

theorem map_incl_sub {x y : GenObj s.poly.Gen} (w : Quiver.Path x y) :
    (s.incl.functor ⋙ s.sub.functor).map (s.poly.quot.map w) = s.poly.quot.map w :=
  ((congrArg s.sub.functor.map (s.incl_functor_quot w)).trans
    (s.sub_functor_quot _)).trans (congrArg s.poly.quot.map (s.subWords_keptPre_mapPath w))

/-- Substituting, then including, is the identity — an *equality*, the 0-cells never moving. -/
theorem sub_comp_incl : s.sub.functor ⋙ s.incl.functor = 𝟭 P.presented :=
  Polygraph.presented_ext_of_gen (fun _ => rfl) fun e => heq_of_eq (s.map_sub_incl e.toPath)

/-- …and including, then substituting, is too. -/
theorem incl_comp_sub : s.incl.functor ⋙ s.sub.functor = 𝟭 s.poly.presented :=
  Polygraph.presented_ext_of_gen (fun _ => rfl) fun e => heq_of_eq (s.map_incl_sub e.toPath)

/-- **Keeping only the cells that suffice loses nothing, in either dimension.** -/
def equivalence : P.presented ≌ s.poly.presented :=
  Equivalence.mk s.sub.functor s.incl.functor (eqToIso s.sub_comp_incl.symm)
    (eqToIso s.incl_comp_sub)

end Spans

/-- **The sub-polygraph presents**: a 1-cell its fellows already spell, and a 2-cell the kept ones
already imply, can both be dropped. -/
noncomputable def Presents.restrictCells {P : Polygraph.{w, u', w₂}}
    {T₁ : ∀ {a b : P.V}, P.Gen a b → Prop} {T₂ : ∀ {x y : GenObj P.Gen}, P.Rel x y → Prop}
    {C : Type u} [Category.{v} C] (p : Presents P C) (s : Spans P T₁ T₂) : Presents s.poly C :=
  ⟨s.equivalence.inverse ⋙ p.E, inferInstance⟩

end CategoryTheory
