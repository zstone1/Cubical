import CubeChains.Machinery.Presentation.Basic

/-!
# Machinery/Presentation/Contract — contracting a family of invertible generators

A `Contraction` names one 0-cell per class together with an invertible `S`-word onto it; `poly`
keeps those 0-cells and conjugates each non-`S` generator onto them, and `equivalence` says the
conjugation loses nothing.  `Restrict` cannot do this: convexity forces closure under isomorphism.

               invWord a         g          word b
    rep a ────────────────▸ a ────────▸ b ────────────▸ rep b
      └─────────────────────── κ g ───────────────────────┘

An `S`-letter makes `κ g` the empty word; that square is `word_comp_of_S`.
-/

universe w u' w₂ v u

namespace CategoryTheory

/-- **Data contracting `P` along a family of invertible `S`-words**: one 0-cell per class, with an
`S`-word onto it which is invertible in `P.presented`. -/
structure Contraction (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop) where
  /-- the representative of a 0-cell -/
  rep : P.V → P.V
  /-- …which is its own representative -/
  rep_idem : ∀ x, rep (rep x) = rep x
  /-- a word from a 0-cell to its representative -/
  word : ∀ x : P.V, Quiver.Path (P.pt x) (P.pt (rep x))
  /-- …spelled out of `S` -/
  word_all : ∀ x, Quiver.Path.All (fun ⦃_ _⦄ e => S e) (word x)
  /-- …and a word back -/
  invWord : ∀ x : P.V, Quiver.Path (P.pt (rep x)) (P.pt x)
  /-- …also spelled out of `S` -/
  invWord_all : ∀ x, Quiver.Path.All (fun ⦃_ _⦄ e => S e) (invWord x)
  /-- the two cancel in `P.presented`… -/
  word_invWord : ∀ x, P.quot.map ((word x).comp (invWord x)) = 𝟙 _
  /-- …on both sides -/
  invWord_word : ∀ x, P.quot.map ((invWord x).comp (word x)) = 𝟙 _
  /-- an `S`-letter does not change the representative… -/
  rep_eq_of_S : ∀ {a b : P.V} {g : P.Gen a b}, S g → rep a = rep b
  /-- …and merging to the representative factors through it -/
  word_comp_of_S : ∀ {a b : P.V} (g : P.Gen a b) (h : S g),
    P.quot.map (cellCongr Quiver.Path rfl (congrArg P.pt (rep_eq_of_S h)) (word a))
      = P.quot.map ((Polygraph.cell g).toPath.comp (word b))

namespace Contraction

variable {P : Polygraph.{w, u', w₂}} {S : ∀ {a b : P.V}, P.Gen a b → Prop} (c : Contraction P S)

/-! ## The contracted polygraph -/

/-- The 0-cells: those of `P` that are their own representative. -/
abbrev V : Type u' := {x : P.V // c.rep x = x}

/-- **A 1-cell**: a non-`S` generator of `P`, carrying the representatives of its endpoints. -/
structure Gen (x y : c.V) where
  /-- where the generator starts -/
  dom : P.V
  /-- …and where it ends -/
  cod : P.V
  /-- the generator -/
  gen : P.Gen dom cod
  /-- …not one of the contracted ones -/
  not_mem : ¬ S gen
  /-- its source represents `x`… -/
  rep_dom : c.rep dom = x.1
  /-- …and its target represents `y` -/
  rep_cod : c.rep cod = y.1

/-- The 0-cell a 0-cell of `P` represents. -/
def repObj (u : GenObj P.Gen) : GenObj c.Gen := ⟨⟨c.rep u.as, c.rep_idem u.as⟩⟩

theorem repObj_self (X : GenObj c.Gen) : c.repObj (P.pt X.as.1) = X :=
  GenObj.ext (Subtype.ext X.as.2)

theorem repObj_eq_of_S {u v : GenObj P.Gen} (g : u ⟶ v) (h : S g) : c.repObj u = c.repObj v :=
  GenObj.ext (Subtype.ext (c.rep_eq_of_S h))

/-- The 1-cell a non-`S` generator becomes. -/
def genCell {u v : GenObj P.Gen} (g : u ⟶ v) (hg : ¬ S g) : c.repObj u ⟶ c.repObj v :=
  ⟨u.as, v.as, g, hg, rfl, rfl⟩

/-- **The conjugation, on a letter**: an `S`-letter becomes the empty word, any other itself. -/
noncomputable def cell {u v : GenObj P.Gen} (g : u ⟶ v) :
    Quiver.Path (c.repObj u) (c.repObj v) :=
  @dite _ (S g) (Classical.propDecidable _)
    (fun hg => cellCongr Quiver.Path rfl (c.repObj_eq_of_S g hg) Quiver.Path.nil)
    (fun hg => (c.genCell g hg).toPath)

theorem cell_of_S {u v : GenObj P.Gen} (g : u ⟶ v) (hg : S g) :
    c.cell g = cellCongr Quiver.Path rfl (c.repObj_eq_of_S g hg) Quiver.Path.nil :=
  dif_pos hg

theorem cell_of_not_S {u v : GenObj P.Gen} (g : u ⟶ v) (hg : ¬ S g) :
    c.cell g = (c.genCell g hg).toPath :=
  dif_neg hg

/-- The conjugation, as a spelling of `P`'s letters by words of the contraction. -/
noncomputable def pre : GenObj P.Gen ⥤q Paths (GenObj c.Gen) where
  obj := c.repObj
  map g := c.cell g

/-- …and on whole words. -/
noncomputable abbrev words : P.Word ⥤ Paths (GenObj c.Gen) := Paths.lift c.pre

/-- **A 2-cell**: a 2-cell of `P`, carrying the representatives of its endpoints. -/
structure Cell (X Y : GenObj c.Gen) where
  /-- where the 2-cell sits, upstairs -/
  dom : GenObj P.Gen
  /-- …and where it ends -/
  cod : GenObj P.Gen
  /-- the 2-cell -/
  cell : P.Rel dom cod
  /-- its source represents `X`… -/
  rep_dom : c.repObj dom = X
  /-- …and its target represents `Y` -/
  rep_cod : c.repObj cod = Y

/-- **The contracted polygraph** — the representatives, the conjugated non-`S` generators, and the
conjugated 2-cells. -/
noncomputable def poly : Polygraph where
  V := c.V
  Gen := c.Gen
  Rel := c.Cell
  src α := cellCongr Quiver.Path α.rep_dom α.rep_cod (c.words.map (P.src α.cell))
  tgt α := cellCongr Quiver.Path α.rep_dom α.rep_cod (c.words.map (P.tgt α.cell))

/-- **A 2-cell of `P` is a 2-cell of the contraction** — that is what its 2-cells are. -/
theorem quot_words_src_tgt {u v : GenObj P.Gen} (α : P.Rel u v) :
    c.poly.quot.map (c.words.map (P.src α)) = c.poly.quot.map (c.words.map (P.tgt α)) :=
  c.poly.quot_src_tgt (⟨u, v, α, rfl, rfl⟩ : c.Cell (c.repObj u) (c.repObj v))

/-- **The conjugation is a spelling** — its soundness is the shape of the 2-cells. -/
noncomputable def spelling : Polygraph.Spelling P c.poly where
  cells := c.pre
  sound α := c.quot_words_src_tgt α

/-! ## An `S`-word conjugates to nothing -/

theorem rep_eq_of_all_S : ∀ {u v : GenObj P.Gen} (w : Quiver.Path u v),
    Quiver.Path.All (fun ⦃_ _⦄ e => S e) w → c.rep u.as = c.rep v.as := by
  intro u v w
  induction w with
  | nil => exact fun _ => rfl
  | cons w e ih =>
      intro h
      rw [Quiver.Path.all_cons_iff] at h
      exact (ih h.1).trans (c.rep_eq_of_S h.2)

theorem repObj_eq_of_all_S {u v : GenObj P.Gen} (w : Quiver.Path u v)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) w) : c.repObj u = c.repObj v :=
  GenObj.ext (Subtype.ext (c.rep_eq_of_all_S w h))

/-! ### Reading a conjugated word

`poly`'s 1-cells are indexed over `P`'s, so its `≫` and its `𝟙` are spelled at `c.Gen` while a
functor out of `poly.Word` carries `poly.Gen`; these say the two spellings agree, once and for all
readings of the contraction. -/

section Read

variable {D : Type*} [Category* D] (G : Paths (GenObj c.Gen) ⥤ D)

theorem map_words_nil (u : GenObj P.Gen) :
    G.map (c.words.map (Quiver.Path.nil : Quiver.Path u u)) = 𝟙 (G.obj (c.repObj u)) :=
  (congrArg (fun t => G.map t) (Paths.lift_nil c.pre u)).trans (G.map_id _)

theorem map_words_cons {u v z : GenObj P.Gen} (w : Quiver.Path u v) (e : v ⟶ z) :
    G.map (c.words.map (w.cons e)) = G.map (c.words.map w) ≫ G.map (c.cell e) :=
  (congrArg (fun t => G.map t) (Paths.lift_cons c.pre w e)).trans (G.map_comp _ _)

theorem map_words_comp {u v z : GenObj P.Gen} (w : Quiver.Path u v) (w' : Quiver.Path v z) :
    G.map (c.words.map (w.comp w')) = G.map (c.words.map w) ≫ G.map (c.words.map w') :=
  (congrArg (fun t => G.map t) (Paths.lift_map_comp c.pre w w')).trans (G.map_comp _ _)

/-- **An `S`-letter conjugates to an identity.** -/
theorem map_cell_of_S {u v : GenObj P.Gen} (g : u ⟶ v) (hg : S g)
    (h : c.repObj u = c.repObj v) : G.map (c.cell g) = eqToHom (congrArg G.obj h) :=
  (congrArg (fun t => G.map t) (c.cell_of_S g hg)).trans
    ((Paths.map_cellCongr G h Quiver.Path.nil).trans
      ((congrArg (· ≫ eqToHom (congrArg G.obj h)) (G.map_id _)).trans (Category.id_comp _)))

/-- …so one more `S`-letter is no letter at all. -/
theorem map_words_cons_of_S {u v z : GenObj P.Gen} (w : Quiver.Path u v) (e : v ⟶ z) (he : S e)
    (h : c.repObj v = c.repObj z) :
    G.map (c.words.map (w.cons e)) = G.map (c.words.map w) ≫ eqToHom (congrArg G.obj h) :=
  (c.map_words_cons G w e).trans
    (congrArg (fun t : G.obj (c.repObj v) ⟶ G.obj (c.repObj z) => G.map (c.words.map w) ≫ t)
      (c.map_cell_of_S G e he h))

/-- **…and so does an `S`-word.** -/
theorem map_words_of_all_S : ∀ {u v : GenObj P.Gen} (w : Quiver.Path u v),
    Quiver.Path.All (fun ⦃_ _⦄ e => S e) w → ∀ h : c.repObj u = c.repObj v,
      G.map (c.words.map w) = eqToHom (congrArg G.obj h) := by
  intro u v w
  induction w with
  | nil => intro _ h; exact (c.map_words_nil G u).trans (eqToHom_refl _ _).symm
  | cons w e ih =>
      intro hw h
      rw [Quiver.Path.all_cons_iff] at hw
      refine (c.map_words_cons_of_S G w e hw.2 (c.repObj_eq_of_S e hw.2)).trans ?_
      refine Eq.trans (congrArg (fun t => t ≫ eqToHom (congrArg G.obj (c.repObj_eq_of_S e hw.2)))
        (ih hw.1 (c.repObj_eq_of_all_S w hw.1))) ?_
      exact eqToHom_trans _ _

end Read

/-! ## Reading a 1-cell of the contraction back in `P` -/

/-- The conjugate of a letter: merge down, cross, merge back up. -/
noncomputable def backWord {u v : GenObj P.Gen} (g : u ⟶ v) :
    Quiver.Path (P.pt (c.rep u.as)) (P.pt (c.rep v.as)) :=
  (c.invWord u.as).comp (g.toPath.comp (c.word v.as))

/-- …read at the representatives the 1-cell actually runs between. -/
noncomputable def backPre : GenObj c.Gen ⥤q P.Word where
  obj X := P.pt X.as.1
  map e := cellCongr Quiver.Path (congrArg P.pt e.rep_dom) (congrArg P.pt e.rep_cod)
    (c.backWord (Polygraph.cell e.gen))

/-- Reading a word of the contraction back in `P.presented`. -/
noncomputable abbrev backQuot : Paths (GenObj c.Gen) ⥤ P.presented :=
  Paths.lift c.backPre ⋙ P.quot

/-- **Merging to the representative, as a factorization in `P.presented`** — `word_comp_of_S` with
its transport read as an `eqToHom`. -/
theorem quot_word_comp_of_S {u v : GenObj P.Gen} (g : u ⟶ v) (h : S g) :
    P.quot.map (c.word u.as)
        ≫ eqToHom (congrArg (fun z : P.V => (⟨P.pt z⟩ : P.presented)) (c.rep_eq_of_S h))
      = P.quot.map g.toPath ≫ P.quot.map (c.word v.as) :=
  ((P.quot_map_cellCongr _ _).symm.trans (c.word_comp_of_S g h)).trans (P.quot_map_comp _ _)

/-- **A non-`S` letter reads back as its own conjugate.** -/
theorem backQuot_cell_of_not_S {u v : GenObj P.Gen} (g : u ⟶ v) (hg : ¬ S g) :
    c.backQuot.map (c.cell g)
      = P.quot.map (c.invWord u.as) ≫ P.quot.map g.toPath ≫ P.quot.map (c.word v.as) := by
  refine Eq.trans (congrArg (fun t => c.backQuot.map t) (c.cell_of_not_S g hg)) ?_
  refine Eq.trans (show c.backQuot.map (c.genCell g hg).toPath = P.quot.map (c.backWord g) from
    congrArg P.quot.map (Paths.lift_toPath c.backPre _)) ?_
  rw [backWord, P.quot_map_comp, P.quot_map_comp]

/-- …so one more non-`S` letter conjugates to that. -/
theorem backQuot_words_cons_of_not_S {u v z : GenObj P.Gen} (w : Quiver.Path u v) (e : v ⟶ z)
    (he : ¬ S e) :
    c.backQuot.map (c.words.map (w.cons e))
      = c.backQuot.map (c.words.map w)
        ≫ (P.quot.map (c.invWord v.as) ≫ P.quot.map e.toPath ≫ P.quot.map (c.word z.as)) :=
  (c.map_words_cons c.backQuot w e).trans
    (congrArg (fun t : c.backQuot.obj (c.repObj v) ⟶ c.backQuot.obj (c.repObj z) =>
      c.backQuot.map (c.words.map w) ≫ t) (c.backQuot_cell_of_not_S e he))

/-- Pushing one `S`-letter past the merge onto the representative. -/
theorem conj_step_of_S {u v z : GenObj P.Gen} (w : Quiver.Path u v) (e : v ⟶ z) (he : S e) :
    (P.quot.map (c.invWord u.as) ≫ P.quot.map w ≫ P.quot.map (c.word v.as))
        ≫ eqToHom (congrArg (fun x : P.V => (⟨P.pt x⟩ : P.presented)) (c.rep_eq_of_S he))
      = P.quot.map (c.invWord u.as) ≫ P.quot.map (w.cons e) ≫ P.quot.map (c.word z.as) := by
  rw [P.quot_map_cons]
  simp only [Category.assoc]
  exact congrArg (fun t => P.quot.map (c.invWord u.as) ≫ P.quot.map w ≫ t)
    (c.quot_word_comp_of_S e he)

/-- …and past one non-`S` letter, where the two merges cancel instead. -/
theorem conj_step_of_not_S {u v z : GenObj P.Gen} (w : Quiver.Path u v) (e : v ⟶ z) :
    (P.quot.map (c.invWord u.as) ≫ P.quot.map w ≫ P.quot.map (c.word v.as))
        ≫ (P.quot.map (c.invWord v.as) ≫ P.quot.map e.toPath ≫ P.quot.map (c.word z.as))
      = P.quot.map (c.invWord u.as) ≫ P.quot.map (w.cons e) ≫ P.quot.map (c.word z.as) := by
  rw [P.quot_map_cons]
  simp only [Category.assoc]
  rw [← Category.assoc (P.quot.map (c.word v.as)), ← P.quot_map_comp, c.word_invWord v.as,
    Category.id_comp]

/-- **The conjugation square, on a whole word**: conjugating a word and reading it back is the word
itself, between the merges onto the two representatives. -/
theorem backQuot_words : ∀ {u v : GenObj P.Gen} (w : Quiver.Path u v),
    c.backQuot.map (c.words.map w)
      = P.quot.map (c.invWord u.as) ≫ P.quot.map w ≫ P.quot.map (c.word v.as) := by
  intro u v w
  induction w with
  | nil =>
      rw [c.map_words_nil c.backQuot u, P.quot_map_nil, Category.id_comp, ← P.quot_map_comp]
      exact (c.invWord_word u.as).symm
  | @cons v z w e ih =>
      by_cases he : S e
      · refine (c.map_words_cons_of_S c.backQuot w e he (c.repObj_eq_of_S e he)).trans ?_
        refine Eq.trans (congrArg
          (fun t => t ≫ eqToHom (congrArg c.backQuot.obj (c.repObj_eq_of_S e he))) ih) ?_
        exact c.conj_step_of_S w e he
      · refine (c.backQuot_words_cons_of_not_S w e he).trans ?_
        refine Eq.trans (congrArg (fun t => t ≫ (P.quot.map (c.invWord v.as)
          ≫ P.quot.map e.toPath ≫ P.quot.map (c.word z.as))) ih) ?_
        exact c.conj_step_of_not_S w e

/-- **Reading back is a spelling** — a 2-cell of the contraction is a 2-cell of `P` conjugated, and
the conjugation square carries it back. -/
noncomputable def backSpelling : Polygraph.Spelling c.poly P where
  cells := c.backPre
  sound α := by
    obtain ⟨u, v, β, rfl, rfl⟩ := α
    exact (c.backQuot_words (P.src β)).trans
      ((congrArg (fun t => P.quot.map (c.invWord u.as) ≫ t ≫ P.quot.map (c.word v.as))
        (P.quot_src_tgt β)).trans (c.backQuot_words (P.tgt β)).symm)

/-! ## The conjugation is an equivalence -/

/-- **Merging onto the representative is invertible.** -/
noncomputable def wordIso (x : P.V) : (⟨P.pt x⟩ : P.presented) ≅ ⟨P.pt (c.rep x)⟩ where
  hom := P.quot.map (c.word x)
  inv := P.quot.map (c.invWord x)
  hom_inv_id := (P.quot_map_comp _ _).symm.trans (c.word_invWord x)
  inv_hom_id := (P.quot_map_comp _ _).symm.trans (c.invWord_word x)

theorem unit_naturality {u v : GenObj P.Gen} (w : Quiver.Path u v) :
    P.quot.map w ≫ P.quot.map (c.word v.as)
      = P.quot.map (c.word u.as)
        ≫ (P.quot.map (c.invWord u.as) ≫ P.quot.map w ≫ P.quot.map (c.word v.as)) := by
  rw [← Category.assoc (P.quot.map (c.word u.as)),
    ← P.quot_map_comp (c.word u.as) (c.invWord u.as), c.word_invWord u.as, Category.id_comp]

/-- **Conjugating, then reading back, is the identity** — the component is the merge onto the
representative, and its naturality is the conjugation square. -/
noncomputable def unitIso : 𝟭 P.presented ≅ c.spelling.functor ⋙ c.backSpelling.functor :=
  NatIso.ofComponents (fun X => c.wordIso X.as.as) fun {X _} f => by
    obtain ⟨w, rfl⟩ := P.quot.map_surjective f
    exact (c.unit_naturality w).trans
      (congrArg (fun t => P.quot.map (c.word X.as.as) ≫ t) (c.backQuot_words w).symm)

/-- **A 1-cell read back and conjugated again is itself** — the counit's naturality. -/
theorem counit_naturality {X Y : GenObj c.Gen} (e : X ⟶ Y) :
    (c.backSpelling.functor ⋙ c.spelling.functor).map (c.poly.quot.map e.toPath)
        ≫ eqToHom (congrArg c.poly.quot.obj (c.repObj_self Y))
      = eqToHom (congrArg c.poly.quot.obj (c.repObj_self X))
        ≫ (𝟭 c.poly.presented).map (c.poly.quot.map e.toPath) := by
  change (c.poly.quot.map (c.words.map ((Paths.lift c.backPre).map e.toPath)) :
        c.poly.quot.obj (c.repObj (P.pt X.as.1)) ⟶ c.poly.quot.obj (c.repObj (P.pt Y.as.1)))
        ≫ eqToHom (congrArg c.poly.quot.obj (c.repObj_self Y))
      = eqToHom (congrArg c.poly.quot.obj (c.repObj_self X)) ≫ c.poly.quot.map e.toPath
  rw [Paths.lift_toPath]
  obtain ⟨⟨x, hx⟩⟩ := X
  obtain ⟨⟨y, hy⟩⟩ := Y
  obtain ⟨a, b, g, hg, hd, hc⟩ := e
  have hd' : c.rep a = x := hd
  have hc' : c.rep b = y := hc
  subst hd'
  subst hc'
  refine Eq.trans (congrArg (fun t => t ≫ eqToHom _)
    (c.map_words_comp c.poly.quot (c.invWord a) ((Polygraph.cell g).toPath.comp (c.word b)))) ?_
  refine Eq.trans (congrArg (fun t => (t ≫ _) ≫ eqToHom _)
    (c.map_words_of_all_S c.poly.quot (c.invWord a) (c.invWord_all a)
      (c.repObj_eq_of_all_S _ (c.invWord_all a)))) ?_
  refine Eq.trans (congrArg (fun t => (_ ≫ t) ≫ eqToHom _)
    (c.map_words_comp c.poly.quot (Polygraph.cell g).toPath (c.word b))) ?_
  refine Eq.trans (congrArg (fun t => (_ ≫ _ ≫ t) ≫ eqToHom _)
    (c.map_words_of_all_S c.poly.quot (c.word b) (c.word_all b)
      (c.repObj_eq_of_all_S _ (c.word_all b)))) ?_
  refine Eq.trans (congrArg (fun t => (_ ≫ t ≫ _) ≫ eqToHom _)
    (congrArg (fun s => c.poly.quot.map s) (Paths.lift_toPath c.pre (Polygraph.cell g)))) ?_
  refine Eq.trans (congrArg (fun t => (_ ≫ t ≫ _) ≫ eqToHom _)
    (congrArg (fun s => c.poly.quot.map s) (c.cell_of_not_S (Polygraph.cell g) hg))) ?_
  simp only [Category.assoc]
  generalize_proofs k₁ k₂ k₃ k₄
  have hT : (eqToHom k₂ ≫ eqToHom k₃ :
      c.poly.quot.obj (c.repObj (P.pt b)) ⟶ c.poly.quot.obj (c.repObj (P.pt b))) = 𝟙 _ :=
    (eqToHom_trans k₂ k₃).trans (eqToHom_refl _ _)
  change eqToHom k₁ ≫ c.poly.quot.map (c.genCell (Polygraph.cell g) hg).toPath
      ≫ (eqToHom k₂ ≫ eqToHom k₃ :
        c.poly.quot.obj (c.repObj (P.pt b)) ⟶ c.poly.quot.obj (c.repObj (P.pt b)))
    = eqToHom k₄ ≫ c.poly.quot.map (c.genCell (Polygraph.cell g) hg).toPath
  rw [hT, Category.comp_id]
  rfl

/-- **Reading back, then conjugating, is the identity** — a representative is its own
representative. -/
noncomputable def counitIso : c.backSpelling.functor ⋙ c.spelling.functor ≅ 𝟭 c.poly.presented :=
  NatIso.ofComponents (fun X => eqToIso (congrArg c.poly.quot.obj (c.repObj_self X.as)))
    fun {_ _} f => by
      obtain ⟨R, rfl⟩ := c.poly.quot.map_surjective f
      exact Polygraph.naturality_of_gen (P := c.poly)
        (fun Z => eqToHom (congrArg c.poly.quot.obj (c.repObj_self Z)))
        (fun {_ _} e => c.counit_naturality e) R

/-- **The conjugation is an equivalence** — conjugating and reading back are mutually inverse. -/
noncomputable def equivalence : P.presented ≌ c.poly.presented :=
  Equivalence.mk c.spelling.functor c.backSpelling.functor c.unitIso c.counitIso

end Contraction

/-- **The contraction presents**: contracting invertible words loses nothing. -/
noncomputable def Presents.contract {P : Polygraph.{w, u', w₂}}
    {S : ∀ {a b : P.V}, P.Gen a b → Prop} {C : Type u} [Category.{v} C] (p : Presents P C)
    (c : Contraction P S) : Presents c.poly C :=
  ⟨c.equivalence.inverse ⋙ p.E, inferInstance⟩

end CategoryTheory
