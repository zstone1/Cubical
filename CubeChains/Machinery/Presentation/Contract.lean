import CubeChains.Machinery.Presentation.Localize

/-!
# Machinery/Presentation/Contract — collapsing a family of generators onto representatives

A `Collapse` names one 0-cell per class together with an `S`-word onto it; `poly` keeps those
0-cells and conjugates each non-`S` generator onto them, and `Presents.collapse` says the
conjugation presents the **localization** at the class `S` generates.  No inverse is asked for: the
formal inverses of `invPoly` supply it, and none of them survives into the cells — a 1-cell of
`poly` is a 1-cell of `P` and a 2-cell of `poly` is a 2-cell of `P`.

               invWord a         g          word b
    rep a ────────────────▸ a ────────▸ b ────────────▸ rep b
      └─────────────────────── κ g ───────────────────────┘

An `S`-letter makes `κ g` the empty word; that square is `word_comp_of_S`.  `Restrict` cannot do
this: convexity forces closure under isomorphism.
-/

universe w u' w₂ v u

namespace CategoryTheory

open Polygraph

/-- **Data collapsing `P` along a family of `S`-words**: one 0-cell per class, with an `S`-word onto
it.  Its inverse is not asked for — the localization supplies one. -/
structure Collapse (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop) where
  /-- the representative of a 0-cell -/
  rep : P.V → P.V
  /-- …which is its own representative -/
  rep_idem : ∀ x, rep (rep x) = rep x
  /-- a word from a 0-cell to its representative -/
  word : ∀ x : P.V, Quiver.Path (P.pt x) (P.pt (rep x))
  /-- …spelled out of `S` -/
  word_all : ∀ x, Quiver.Path.All (fun ⦃_ _⦄ e => S e) (word x)
  /-- an `S`-letter does not change the representative… -/
  rep_eq_of_S : ∀ {a b : P.V} {g : P.Gen a b}, S g → rep a = rep b
  /-- …and merging to the representative factors through it -/
  word_comp_of_S : ∀ {a b : P.V} (g : P.Gen a b) (h : S g),
    P.quot.map (cellCongr Quiver.Path rfl (congrArg P.pt (rep_eq_of_S h)) (word a))
      = P.quot.map ((Polygraph.cell g).toPath.comp (word b))

namespace Collapse

variable {P : Polygraph.{w, u', w₂}} {S : ∀ {a b : P.V}, P.Gen a b → Prop} (c : Collapse P S)

/-! ## The collapsed polygraph -/

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
  /-- …not one of the collapsed ones -/
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

/-- **A 1-cell of the collapse is its generator** — the two representative equations are
propositions, so the endpoints it carries and that generator are all of it. -/
theorem Gen.ext {x y : c.V} :
    ∀ g g' : c.Gen x y, g.dom = g'.dom → g.cod = g'.cod → g.gen ≍ g'.gen → g = g'
  | ⟨dom, cod, gen, _, _, _⟩, ⟨dom', cod', gen', _, _, _⟩, hdom, hcod, hgen => by
      obtain rfl : dom = dom' := hdom
      obtain rfl : cod = cod' := hcod
      obtain rfl : gen = gen' := eq_of_heq hgen
      rfl

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

/-- The conjugation, as a spelling of `P`'s letters by words of the collapse. -/
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

/-- **The collapsed polygraph** — the representatives, the conjugated non-`S` generators, and the
conjugated 2-cells. -/
noncomputable def poly : Polygraph where
  V := c.V
  Gen := c.Gen
  Rel := c.Cell
  src α := cellCongr Quiver.Path α.rep_dom α.rep_cod (c.words.map (P.src α.cell))
  tgt α := cellCongr Quiver.Path α.rep_dom α.rep_cod (c.words.map (P.tgt α.cell))

/-- **A 2-cell of `P` is a 2-cell of the collapse** — that is what its 2-cells are. -/
theorem quot_words_src_tgt {u v : GenObj P.Gen} (α : P.Rel u v) :
    c.poly.quot.map (c.words.map (P.src α)) = c.poly.quot.map (c.words.map (P.tgt α)) :=
  c.poly.quot_src_tgt (⟨u, v, α, rfl, rfl⟩ : c.Cell (c.repObj u) (c.repObj v))

/-! ## The extension the collapse takes place in

The conjugate of a letter runs backwards along a merge, which exists only once the merges are
formally inverted; `invPoly` is that ambient, and the collapsed polygraph is the equivalent of
*its* presented category. -/

/-- The merge onto the representative, in the extension. -/
noncomputable def locWord (x : P.V) :
    Quiver.Path ((invPoly P S).pt x) ((invPoly P S).pt (c.rep x)) :=
  (fwdPre P S).mapPath (c.word x)

/-- …and its formal inverse. -/
noncomputable def invWord (x : P.V) :
    Quiver.Path ((invPoly P S).pt (c.rep x)) ((invPoly P S).pt x) :=
  Polygraph.invWord P S (c.word x) (c.word_all x)

theorem all_locWord (x : P.V) :
    Quiver.Path.All (fun ⦃_ _⦄ e => invPicked P S e) (c.locWord x) :=
  Quiver.Path.All.mapPath (fwdPre P S) (fun _ he => he) (c.word_all x)

theorem all_invWord (x : P.V) :
    Quiver.Path.All (fun ⦃_ _⦄ e => invPicked P S e) (c.invWord x) :=
  Polygraph.all_invWord P S (fun _ _ => trivial) (c.word x) (c.word_all x)

theorem locWord_invWord (x : P.V) :
    (invPoly P S).quot.map ((c.locWord x).comp (c.invWord x)) = 𝟙 _ :=
  (Polygraph.quot_map_comp _ _ _).trans
    (Polygraph.quot_fwd_invWord P S (c.word x) (c.word_all x))

theorem invWord_locWord (x : P.V) :
    (invPoly P S).quot.map ((c.invWord x).comp (c.locWord x)) = 𝟙 _ :=
  (Polygraph.quot_map_comp _ _ _).trans
    (Polygraph.quot_invWord_fwd P S (c.word x) (c.word_all x))

/-- **Merging onto the representative is invertible** — that is what the extension buys. -/
noncomputable def wordIso (x : P.V) :
    (⟨(invPoly P S).pt x⟩ : (invPoly P S).presented) ≅ ⟨(invPoly P S).pt (c.rep x)⟩ where
  hom := (invPoly P S).quot.map (c.locWord x)
  inv := (invPoly P S).quot.map (c.invWord x)
  hom_inv_id := (Polygraph.quot_map_comp _ _ _).symm.trans (c.locWord_invWord x)
  inv_hom_id := (Polygraph.quot_map_comp _ _ _).symm.trans (c.invWord_locWord x)

/-- **An inverted letter does not change the representative either** — a formal inverse undoes what
the letter it inverts did. -/
theorem rep_eq_of_invPicked : ∀ {a b : P.V} (g : InvGen P S a b), invPicked P S g →
    c.rep a = c.rep b
  | _, _, .inl _, h => c.rep_eq_of_S h
  | _, _, .inr ⟨_, he⟩, _ => (c.rep_eq_of_S he).symm

theorem repObj_eq_of_invPicked {a b : P.V} (g : InvGen P S a b) (h : invPicked P S g) :
    c.repObj (P.pt a) = c.repObj (P.pt b) :=
  GenObj.ext (Subtype.ext (c.rep_eq_of_invPicked g h))

theorem rep_eq_of_all_invPicked : ∀ {u v : GenObj (invPoly P S).Gen} (w : Quiver.Path u v),
    Quiver.Path.All (fun ⦃_ _⦄ e => invPicked P S e) w → c.rep u.as = c.rep v.as := by
  intro u v w
  induction w with
  | nil => exact fun _ => rfl
  | cons w e ih =>
      intro h
      rw [Quiver.Path.all_cons_iff] at h
      exact (ih h.1).trans (c.rep_eq_of_invPicked e h.2)

theorem repObj_eq_of_all_invPicked {u v : GenObj (invPoly P S).Gen} (w : Quiver.Path u v)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => invPicked P S e) w) :
    c.repObj (P.pt u.as) = c.repObj (P.pt v.as) :=
  GenObj.ext (Subtype.ext (c.rep_eq_of_all_invPicked w h))

/-- **The conjugation, on a letter of the extension** — an inverted letter becomes the empty word
just as the letter it inverts does. -/
noncomputable def locCell : ∀ {a b : P.V}, InvGen P S a b →
    Quiver.Path (c.repObj (P.pt a)) (c.repObj (P.pt b))
  | _, _, .inl e => c.cell (Polygraph.cell e)
  | _, _, .inr ⟨e, he⟩ =>
      cellCongr Quiver.Path rfl (c.repObj_eq_of_S (Polygraph.cell e) he).symm Quiver.Path.nil

theorem locCell_of_invPicked : ∀ {a b : P.V} (g : InvGen P S a b) (hg : invPicked P S g),
    c.locCell g = cellCongr Quiver.Path rfl (c.repObj_eq_of_invPicked g hg) Quiver.Path.nil
  | _, _, .inl e, hg => c.cell_of_S (Polygraph.cell e) hg
  | _, _, .inr ⟨_, _⟩, _ => rfl

/-- The conjugation, on the extension's letters. -/
noncomputable def locPre : GenObj (invPoly P S).Gen ⥤q Paths (GenObj c.Gen) where
  obj x := c.repObj (P.pt x.as)
  map {x y} g := c.locCell (g : InvGen P S x.as y.as)

/-- …and on whole words. -/
noncomputable abbrev locWords : (invPoly P S).Word ⥤ Paths (GenObj c.Gen) := Paths.lift c.locPre

/-- **A word of `P` conjugates the same way through the extension.** -/
theorem locWords_fwd {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    c.locWords.map ((fwdPre P S).mapPath u) = c.words.map u :=
  Paths.lift_mapPath (fwdPre P S) c.locPre u

/-! ### Reading a conjugated word

`poly`'s 1-cells are indexed over `P`'s, so its `≫` and its `𝟙` are spelled at `c.Gen` while a
functor out of `poly.Word` carries `poly.Gen`; these say the two spellings agree, once and for all
readings of the collapse. -/

section Read

variable {D : Type*} [Category* D] (G : Paths (GenObj c.Gen) ⥤ D)

theorem map_locWords_nil (u : GenObj (invPoly P S).Gen) :
    G.map (c.locWords.map (Quiver.Path.nil : Quiver.Path u u)) = 𝟙 (G.obj (c.locPre.obj u)) :=
  (c.locWords ⋙ G).map_id u

theorem map_locWords_cons {u v z : GenObj (invPoly P S).Gen} (w : Quiver.Path u v) (e : v ⟶ z) :
    G.map (c.locWords.map (w.cons e)) = G.map (c.locWords.map w) ≫ G.map (c.locCell e) :=
  (congrArg (fun t => G.map t) (Paths.lift_cons c.locPre w e)).trans (G.map_comp _ _)

theorem map_locWords_comp {u v z : GenObj (invPoly P S).Gen} (w : Quiver.Path u v)
    (w' : Quiver.Path v z) :
    G.map (c.locWords.map (w.comp w')) = G.map (c.locWords.map w) ≫ G.map (c.locWords.map w') :=
  (c.locWords ⋙ G).map_comp w w'

/-- The empty word, read at another name for its endpoint. -/
private theorem map_nil_cellCongr {X Y : GenObj c.Gen} (h : X = Y) :
    G.map (cellCongr Quiver.Path rfl h (Quiver.Path.nil : Quiver.Path X X))
      = eqToHom (congrArg G.obj h) := by
  subst h
  exact (G.map_id X).trans (eqToHom_refl _ _).symm

/-- **An inverted letter conjugates to an identity.** -/
theorem map_locCell_of_invPicked {a b : P.V} (g : InvGen P S a b) (hg : invPicked P S g)
    (h : c.repObj (P.pt a) = c.repObj (P.pt b)) :
    G.map (c.locCell g) = eqToHom (congrArg G.obj h) :=
  (congrArg (fun t => G.map t) (c.locCell_of_invPicked g hg)).trans (c.map_nil_cellCongr G h)

/-- …so one more inverted letter is no letter at all. -/
theorem map_locWords_cons_of_invPicked {u v z : GenObj (invPoly P S).Gen} (w : Quiver.Path u v)
    (e : v ⟶ z) (he : invPicked P S e) (h : c.locPre.obj v = c.locPre.obj z) :
    G.map (c.locWords.map (w.cons e)) = G.map (c.locWords.map w) ≫ eqToHom (congrArg G.obj h) :=
  (c.map_locWords_cons G w e).trans
    (congrArg (fun t : G.obj (c.locPre.obj v) ⟶ G.obj (c.locPre.obj z) =>
      G.map (c.locWords.map w) ≫ t) (c.map_locCell_of_invPicked G e he h))

/-- **…and so does a whole inverted word.** -/
theorem map_locWords_of_all : ∀ {u v : GenObj (invPoly P S).Gen} (w : Quiver.Path u v),
    Quiver.Path.All (fun ⦃_ _⦄ e => invPicked P S e) w →
    ∀ h : c.locPre.obj u = c.locPre.obj v,
      G.map (c.locWords.map w) = eqToHom (congrArg G.obj h) := by
  intro u v w
  induction w with
  | nil => intro _ h; exact (c.map_locWords_nil G u).trans (eqToHom_refl _ _).symm
  | cons w e ih =>
      intro hw h
      rw [Quiver.Path.all_cons_iff] at hw
      refine (c.map_locWords_cons_of_invPicked G w e hw.2
        (c.repObj_eq_of_invPicked e hw.2)).trans ?_
      refine Eq.trans (congrArg (fun t => t ≫ eqToHom (congrArg G.obj
        (c.repObj_eq_of_invPicked e hw.2))) (ih hw.1 (c.repObj_eq_of_all_invPicked w hw.1))) ?_
      exact eqToHom_trans _ _

end Read

/-! ## The conjugation, as a spelling -/

/-- **The conjugation is a spelling of the extension** — a 2-cell of `P` is a 2-cell of the
collapse, and a cancellation is two inverted letters against none. -/
noncomputable def spelling : Polygraph.Spelling (invPoly P S) c.poly where
  cells := c.locPre
  sound α := by
    cases α with
    | keep β =>
        exact ((congrArg c.poly.quot.map (c.locWords_fwd (P.src β))).trans
          (c.quot_words_src_tgt β)).trans
          (congrArg c.poly.quot.map (c.locWords_fwd (P.tgt β))).symm
    | cancel e he =>
        exact (c.map_locWords_of_all c.poly.quot _
            ((Quiver.Path.all_toPath.mpr (show invPicked P S (fwdCell P S e) from he)).comp
              (Quiver.Path.all_toPath.mpr (show invPicked P S (bwdCell P S e he) from trivial)))
            rfl).trans
          (c.map_locWords_of_all c.poly.quot Quiver.Path.nil (Quiver.Path.all_nil _) rfl).symm
    | cancel' e he =>
        exact (c.map_locWords_of_all c.poly.quot _
            ((Quiver.Path.all_toPath.mpr (show invPicked P S (bwdCell P S e he) from trivial)).comp
              (Quiver.Path.all_toPath.mpr (show invPicked P S (fwdCell P S e) from he)))
            rfl).trans
          (c.map_locWords_of_all c.poly.quot Quiver.Path.nil (Quiver.Path.all_nil _) rfl).symm

/-! ## Reading a 1-cell of the collapse back in the extension -/

/-- The conjugate of a letter: merge down, cross, merge back up. -/
noncomputable def backWord {u v : GenObj P.Gen} (g : u ⟶ v) :
    Quiver.Path ((invPoly P S).pt (c.rep u.as)) ((invPoly P S).pt (c.rep v.as)) :=
  (c.invWord u.as).comp (((fwdPre P S).map g).toPath.comp (c.locWord v.as))

/-- …read at the representatives the 1-cell actually runs between. -/
noncomputable def backPre : GenObj c.Gen ⥤q (invPoly P S).Word where
  obj X := (invPoly P S).pt X.as.1
  map e := cellCongr Quiver.Path (congrArg (invPoly P S).pt e.rep_dom)
    (congrArg (invPoly P S).pt e.rep_cod) (c.backWord (Polygraph.cell e.gen))

/-- Reading a word of the collapse back in the extension. -/
noncomputable abbrev backQuot : Paths (GenObj c.Gen) ⥤ (invPoly P S).presented :=
  Paths.lift c.backPre ⋙ (invPoly P S).quot

/-- **Merging to the representative, as a factorization** — `word_comp_of_S`, pushed into the
extension, with its transport read as an `eqToHom`. -/
theorem quot_locWord_comp_of_S {a b : P.V} (e : P.Gen a b) (he : S e) :
    (invPoly P S).quot.map (c.locWord a)
        ≫ eqToHom (congrArg (fun z : P.V => (⟨(invPoly P S).pt z⟩ : (invPoly P S).presented))
          (c.rep_eq_of_S he))
      = (invPoly P S).quot.map ((fwdCell P S e).toPath)
        ≫ (invPoly P S).quot.map (c.locWord b) :=
  have hev : (invPoly P S).quot.map ((fwdPre P S).mapPath
        (cellCongr Quiver.Path rfl (congrArg P.pt (c.rep_eq_of_S he)) (c.word a)))
      = (invPoly P S).quot.map ((fwdPre P S).mapPath
        ((Polygraph.cell e).toPath.comp (c.word b))) :=
    Polygraph.Hom.quot_map_congr (Polygraph.invIncl P S) (c.word_comp_of_S e he)
  have hsrc : (fwdPre P S).mapPath
        (cellCongr Quiver.Path rfl (congrArg P.pt (c.rep_eq_of_S he)) (c.word a))
      = cellCongr Quiver.Path rfl
          (congrArg (fwdPre P S).obj (congrArg P.pt (c.rep_eq_of_S he))) (c.locWord a) :=
    Prefunctor.mapPath_cellCongr (fwdPre P S) rfl _ (c.word a)
  have htgt : (fwdPre P S).mapPath ((Polygraph.cell e).toPath.comp (c.word b))
      = (fwdCell P S e).toPath.comp (c.locWord b) :=
    (Prefunctor.mapPath_comp (fwdPre P S) (Polygraph.cell e).toPath (c.word b)).trans
      (congrArg (fun t => Quiver.Path.comp t (c.locWord b))
        (Prefunctor.mapPath_toPath (fwdPre P S) (Polygraph.cell e)))
  ((Polygraph.quot_map_cellCongr (invPoly P S) _ (c.locWord a)).symm.trans
      (((congrArg (invPoly P S).quot.map hsrc).symm.trans hev).trans
        (congrArg (invPoly P S).quot.map htgt))).trans
    (Polygraph.quot_map_comp (invPoly P S) _ _)

/-- A composite with a renaming on its far side, read back. -/
private theorem comp_eqToHom_symm {D : Type*} [Category D] {X Y Z Z' : D} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z = Z'} {h' : Z' = Z} {w : X ⟶ Z'} (hw : f ≫ g ≫ eqToHom h = w) :
    w ≫ eqToHom h' = f ≫ g := by
  subst h
  simpa using hw.symm

/-- **…and at a formal inverse**, by cancelling the merge it inverts. -/
theorem quot_locWord_comp_of_bwd {a b : P.V} (e : P.Gen b a) (he : S e) :
    (invPoly P S).quot.map (c.locWord a)
        ≫ eqToHom (congrArg (fun z : P.V => (⟨(invPoly P S).pt z⟩ : (invPoly P S).presented))
          (c.rep_eq_of_S he).symm)
      = (invPoly P S).quot.map ((bwdCell P S e he).toPath)
        ≫ (invPoly P S).quot.map (c.locWord b) := by
  refine comp_eqToHom_symm (h := congrArg
    (fun z : P.V => (⟨(invPoly P S).pt z⟩ : (invPoly P S).presented)) (c.rep_eq_of_S he)) ?_
  refine Eq.trans (congrArg (fun t => (invPoly P S).quot.map ((bwdCell P S e he).toPath) ≫ t)
    (c.quot_locWord_comp_of_S e he)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact (congrArg (fun t => t ≫ (invPoly P S).quot.map (c.locWord a))
    (Polygraph.bwdArrow_fwdArrow P S e he)).trans (Category.id_comp _)

/-- **Merging to the representative factors through any inverted letter.** -/
theorem quot_locWord_comp {a b : P.V} (g : InvGen P S a b) (hg : invPicked P S g) :
    (invPoly P S).quot.map (c.locWord a)
        ≫ eqToHom (congrArg (fun z : P.V => (⟨(invPoly P S).pt z⟩ : (invPoly P S).presented))
          (c.rep_eq_of_invPicked g hg))
      = (invPoly P S).quot.map ((Polygraph.cell (P := invPoly P S) g).toPath)
        ≫ (invPoly P S).quot.map (c.locWord b) := by
  rcases g with e | ⟨e, he⟩
  · exact c.quot_locWord_comp_of_S e hg
  · exact c.quot_locWord_comp_of_bwd e he

/-- **A letter the extension does not invert reads back as its own conjugate.** -/
theorem backQuot_locCell_of_not_invPicked {u v : GenObj (invPoly P S).Gen} (g : u ⟶ v)
    (hg : ¬ invPicked P S g) :
    c.backQuot.map (c.locCell g)
      = (invPoly P S).quot.map (c.invWord u.as)
        ≫ (invPoly P S).quot.map (g.toPath)
        ≫ (invPoly P S).quot.map (c.locWord v.as) := by
  rcases g with e | ⟨e, he⟩
  case inr => exact absurd trivial hg
  refine Eq.trans (congrArg c.backQuot.map (c.cell_of_not_S (Polygraph.cell e) hg)) ?_
  refine Eq.trans (congrArg (invPoly P S).quot.map
    (Paths.lift_toPath c.backPre (c.genCell (Polygraph.cell e) hg))) ?_
  exact (Polygraph.quot_map_comp _ _ _).trans
    (congrArg (fun t => (invPoly P S).quot.map (c.invWord u.as) ≫ t)
      (Polygraph.quot_map_comp _ _ _))

/-- …so one more such letter conjugates to that. -/
theorem backQuot_locWords_cons_of_not {u v z : GenObj (invPoly P S).Gen} (w : Quiver.Path u v)
    (e : v ⟶ z) (he : ¬ invPicked P S e) :
    c.backQuot.map (c.locWords.map (w.cons e))
      = c.backQuot.map (c.locWords.map w)
        ≫ ((invPoly P S).quot.map (c.invWord v.as)
          ≫ (invPoly P S).quot.map (e.toPath)
          ≫ (invPoly P S).quot.map (c.locWord z.as)) :=
  (c.map_locWords_cons c.backQuot w e).trans
    (congrArg (fun t : c.backQuot.obj (c.locPre.obj v) ⟶ c.backQuot.obj (c.locPre.obj z) =>
      c.backQuot.map (c.locWords.map w) ≫ t) (c.backQuot_locCell_of_not_invPicked e he))

/-- Pushing one inverted letter past the merge onto the representative. -/
theorem conj_step_of_invPicked {u v z : GenObj (invPoly P S).Gen} (w : Quiver.Path u v) (e : v ⟶ z)
    (he : invPicked P S e) :
    ((invPoly P S).quot.map (c.invWord u.as) ≫ (invPoly P S).quot.map w
          ≫ (invPoly P S).quot.map (c.locWord v.as))
        ≫ eqToHom (congrArg (fun x : P.V => (⟨(invPoly P S).pt x⟩ : (invPoly P S).presented))
          (c.rep_eq_of_invPicked e he))
      = (invPoly P S).quot.map (c.invWord u.as) ≫ (invPoly P S).quot.map (w.cons e)
        ≫ (invPoly P S).quot.map (c.locWord z.as) := by
  rw [Polygraph.quot_map_cons]
  simp only [Category.assoc]
  exact congrArg (fun t => (invPoly P S).quot.map (c.invWord u.as)
      ≫ (invPoly P S).quot.map w ≫ t) (c.quot_locWord_comp e he)

/-- …and past one other letter, where the two merges cancel instead. -/
theorem conj_step_of_not {u v z : GenObj (invPoly P S).Gen} (w : Quiver.Path u v) (e : v ⟶ z) :
    ((invPoly P S).quot.map (c.invWord u.as) ≫ (invPoly P S).quot.map w
          ≫ (invPoly P S).quot.map (c.locWord v.as))
        ≫ ((invPoly P S).quot.map (c.invWord v.as)
          ≫ (invPoly P S).quot.map (e.toPath)
          ≫ (invPoly P S).quot.map (c.locWord z.as))
      = (invPoly P S).quot.map (c.invWord u.as) ≫ (invPoly P S).quot.map (w.cons e)
        ≫ (invPoly P S).quot.map (c.locWord z.as) := by
  rw [Polygraph.quot_map_cons]
  simp only [Category.assoc]
  rw [← Category.assoc ((invPoly P S).quot.map (c.locWord v.as)), ← Polygraph.quot_map_comp,
    c.locWord_invWord v.as, Category.id_comp]

/-- **The conjugation square, on a whole word**: conjugating a word and reading it back is the word
itself, between the merges onto the two representatives. -/
theorem backQuot_locWords : ∀ {u v : GenObj (invPoly P S).Gen} (w : Quiver.Path u v),
    c.backQuot.map (c.locWords.map w)
      = (invPoly P S).quot.map (c.invWord u.as) ≫ (invPoly P S).quot.map w
        ≫ (invPoly P S).quot.map (c.locWord v.as) := by
  intro u v w
  induction w with
  | nil =>
      rw [c.map_locWords_nil c.backQuot u, Polygraph.quot_map_nil, Category.id_comp,
        ← Polygraph.quot_map_comp]
      exact (c.invWord_locWord u.as).symm
  | @cons v z w e ih =>
      by_cases he : invPicked P S e
      · refine (c.map_locWords_cons_of_invPicked c.backQuot w e he
          (c.repObj_eq_of_invPicked e he)).trans ?_
        refine Eq.trans (congrArg
          (fun t => t ≫ eqToHom (congrArg c.backQuot.obj (c.repObj_eq_of_invPicked e he))) ih) ?_
        exact c.conj_step_of_invPicked w e he
      · refine (c.backQuot_locWords_cons_of_not w e he).trans ?_
        refine Eq.trans (congrArg (fun t => t ≫ ((invPoly P S).quot.map (c.invWord v.as)
          ≫ (invPoly P S).quot.map (e.toPath)
          ≫ (invPoly P S).quot.map (c.locWord z.as))) ih) ?_
        exact c.conj_step_of_not w e

/-- **Reading back is a spelling** — a 2-cell of the collapse is a 2-cell of `P` conjugated, and the
conjugation square carries it back. -/
noncomputable def backSpelling : Polygraph.Spelling c.poly (invPoly P S) where
  cells := c.backPre
  sound α := by
    obtain ⟨u, v, β, rfl, rfl⟩ := α
    refine Eq.trans (congrArg c.backQuot.map (c.locWords_fwd (P.src β)).symm) ?_
    refine Eq.trans (c.backQuot_locWords ((fwdPre P S).mapPath (P.src β))) ?_
    refine Eq.trans (congrArg (fun t => (invPoly P S).quot.map (c.invWord u.as) ≫ t
      ≫ (invPoly P S).quot.map (c.locWord v.as))
      (Polygraph.Hom.quot_map_congr (Polygraph.invIncl P S) (P.quot_src_tgt β))) ?_
    refine Eq.trans (c.backQuot_locWords ((fwdPre P S).mapPath (P.tgt β))).symm ?_
    exact congrArg c.backQuot.map (c.locWords_fwd (P.tgt β))

/-! ## The conjugation is an equivalence -/

theorem unit_naturality {u v : GenObj (invPoly P S).Gen} (w : Quiver.Path u v) :
    (invPoly P S).quot.map w ≫ (invPoly P S).quot.map (c.locWord v.as)
      = (invPoly P S).quot.map (c.locWord u.as)
        ≫ ((invPoly P S).quot.map (c.invWord u.as) ≫ (invPoly P S).quot.map w
          ≫ (invPoly P S).quot.map (c.locWord v.as)) := by
  rw [← Category.assoc ((invPoly P S).quot.map (c.locWord u.as)),
    ← Polygraph.quot_map_comp (invPoly P S) (c.locWord u.as) (c.invWord u.as),
    c.locWord_invWord u.as, Category.id_comp]

/-- **Conjugating, then reading back, is the identity** — the component is the merge onto the
representative, and its naturality is the conjugation square. -/
noncomputable def unitIso :
    𝟭 (invPoly P S).presented ≅ c.spelling.functor ⋙ c.backSpelling.functor :=
  NatIso.ofComponents (fun X => c.wordIso X.as.as) fun {X _} f => by
    obtain ⟨w, rfl⟩ := (invPoly P S).quot.map_surjective f
    exact (c.unit_naturality w).trans
      (congrArg (fun t => (invPoly P S).quot.map (c.locWord X.as.as) ≫ t)
        (c.backQuot_locWords w).symm)

/-- **A 1-cell read back and conjugated again is itself** — the counit's naturality. -/
theorem counit_naturality {X Y : GenObj c.Gen} (e : X ⟶ Y) :
    (c.backSpelling.functor ⋙ c.spelling.functor).map (c.poly.quot.map e.toPath)
        ≫ eqToHom (congrArg c.poly.quot.obj (c.repObj_self Y))
      = eqToHom (congrArg c.poly.quot.obj (c.repObj_self X))
        ≫ (𝟭 c.poly.presented).map (c.poly.quot.map e.toPath) := by
  change (c.poly.quot.map (c.locWords.map ((Paths.lift c.backPre).map e.toPath)) :
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
    (c.map_locWords_comp c.poly.quot (c.invWord a)
      (((fwdPre P S).map (Polygraph.cell g)).toPath.comp (c.locWord b)))) ?_
  refine Eq.trans (congrArg (fun t => (t ≫ _) ≫ eqToHom _)
    (c.map_locWords_of_all c.poly.quot (c.invWord a) (c.all_invWord a)
      (c.repObj_eq_of_all_invPicked _ (c.all_invWord a)))) ?_
  refine Eq.trans (congrArg (fun t => (_ ≫ t) ≫ eqToHom _)
    (c.map_locWords_comp c.poly.quot ((fwdPre P S).map (Polygraph.cell g)).toPath
      (c.locWord b))) ?_
  refine Eq.trans (congrArg (fun t => (_ ≫ _ ≫ t) ≫ eqToHom _)
    (c.map_locWords_of_all c.poly.quot (c.locWord b) (c.all_locWord b)
      (c.repObj_eq_of_all_invPicked _ (c.all_locWord b)))) ?_
  refine Eq.trans (congrArg (fun t => (_ ≫ t ≫ _) ≫ eqToHom _)
    (congrArg (fun s => c.poly.quot.map s)
      (Paths.lift_toPath c.locPre ((fwdPre P S).map (Polygraph.cell g))))) ?_
  refine Eq.trans (congrArg (fun t => (_ ≫ t ≫ _) ≫ eqToHom _)
    (congrArg (fun s => c.poly.quot.map s)
      (c.cell_of_not_S (Polygraph.cell g) hg))) ?_
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
noncomputable def equivalence : (invPoly P S).presented ≌ c.poly.presented :=
  Equivalence.mk c.spelling.functor c.backSpelling.functor c.unitIso c.counitIso

end Collapse

/-- **The collapse presents the localization**: making the picked 1-cells identities is exactly
inverting them, and it leaves the surviving cells untouched. -/
noncomputable def Presents.collapse {P : Polygraph.{w, u', w₂}}
    {S : ∀ {a b : P.V}, P.Gen a b → Prop} {C : Type u} [Category.{v} C] (p : Presents P C)
    (c : Collapse P S) {W : MorphismProperty C}
    (hW : W = (p.pickedArrows S).multiplicativeClosure) : Presents c.poly W.Localization :=
  ⟨c.equivalence.inverse ⋙ (p.presentsLocalization S hW).E, inferInstance⟩

end CategoryTheory
