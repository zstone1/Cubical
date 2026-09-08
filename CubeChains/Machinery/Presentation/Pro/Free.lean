import CubeChains.Machinery.Presentation.ColimitCells

/-!
# Machinery/Presentation/Pro/Free — SCOPING PROTOTYPE: the free pro on a 3-polygraph

A **pro** is a 2-category with one 0-cell whose 1-cells are `(ℕ, +)`.  Its presentation device is a
3-polygraph: 1-cells the strand counts, 2-cells the generators, 3-cells the relations.  This file
builds the free 2-category on such a `ProGraph` and asks what the shift buys.

The answer is `unfold`: a 2-cell of the free 2-category is a word in **positioned** generators
(`Step`), and two words name one 2-cell exactly when the exchange law relates them.  So the free
pro *is* `(unfold P).presented` — a 2-polygraph again, with the exchange squares among its 2-cells.
Interchange is not ambient; it is `PiRel.interchange` moved inside the free construction.

Three things this file records, and they are the evidence for the verdict:

* `quot_exchange` — exchange holds for whole **words**, so a functor out of the free pro never has
  to send it anywhere.  That is the real gain, and it is local to the free construction.
* `whiskerRight_comp_heq` — every cell now carries a position and two `Nat` equations, and
  whiskering twice differs from whiskering once by `Nat.add_assoc`.  The 2-polygraph's 0-cells are
  a bare index set and carry none of this.
* `commuting_copies` — the exchange 2-cells are indexed by a **pair** of 1-cells, so `unfold` is
  quadratic in the generators and cannot commute with colimits.
-/

universe u

namespace CategoryTheory

namespace ProPrototype

/-! ## Positioned generators

A 2-cell of a pro sits inside a 1-cell, with idle strands on either side.  `l`, `a`, `b`, `r` are
that position; the two equations are the price of indexing a quiver by `ℕ`, whose `+` is
associative only propositionally, so a step cannot compute its own endpoints. -/

/-- A **positioned 2-generator**: `gen : Gen a b`, with `l` idle strands to its left and `r` to its
right, read as a 1-cell of the unfolded 2-polygraph. -/
structure Step (Gen : ℕ → ℕ → Type) (m n : ℕ) where
  /-- idle strands on the left -/
  l : ℕ
  /-- the generator's source width -/
  a : ℕ
  /-- …and its target width -/
  b : ℕ
  /-- idle strands on the right -/
  r : ℕ
  /-- the generator -/
  gen : Gen a b
  /-- the source count it spans -/
  src_eq : l + a + r = m
  /-- …and the target count -/
  tgt_eq : l + b + r = n

namespace Step

variable {Gen : ℕ → ℕ → Type} {m n : ℕ}

/-- **A step is its position and its generator** — the two equations are `Prop`s, so a comparison
of steps over different counts is still only the four numbers and the generator. -/
theorem mk_heq_mk {m n m' n' l a b r l' a' b' r' : ℕ} {g : Gen a b} {g' : Gen a' b'}
    {h₁ : l + a + r = m} {h₂ : l + b + r = n} {h₁' : l' + a' + r' = m'}
    {h₂' : l' + b' + r' = n'} (hm : m = m') (hn : n = n') (hl : l = l') (ha : a = a')
    (hb : b = b') (hr : r = r') (hg : g ≍ g') :
    (Step.mk l a b r g h₁ h₂ : Step Gen m n)
      ≍ (Step.mk l' a' b' r' g' h₁' h₂' : Step Gen m' n') := by
  subst hm; subst hn; subst hl; subst ha; subst hb; subst hr
  cases hg
  rfl

/-- `c` idle strands added on the right. -/
def whiskerRight (s : Step Gen m n) (c : ℕ) : Step Gen (m + c) (n + c) where
  l := s.l
  a := s.a
  b := s.b
  r := s.r + c
  gen := s.gen
  src_eq := by have h := s.src_eq; omega
  tgt_eq := by have h := s.tgt_eq; omega

/-- …and on the left. -/
def whiskerLeft (c : ℕ) (s : Step Gen m n) : Step Gen (c + m) (c + n) where
  l := c + s.l
  a := s.a
  b := s.b
  r := s.r
  gen := s.gen
  src_eq := by have h := s.src_eq; omega
  tgt_eq := by have h := s.tgt_eq; omega

/-- **Whiskering twice is whiskering once, only up to `Nat.add_assoc`** — three transports, two of
them in the *type*, because `(m + c) + d` and `m + (c + d)` are equal only propositionally.  The
free pro's tensor is therefore not strict, and neither is any consumer of it. -/
theorem whiskerRight_comp_heq (s : Step Gen m n) (c d : ℕ) :
    (s.whiskerRight c).whiskerRight d ≍ s.whiskerRight (c + d) := by
  obtain ⟨l, a, b, r, g, h₁, h₂⟩ := s
  exact mk_heq_mk (Nat.add_assoc m c d) (Nat.add_assoc n c d) rfl rfl rfl
    (Nat.add_assoc r c d) HEq.rfl

end Step

/-! ## The unfolded 2-polygraph -/

/-- The positioned generators, as a prefunctor adding `c` idle strands on the right. -/
def whiskerRightPre (Gen : ℕ → ℕ → Type) (c : ℕ) :
    GenObj (Step Gen) ⥤q GenObj (Step Gen) where
  obj x := ⟨x.as + c⟩
  map {_ _} s := s.whiskerRight c

/-- …and on the left. -/
def whiskerLeftPre (Gen : ℕ → ℕ → Type) (c : ℕ) :
    GenObj (Step Gen) ⥤q GenObj (Step Gen) where
  obj x := ⟨c + x.as⟩
  map {_ _} s := Step.whiskerLeft c s

/-- **A 3-polygraph with one 0-cell whose 1-cells are `(ℕ, +)`**: 2-cells `Gen a b`, 3-cells `Rel`
with a source and a target 2-cell of the free 2-category — i.e. a word of positioned generators. -/
structure ProGraph where
  /-- the 2-cells -/
  Gen : ℕ → ℕ → Type
  /-- the 3-cells -/
  Rel : ℕ → ℕ → Type
  /-- a 3-cell's source 2-cell -/
  src : ∀ {m n : ℕ}, Rel m n → Quiver.Path (⟨m⟩ : GenObj (Step Gen)) ⟨n⟩
  /-- …and its target -/
  tgt : ∀ {m n : ℕ}, Rel m n → Quiver.Path (⟨m⟩ : GenObj (Step Gen)) ⟨n⟩

/-- **The 2-cells of the unfolded polygraph**: the exchange squares, and the 3-cells in every
position.  `exch` is indexed by a *pair* of 1-cells — the fact that makes `unfold` quadratic. -/
inductive UnfoldRel (P : ProGraph) : GenObj (Step P.Gen) → GenObj (Step P.Gen) → Type
  /-- two generators in disjoint blocks commute -/
  | exch {m m' n n' : ℕ} (s : Step P.Gen m m') (t : Step P.Gen n n') :
      UnfoldRel P ⟨m + n⟩ ⟨m' + n'⟩
  /-- a 3-cell, positioned -/
  | cell (l r : ℕ) {m n : ℕ} (α : P.Rel m n) :
      UnfoldRel P ⟨l + (m + r)⟩ ⟨l + (n + r)⟩

namespace UnfoldRel

variable {P : ProGraph}

/-- The source word of a 2-cell of the unfolded polygraph. -/
def src : ∀ {x y : GenObj (Step P.Gen)}, UnfoldRel P x y → Quiver.Path x y
  | _, _, .exch s t =>
      (Quiver.Hom.toPath (s.whiskerRight _)).comp (Quiver.Hom.toPath (Step.whiskerLeft _ t))
  | _, _, .cell l r α =>
      (whiskerLeftPre _ l).mapPath ((whiskerRightPre _ r).mapPath (P.src α))

/-- …and its target. -/
def tgt : ∀ {x y : GenObj (Step P.Gen)}, UnfoldRel P x y → Quiver.Path x y
  | _, _, .exch s t =>
      (Quiver.Hom.toPath (Step.whiskerLeft _ t)).comp (Quiver.Hom.toPath (s.whiskerRight _))
  | _, _, .cell l r α =>
      (whiskerLeftPre _ l).mapPath ((whiskerRightPre _ r).mapPath (P.tgt α))

end UnfoldRel

/-- **The free 2-category on a pro-graph, as a 2-polygraph**: 0-cells the strand counts, 1-cells
the positioned generators, 2-cells the exchange squares and the positioned 3-cells. -/
def unfold (P : ProGraph) : Polygraph.{0, 0, 0} where
  V := ℕ
  Gen := Step P.Gen
  Rel := UnfoldRel P
  src := UnfoldRel.src
  tgt := UnfoldRel.tgt

/-- The free pro's 2-cells: words of positioned generators, modulo exchange and the 3-cells. -/
abbrev freePro (P : ProGraph) : Type := (unfold P).presented

/-! ## Exchange is a theorem about words

The one real gain of the shift: a functor out of the free pro never has to send interchange
anywhere, because `quot_exchange` holds for whole words.  It costs a double induction, once. -/

section Words

variable {P : ProGraph}

/-- A word extended by a letter, read as a composite. -/
theorem mapPath_cons' {V : Type*} [Quiver V] {W : Type*} [Quiver W] (F : V ⥤q W)
    {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c) :
    F.mapPath (p.cons e) = (F.mapPath p).comp (F.map e).toPath := by
  rw [Prefunctor.mapPath_cons, Quiver.Path.comp_toPath_eq_cons]

/-- Postcomposing a word preserves an equation of words in `presented`. -/
theorem quot_comp_congr {x y z : GenObj (Step P.Gen)} (r : Quiver.Path x y)
    {p q : Quiver.Path y z} (h : (unfold P).quot.map p = (unfold P).quot.map q) :
    (unfold P).quot.map (r.comp p) = (unfold P).quot.map (r.comp q) :=
  (((unfold P).quot.map_comp r p).trans
      (congrArg (fun f => (unfold P).quot.map r ≫ f) h)).trans
    ((unfold P).quot.map_comp r q).symm

/-- …and so does precomposing one. -/
theorem quot_congr_comp {x y z : GenObj (Step P.Gen)} {p q : Quiver.Path x y}
    (h : (unfold P).quot.map p = (unfold P).quot.map q) (r : Quiver.Path y z) :
    (unfold P).quot.map (p.comp r) = (unfold P).quot.map (q.comp r) :=
  (((unfold P).quot.map_comp p r).trans
      (congrArg (fun f => f ≫ (unfold P).quot.map r) h)).trans
    ((unfold P).quot.map_comp q r).symm

/-- **Exchange, on two generators** — the 2-cell `UnfoldRel.exch`, and nothing else. -/
theorem quot_exchange_gen {x y z w : GenObj (Step P.Gen)} (s : x ⟶ y) (t : z ⟶ w) :
    (unfold P).quot.map
        ((Quiver.Hom.toPath ((whiskerRightPre P.Gen z.as).map s)).comp
          (Quiver.Hom.toPath ((whiskerLeftPre P.Gen y.as).map t)))
      = (unfold P).quot.map
        ((Quiver.Hom.toPath ((whiskerLeftPre P.Gen x.as).map t)).comp
          (Quiver.Hom.toPath ((whiskerRightPre P.Gen w.as).map s))) :=
  (unfold P).quot_src_tgt (UnfoldRel.exch s t)

/-- **Exchange, a generator against a word.** -/
theorem quot_exchange_gen_word {x y : GenObj (Step P.Gen)} (s : x ⟶ y) :
    ∀ {z w : GenObj (Step P.Gen)} (v : Quiver.Path z w),
      (unfold P).quot.map
          ((Quiver.Hom.toPath ((whiskerRightPre P.Gen z.as).map s)).comp
            ((whiskerLeftPre P.Gen y.as).mapPath v))
        = (unfold P).quot.map
          (((whiskerLeftPre P.Gen x.as).mapPath v).comp
            (Quiver.Hom.toPath ((whiskerRightPre P.Gen w.as).map s))) := by
  intro z w v
  induction v with
  | nil => exact congrArg (unfold P).quot.map (Quiver.Path.nil_comp _).symm
  | @cons k w v' e ih =>
      have p₁ : (Quiver.Hom.toPath ((whiskerRightPre P.Gen z.as).map s)).comp
            ((whiskerLeftPre P.Gen y.as).mapPath (v'.cons e))
          = ((Quiver.Hom.toPath ((whiskerRightPre P.Gen z.as).map s)).comp
              ((whiskerLeftPre P.Gen y.as).mapPath v')).comp
            (Quiver.Hom.toPath ((whiskerLeftPre P.Gen y.as).map e)) := by
        rw [mapPath_cons']
        exact (Quiver.Path.comp_assoc _ _ _).symm
      have p₂ : ((whiskerLeftPre P.Gen x.as).mapPath (v'.cons e)).comp
            (Quiver.Hom.toPath ((whiskerRightPre P.Gen w.as).map s))
          = ((whiskerLeftPre P.Gen x.as).mapPath v').comp
            ((Quiver.Hom.toPath ((whiskerLeftPre P.Gen x.as).map e)).comp
              (Quiver.Hom.toPath ((whiskerRightPre P.Gen w.as).map s))) := by
        rw [mapPath_cons', Quiver.Path.comp_assoc]
      rw [p₁, p₂]
      exact (quot_congr_comp ih _).trans
        ((congrArg (unfold P).quot.map (Quiver.Path.comp_assoc _ _ _)).trans
          (quot_comp_congr _ (quot_exchange_gen s e)))

/-- **Exchange, on whole words** — the ambient interchange law of the free pro.  A functor out of
`freePro P` has nothing to send it to, because it is an equation, not a cell. -/
theorem quot_exchange :
    ∀ {x y z w : GenObj (Step P.Gen)} (u : Quiver.Path x y) (v : Quiver.Path z w),
      (unfold P).quot.map
          (((whiskerRightPre P.Gen z.as).mapPath u).comp
            ((whiskerLeftPre P.Gen y.as).mapPath v))
        = (unfold P).quot.map
          (((whiskerLeftPre P.Gen x.as).mapPath v).comp
            ((whiskerRightPre P.Gen w.as).mapPath u)) := by
  intro x y z w u
  induction u with
  | nil => intro v; exact congrArg (unfold P).quot.map (Quiver.Path.nil_comp _)
  | @cons j y u' s ih =>
      intro v
      have p₁ : ((whiskerRightPre P.Gen z.as).mapPath (u'.cons s)).comp
            ((whiskerLeftPre P.Gen y.as).mapPath v)
          = ((whiskerRightPre P.Gen z.as).mapPath u').comp
            ((Quiver.Hom.toPath ((whiskerRightPre P.Gen z.as).map s)).comp
              ((whiskerLeftPre P.Gen y.as).mapPath v)) := by
        rw [mapPath_cons', Quiver.Path.comp_assoc]
      have p₂ : ((whiskerLeftPre P.Gen x.as).mapPath v).comp
            ((whiskerRightPre P.Gen w.as).mapPath (u'.cons s))
          = (((whiskerLeftPre P.Gen x.as).mapPath v).comp
              ((whiskerRightPre P.Gen w.as).mapPath u')).comp
            (Quiver.Hom.toPath ((whiskerRightPre P.Gen w.as).map s)) := by
        rw [mapPath_cons']
        exact (Quiver.Path.comp_assoc _ _ _).symm
      rw [p₁, p₂]
      exact (quot_comp_congr _ (quot_exchange_gen_word s v)).trans
        ((congrArg (unfold P).quot.map (Quiver.Path.comp_assoc _ _ _).symm).trans
          (quot_congr_comp (ih v) _))

end Words

/-! ## …and the cells it identifies are quadratic

`UnfoldRel.exch` ranges over **pairs** of 1-cells, so the 2-cells of `unfold P` are not a levelwise
construction on `P`'s cells.  Two generators from two different copies of a diagram acquire a
commutation that neither copy carries: `commuting_copies` is that identification at its smallest,
and it is why a colimit of pros is not the colimit of the underlying categories. -/

/-- One 2-generator, of width one. -/
def oneGen : ℕ → ℕ → Type := fun a b => PLift (a = 1 ∧ b = 1)

/-- The pro-graph with a single 2-generator and no 3-cells. -/
def onePro : ProGraph where
  Gen := oneGen
  Rel := fun _ _ => Empty
  src := fun e => e.elim
  tgt := fun e => e.elim

/-- The generator itself. -/
def oneGenCell : Step onePro.Gen 1 1 :=
  ⟨0, 1, 1, 0, ⟨⟨rfl, rfl⟩⟩, rfl, rfl⟩

/-- The generator in the left block of the 1-cell `2`. -/
def leftCopy : (⟨1 + 1⟩ : GenObj (Step onePro.Gen)) ⟶ ⟨1 + 1⟩ := oneGenCell.whiskerRight 1

/-- …and in the right block. -/
def rightCopy : (⟨1 + 1⟩ : GenObj (Step onePro.Gen)) ⟶ ⟨1 + 1⟩ := Step.whiskerLeft 1 oneGenCell

/-- **The two copies of one generator commute in the free pro.**  The free *category* on the same
1-cells does not identify them: the identification is created by `UnfoldRel.exch`, whose index is a
pair.  So `unfold` is quadratic and does not commute with colimits — a colimit of pros identifies
generators from different copies that the colimit of the underlying categories keeps apart. -/
theorem commuting_copies :
    (unfold onePro).quot.map
        ((Quiver.Hom.toPath leftCopy).comp (Quiver.Hom.toPath rightCopy))
      = (unfold onePro).quot.map
        ((Quiver.Hom.toPath rightCopy).comp (Quiver.Hom.toPath leftCopy)) :=
  (unfold onePro).quot_src_tgt (UnfoldRel.exch oneGenCell oneGenCell)

end ProPrototype

end CategoryTheory
