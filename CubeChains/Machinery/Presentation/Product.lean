import CubeChains.Machinery.Presentation.Basic
import Mathlib.CategoryTheory.Products.Basic

/-!
# Machinery/Presentation/Product — the product of polygraphs

`Polygraph.prod P Q` has 0-cells `P.V × Q.V` and, at each of them, a copy of `P`'s 1-cells with the
`Q`-coordinate frozen and a copy of `Q`'s with the `P`-coordinate frozen (`ProdGen`, an indexed
inductive, so no transport is ever spelled).

**The 2-cells are not just the two copies' 2-cells.**  `ProdRel.interchange` imposes
`(g, 1) · (1, h) = (1, h) · (g, 1)` for every pair of 1-cells; without it the two families of
generators could never move past each other and the words would present a free product.  It is
exactly what makes `exists_normalForm` — every word is a `P`-word then a `Q`-word — true, and that
normal form is the whole completeness argument.

A bare `Quiver.Path` does not tell Lean which category its `≫` lives in, so every statement below
keeps its words inside `quot.map` or `Paths.lift`, where the argument type pins it.
-/

universe wp wq up uq w₂p w₂q va vb ua ub

namespace CategoryTheory

namespace Polygraph

variable (P : Polygraph.{wp, up, w₂p}) (Q : Polygraph.{wq, uq, w₂q})

/-- 1-cells of a product: one of `P` at a frozen 0-cell of `Q`, or one of `Q` at a frozen 0-cell
of `P`. -/
inductive ProdGen : P.V × Q.V → P.V × Q.V → Type (max wp wq up uq)
  | left {x x' : P.V} (g : P.Gen x x') (y : Q.V) : ProdGen (x, y) (x', y)
  | right (x : P.V) {y y' : Q.V} (h : Q.Gen y y') : ProdGen (x, y) (x, y')

/-- A `P`-generator as a one-letter word, at a frozen 0-cell of `Q`. -/
abbrev leftLetter (y : Q.V) {x x' : P.V} (g : P.Gen x x') :
    Quiver.Path (⟨(x, y)⟩ : GenObj (ProdGen P Q)) ⟨(x', y)⟩ :=
  Quiver.Hom.toPath (ProdGen.left g y)

/-- A `Q`-generator as a one-letter word, at a frozen 0-cell of `P`. -/
abbrev rightLetter (x : P.V) {y y' : Q.V} (h : Q.Gen y y') :
    Quiver.Path (⟨(x, y)⟩ : GenObj (ProdGen P Q)) ⟨(x, y')⟩ :=
  Quiver.Hom.toPath (ProdGen.right x h)

/-- The copy of `P` at a 0-cell of `Q`. -/
abbrev prodLeft (y : Q.V) : GenObj P.Gen ⥤q GenObj (ProdGen P Q) where
  obj x := ⟨(x.as, y)⟩
  map g := ProdGen.left g y

/-- The copy of `Q` at a 0-cell of `P`. -/
abbrev prodRight (x : P.V) : GenObj Q.Gen ⥤q GenObj (ProdGen P Q) where
  obj y := ⟨(x, y.as)⟩
  map h := ProdGen.right x h

/-- 2-cells of a product: each copy's own, **and** the interchange squares. -/
inductive ProdRel : GenObj (ProdGen P Q) → GenObj (ProdGen P Q) → Type (max wp wq up uq w₂p w₂q)
  | left (y : Q.V) {x x' : GenObj P.Gen} :
      P.Rel x x' → ProdRel ((prodLeft P Q y).obj x) ((prodLeft P Q y).obj x')
  | right (x : P.V) {y y' : GenObj Q.Gen} :
      Q.Rel y y' → ProdRel ((prodRight P Q x).obj y) ((prodRight P Q x).obj y')
  | interchange {x x' : P.V} {y y' : Q.V} (g : P.Gen x x') (h : Q.Gen y y') :
      ProdRel ⟨(x, y)⟩ ⟨(x', y')⟩

/-- The source of a product 2-cell: a copy's own, included, or a side of the interchange square. -/
def ProdRel.src : ∀ {a b : GenObj (ProdGen P Q)}, ProdRel P Q a b → Quiver.Path a b
  | _, _, .left y α => (prodLeft P Q y).mapPath (P.src α)
  | _, _, .right x α => (prodRight P Q x).mapPath (Q.src α)
  | _, _, .interchange (y := y) (x' := x') g h => (leftLetter P Q y g).comp (rightLetter P Q x' h)

/-- The target of a product 2-cell: the other corner. -/
def ProdRel.tgt : ∀ {a b : GenObj (ProdGen P Q)}, ProdRel P Q a b → Quiver.Path a b
  | _, _, .left y α => (prodLeft P Q y).mapPath (P.tgt α)
  | _, _, .right x α => (prodRight P Q x).mapPath (Q.tgt α)
  | _, _, .interchange (x := x) (y' := y') g h => (rightLetter P Q x h).comp (leftLetter P Q y' g)

/-- **The product of polygraphs.** -/
def prod : Polygraph.{max wp wq up uq, max up uq, max wp wq up uq w₂p w₂q} where
  V := P.V × Q.V
  Gen := ProdGen P Q
  Rel := ProdRel P Q
  src := ProdRel.src P Q
  tgt := ProdRel.tgt P Q

/-- The copy of `P` at a 0-cell of `Q`, as a morphism of polygraphs. -/
def prodInl (y : Q.V) : Hom P (prod P Q) where
  pre := prodLeft P Q y
  two α := ProdRel.left y α
  src_two _ := rfl
  tgt_two _ := rfl

/-- The copy of `Q` at a 0-cell of `P`, as a morphism of polygraphs. -/
def prodInr (x : P.V) : Hom Q (prod P Q) where
  pre := prodRight P Q x
  two α := ProdRel.right x α
  src_two _ := rfl
  tgt_two _ := rfl

/-! ## Interchange, propagated to words

Every statement here keeps a whole word inside one `quot.map`, and every step goes through
`quot_comp_congr`, whose 0-cells are variables.  Splitting a word with `Functor.map_comp` instead
pins the middle 0-cell to whichever of its two defeq spellings the elaborator happened to pick,
and then nothing matches. -/

/-- Congruence of `presented` under composition of words. -/
theorem quot_comp_congr {a b c : (prod P Q).Word} {A A' : a ⟶ b} {B B' : b ⟶ c}
    (hA : (prod P Q).quot.map A = (prod P Q).quot.map A')
    (hB : (prod P Q).quot.map B = (prod P Q).quot.map B') :
    (prod P Q).quot.map (A ≫ B) = (prod P Q).quot.map (A' ≫ B') := by
  rw [Functor.map_comp, Functor.map_comp, hA, hB]

/-- The last letter of a word, split off — with the 0-cells left as variables. -/
theorem quot_cons {a b c : GenObj (ProdGen P Q)} (w : Quiver.Path a b) (e : b ⟶ c) :
    (prod P Q).quot.map (w.cons e) = (prod P Q).quot.map (w ≫ Quiver.Hom.toPath e) := rfl

/-- **The interchange square**, as an equation of arrows. -/
theorem quot_interchange {x x' : P.V} {y y' : Q.V} (g : P.Gen x x') (h : Q.Gen y y') :
    (prod P Q).quot.map (leftLetter P Q y g ≫ rightLetter P Q x' h)
      = (prod P Q).quot.map (rightLetter P Q x h ≫ leftLetter P Q y' g) :=
  (prod P Q).quot_src_tgt (ProdRel.interchange g h)

/-- A `Q`-word commutes past a `P`-generator — the interchange square, iterated. -/
theorem quot_word_comm {x x' : P.V} (g : P.Gen x x') {y₀ y : GenObj Q.Gen}
    (v : Quiver.Path y₀ y) :
    (prod P Q).quot.map ((prodRight P Q x).mapPath v ≫ leftLetter P Q y.as g)
      = (prod P Q).quot.map (leftLetter P Q y₀.as g ≫ (prodRight P Q x').mapPath v) := by
  induction v with
  | nil =>
      change (prod P Q).quot.map (𝟙 _ ≫ leftLetter P Q y₀.as g)
        = (prod P Q).quot.map (leftLetter P Q y₀.as g ≫ 𝟙 _)
      rw [Category.id_comp, Category.comp_id]
  | @cons y₁ y₂ v h ih =>
      change (prod P Q).quot.map
          (((prodRight P Q x).mapPath v ≫ rightLetter P Q x h) ≫ leftLetter P Q y₂.as g) = _
      rw [Category.assoc]
      refine (quot_comp_congr P Q rfl (quot_interchange P Q g h).symm).trans ?_
      rw [← Category.assoc]
      exact (quot_comp_congr P Q ih rfl).trans (by rw [Category.assoc]; rfl)

/-- **Every word of the product is a `P`-word then a `Q`-word.**  This is what the interchange
2-cells buy, and it is the whole of `Presents.prod`'s completeness. -/
theorem exists_normalForm {a b : GenObj (ProdGen P Q)} (w : Quiver.Path a b) :
    ∃ (u : Quiver.Path (⟨a.as.1⟩ : GenObj P.Gen) ⟨b.as.1⟩)
      (v : Quiver.Path (⟨a.as.2⟩ : GenObj Q.Gen) ⟨b.as.2⟩),
      (prod P Q).quot.map w = (prod P Q).quot.map
        ((prodLeft P Q a.as.2).mapPath u ≫ (prodRight P Q b.as.1).mapPath v) := by
  induction w with
  | nil => exact ⟨Quiver.Path.nil, Quiver.Path.nil, rfl⟩
  | @cons m n w e ih =>
      obtain ⟨⟨n1, n2⟩⟩ := n
      obtain ⟨⟨m1, m2⟩⟩ := m
      obtain ⟨u, v, hw⟩ := ih
      cases e with
      | left g =>
          refine ⟨u.cons g, v, ?_⟩
          rw [quot_cons]
          refine (quot_comp_congr P Q hw rfl).trans ?_
          rw [Category.assoc]
          refine (quot_comp_congr P Q rfl (quot_word_comm P Q g v)).trans ?_
          rw [← Category.assoc]
          rfl
      | right =>
          rename_i h
          refine ⟨u, v.cons h, ?_⟩
          rw [quot_cons]
          refine (quot_comp_congr P Q hw rfl).trans ?_
          rw [Category.assoc]
          rfl

end Polygraph

namespace Presents

variable {P : Polygraph.{wp, up, w₂p}} {Q : Polygraph.{wq, uq, w₂q}}
  {A : Type ua} [Category.{va} A] {B : Type ub} [Category.{vb} B]
  (p : Presents P A) (q : Presents Q B)

/-- The arrow a 1-cell of the product names: one factor's arrow, the identity on the other. -/
def prodArrow : ∀ (a b : P.V × Q.V), Polygraph.ProdGen P Q a b →
    (((p.at' ⟨a.1⟩, q.at' ⟨a.2⟩) : A × B) ⟶ (p.at' ⟨b.1⟩, q.at' ⟨b.2⟩))
  | _, _, .left g _ => ⟨p.arrow g, 𝟙 _⟩
  | _, _, .right _ h => ⟨𝟙 _, q.arrow h⟩

/-- The cells of the product, interpreted in the product category. -/
def prodEval : GenObj (Polygraph.ProdGen P Q) ⥤q (A × B) where
  obj z := (p.at' ⟨z.as.1⟩, q.at' ⟨z.as.2⟩)
  map e := prodArrow p q _ _ e

/-- A `P`-word, evaluated in the product. -/
theorem prodEval_left (y : Q.V) {x x' : GenObj P.Gen} (u : Quiver.Path x x') :
    (Paths.lift (prodEval p q)).map ((Polygraph.prodLeft P Q y).mapPath u)
      = (Prod.sectL A (q.at' ⟨y⟩)).map (p.eval.map u) := by
  rw [Paths.lift_mapPath]
  exact p.lift_evalPre_comp (Prod.sectL A (q.at' ⟨y⟩)) u

/-- A `Q`-word, evaluated in the product. -/
theorem prodEval_right (x : P.V) {y y' : GenObj Q.Gen} (v : Quiver.Path y y') :
    (Paths.lift (prodEval p q)).map ((Polygraph.prodRight P Q x).mapPath v)
      = (Prod.sectR (p.at' ⟨x⟩) B).map (q.eval.map v) := by
  rw [Paths.lift_mapPath]
  exact q.lift_evalPre_comp (Prod.sectR (p.at' ⟨x⟩) B) v

/-- **A normal form, evaluated**: the two coordinates, side by side. -/
theorem prodEval_normalForm {x x' : GenObj P.Gen} {y y' : GenObj Q.Gen}
    (u : Quiver.Path x x') (v : Quiver.Path y y') :
    (Paths.lift (prodEval p q)).map ((Polygraph.prodLeft P Q y.as).mapPath u)
        ≫ (Paths.lift (prodEval p q)).map ((Polygraph.prodRight P Q x'.as).mapPath v)
      = (p.eval.map u, q.eval.map v) := by
  rw [prodEval_left, prodEval_right]
  exact Prod.hom_ext (Category.comp_id _) (Category.id_comp _)

theorem prod_sound {a b : GenObj (Polygraph.ProdGen P Q)} (α : (Polygraph.prod P Q).Rel a b) :
    (Paths.lift (prodEval p q)).map ((Polygraph.prod P Q).src α)
      = (Paths.lift (prodEval p q)).map ((Polygraph.prod P Q).tgt α) := by
  cases α with
  | left y α =>
      change (Paths.lift (prodEval p q)).map ((Polygraph.prodLeft P Q y).mapPath (P.src α))
        = (Paths.lift (prodEval p q)).map ((Polygraph.prodLeft P Q y).mapPath (P.tgt α))
      rw [prodEval_left, prodEval_left]
      exact congrArg _ (p.sound α)
  | right x α =>
      change (Paths.lift (prodEval p q)).map ((Polygraph.prodRight P Q x).mapPath (Q.src α))
        = (Paths.lift (prodEval p q)).map ((Polygraph.prodRight P Q x).mapPath (Q.tgt α))
      rw [prodEval_right, prodEval_right]
      exact congrArg _ (q.sound α)
  | interchange g h =>
      change (Paths.lift (prodEval p q)).map
            (Polygraph.leftLetter P Q _ g ≫ Polygraph.rightLetter P Q _ h)
          = (Paths.lift (prodEval p q)).map
            (Polygraph.rightLetter P Q _ h ≫ Polygraph.leftLetter P Q _ g)
      rw [Functor.map_comp, Functor.map_comp, Paths.lift_toPath, Paths.lift_toPath,
        Paths.lift_toPath, Paths.lift_toPath]
      exact Prod.hom_ext ((Category.comp_id _).trans (Category.id_comp _).symm)
        ((Category.id_comp _).trans (Category.comp_id _).symm)

theorem prod_complete {a b : GenObj (Polygraph.ProdGen P Q)} {u v : Quiver.Path a b}
    (h : (Paths.lift (prodEval p q)).map u = (Paths.lift (prodEval p q)).map v) :
    (Polygraph.prod P Q).quot.map u = (Polygraph.prod P Q).quot.map v := by
  obtain ⟨u₁, u₂, hu⟩ := Polygraph.exists_normalForm P Q u
  obtain ⟨v₁, v₂, hv⟩ := Polygraph.exists_normalForm P Q v
  have eval_of (w : Quiver.Path a b) {w₁ : Quiver.Path (⟨a.as.1⟩ : GenObj P.Gen) ⟨b.as.1⟩}
      {w₂ : Quiver.Path (⟨a.as.2⟩ : GenObj Q.Gen) ⟨b.as.2⟩}
      (hw : (Polygraph.prod P Q).quot.map w = (Polygraph.prod P Q).quot.map
        ((Polygraph.prodLeft P Q a.as.2).mapPath w₁
          ≫ (Polygraph.prodRight P Q b.as.1).mapPath w₂)) :
      (Paths.lift (prodEval p q)).map w = (p.eval.map w₁, q.eval.map w₂) :=
    (Polygraph.lift_map_eq_of_quot_eq (prodEval p q) (prod_sound p q) hw).trans
      ((Functor.map_comp _ _ _).trans (prodEval_normalForm p q w₁ w₂))
  have key := (eval_of u hu).symm.trans (h.trans (eval_of v hv))
  have hP : p.E.map (P.quot.map u₁) = p.E.map (P.quot.map v₁) := congrArg _root_.Prod.fst key
  have hQ : q.E.map (Q.quot.map u₂) = q.E.map (Q.quot.map v₂) := congrArg _root_.Prod.snd key
  rw [hu, hv]
  exact Polygraph.quot_comp_congr P Q
    ((Polygraph.prodInl P Q a.as.2).quot_map_congr (p.E.map_injective hP))
    ((Polygraph.prodInr P Q b.as.1).quot_map_congr (q.E.map_injective hQ))

theorem prod_full : (Paths.lift (prodEval p q)).Full where
  map_surjective := by
    rintro ⟨⟨x, y⟩⟩ ⟨⟨x', y'⟩⟩ ⟨f, k⟩
    obtain ⟨u, hu⟩ : ∃ u : Quiver.Path (⟨x⟩ : GenObj P.Gen) ⟨x'⟩, p.eval.map u = f :=
      p.eval.map_surjective f
    obtain ⟨v, hv⟩ : ∃ v : Quiver.Path (⟨y⟩ : GenObj Q.Gen) ⟨y'⟩, q.eval.map v = k :=
      q.eval.map_surjective k
    refine ⟨(Polygraph.prodLeft P Q y).mapPath u ≫ (Polygraph.prodRight P Q x').mapPath v, ?_⟩
    rw [Functor.map_comp, prodEval_normalForm, hu, hv]
    rfl

theorem prod_essSurj : (Paths.lift (prodEval p q)).EssSurj where
  mem_essImage := by
    rintro ⟨a, b⟩
    obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := p.eval) a
    obtain ⟨y, ⟨e'⟩⟩ := Functor.EssSurj.mem_essImage (F := q.eval) b
    exact ⟨⟨(x.as, y.as)⟩, ⟨Iso.prod e e'⟩⟩

/-- **Two presentations present the product** — the interchange 2-cells are exactly what stops the
words from presenting a free product. -/
def prod : Presents (Polygraph.prod P Q) (A × B) :=
  Presents.ofDesc (prodEval p q) (prod_sound p q) (prod_complete p q) (prod_full p q)
    (prod_essSurj p q)

end Presents

end CategoryTheory
