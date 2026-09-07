import CubeChains.Machinery.Presentation.Basic

/-!
# Machinery/Presentation/Opposite — a polygraph reversed

A presentation of `C` is *not* a presentation of `Cᵒᵖ`: a word composes source-first, so comparing
one with the other means reversing words.  `Polygraph.op` does that — same 0-cells, 1-cells
reversed, and a 2-cell read on the reversed words — and `Presents.op` carries a presentation across.

Reversal is a bijection on words, so nothing is lost: it is an involution, which is what turns a
chain of rewrites downstairs into one upstairs (`quot_map_of_rev`).

Two spelling rules the file obeys, both forced.  `revPath` is `Quiver.Path.rec` and not the equation
compiler: the motive is the *reversed* hom-type, and only the eliminator gives definitional
equations.  And every statement that composes reversed words uses `revWord`, whose declared type
names its endpoints in `P.Word`: an anonymous constructor ascribed to `P.Word` still gets type
`GenObj P.Gen`, where `≫` has no instance.
-/

universe v w w' u u' u'' w₂ w₂'

namespace CategoryTheory

namespace Polygraph

/-! ## Reversing words -/

section Raw

variable {V : Type u'} {Gen : V → V → Type w}

/-- The generating quiver, reversed.  Reducible: `opGen (opGen Gen)` is `Gen` only up to unfolding,
and every statement about a twice-reversed word needs `rw` to see that. -/
@[reducible] def opGen (Gen : V → V → Type w) : V → V → Type w := fun a b => Gen b a

/-- A 1-cell, read in the reversed quiver.  Definitionally the identity; it exists only to fix the
spelling of the endpoints. -/
@[reducible] def opHom {x y : GenObj (opGen Gen)} (e : x ⟶ y) :
    (⟨y.as⟩ : GenObj Gen) ⟶ ⟨x.as⟩ := e

/-- **A word of the reversed quiver, read backwards.** -/
def revPath {x : GenObj (opGen Gen)} :
    ∀ {y : GenObj (opGen Gen)}, Quiver.Path x y → Quiver.Path (⟨y.as⟩ : GenObj Gen) ⟨x.as⟩ :=
  fun {_} u =>
    Quiver.Path.rec (motive := fun {y} _ => Quiver.Path (⟨y.as⟩ : GenObj Gen) ⟨x.as⟩)
      Quiver.Path.nil (fun {_ _} _ e ih => (Quiver.Hom.toPath (opHom e)).comp ih) u

@[simp] theorem revPath_nil (x : GenObj (opGen Gen)) :
    revPath (Quiver.Path.nil : Quiver.Path x x) = Quiver.Path.nil := rfl

theorem revPath_cons {x y z : GenObj (opGen Gen)} (u : Quiver.Path x y) (e : y ⟶ z) :
    revPath (u.cons e) = (Quiver.Hom.toPath (opHom e)).comp (revPath u) := rfl

@[simp] theorem revPath_toPath {x y : GenObj (opGen Gen)} (e : x ⟶ y) :
    revPath (Quiver.Hom.toPath e) = Quiver.Hom.toPath (opHom e) := rfl

theorem revPath_comp {x y z : GenObj (opGen Gen)} (u : Quiver.Path x y) (v : Quiver.Path y z) :
    revPath (u.comp v) = (revPath v).comp (revPath u) := by
  induction v with
  | nil => rw [Quiver.Path.comp_nil, revPath_nil, Quiver.Path.nil_comp]
  | cons v e ih =>
      rw [Quiver.Path.comp_cons, revPath_cons, revPath_cons, ih, Quiver.Path.comp_assoc]

/-- **Reversal is an involution** — `opGen (opGen Gen)` is `Gen`, so the two readings compose. -/
theorem revPath_revPath {x y : GenObj (opGen Gen)} (u : Quiver.Path x y) :
    revPath (revPath u) = u := by
  induction u with
  | nil => rfl
  | @cons b c u e ih =>
      refine (congrArg (fun t => revPath t) (revPath_cons u e)).trans ?_
      rw [revPath_comp, ih, revPath_toPath]
      exact (Quiver.Path.comp_cons u Quiver.Path.nil (opHom (opHom e))).trans
        (congrArg (fun w => w.cons (opHom (opHom e))) (Quiver.Path.comp_nil u))

end Raw

/-! ## The reversed polygraph -/

variable (P : Polygraph.{w, u', w₂})

/-- **A polygraph reversed**: the same 0-cells, the 1-cells turned round, and each 2-cell read on
the reversed words.  Reducible, so that `P.op.Gen` and `opGen P.Gen` are one spelling. -/
@[reducible] def op : Polygraph.{w, u', w₂} where
  V := P.V
  Gen := opGen P.Gen
  Rel x y := P.Rel ⟨y.as⟩ ⟨x.as⟩
  src α := revPath (Gen := opGen P.Gen) (P.src α)
  tgt α := revPath (Gen := opGen P.Gen) (P.tgt α)

/-- A 0-cell, as a word. -/
def wordPt (a : P.V) : P.Word := ⟨a⟩

/-- **A word of `P.op`, reversed** — the same function as `revPath`, with its endpoints named in
`P.Word` so that `≫` resolves on them. -/
def revWord {x y : P.op.Word} (u : x ⟶ y) : P.wordPt y.as ⟶ P.wordPt x.as := revPath u

theorem revWord_comp {x y z : P.op.Word} (u : x ⟶ y) (v : y ⟶ z) :
    P.revWord (u ≫ v) = P.revWord v ≫ P.revWord u := revPath_comp u v

theorem revWord_revWord {x y : P.op.Word} (u : x ⟶ y) : P.op.revWord (P.revWord u) = u :=
  revPath_revPath u

/-- …and the same, starting downstairs.  `P.op.op` is `P` only up to unfolding, so the two
directions are two statements. -/
theorem revWord_revWord' {X Y : P.Word} (U : X ⟶ Y) : P.revWord (P.op.revWord U) = U :=
  revPath_revPath (Gen := opGen P.Gen) U

theorem revWord_injective {x y : P.op.Word} :
    Function.Injective (P.revWord : (x ⟶ y) → _) :=
  Function.LeftInverse.injective P.revWord_revWord

/-- A 2-cell of `P.op` **is** a 2-cell of `P`; only its boundary is read backwards. -/
theorem revPath_op_src {x y : GenObj P.op.Gen} (α : P.op.Rel x y) :
    revPath (P.op.src α) = P.src α := P.revWord_revWord' _

theorem revPath_op_tgt {x y : GenObj P.op.Gen} (α : P.op.Rel x y) :
    revPath (P.op.tgt α) = P.tgt α := P.revWord_revWord' _

theorem op_homRel_iff {x y : P.op.Word} (u v : x ⟶ y) :
    P.op.homRel u v ↔ P.homRel (P.revWord u) (P.revWord v) := by
  constructor
  · rintro ⟨α, rfl, rfl⟩
    exact ⟨α, (P.revPath_op_src α).symm, (P.revPath_op_tgt α).symm⟩
  · rintro ⟨α, hu, hv⟩
    refine ⟨α, ?_, ?_⟩
    · change P.op.revWord (P.src α) = u
      rw [hu]; exact P.revWord_revWord u
    · change P.op.revWord (P.tgt α) = v
      rw [hv]; exact P.revWord_revWord v

/-- **A rewriting step downstairs is one upstairs, reversed.**  The endpoints are quantified
*inside* the conclusion so that `cases` sees `CompClosure`'s indices as variables. -/
theorem compClosure_rev {X Y : P.Word} {U U' : X ⟶ Y} (h : HomRel.CompClosure P.homRel U U') :
    ∀ {x y : P.op.Word}, P.wordPt y.as = X → P.wordPt x.as = Y → ∀ {u v : x ⟶ y},
      P.revWord u ≍ U → P.revWord v ≍ U' → HomRel.CompClosure P.op.homRel u v := by
  cases h with
  | intro a b f m₁ m₂ g hr =>
      rintro x y rfl rfl u v hu hv
      have hsplit : ∀ m : a ⟶ b, P.op.revWord (f ≫ m ≫ g)
          = P.op.revWord g ≫ P.op.revWord m ≫ P.op.revWord f := fun m =>
        ((P.op.revWord_comp f (m ≫ g)).trans
            (congrArg (fun t => t ≫ P.op.revWord f) (P.op.revWord_comp m g))).trans
          (Category.assoc _ _ _)
      have hback : ∀ m : a ⟶ b,
          P.revWord (P.op.revWord g ≫ P.op.revWord m ≫ P.op.revWord f) = f ≫ m ≫ g := fun m =>
        (congrArg (fun t => P.revWord t) (hsplit m).symm).trans (P.revWord_revWord' _)
      obtain rfl : u = P.op.revWord g ≫ P.op.revWord m₁ ≫ P.op.revWord f :=
        P.revWord_injective ((eq_of_heq hu).trans (hback m₁).symm)
      obtain rfl : v = P.op.revWord g ≫ P.op.revWord m₂ ≫ P.op.revWord f :=
        P.revWord_injective ((eq_of_heq hv).trans (hback m₂).symm)
      refine HomRel.CompClosure.intro _ _ (P.op.revWord g) (P.op.revWord m₁) (P.op.revWord m₂)
        (P.op.revWord f) ?_
      rw [P.op_homRel_iff, P.revWord_revWord' m₁, P.revWord_revWord' m₂]
      exact hr

/-- **A chain of rewrites downstairs lifts**, because reversal is a bijection on words: every term
of the chain is itself a reversed word. -/
theorem quot_map_of_rev {x y : P.op.Word} {u v : x ⟶ y}
    (h : P.quot.map (P.revWord u) = P.quot.map (P.revWord v)) :
    P.op.quot.map u = P.op.quot.map v := by
  refine (Quotient.functor_homRel_eq_compClosure_eqvGen P.op.homRel u v).mpr ?_
  have h' := (Quotient.functor_homRel_eq_compClosure_eqvGen P.homRel
    (P.revWord u) (P.revWord v)).mp h
  suffices H : ∀ U U' : P.wordPt y.as ⟶ P.wordPt x.as,
      Relation.EqvGen (@HomRel.CompClosure P.Word _ P.homRel _ _) U U' →
      ∀ u v : x ⟶ y, P.revWord u = U → P.revWord v = U' →
        Relation.EqvGen (@HomRel.CompClosure P.op.Word _ P.op.homRel x y) u v from
    H _ _ h' u v rfl rfl
  intro U U' hUU'
  induction hUU' with
  | rel U U' hr =>
      exact fun u v hu hv => Relation.EqvGen.rel _ _
        (P.compClosure_rev hr rfl rfl (heq_of_eq hu) (heq_of_eq hv))
  | refl U =>
      intro u v hu hv
      obtain rfl := P.revWord_injective (hu.trans hv.symm)
      exact Relation.EqvGen.refl _
  | symm U U' _ ih => exact fun u v hu hv => (ih v u hv hu).symm
  | trans U U' U'' _ _ ih₁ ih₂ =>
      intro u v hu hv
      exact Relation.EqvGen.trans _ _ _ (ih₁ u (P.op.revWord U') hu (P.revWord_revWord' U'))
        (ih₂ (P.op.revWord U') v (P.revWord_revWord' U') hv)

/-! ## Reversal is a functor

A morphism of polygraphs reverses: the same map in every dimension, with the boundary words read
backwards.  Every law is `rfl`, so the only content is that `mapPath` commutes with reversal. -/

section Functorial

variable {V : Type u'} {Gen : V → V → Type w} {V' : Type u''} {Gen' : V' → V' → Type w'}

/-- A map of generating quivers, reversed. -/
def opPre (π : GenObj Gen ⥤q GenObj Gen') : GenObj (opGen Gen) ⥤q GenObj (opGen Gen') where
  obj x := ⟨(π.obj ⟨x.as⟩).as⟩
  map {_ _} e := π.map (opHom e)

theorem opPre_mapPath (π : GenObj Gen ⥤q GenObj Gen') {a b : GenObj Gen}
    (u : Quiver.Path a b) :
    (opPre π).mapPath (revPath (Gen := opGen Gen) u)
      = revPath (Gen := opGen Gen') (π.mapPath u) := by
  induction u with
  | nil => rfl
  | cons u e ih =>
      rw [revPath_cons, Prefunctor.mapPath_comp, ih]
      rfl

end Functorial

namespace Hom

variable {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}}

/-- **A morphism of polygraphs, reversed.** -/
def op (F : Hom P Q) : Hom P.op Q.op where
  pre := opPre F.pre
  two α := F.two α
  src_two α := (congrArg (revPath (Gen := opGen Q.Gen)) (F.src_two α)).trans
    (opPre_mapPath F.pre (P.src α)).symm
  tgt_two α := (congrArg (revPath (Gen := opGen Q.Gen)) (F.tgt_two α)).trans
    (opPre_mapPath F.pre (P.tgt α)).symm

@[simp] theorem op_pre (F : Hom P Q) : (Hom.op F).pre = opPre F.pre := rfl

end Hom

/-- **Reversal, as a functor on polygraphs.** -/
def opFunctor : Polygraph.{w, u', w₂} ⥤ Polygraph.{w, u', w₂} where
  obj P := P.op
  map F := Hom.op F
  map_id _ := Hom.ext' rfl fun _ => HEq.rfl
  map_comp _ _ := Hom.ext' rfl fun _ => HEq.rfl

@[simp] theorem opFunctor_obj (P : Polygraph.{w, u', w₂}) : opFunctor.obj P = P.op := rfl

end Polygraph

/-! ## A presentation, reversed -/

namespace Presents

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C] (p : Presents P C)

open Polygraph

/-- The cells of `P.op`, read in `Cᵒᵖ`. -/
def opInterp : GenObj P.op.Gen ⥤q Cᵒᵖ where
  obj x := Opposite.op (p.at' ⟨x.as⟩)
  map {_ _} e := (p.arrow (opHom e)).op

/-- **A word of `P.op` names the reversed word's arrow.**  Stated on `Quiver.Path` over
`GenObj P.op.Gen`, which is the spelling `Presents.ofDesc` and `Paths.lift_cons` both use. -/
theorem lift_opInterp {x y : GenObj P.op.Gen} (u : Quiver.Path x y) :
    (Paths.lift p.opInterp).map u = (p.eval.map (revPath u)).op := by
  induction u with
  | nil => rw [Paths.lift_nil, revPath_nil, p.eval_nil]; rfl
  | @cons b c u e ih =>
      rw [Paths.lift_cons, ih, revPath_cons,
        show p.eval.map ((Quiver.Hom.toPath (opHom e)).comp (revPath u))
            = p.arrow (opHom e) ≫ p.eval.map (revPath u) from
          p.eval.map_comp (Quiver.Hom.toPath (opHom e)) (revPath u)]
      rfl

/-- **A presentation of `C` reverses to one of `Cᵒᵖ`** — the same 0-cells and 1-cells, the words
read backwards.  Nothing is chosen: reversal is a bijection. -/
def op : Presents P.op Cᵒᵖ :=
  Presents.ofDesc p.opInterp
    (fun α => by
      rw [lift_opInterp, lift_opInterp, P.revPath_op_src α, P.revPath_op_tgt α, p.sound α])
    (fun {_ _} {u v} h => Polygraph.quot_map_of_rev P (p.E.map_injective (Quiver.Hom.op_inj
      ((lift_opInterp p u).symm.trans (h.trans (lift_opInterp p v))))))
    { map_surjective := fun {_ _} f => by
        obtain ⟨u, hu⟩ := p.eval.map_surjective f.unop
        exact ⟨P.op.revWord u, (lift_opInterp p _).trans
          (((congrArg (fun t => (p.eval.map t).op) (P.revWord_revWord' u)).trans
            (congrArg Quiver.Hom.op hu)).trans (Quiver.Hom.op_unop f))⟩ }
    { mem_essImage := fun X => by
        obtain ⟨x, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := p.eval) X.unop
        exact ⟨⟨x.as⟩, ⟨(i.op).symm ≪≫ eqToIso (Opposite.op_unop X)⟩⟩ }

@[simp] theorem op_arrow {x y : GenObj P.op.Gen} (e : x ⟶ y) :
    p.op.arrow e = (p.arrow (opHom e)).op := Paths.lift_toPath p.opInterp e

end Presents

end CategoryTheory
