import CubeChains.Machinery.Presentation.Basic

/-!
# Machinery/Presentation/Opposite — a polygraph reversed

A presentation of `C` is *not* a presentation of `Cᵒᵖ`: a word composes source-first, so comparing
one with the other means reversing words.  `Polygraph.op` does that — same 0-cells, 1-cells
reversed, and a 2-cell read on the reversed words — and `Presents.op` carries a presentation across.
Reversal is an isomorphism onto the opposite word category (`revFunctor`) carrying one relation to
the other, so a chain of rewrites downstairs is one upstairs by `gen_pullbackRel`.

Two forced spellings.  `revPath` is `Quiver.Path.rec` and not the equation compiler: the motive is
the *reversed* hom-type, and only the eliminator gives definitional equations.  And every statement
composing reversed words uses `revWord`, whose declared type names its endpoints in `P.Word`: an
anonymous constructor ascribed to `P.Word` still gets type `GenObj P.Gen`, where `≫` has no
instance.
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

/-! ## Reversal, as an isomorphism of word categories

`revWord` is a bijection on words turning composition round, so it is a fully faithful functor into
the opposite word category carrying `P.op.homRel` to `P.homRel` reversed.  A fully faithful functor
reflects the congruence a relation generates (`gen_pullbackRel`), which is the whole of
`quot_map_of_rev`. -/

/-- **A word of `P.op`, as an arrow of the opposite word category.** -/
def revFunctor : P.op.Word ⥤ (P.Word)ᵒᵖ where
  obj x := Opposite.op (P.wordPt x.as)
  map u := (P.revWord u).op
  map_id _ := rfl
  map_comp u v := congrArg Quiver.Hom.op (P.revWord_comp u v)

instance : P.revFunctor.Faithful where
  map_injective h := P.revWord_injective (Quiver.Hom.op_inj h)

instance : P.revFunctor.Full where
  map_surjective {_ _} f :=
    ⟨P.op.revWord f.unop, congrArg Quiver.Hom.op (P.revWord_revWord' f.unop)⟩

theorem exists_revFunctor_obj (X : (P.Word)ᵒᵖ) : ∃ x : P.op.Word, P.revFunctor.obj x = X :=
  ⟨⟨X.unop.as⟩, rfl⟩

/-- **A chain of rewrites downstairs lifts**, because reversal is a bijection on words. -/
theorem quot_map_of_rev {x y : P.op.Word} {u v : x ⟶ y}
    (h : P.quot.map (P.revWord u) = P.quot.map (P.revWord v)) :
    P.op.quot.map u = P.op.quot.map v :=
  (HomRel.gen_iff_functor_map_eq P.op.homRel u v).mp
    (HomRel.Gen.mono (fun {_ _ a b} hr => (P.op_homRel_iff a b).mpr hr)
      (gen_pullbackRel P.revFunctor (HomRel.op P.homRel)
        (fun {_ _ X} _ _ => P.exists_revFunctor_obj X)
        (HomRel.Gen.op ((HomRel.gen_iff_functor_map_eq P.homRel _ _).mpr h))))

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
end Hom

/-- **Reversal, as a functor on polygraphs.** -/
def opFunctor : Polygraph.{w, u', w₂} ⥤ Polygraph.{w, u', w₂} where
  obj P := P.op
  map F := Hom.op F
  map_id _ := rfl
  map_comp _ _ := rfl
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
end Presents

end CategoryTheory
