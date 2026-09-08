import CubeChains.Machinery.Presentation.Product
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Basic

/-!
# Machinery/Presentation/Pi — the strictly associative model of the polygraph tensor

`Polygraph.prod` is a **tensor**, not a categorical product: it carries `ProdRel.interchange`
exactly so that `presented : (Polygraph, ⊗) ⥤ (Cat, ×)` is strong monoidal, which is `Presents.prod`.

`Polygraph.pi P` is that tensor over a finite index, in its strictly associative model: `(P ⊗ Q) ⊗ R`
has 0-cells `(V_P × V_Q) × V_R` and `P ⊗ (Q ⊗ R)` has `V_P × (V_Q × V_R)`, so a monoidal functor
into `⊗` carries coherence isos exactly where a consumer needs a strict `map_comp`.  A tuple over
the index removes them, as `List` models the free monoid where nested pairs do not.

Every cell pins its endpoint 0-cells by a **proposition** (`Shift`), never by a `Function.update` in
its index: `Function.update` does not reduce at a variable index, so an endpoint spelled that way
forces a transport at every composition.  With them free, no transport is ever spelled.
-/

universe t w u' v u w₂

namespace CategoryTheory

namespace Polygraph

variable {ι : Type t} [DecidableEq ι] (P : ι → Polygraph.{w, u', w₂})

/-- **Two tuples that differ only at `i`**, where they read `a` and `b`.  Every 1-cell of the tensor
is pinned this way, rather than by a `Function.update` in its index. -/
structure Shift (i : ι) (a b : (P i).V) (X Y : ∀ j, (P j).V) : Prop where
  /-- the source reads `a` at `i` -/
  src : X i = a
  /-- the target reads `b` at `i` -/
  tgt : Y i = b
  /-- and nothing else moves -/
  fix : ∀ j, j ≠ i → X j = Y j

namespace Shift

variable {P}

theorem symm {i : ι} {a b : (P i).V} {X Y : ∀ j, (P j).V} (h : Shift P i a b X Y) :
    Shift P i b a Y X :=
  ⟨h.tgt, h.src, fun j hj => (h.fix j hj).symm⟩

/-- **The target of a shift is the source updated.**  This is the one bridge to `Function.update`:
it turns a shift into an equation of tuples that `subst` can consume. -/
theorem eq_update {i : ι} {a b : (P i).V} {X Y : ∀ j, (P j).V} (h : Shift P i a b X Y) :
    Y = Function.update X i b :=
  funext fun j => if hj : j = i then by subst hj; rw [Function.update_self, h.tgt]
    else (h.fix j hj).symm.trans (Function.update_of_ne hj ..).symm

theorem self_eq_update {i : ι} {a b : (P i).V} {X Y : ∀ j, (P j).V} (h : Shift P i a b X Y) :
    X = Function.update X i a :=
  h.src ▸ (Function.update_eq_self i X).symm

/-- **A shift with equal ends is no shift at all.** -/
theorem eq_of {i : ι} {a : (P i).V} {X Y : ∀ j, (P j).V} (h : Shift P i a a X Y) : X = Y :=
  h.self_eq_update.trans h.eq_update.symm

theorem update {i : ι} {a b : (P i).V} {X : ∀ j, (P j).V} (h : X i = a) :
    Shift P i a b X (Function.update X i b) :=
  ⟨h, Function.update_self .., fun _ hj => (Function.update_of_ne hj ..).symm⟩

theorem betweenUpdates {i : ι} (b c : (P i).V) (X : ∀ j, (P j).V) :
    Shift P i b c (Function.update X i b) (Function.update X i c) :=
  ⟨Function.update_self .., Function.update_self ..,
    fun _ hj => (Function.update_of_ne hj ..).trans (Function.update_of_ne hj ..).symm⟩

end Shift

/-- 1-cells of the tensor: one factor's generator, every other coordinate frozen. -/
inductive PiGen : (∀ i, (P i).V) → (∀ i, (P i).V) → Type (max t u' w)
  | mk {X Y : ∀ j, (P j).V} (i : ι) {a b : (P i).V} (g : (P i).Gen a b) (hs : Shift P i a b X Y) :
      PiGen X Y

/-- A one-letter word. -/
abbrev piLetter {X Y : ∀ j, (P j).V} (i : ι) {a b : (P i).V} (g : (P i).Gen a b)
    (hs : Shift P i a b X Y) : Quiver.Path (⟨X⟩ : GenObj (PiGen P)) ⟨Y⟩ :=
  Quiver.Hom.toPath (PiGen.mk i g hs)

/-- The copy of `P i` at a frozen background `z`. -/
def piPre (i : ι) (z : ∀ j, (P j).V) : GenObj (P i).Gen ⥤q GenObj (PiGen P) where
  obj A := ⟨Function.update z i A.as⟩
  map {_ _} g := PiGen.mk i g (Shift.betweenUpdates _ _ z)

/-- **A factor's word, read with the other coordinates frozen.**  Both end tuples are free, pinned
only by a `Shift`; `piPath_nil` and `piPath_cons` are its whole interface, and `piPath_cons` leaves
the intermediate tuple free too, so no caller ever spells one. -/
def piPath (i : ι) : ∀ {A B : GenObj (P i).Gen}, Quiver.Path A B →
    ∀ (X Y : ∀ j, (P j).V), Shift P i A.as B.as X Y →
      Quiver.Path (⟨X⟩ : GenObj (PiGen P)) ⟨Y⟩
  | _, _, .nil, X, _, hs =>
      hs.eq_of ▸ (Quiver.Path.nil : Quiver.Path (⟨X⟩ : GenObj (PiGen P)) ⟨X⟩)
  | _, _, .cons (b := M) u e, X, Y, hs =>
      (piPath i u X (Function.update Y i M.as)
          ⟨hs.src, Function.update_self .., fun j hj =>
            (hs.fix j hj).trans (Function.update_of_ne hj ..).symm⟩).cons
        (PiGen.mk i e ⟨Function.update_self .., hs.tgt, fun j hj => Function.update_of_ne hj ..⟩)

@[simp] theorem piPath_nil (i : ι) {A : GenObj (P i).Gen} (X : ∀ j, (P j).V) (hs) :
    piPath P i (Quiver.Path.nil : Quiver.Path A A) X X hs = Quiver.Path.nil := by
  simp only [piPath]

/-- **The last letter of a factor's word, split off with the intermediate tuple left free.** -/
theorem piPath_cons (i : ι) {A M B : GenObj (P i).Gen} (u : Quiver.Path A M) (e : M ⟶ B)
    (X Y W : ∀ j, (P j).V) (hs) (hu : Shift P i A.as M.as X W) (he : Shift P i M.as B.as W Y) :
    piPath P i (u.cons e) X Y hs = (piPath P i u X W hu).cons (PiGen.mk i e he) := by
  obtain rfl : W = Function.update Y i M.as := he.symm.eq_update
  simp only [piPath]

/-- 2-cells of the tensor: a factor's own, **and** the interchange squares.  Without them the words
would present a free product rather than the product. -/
inductive PiRel : GenObj (PiGen P) → GenObj (PiGen P) → Type (max t u' w w₂)
  | factor {X Y : ∀ j, (P j).V} (i : ι) {A B : GenObj (P i).Gen} (α : (P i).Rel A B)
      (hs : Shift P i A.as B.as X Y) : PiRel ⟨X⟩ ⟨Y⟩
  | interchange {X M M' Y : ∀ k, (P k).V} {i j : ι} (hij : i ≠ j)
      {a a' : (P i).V} (g : (P i).Gen a a') {b b' : (P j).V} (h : (P j).Gen b b')
      (h₁ : Shift P i a a' X M) (h₂ : Shift P j b b' M Y)
      (h₃ : Shift P j b b' X M') (h₄ : Shift P i a a' M' Y) : PiRel ⟨X⟩ ⟨Y⟩

/-- The source of a 2-cell: the factor's source word, or the `i`-then-`j` side of the square. -/
def PiRel.src : ∀ {A B : GenObj (PiGen P)}, PiRel P A B → Quiver.Path A B
  | _, _, .factor i α hs => piPath P i ((P i).src α) _ _ hs
  | _, _, .interchange (i := i) (j := j) _ g h h₁ h₂ _ _ =>
      (piLetter P i g h₁).comp (piLetter P j h h₂)

/-- The target of a 2-cell: the factor's target word, or the `j`-then-`i` side of the square. -/
def PiRel.tgt : ∀ {A B : GenObj (PiGen P)}, PiRel P A B → Quiver.Path A B
  | _, _, .factor i α hs => piPath P i ((P i).tgt α) _ _ hs
  | _, _, .interchange (i := i) (j := j) _ g h _ _ h₃ h₄ =>
      (piLetter P j h h₃).comp (piLetter P i g h₄)

/-- **The tensor of a family of polygraphs**, in its strictly associative model. -/
def pi : Polygraph.{max t u' w, max t u', max t u' w w₂} where
  V := ∀ i, (P i).V
  Gen := PiGen P
  Rel := PiRel P
  src := PiRel.src P
  tgt := PiRel.tgt P

/-- **A factor's word at its own frozen background is that word, included.** -/
theorem piPath_eq_mapPath (i : ι) (z : ∀ j, (P j).V) : ∀ {A B : GenObj (P i).Gen}
    (u : Quiver.Path A B) (hs),
    piPath P i u (Function.update z i A.as) (Function.update z i B.as) hs
      = (piPre P i z).mapPath u := by
  intro A B u
  induction u with
  | nil => intro hs; exact piPath_nil P i _ _
  | @cons M B u e ih =>
      intro hs
      rw [piPath_cons P i u e _ _ (Function.update z i M.as) hs (Shift.betweenUpdates _ _ z)
        (Shift.betweenUpdates _ _ z), ih]
      rfl

/-- The copy of `P i` at a frozen background, as a morphism of polygraphs. -/
def piIncl (i : ι) (z : ∀ j, (P j).V) : Hom (P i) (pi P) where
  pre := piPre P i z
  two α := PiRel.factor i α (Shift.betweenUpdates _ _ z)
  src_two α := piPath_eq_mapPath P i z ((P i).src α) _
  tgt_two α := piPath_eq_mapPath P i z ((P i).tgt α) _

/-- **A factor's word, and its class, do not see which tuples spell its ends.** -/
theorem quot_piPath_congr (i : ι) {A B : GenObj (P i).Gen} {u v : Quiver.Path A B}
    (h : (P i).quot.map u = (P i).quot.map v) (X Y : ∀ j, (P j).V)
    (hs : Shift P i A.as B.as X Y) :
    (pi P).quot.map (piPath P i u X Y hs) = (pi P).quot.map (piPath P i v X Y hs) := by
  obtain ⟨Z, hX, hY⟩ : ∃ Z, X = Function.update Z i A.as ∧ Y = Function.update Z i B.as :=
    ⟨X, hs.self_eq_update, hs.eq_update⟩
  subst hX; subst hY
  rw [piPath_eq_mapPath, piPath_eq_mapPath]
  exact (piIncl P i Z).quot_map_congr h

/-! ## Interchange, propagated to words

Every statement keeps a whole word inside one `quot.map`, and every step goes through
`piQuotCompCongr`, whose 0-cells are variables. -/

/-- Congruence of `presented` under composition of words. -/
theorem piQuotCompCongr {A B C : (pi P).Word} {f f' : A ⟶ B} {g g' : B ⟶ C}
    (hf : (pi P).quot.map f = (pi P).quot.map f') (hg : (pi P).quot.map g = (pi P).quot.map g') :
    (pi P).quot.map (f ≫ g) = (pi P).quot.map (f' ≫ g') := by
  rw [Functor.map_comp, Functor.map_comp, hf, hg]

/-- **The interchange square**, as an equation of arrows: two letters at different indices commute,
whichever tuples spell the two middles. -/
theorem quot_letter_comm {X M M' Y : ∀ k, (P k).V} {i j : ι} (hij : i ≠ j)
    {a a' : (P i).V} (g : (P i).Gen a a') {b b' : (P j).V} (h : (P j).Gen b b')
    (h₁ : Shift P i a a' X M) (h₂ : Shift P j b b' M Y)
    (h₃ : Shift P j b b' X M') (h₄ : Shift P i a a' M' Y) :
    (pi P).quot.map (piLetter P i g h₁ ≫ piLetter P j h h₂)
      = (pi P).quot.map (piLetter P j h h₃ ≫ piLetter P i g h₄) :=
  (pi P).quot_src_tgt (PiRel.interchange hij g h h₁ h₂ h₃ h₄)

/-- **A letter commutes past a whole word of another factor** — the interchange square, iterated. -/
theorem quot_comm_piPath {i j : ι} (hij : i ≠ j) {a a' : (P i).V} (g : (P i).Gen a a') :
    ∀ {A B : GenObj (P j).Gen} (u : Quiver.Path A B) {X Y X' Y' : ∀ k, (P k).V}
      (hu : Shift P j A.as B.as X Y) (hu' : Shift P j A.as B.as X' Y')
      (hg : Shift P i a a' X X') (hg' : Shift P i a a' Y Y'),
      (pi P).quot.map (piPath P j u X Y hu ≫ piLetter P i g hg')
        = (pi P).quot.map (piLetter P i g hg ≫ piPath P j u X' Y' hu') := by
  intro A B u
  induction u with
  | nil =>
      intro X Y X' Y' hu hu' hg hg'
      obtain rfl : X = Y := hu.eq_of
      obtain rfl : X' = Y' := hu'.eq_of
      rw [piPath_nil, piPath_nil]
      change (pi P).quot.map (𝟙 _ ≫ piLetter P i g hg')
        = (pi P).quot.map (piLetter P i g hg ≫ 𝟙 _)
      rw [Category.id_comp, Category.comp_id]
  | @cons M B u e ih =>
      intro X Y X' Y' hu hu' hg hg'
      have huW : Shift P j A.as M.as X (Function.update Y j M.as) :=
        ⟨hu.src, Function.update_self .., fun k hk =>
          (hu.fix k hk).trans (Function.update_of_ne hk ..).symm⟩
      have heW : Shift P j M.as B.as (Function.update Y j M.as) Y :=
        ⟨Function.update_self .., hu.tgt, fun k hk => Function.update_of_ne hk ..⟩
      have huW' : Shift P j A.as M.as X' (Function.update Y' j M.as) :=
        ⟨hu'.src, Function.update_self .., fun k hk =>
          (hu'.fix k hk).trans (Function.update_of_ne hk ..).symm⟩
      have heW' : Shift P j M.as B.as (Function.update Y' j M.as) Y' :=
        ⟨Function.update_self .., hu'.tgt, fun k hk => Function.update_of_ne hk ..⟩
      have hgW : Shift P i a a' (Function.update Y j M.as) (Function.update Y' j M.as) :=
        ⟨(Function.update_of_ne hij ..).trans hg'.src,
          (Function.update_of_ne hij ..).trans hg'.tgt, fun k hk => by
            by_cases hkj : k = j
            · subst hkj; rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hkj, Function.update_of_ne hkj]; exact hg'.fix k hk⟩
      rw [piPath_cons P j u e X Y _ hu huW heW, piPath_cons P j u e X' Y' _ hu' huW' heW']
      change (pi P).quot.map ((piPath P j u X _ huW ≫ piLetter P j e heW) ≫ piLetter P i g hg')
        = (pi P).quot.map (piLetter P i g hg ≫ (piPath P j u X' _ huW' ≫ piLetter P j e heW'))
      rw [Category.assoc]
      refine (piQuotCompCongr P rfl (quot_letter_comm P hij.symm e g heW hg' hgW heW')).trans ?_
      rw [← Category.assoc]
      exact (piQuotCompCongr P (ih huW huW' hg hgW) rfl).trans (by rw [Category.assoc])



/-! ## Functoriality in the family

`pi` is a functor of the family, strictly: `piMap_id` and `piMap_comp` are equalities on the nose,
with nothing to reassociate.  This is the whole point of the strict model — the same statement for
an iterated `prod` would carry the associator. -/

section Map

variable {Q R : ι → Polygraph.{w, u', w₂}}

/-- A shift, pushed along a map of families. -/
theorem piMapShift (φ : ∀ i, P i ⟶ Q i) {i : ι} {a b : (P i).V} {X Y : ∀ k, (P k).V}
    (hs : Shift P i a b X Y) :
    Shift Q i ((φ i).pre.obj ⟨a⟩).as ((φ i).pre.obj ⟨b⟩).as
      (fun k => ((φ k).pre.obj ⟨X k⟩).as) fun k => ((φ k).pre.obj ⟨Y k⟩).as :=
  ⟨congrArg (fun t => ((φ i).pre.obj ⟨t⟩).as) hs.src,
    congrArg (fun t => ((φ i).pre.obj ⟨t⟩).as) hs.tgt,
    fun j hj => congrArg (fun t => ((φ j).pre.obj ⟨t⟩).as) (hs.fix j hj)⟩

/-- The 1-cells of a map of families, coordinate by coordinate. -/
def piMapGen (φ : ∀ i, P i ⟶ Q i) :
    ∀ {X Y : ∀ i, (P i).V}, PiGen P X Y →
      PiGen Q (fun i => ((φ i).pre.obj ⟨X i⟩).as) fun i => ((φ i).pre.obj ⟨Y i⟩).as
  | _, _, .mk i g hs => PiGen.mk i ((φ i).pre.map g) (piMapShift P φ hs)

/-- The cells of a map of families. -/
def piMapPre (φ : ∀ i, P i ⟶ Q i) : GenObj (PiGen P) ⥤q GenObj (PiGen Q) where
  obj X := ⟨fun i => ((φ i).pre.obj ⟨X.as i⟩).as⟩
  map {_ _} e := piMapGen P φ e

/-- **A factor's word, pushed along a map of families.** -/
theorem piMapPre_piPath (φ : ∀ i, P i ⟶ Q i) (i : ι) :
    ∀ {A B : GenObj (P i).Gen} (u : Quiver.Path A B) (X Y : ∀ k, (P k).V)
      (hs : Shift P i A.as B.as X Y) (hs'),
      (piMapPre P φ).mapPath (piPath P i u X Y hs)
        = piPath Q i ((φ i).pre.mapPath u) _ _ hs' := by
  intro A B u
  induction u with
  | nil =>
      intro X Y hs hs'
      obtain rfl : X = Y := hs.eq_of
      rw [piPath_nil]
      exact (piPath_nil Q i _ hs').symm
  | @cons M B u e ih =>
      intro X Y hs hs'
      have hu : Shift P i A.as M.as X (Function.update Y i M.as) :=
        ⟨hs.src, Function.update_self .., fun k hk =>
          (hs.fix k hk).trans (Function.update_of_ne hk ..).symm⟩
      have he : Shift P i M.as B.as (Function.update Y i M.as) Y :=
        ⟨Function.update_self .., hs.tgt, fun k hk => Function.update_of_ne hk ..⟩
      rw [piPath_cons P i u e X Y _ hs hu he]
      refine Eq.trans ?_ (piPath_cons Q i ((φ i).pre.mapPath u) ((φ i).pre.map e)
        (fun k => ((φ k).pre.obj ⟨X k⟩).as) (fun k => ((φ k).pre.obj ⟨Y k⟩).as)
        (fun k => ((φ k).pre.obj ⟨Function.update Y i M.as k⟩).as) hs'
        (piMapShift P φ hu) (piMapShift P φ he)).symm
      have hcons : (piMapPre P φ).mapPath ((piPath P i u X (Function.update Y i M.as) hu).cons
            (PiGen.mk i e he))
          = ((piMapPre P φ).mapPath (piPath P i u X (Function.update Y i M.as) hu)).cons
            ((piMapPre P φ).map (PiGen.mk i e he)) := rfl
      rw [hcons, ih X (Function.update Y i M.as) hu (piMapShift P φ hu)]
      rfl

/-- **A map of families is a map of tensors.** -/
def piMap (φ : ∀ i, P i ⟶ Q i) : Polygraph.pi P ⟶ Polygraph.pi Q where
  pre := piMapPre P φ
  two := fun {_ _} α => match α with
    | .factor i a hs => PiRel.factor i ((φ i).two a) (piMapShift P φ hs)
    | .interchange hij g h h₁ h₂ h₃ h₄ =>
        PiRel.interchange hij ((φ _).pre.map g) ((φ _).pre.map h)
          (piMapShift P φ h₁) (piMapShift P φ h₂) (piMapShift P φ h₃) (piMapShift P φ h₄)
  src_two := by
    rintro _ _ (⟨i, a, hs⟩ | ⟨hij, g, h, h₁, h₂, h₃, h₄⟩)
    · change piPath Q i ((Q i).src ((φ i).two a)) _ _ (piMapShift P φ hs)
        = (piMapPre P φ).mapPath (piPath P i ((P i).src a) _ _ hs)
      rw [(φ i).src_two a, piMapPre_piPath P φ i ((P i).src a) _ _ hs (piMapShift P φ hs)]
    · rfl
  tgt_two := by
    rintro _ _ (⟨i, a, hs⟩ | ⟨hij, g, h, h₁, h₂, h₃, h₄⟩)
    · change piPath Q i ((Q i).tgt ((φ i).two a)) _ _ (piMapShift P φ hs)
        = (piMapPre P φ).mapPath (piPath P i ((P i).tgt a) _ _ hs)
      rw [(φ i).tgt_two a, piMapPre_piPath P φ i ((P i).tgt a) _ _ hs (piMapShift P φ hs)]
    · rfl

@[simp] theorem piMap_pre (φ : ∀ i, P i ⟶ Q i) : (piMap P φ).pre = piMapPre P φ := rfl

end Map

/-- **`pi` is a functor of the family** — this strictness is why the tensor is modelled by a tuple
over the index rather than by nested pairs. -/
def piFunctor : (∀ _ : ι, Polygraph.{w, u', w₂}) ⥤
    Polygraph.{max t u' w, max t u', max t u' w w₂} where
  obj P := Polygraph.pi P
  map {P Q} φ := piMap P φ
  map_id P := by
    refine Hom.ext' (Prefunctor.ext' (fun _ => rfl) ?_) ?_
    · rintro ⟨X⟩ ⟨Y⟩ ⟨i, g, hs⟩; rfl
    · rintro _ _ (⟨i, a, hs⟩ | ⟨hij, g, h, hs⟩) <;> rfl
  map_comp {P Q R} φ ψ := by
    refine Hom.ext' (Prefunctor.ext' (fun _ => rfl) ?_) ?_
    · rintro ⟨X⟩ ⟨Y⟩ ⟨i, g, hs⟩; rfl
    · rintro _ _ (⟨i, a, hs⟩ | ⟨hij, g, h, hs⟩) <;> rfl

/-- **Reindexing the identity family is the identity.** -/
@[simp] theorem piMap_id : piMap P (fun i => 𝟙 (P i)) = 𝟙 (Polygraph.pi P) :=
  (piFunctor (ι := ι)).map_id P

/-- **Reindexing a composite is the composite of the reindexings.** -/
@[simp] theorem piMap_comp {Q R : ι → Polygraph.{w, u', w₂}} (φ : ∀ i, P i ⟶ Q i)
    (ψ : ∀ i, Q i ⟶ R i) : piMap P (fun i => φ i ≫ ψ i) = piMap P φ ≫ piMap Q ψ :=
  (piFunctor (ι := ι)).map_comp φ ψ

/-! ## The normal form

Interchange lets every word be sorted by index: run each factor's word once, in the order of a
list of the indices.  `After` names the tuple reached when the factors in `l` have run, as a
proposition, so a caller supplies whichever tuple it already has and no transport appears. -/

/-- The tuple reached once the factors in `l` have run. -/
structure After (l : List ι) (x y z : ∀ i, (P i).V) : Prop where
  /-- an index of `l` has moved -/
  ran : ∀ k, k ∈ l → z k = y k
  /-- and no other has -/
  rest : ∀ k, k ∉ l → z k = x k

namespace After

variable {P}

theorem tail {l : List ι} {i : ι} (hi : i ∉ l) {x y z : ∀ k, (P k).V}
    (hz : After P (i :: l) x y z) : After P l x y (Function.update z i (x i)) where
  ran k hk := by
    have hki : k ≠ i := by rintro rfl; exact hi hk
    rw [Function.update_of_ne hki]
    exact hz.ran k (List.mem_cons_of_mem _ hk)
  rest k hk := by
    by_cases h : k = i
    · subst h; exact Function.update_self ..
    · rw [Function.update_of_ne h]
      exact hz.rest k fun hm => (List.mem_cons.mp hm).elim h hk

theorem headShift {l : List ι} {i : ι} {x y z : ∀ k, (P k).V} (hz : After P (i :: l) x y z) :
    Shift P i (x i) (y i) (Function.update z i (x i)) z :=
  ⟨Function.update_self .., hz.ran i List.mem_cons_self,
    fun _ hk => Function.update_of_ne hk ..⟩

theorem refl (l : List ι) (x : ∀ k, (P k).V) : After P l x x x := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem cover {l : List ι} (hcov : ∀ k, k ∈ l) {x y : ∀ k, (P k).V} : After P l x y y :=
  ⟨fun _ _ => rfl, fun k hk => absurd (hcov k) hk⟩

end After

/-- **The sorted word**: each factor's word run once, in the order of `l`. -/
def piNormalWord : ∀ (l : List ι) (hl : l.Nodup) {x y : ∀ i, (P i).V}
    (u : ∀ i, Quiver.Path (⟨x i⟩ : GenObj (P i).Gen) ⟨y i⟩)
    (z : ∀ i, (P i).V) (hz : After P l x y z),
    Quiver.Path (⟨x⟩ : GenObj (PiGen P)) ⟨z⟩
  | [], _, x, _, _, z, hz => by
      obtain rfl : x = z := funext fun k => (hz.rest k List.not_mem_nil).symm
      exact Quiver.Path.nil
  | i :: l, hl, _, _, u, z, hz =>
      (piNormalWord l hl.of_cons u _ (hz.tail (List.nodup_cons.mp hl).1)).comp
        (piPath P i (u i) _ z hz.headShift)


@[simp] theorem piNormalWord_nil (hl : ([] : List ι).Nodup) {x y : ∀ k, (P k).V}
    (u : ∀ k, Quiver.Path (⟨x k⟩ : GenObj (P k).Gen) ⟨y k⟩) (hz : After P [] x y x) :
    piNormalWord P [] hl u x hz = Quiver.Path.nil := by
  simp only [piNormalWord]

/-- **The last factor of a sorted word, split off with its intermediate tuple left free.** -/
theorem piNormalWord_cons (i : ι) (l : List ι) (hl : (i :: l).Nodup) {x y : ∀ k, (P k).V}
    (u : ∀ k, Quiver.Path (⟨x k⟩ : GenObj (P k).Gen) ⟨y k⟩) (z m : ∀ k, (P k).V)
    (hz : After P (i :: l) x y z) (hm : After P l x y m) (hs : Shift P i (x i) (y i) m z) :
    piNormalWord P (i :: l) hl u z hz
      = (piNormalWord P l hl.of_cons u m hm).comp (piPath P i (u i) m z hs) := by
  obtain rfl : m = Function.update z i (x i) := hs.symm.eq_update
  simp only [piNormalWord]

/-- **A factor's word does not see which 0-cell spells its target.** -/
theorem piPath_heq_congr (i : ι) {A B B' : GenObj (P i).Gen} (hB : B = B')
    {u : Quiver.Path A B} {v : Quiver.Path A B'} (huv : u ≍ v) (X Y : ∀ j, (P j).V) (hs hs') :
    piPath P i u X Y hs = piPath P i v X Y hs' := by
  subst hB
  obtain rfl : u = v := eq_of_heq huv
  rfl

/-- **A sorted word only reads the factors it runs.** -/
theorem piNormalWord_congr : ∀ (l : List ι) (hl : l.Nodup) {x y y' : ∀ k, (P k).V}
    (u : ∀ k, Quiver.Path (⟨x k⟩ : GenObj (P k).Gen) ⟨y k⟩)
    (v : ∀ k, Quiver.Path (⟨x k⟩ : GenObj (P k).Gen) ⟨y' k⟩)
    (hy : ∀ k, k ∈ l → y k = y' k) (huv : ∀ k, k ∈ l → u k ≍ v k)
    (z : ∀ k, (P k).V) (hz : After P l x y z) (hz' : After P l x y' z),
    piNormalWord P l hl u z hz = piNormalWord P l hl v z hz'
  | [], _, x, _, _, _, _, _, _, z, hz, _ => by
      obtain rfl : x = z := funext fun k => (hz.rest k List.not_mem_nil).symm
      rw [piNormalWord_nil, piNormalWord_nil]
  | i :: l, hl, x, y, y', u, v, hy, huv, z, hz, hz' => by
      have hi : i ∉ l := (List.nodup_cons.mp hl).1
      rw [piNormalWord_cons P i l hl u z _ hz (hz.tail hi) hz.headShift,
        piNormalWord_cons P i l hl v z _ hz' (hz'.tail hi) hz'.headShift]
      refine congrArg₂ Quiver.Path.comp ?_ ?_
      · exact piNormalWord_congr l hl.of_cons u v (fun k hk => hy k (List.mem_cons_of_mem _ hk))
          (fun k hk => huv k (List.mem_cons_of_mem _ hk)) _ _ _
      · exact piPath_heq_congr P i (congrArg GenObj.mk (hy i List.mem_cons_self))
          (huv i List.mem_cons_self) _ _ _ _

/-- **The empty family sorts to the empty word.** -/
theorem piNormalWord_eq_nil : ∀ (l : List ι) (hl : l.Nodup) {x : ∀ k, (P k).V}
    (hz : After P l x x x),
    piNormalWord P l hl (fun _ => Quiver.Path.nil) x hz = Quiver.Path.nil
  | [], _, _, _ => piNormalWord_nil P _ _ _
  | i :: l, hl, x, hz => by
      rw [piNormalWord_cons P i l hl _ x x hz (After.refl l x) ⟨rfl, rfl, fun _ _ => rfl⟩,
        piNormalWord_eq_nil l hl.of_cons (After.refl l x), piPath_nil]
      rfl

/-- **A letter, absorbed into the sorted word** — it commutes back to its own factor's slot. -/
theorem quot_normalWord_snoc (i : ι) : ∀ (l : List ι) (hl : l.Nodup) (hi : i ∈ l)
    {x m y : ∀ k, (P k).V} {u' : ∀ k, Quiver.Path (⟨x k⟩ : GenObj (P k).Gen) ⟨m k⟩}
    {u : ∀ k, Quiver.Path (⟨x k⟩ : GenObj (P k).Gen) ⟨y k⟩}
    {g : (P i).Gen (m i) (y i)} (hs : Shift P i (m i) (y i) m y)
    (hui : u i ≍ (u' i).cons (show (⟨m i⟩ : GenObj (P i).Gen) ⟶ ⟨y i⟩ from g))
    (huk : ∀ k, k ≠ i → u k ≍ u' k)
    (z z' : ∀ k, (P k).V) (hz : After P l x m z) (hz' : After P l x y z')
    (hzz : Shift P i (m i) (y i) z z'),
    (pi P).quot.map (piNormalWord P l hl u' z hz ≫ piLetter P i g hzz)
      = (pi P).quot.map (piNormalWord P l hl u z' hz')
  | [], _, hi, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd hi List.not_mem_nil
  | j :: l, hl, hi, x, m, y, u', u, g, hs, hui, huk, z, z', hz, hz', hzz => by
      have hj : j ∉ l := (List.nodup_cons.mp hl).1
      by_cases hij : i = j
      · subst hij
        have hym : After P l x y (Function.update z i (x i)) :=
          { ran := fun k hk => by
              have hki : k ≠ i := by rintro rfl; exact hj hk
              rw [Function.update_of_ne hki]
              exact (hz.ran k (List.mem_cons_of_mem _ hk)).trans (hs.fix k hki)
            rest := fun k hk => by
              by_cases h : k = i
              · subst h; exact Function.update_self ..
              · rw [Function.update_of_ne h]
                exact hz.rest k fun hm => (List.mem_cons.mp hm).elim h hk }
        have hsz' : Shift P i (x i) (y i) (Function.update z i (x i)) z' :=
          ⟨Function.update_self .., hz'.ran i List.mem_cons_self,
            fun k hk => (Function.update_of_ne hk ..).trans (hzz.fix k hk)⟩
        have h₁ := piNormalWord_congr P l hl.of_cons u' u
          (fun k hk => hs.fix k (by rintro rfl; exact hj hk))
          (fun k hk => (huk k (by rintro rfl; exact hj hk)).symm)
          (Function.update z i (x i)) (hz.tail hj) hym
        have h₂ : (piPath P i (u' i) (Function.update z i (x i)) z hz.headShift).cons
              (PiGen.mk i g hzz)
            = piPath P i (u i) (Function.update z i (x i)) z' hsz' :=
          (piPath_cons P i (u' i) g (Function.update z i (x i)) z' z hsz' hz.headShift
            hzz).symm.trans (piPath_heq_congr P i rfl hui.symm _ _ _ _)
        rw [piNormalWord_cons P i l hl u' z _ hz (hz.tail hj) hz.headShift,
          piNormalWord_cons P i l hl u z' _ hz' hym hsz']
        change (pi P).quot.map ((piNormalWord P l hl.of_cons u' _ (hz.tail hj)).comp
            ((piPath P i (u' i) _ z hz.headShift).cons (PiGen.mk i g hzz)))
          = (pi P).quot.map ((piNormalWord P l hl.of_cons u _ hym).comp
            (piPath P i (u i) _ z' hsz'))
        rw [h₁, h₂]
      · have hji : j ≠ i := fun h => hij h.symm
        have hmy : Shift P i (m i) (y i) (Function.update z j (x j))
            (Function.update z' j (x j)) :=
          ⟨(Function.update_of_ne hij ..).trans hzz.src,
            (Function.update_of_ne hij ..).trans hzz.tgt, fun k hk => by
              by_cases hk' : k = j
              · subst hk'; rw [Function.update_self, Function.update_self]
              · rw [Function.update_of_ne hk', Function.update_of_ne hk']; exact hzz.fix k hk⟩
        have hjy : Shift P j (x j) (m j) (Function.update z' j (x j)) z' :=
          ⟨Function.update_self .., (hz'.ran j List.mem_cons_self).trans (hs.fix j hji).symm,
            fun k hk => Function.update_of_ne hk ..⟩
        rw [piNormalWord_cons P j l hl u' z _ hz (hz.tail hj) hz.headShift,
          piNormalWord_cons P j l hl u z' _ hz' (hz'.tail hj) hz'.headShift]
        change (pi P).quot.map ((piNormalWord P l hl.of_cons u' _ (hz.tail hj)
            ≫ piPath P j (u' j) _ z hz.headShift) ≫ piLetter P i g hzz)
          = (pi P).quot.map (piNormalWord P l hl.of_cons u _ (hz'.tail hj)
            ≫ piPath P j (u j) _ z' hz'.headShift)
        rw [Category.assoc]
        refine (piQuotCompCongr P rfl
          (quot_comm_piPath P hij g (u' j) hz.headShift hjy hmy hzz)).trans ?_
        rw [← Category.assoc]
        refine (piQuotCompCongr P (quot_normalWord_snoc i l hl.of_cons
          ((List.mem_cons.mp hi).resolve_left hij) hs hui huk _ _ (hz.tail hj) (hz'.tail hj)
          hmy) rfl).trans ?_
        exact piQuotCompCongr P rfl (congrArg _
          (piPath_heq_congr P j (congrArg GenObj.mk (hs.fix j hji)) (huk j hji).symm _ _ _ _))

/-- **Every word of the tensor sorts by index** — what the interchange 2-cells buy, and the whole
of `Presents.pi`'s completeness. -/
theorem exists_piNormalForm (l : List ι) (hl : l.Nodup) (hcov : ∀ i, i ∈ l) :
    ∀ {A B : GenObj (PiGen P)} (w : Quiver.Path A B),
      ∃ u : ∀ i, Quiver.Path (⟨A.as i⟩ : GenObj (P i).Gen) ⟨B.as i⟩,
        (pi P).quot.map w
          = (pi P).quot.map (piNormalWord P l hl u B.as (After.cover hcov)) := by
  intro A B w
  induction w with
  | nil => exact ⟨fun _ => Quiver.Path.nil, by rw [piNormalWord_eq_nil]⟩
  | @cons M N w e ih =>
      obtain ⟨m⟩ := M
      obtain ⟨n⟩ := N
      obtain ⟨u', hw⟩ := ih
      cases e with
      | @mk i a b g hs =>
          obtain rfl : a = m i := hs.src.symm
          obtain rfl : b = n i := hs.tgt.symm
          refine ⟨fun k => if h : k = i then cast (by rw [h]) ((u' i).cons g)
            else cast (by rw [hs.fix k h]) (u' k), ?_⟩
          change (pi P).quot.map (w ≫ piLetter P i g hs) = _
          refine (piQuotCompCongr P hw rfl).trans ?_
          refine quot_normalWord_snoc P i l hl (hcov i) hs ?_ ?_ m n
            (After.cover hcov) (After.cover hcov) hs
          · rw [dif_pos rfl]; exact cast_heq _ _
          · intro k hk; rw [dif_neg hk]; exact cast_heq _ _



/-- **Equal factor words spell equal sorted words.** -/
theorem quot_piNormalWord_congr : ∀ (l : List ι) (hl : l.Nodup) {x y : ∀ k, (P k).V}
    (u v : ∀ k, Quiver.Path (⟨x k⟩ : GenObj (P k).Gen) ⟨y k⟩)
    (h : ∀ k, (P k).quot.map (u k) = (P k).quot.map (v k))
    (z : ∀ k, (P k).V) (hz : After P l x y z),
    (pi P).quot.map (piNormalWord P l hl u z hz)
      = (pi P).quot.map (piNormalWord P l hl v z hz)
  | [], _, x, _, _, _, _, z, hz => by
      obtain rfl : x = z := funext fun k => (hz.rest k List.not_mem_nil).symm
      rw [piNormalWord_nil, piNormalWord_nil]
  | i :: l, hl, _, _, u, v, h, z, hz => by
      have hi : i ∉ l := (List.nodup_cons.mp hl).1
      rw [piNormalWord_cons P i l hl u z _ hz (hz.tail hi) hz.headShift,
        piNormalWord_cons P i l hl v z _ hz (hz.tail hi) hz.headShift]
      exact piQuotCompCongr P (quot_piNormalWord_congr l hl.of_cons u v h _ _)
        (quot_piPath_congr P i (h i) _ _ _)
/-! ## An index list

The sorting order.  Any duplicate-free list of every index will do; the presentation does not
depend on which. -/

variable [Fintype ι]

variable (ι) in
/-- Every index, once. -/
noncomputable def piList : List ι := Finset.univ.toList

variable (ι) in
theorem piList_nodup : (piList ι).Nodup := Finset.nodup_toList _

theorem piList_mem (i : ι) : i ∈ piList ι := Finset.mem_toList.mpr (Finset.mem_univ i)

end Polygraph

namespace Presents

open Polygraph

variable {ι : Type t} [DecidableEq ι] {P : ι → Polygraph.{w, u', w₂}}
  {C : ι → Type u} [∀ i, Category.{v} (C i)] (p : ∀ i, Presents (P i) (C i))

/-- The tuple of objects a tuple of 0-cells names. -/
abbrev piObj (X : ∀ i, (P i).V) : ∀ i, C i := fun i => (p i).at' ⟨X i⟩

/-- Equal 0-cells name equal objects. -/
theorem atCongr (i : ι) {a b : (P i).V} (h : a = b) :
    (p i).at' (⟨a⟩ : GenObj (P i).Gen) = (p i).at' ⟨b⟩ := by rw [h]

/-! ### Sandwiches

A coordinate of the evaluation is an arrow between two `eqToHom`s, and a composite telescopes.  The
normal forms are stated here, where the category is a variable and `simp` can see the composition;
in the goals they arise in, `rw` on a composition does not match. -/

section Sandwich

variable {D : Type*} [Category D]

theorem eqToHom_sandwich_comp {A B B' W E E' : D} (h : A = B) (f : B ⟶ B') (h' : B' = W)
    (g : B' ⟶ E) (h'' : E = E') :
    (eqToHom h ≫ f ≫ eqToHom h') ≫ eqToHom h'.symm ≫ g ≫ eqToHom h''
      = eqToHom h ≫ (f ≫ g) ≫ eqToHom h'' := by simp

theorem eqToHom_sandwich_cancel {A B B' E : D} (h : A = B) (f : A ⟶ B') (h' : B' = E) :
    eqToHom h ≫ eqToHom h.symm ≫ f ≫ eqToHom h' = f ≫ eqToHom h' := by simp

theorem eqToHom_comp_trans {A B W E : D} (f : A ⟶ B) (h : B = W) (h' : W = E) :
    (f ≫ eqToHom h) ≫ eqToHom h' = f ≫ eqToHom (h.trans h') := by simp

theorem eqToHom_sandwich_eq {A A' B B' E E' : D} (f : B ⟶ B') (h : A = B) (h' : B' = E)
    (h'' : E = E') (k : A = A') (k' : A' = B) (k'' : B' = E') :
    (eqToHom h ≫ f ≫ eqToHom h') ≫ eqToHom h''
      = eqToHom k ≫ eqToHom k' ≫ f ≫ eqToHom k'' := by simp

theorem eqToHom_comp_eq {A B B' E : D} (h : A = B) (h' : B = E) (k : A = B') (k' : B' = E) :
    eqToHom h ≫ eqToHom h' = eqToHom k ≫ eqToHom k' := by simp

theorem comp_eqToHom_self {A B : D} (f : A ⟶ B) (h : B = B) : f ≫ eqToHom h = f := by simp

theorem comp_eqToHom_inj {A B E : D} {f g : A ⟶ B} (h : B = E)
    (hfg : f ≫ eqToHom h = g ≫ eqToHom h) : f = g :=
  (cancel_mono (eqToHom h)).mp hfg

end Sandwich

/-- The arrow a 1-cell names: one factor's arrow, the identity — up to the 0-cell equations the
`Shift` provides — on every other coordinate. -/
def piArrow {X Y : ∀ j, (P j).V} (i : ι) {a b : (P i).V} (g : (P i).Gen a b)
    (hs : Shift P i a b X Y) : piObj p X ⟶ piObj p Y := fun k =>
  if h : k = i then
    Eq.mpr (congrArg (fun t => piObj p X t ⟶ piObj p Y t) h)
      (eqToHom (atCongr p i hs.src) ≫ (p i).arrow g ≫ eqToHom (atCongr p i hs.tgt).symm)
  else eqToHom (atCongr p k (hs.fix k h))

@[simp] theorem piArrow_self {X Y : ∀ j, (P j).V} (i : ι) {a b : (P i).V} (g : (P i).Gen a b)
    (hs : Shift P i a b X Y) :
    piArrow p i g hs i
      = eqToHom (atCongr p i hs.src) ≫ (p i).arrow g ≫ eqToHom (atCongr p i hs.tgt).symm :=
  dif_pos rfl

@[simp] theorem piArrow_of_ne {X Y : ∀ j, (P j).V} (i : ι) {a b : (P i).V} (g : (P i).Gen a b)
    (hs : Shift P i a b X Y) {k : ι} (h : k ≠ i) :
    piArrow p i g hs k = eqToHom (atCongr p k (hs.fix k h)) :=
  dif_neg h

/-- The cells of the tensor, interpreted in the product category. -/
def piEval : GenObj (PiGen P) ⥤q (∀ i, C i) where
  obj Z := piObj p Z.as
  map {_ _} e := match e with | .mk i g hs => piArrow p i g hs

@[simp] theorem piEval_letter {X Y : ∀ j, (P j).V} (i : ι) {a b : (P i).V} (g : (P i).Gen a b)
    (hs : Shift P i a b X Y) :
    (Paths.lift (piEval p)).map (piLetter P i g hs) = piArrow p i g hs :=
  Paths.lift_toPath _ _

/-- **A factor's word, evaluated at its own coordinate.** -/
theorem piEval_piPath_self (j : ι) : ∀ {A B : GenObj (P j).Gen} (u : Quiver.Path A B)
    (X Y : ∀ k, (P k).V) (hs : Shift P j A.as B.as X Y),
    (Paths.lift (piEval p)).map (piPath P j u X Y hs) j
      = eqToHom (atCongr p j hs.src) ≫ (p j).eval.map u ≫ eqToHom (atCongr p j hs.tgt).symm := by
  intro A B u
  induction u with
  | nil =>
      intro X Y hs
      obtain rfl : X = Y := hs.eq_of
      rw [piPath_nil]
      change (𝟙 (piObj p X) : piObj p X ⟶ piObj p X) j = _
      rw [Presents.eval_nil, Category.id_comp, eqToHom_trans, eqToHom_refl]
      rfl
  | @cons M B u e ih =>
      intro X Y hs
      have hu : Shift P j A.as M.as X (Function.update Y j M.as) :=
        ⟨hs.src, Function.update_self .., fun k hk =>
          (hs.fix k hk).trans (Function.update_of_ne hk ..).symm⟩
      have he : Shift P j M.as B.as (Function.update Y j M.as) Y :=
        ⟨Function.update_self .., hs.tgt, fun k hk => Function.update_of_ne hk ..⟩
      rw [piPath_cons P j u e X Y _ hs hu he]
      change ((Paths.lift (piEval p)).map (piPath P j u X _ hu ≫ piLetter P j e he)) j = _
      rw [Functor.map_comp]
      change (Paths.lift (piEval p)).map (piPath P j u X _ hu) j
        ≫ (Paths.lift (piEval p)).map (piLetter P j e he) j = _
      rw [ih, piEval_letter, piArrow_self, Presents.eval_cons]
      exact eqToHom_sandwich_comp (D := C j) _ _ _ _ _

/-- **A factor's word does not move the other coordinates.** -/
theorem piEval_piPath_of_ne (j : ι) {i : ι} (hij : i ≠ j) :
    ∀ {A B : GenObj (P j).Gen} (u : Quiver.Path A B) (X Y : ∀ k, (P k).V)
      (hs : Shift P j A.as B.as X Y),
      (Paths.lift (piEval p)).map (piPath P j u X Y hs) i
        = eqToHom (atCongr p i (hs.fix i hij)) := by
  intro A B u
  induction u with
  | nil =>
      intro X Y hs
      obtain rfl : X = Y := hs.eq_of
      rw [piPath_nil]
      change (𝟙 (piObj p X) : piObj p X ⟶ piObj p X) i = _
      rw [eqToHom_refl]
      rfl
  | @cons M B u e ih =>
      intro X Y hs
      have hu : Shift P j A.as M.as X (Function.update Y j M.as) :=
        ⟨hs.src, Function.update_self .., fun k hk =>
          (hs.fix k hk).trans (Function.update_of_ne hk ..).symm⟩
      have he : Shift P j M.as B.as (Function.update Y j M.as) Y :=
        ⟨Function.update_self .., hs.tgt, fun k hk => Function.update_of_ne hk ..⟩
      rw [piPath_cons P j u e X Y _ hs hu he]
      change ((Paths.lift (piEval p)).map (piPath P j u X _ hu ≫ piLetter P j e he)) i = _
      rw [Functor.map_comp]
      change (Paths.lift (piEval p)).map (piPath P j u X _ hu) i
        ≫ (Paths.lift (piEval p)).map (piLetter P j e he) i = _
      rw [ih, piEval_letter, piArrow_of_ne p j e he hij]
      exact eqToHom_trans _ _

/-- **A sorted word does not move a coordinate it never runs.** -/
theorem piEval_normalWord_of_not_mem (i : ι) : ∀ (l : List ι) (hl : l.Nodup)
    {x y : ∀ k, (P k).V} (u : ∀ k, Quiver.Path (⟨x k⟩ : GenObj (P k).Gen) ⟨y k⟩)
    (z : ∀ k, (P k).V) (hz : After P l x y z) (hi : i ∉ l),
    (Paths.lift (piEval p)).map (piNormalWord P l hl u z hz) i
      = eqToHom (atCongr p i (hz.rest i hi).symm)
  | [], _, x, _, _, z, hz, _ => by
      obtain rfl : x = z := funext fun k => (hz.rest k List.not_mem_nil).symm
      rw [piNormalWord_nil]
      change (𝟙 (piObj p x) : piObj p x ⟶ piObj p x) i = _
      rw [eqToHom_refl]
      rfl
  | j :: l, hl, x, y, u, z, hz, hi => by
      have hj : j ∉ l := (List.nodup_cons.mp hl).1
      have hij : i ≠ j := fun h => hi (h ▸ List.mem_cons_self)
      rw [piNormalWord_cons P j l hl u z _ hz (hz.tail hj) hz.headShift]
      change ((Paths.lift (piEval p)).map (piNormalWord P l hl.of_cons u _ (hz.tail hj)
        ≫ piPath P j (u j) _ z hz.headShift)) i = _
      rw [Functor.map_comp]
      change (Paths.lift (piEval p)).map (piNormalWord P l hl.of_cons u _ (hz.tail hj)) i
        ≫ (Paths.lift (piEval p)).map (piPath P j (u j) _ z hz.headShift) i = _
      rw [piEval_normalWord_of_not_mem i l hl.of_cons u _ (hz.tail hj)
        (fun h => hi (List.mem_cons_of_mem _ h)), piEval_piPath_of_ne p j hij]
      exact eqToHom_trans _ _

/-- **A sorted word, evaluated at a coordinate it runs.** -/
theorem piEval_normalWord (i : ι) : ∀ (l : List ι) (hl : l.Nodup) {x y : ∀ k, (P k).V}
    (u : ∀ k, Quiver.Path (⟨x k⟩ : GenObj (P k).Gen) ⟨y k⟩) (z : ∀ k, (P k).V)
    (hz : After P l x y z) (hi : i ∈ l),
    (Paths.lift (piEval p)).map (piNormalWord P l hl u z hz) i
      = (p i).eval.map (u i) ≫ eqToHom (atCongr p i (hz.ran i hi).symm)
  | [], _, _, _, _, _, _, hi => absurd hi List.not_mem_nil
  | j :: l, hl, x, y, u, z, hz, hi => by
      have hj : j ∉ l := (List.nodup_cons.mp hl).1
      rw [piNormalWord_cons P j l hl u z _ hz (hz.tail hj) hz.headShift]
      change ((Paths.lift (piEval p)).map (piNormalWord P l hl.of_cons u _ (hz.tail hj)
        ≫ piPath P j (u j) _ z hz.headShift)) i = _
      rw [Functor.map_comp]
      change (Paths.lift (piEval p)).map (piNormalWord P l hl.of_cons u _ (hz.tail hj)) i
        ≫ (Paths.lift (piEval p)).map (piPath P j (u j) _ z hz.headShift) i = _
      by_cases hij : i = j
      · subst hij
        rw [piEval_normalWord_of_not_mem p i l hl.of_cons u _ (hz.tail hj) hj,
          piEval_piPath_self]
        exact eqToHom_sandwich_cancel (D := C i) _ _ _
      · rw [piEval_normalWord i l hl.of_cons u _ (hz.tail hj)
          ((List.mem_cons.mp hi).resolve_left hij),
          piEval_piPath_of_ne p j hij]
        exact eqToHom_comp_trans (D := C i) _ _ _



/-! ## The presentation -/

variable [Fintype ι]

theorem pi_sound {A B : GenObj (PiGen P)} (α : (Polygraph.pi P).Rel A B) :
    (Paths.lift (piEval p)).map ((Polygraph.pi P).src α)
      = (Paths.lift (piEval p)).map ((Polygraph.pi P).tgt α) := by
  cases α with
  | factor i α hs =>
      funext k
      by_cases hk : k = i
      · subst hk
        change (Paths.lift (piEval p)).map (piPath P k ((P k).src α) _ _ hs) k
          = (Paths.lift (piEval p)).map (piPath P k ((P k).tgt α) _ _ hs) k
        rw [piEval_piPath_self, piEval_piPath_self, (p k).sound α]
      · change (Paths.lift (piEval p)).map (piPath P i ((P i).src α) _ _ hs) k
          = (Paths.lift (piEval p)).map (piPath P i ((P i).tgt α) _ _ hs) k
        rw [piEval_piPath_of_ne p i hk, piEval_piPath_of_ne p i hk]
  | @interchange _ _ _ _ i j hij _ _ g _ _ h h₁ h₂ h₃ h₄ =>
      funext k
      change ((Paths.lift (piEval p)).map (piLetter P i g h₁ ≫ piLetter P j h h₂)) k
        = ((Paths.lift (piEval p)).map (piLetter P j h h₃ ≫ piLetter P i g h₄)) k
      rw [Functor.map_comp, Functor.map_comp]
      change (Paths.lift (piEval p)).map (piLetter P i g h₁) k
          ≫ (Paths.lift (piEval p)).map (piLetter P j h h₂) k
        = (Paths.lift (piEval p)).map (piLetter P j h h₃) k
          ≫ (Paths.lift (piEval p)).map (piLetter P i g h₄) k
      rw [piEval_letter, piEval_letter, piEval_letter, piEval_letter]
      by_cases hki : k = i
      · subst hki
        rw [piArrow_self, piArrow_of_ne p j h _ hij, piArrow_of_ne p j h _ hij, piArrow_self]
        exact eqToHom_sandwich_eq (D := C k) _ _ _ _ _ _ _
      · by_cases hkj : k = j
        · subst hkj
          rw [piArrow_of_ne p i g _ hki, piArrow_self, piArrow_self,
            piArrow_of_ne p i g _ hki]
          exact (eqToHom_sandwich_eq (D := C k) _ _ _ _ _ _ _).symm
        · rw [piArrow_of_ne p i g _ hki, piArrow_of_ne p j h _ hkj,
            piArrow_of_ne p j h _ hkj, piArrow_of_ne p i g _ hki]
          exact eqToHom_comp_eq (D := C k) _ _ _ _

theorem pi_complete {A B : GenObj (PiGen P)} {w w' : Quiver.Path A B}
    (hw : (Paths.lift (piEval p)).map w = (Paths.lift (piEval p)).map w') :
    (Polygraph.pi P).quot.map w = (Polygraph.pi P).quot.map w' := by
  obtain ⟨u, hu⟩ := exists_piNormalForm P (piList ι) (piList_nodup ι) piList_mem w
  obtain ⟨v, hv⟩ := exists_piNormalForm P (piList ι) (piList_nodup ι) piList_mem w'
  have key : ∀ i, (P i).quot.map (u i) = (P i).quot.map (v i) := by
    intro i
    have h1 := congrFun (Polygraph.lift_map_eq_of_quot_eq (piEval p) (pi_sound p) hu) i
    have h2 := congrFun (Polygraph.lift_map_eq_of_quot_eq (piEval p) (pi_sound p) hv) i
    have e1 := piEval_normalWord p i (piList ι) (piList_nodup ι) u B.as
      (After.cover piList_mem) (piList_mem i)
    have e2 := piEval_normalWord p i (piList ι) (piList_nodup ι) v B.as
      (After.cover piList_mem) (piList_mem i)
    exact (p i).E.map_injective (comp_eqToHom_inj (D := C i) _
      (e1.symm.trans (h1.symm.trans ((congrFun hw i).trans (h2.trans e2)))))
  rw [hu, hv]
  exact quot_piNormalWord_congr P _ _ u v key _ _

theorem pi_full : (Paths.lift (piEval p)).Full where
  map_surjective := by
    rintro ⟨X⟩ ⟨Y⟩ f
    choose u hu using fun i => (p i).eval.map_surjective
      (f i : (p i).at' (⟨X i⟩ : GenObj (P i).Gen) ⟶ (p i).at' ⟨Y i⟩)
    refine ⟨piNormalWord P (piList ι) (piList_nodup ι) u Y (After.cover piList_mem), ?_⟩
    funext i
    exact (piEval_normalWord p i (piList ι) (piList_nodup ι) u Y (After.cover piList_mem)
      (piList_mem i)).trans ((comp_eqToHom_self (D := C i) _ _).trans (hu i))

theorem pi_essSurj : (Paths.lift (piEval p)).EssSurj where
  mem_essImage c := by
    choose x e using fun i => Functor.EssSurj.mem_essImage (F := (p i).eval) (c i)
    exact ⟨⟨fun i => (x i).as⟩, ⟨{ hom := fun i => (e i).some.hom
                                   inv := fun i => (e i).some.inv
                                   hom_inv_id := funext fun i => (e i).some.hom_inv_id
                                   inv_hom_id := funext fun i => (e i).some.inv_hom_id }⟩⟩

/-- **A family of presentations presents the product** — the interchange 2-cells are exactly what
stops the words from presenting a free product, and the sorted word is the normal form they buy. -/
def pi : Presents (Polygraph.pi P) (∀ i, C i) :=
  Presents.ofDesc (piEval p) (pi_sound p) (pi_complete p) (pi_full p) (pi_essSurj p)

/-- **A 1-cell names its factor's arrow**, the other coordinates fixed. -/
@[simp] theorem pi_arrow {X Y : ∀ j, (P j).V} (i : ι) {a b : (P i).V} (g : (P i).Gen a b)
    (hs : Shift P i a b X Y) :
    (Presents.pi p).arrow (PiGen.mk i g hs) = piArrow p i g hs :=
  Presents.ofDesc_arrow _ (pi_sound p) _

end Presents

end CategoryTheory
