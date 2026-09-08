import CubeChains.Machinery.Presentation.ColimitCells
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sigma.Basic

/-!
# Machinery/Presentation/Coproduct — the coproduct of polygraphs

`coprod P` is the disjoint union in every dimension, and `coprodIsColimit` says it *is* the
categorical coproduct.  It is built by hand rather than taken as `∐` for one reason: `HasColimit` is
a `Prop`, so an abstract leg is `Classical.choice`-opaque, whereas here a leg's 0-cell **is** a pair
and `coprodDesc` restricts to its family by `rfl` — which is what keeps `coproduct_at`, and hence
everything a generator of a leg names, transport-free.  The leg constraint is carried by indexed
inductives (`CoprodGen`, `CoprodRel`, mirroring mathlib's `Sigma.SigmaHom`) so that `cases` reads
the leg off a cell.

A leg is star-bijective and injective on 0-cells, so a word between 0-cells of one leg is that
leg's word (`coprod_pathsFunctor_full`); that, plus the absence of cross-leg words, is the whole
content of `Presents.coproduct`.  The converse — a presentation cut down to one leg — is
`Presents.restrict`.
-/

universe u

namespace CategoryTheory

/-- **An arrow of a disjoint union is one leg's**, up to the transport its endpoints carry. -/
theorem Sigma.exists_incl_map {ι : Type*} {C : ι → Type*} [∀ i, Category (C i)]
    {X Y : Σ i, C i} (f : X ⟶ Y) :
    ∃ (i : ι) (a b : C i) (g : a ⟶ b) (hx : (⟨i, a⟩ : Σ i, C i) = X)
      (hy : (⟨i, b⟩ : Σ i, C i) = Y),
      Quiver.homOfEq ((Sigma.incl i).map g) hx hy = f := by
  cases f with
  | mk g => exact ⟨_, _, _, g, rfl, rfl, rfl⟩

namespace Polygraph

open Limits

variable {ι : Type u} (P : ι → Polygraph.{u, u, u})

/-! ## The construction -/

/-- 1-cells of a coproduct: a leg's own, and nothing across legs. -/
inductive CoprodGen : (Σ i, (P i).V) → (Σ i, (P i).V) → Type u
  | mk {i : ι} {x y : (P i).V} : (P i).Gen x y → CoprodGen ⟨i, x⟩ ⟨i, y⟩

/-- The inclusion of one leg's generating quiver. -/
def coprodPre (i : ι) : GenObj (P i).Gen ⥤q GenObj (CoprodGen P) where
  obj x := ⟨⟨i, x.as⟩⟩
  map e := CoprodGen.mk e

/-- 2-cells of a coproduct: a leg's own. -/
inductive CoprodRel : GenObj (CoprodGen P) → GenObj (CoprodGen P) → Type u
  | mk {i : ι} {x y : GenObj (P i).Gen} :
      (P i).Rel x y → CoprodRel ((coprodPre P i).obj x) ((coprodPre P i).obj y)

/-- The source of a coproduct 2-cell: its leg's, included. -/
def CoprodRel.src : ∀ {a b : GenObj (CoprodGen P)}, CoprodRel P a b → Quiver.Path a b
  | _, _, .mk (i := i) α => (coprodPre P i).mapPath ((P i).src α)

/-- The target of a coproduct 2-cell: its leg's, included. -/
def CoprodRel.tgt : ∀ {a b : GenObj (CoprodGen P)}, CoprodRel P a b → Quiver.Path a b
  | _, _, .mk (i := i) α => (coprodPre P i).mapPath ((P i).tgt α)

/-- **The coproduct of polygraphs.** -/
def coprod : Polygraph.{u, u, u} where
  V := Σ i, (P i).V
  Gen := CoprodGen P
  Rel := CoprodRel P
  src := CoprodRel.src P
  tgt := CoprodRel.tgt P

/-- The coproduct injection. -/
def coprodι (i : ι) : P i ⟶ coprod P where
  pre := coprodPre P i
  two α := CoprodRel.mk α
  src_two _ := rfl
  tgt_two _ := rfl

/-! ## Descending a family

A prefunctor out of each leg descends, with nothing to check and nothing to transport: the leg is
definitional, so the descent restricts to the family it came from by `rfl`.  The target is any
quiver — the cells of another polygraph, a category, or a polygraph's words. -/

section Desc

variable {W : Type u} [Quiver.{u} W] (ψ : ∀ i : ι, GenObj (P i).Gen ⥤q W)

/-- The arrow of `W` a 1-cell of the coproduct is sent to: the leg it lies in decides. -/
def coprodDescMap : ∀ a b : Σ i, (P i).V, CoprodGen P a b →
    ((ψ a.1).obj ⟨a.2⟩ ⟶ (ψ b.1).obj ⟨b.2⟩)
  | _, _, .mk (i := i) g => (ψ i).map g

/-- **A family of prefunctors descends to the coproduct's cells.** -/
def coprodDesc : GenObj (coprod P).Gen ⥤q W where
  obj A := (ψ A.as.1).obj ⟨A.as.2⟩
  map {A B} e := coprodDescMap P ψ A.as B.as e

/-- **…restricting to the family it came from**, on the nose. -/
@[simp] theorem ι_pre_comp_coprodDesc (i : ι) : (coprodι P i).pre ⋙q coprodDesc P ψ = ψ i := rfl

/-- **A prefunctor on a coproduct's cells is pinned by its legs.** -/
theorem coprod_pre_ext {φ φ' : GenObj (coprod P).Gen ⥤q W}
    (h : ∀ i : ι, (coprodι P i).pre ⋙q φ = (coprodι P i).pre ⋙q φ') : φ = φ' := by
  have hobj : ∀ A : GenObj (coprod P).Gen, φ.obj A = φ'.obj A := fun A =>
    congrArg (fun π : GenObj (P A.as.1).Gen ⥤q W => π.obj ⟨A.as.2⟩) (h A.as.1)
  refine Prefunctor.ext' hobj fun A B e => ?_
  obtain ⟨A⟩ := A
  obtain ⟨B⟩ := B
  cases e with
  | @mk i _ _ g => exact Prefunctor.map_of_eq (h i) g

end Desc

/-! ## …and the universal property

The same descent for morphisms of polygraphs: a 2-cell of the coproduct is a leg's, so it goes
where that leg's does, and both boundary conditions are the leg's own. -/

section Colim

variable {R : Polygraph.{u, u, u}} (m : ∀ i : ι, P i ⟶ R)

/-- The 2-cell of `R` a 2-cell of the coproduct is sent to. -/
def coprodDescTwo : ∀ {A B : GenObj (coprod P).Gen}, (coprod P).Rel A B →
    R.Rel ((coprodDesc P fun i => (m i).pre).obj A) ((coprodDesc P fun i => (m i).pre).obj B)
  | _, _, .mk (i := i) β => (m i).two β

/-- **A family of morphisms descends to the coproduct.** -/
def coprodDescHom : coprod P ⟶ R where
  pre := coprodDesc P fun i => (m i).pre
  two α := coprodDescTwo P m α
  src_two := by
    rintro _ _ ⟨β⟩
    exact ((m _).src_two β).trans
      (Prefunctor.mapPath_comp_apply (coprodPre P _) (coprodDesc P fun i => (m i).pre) _)
  tgt_two := by
    rintro _ _ ⟨β⟩
    exact ((m _).tgt_two β).trans
      (Prefunctor.mapPath_comp_apply (coprodPre P _) (coprodDesc P fun i => (m i).pre) _)

@[simp] theorem coprodι_comp_descHom (i : ι) : coprodι P i ≫ coprodDescHom P m = m i :=
  Hom.ext' rfl fun _ => HEq.rfl

/-- **A morphism out of a coproduct is pinned by its legs.** -/
theorem coprod_hom_ext {F G : coprod P ⟶ R} (h : ∀ i : ι, coprodι P i ≫ F = coprodι P i ≫ G) :
    F = G :=
  Hom.ext' (coprod_pre_ext P fun i => congrArg Hom.pre (h i)) <| by
    rintro _ _ ⟨β⟩
    exact Hom.two_heq_of_eq (h _) β

/-- **The disjoint union is the coproduct.** -/
def coprodIsColimit : IsColimit (Cofan.mk (coprod P) (coprodι P)) :=
  Cofan.IsColimit.mk _ (fun s => coprodDescHom P s.inj)
    (fun s i => coprodι_comp_descHom P s.inj i)
    fun s _ hf => coprod_hom_ext P fun i => (hf i).trans (coprodι_comp_descHom P s.inj i).symm

end Colim

/-! ## The 0-cells -/

/-- The leg a 0-cell lies in. -/
def coprodFibre (A : GenObj (coprod P).Gen) : ι := A.as.1

@[simp] theorem coprodFibre_ι (i : ι) (x : GenObj (P i).Gen) :
    coprodFibre P ((coprodι P i).pre.obj x) = i := rfl

/-- **A 0-cell of a coproduct is a leg's, and remembers which.** -/
def coprodObjEquiv : (Σ i : ι, GenObj (P i).Gen) ≃ GenObj (coprod P).Gen where
  toFun a := (coprodι P a.1).pre.obj a.2
  invFun A := ⟨A.as.1, ⟨A.as.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem coprod_pre_obj_injective (i : ι) :
    Function.Injective (coprodι P i).pre.obj := by
  rintro ⟨x⟩ ⟨y⟩ h
  have hxy : (⟨i, x⟩ : Σ i, (P i).V) = ⟨i, y⟩ := congrArg GenObj.as h
  simpa using hxy

/-- **…and the leg it lies in is the one it names.** -/
theorem coprod_index_eq {i j : ι} {x : GenObj (P i).Gen} {y : GenObj (P j).Gen}
    (h : (coprodι P i).pre.obj x = (coprodι P j).pre.obj y) : i = j :=
  congrArg (coprodFibre P) h

/-- **Every 0-cell of a coproduct is a leg's.** -/
theorem exists_coprod_obj (A : GenObj (coprod P).Gen) :
    ∃ (i : ι) (x : GenObj (P i).Gen), (coprodι P i).pre.obj x = A :=
  ⟨A.as.1, ⟨A.as.2⟩, rfl⟩

/-! ## The 1-cells -/

/-- **Every 1-cell of a coproduct is a leg's**, up to the transport its endpoints carry. -/
theorem exists_coprod_map {A B : GenObj (coprod P).Gen} (e : A ⟶ B) :
    ∃ (i : ι) (x y : GenObj (P i).Gen) (g : x ⟶ y)
      (hx : (coprodι P i).pre.obj x = A) (hy : (coprodι P i).pre.obj y = B),
      Quiver.homOfEq ((coprodι P i).pre.map g) hx hy = e := by
  obtain ⟨A⟩ := A
  obtain ⟨B⟩ := B
  cases e with
  | mk g => exact ⟨_, _, _, g, rfl, rfl, rfl⟩

theorem coprod_star_surjective (i : ι) (x : GenObj (P i).Gen) :
    Function.Surjective ((coprodι P i).pre.star x) := by
  rintro ⟨⟨⟨j, y⟩⟩, e⟩
  cases e with
  | mk g => exact ⟨⟨⟨_⟩, g⟩, rfl⟩

theorem coprod_star_injective (i : ι) (x : GenObj (P i).Gen) :
    Function.Injective ((coprodι P i).pre.star x) := by
  rintro ⟨y₁, e₁⟩ ⟨y₂, e₂⟩ h
  obtain ⟨hy, he⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : y₁ = y₂ := coprod_pre_obj_injective P i hy
  refine Sigma.ext rfl (heq_of_eq ?_)
  have hmk : CoprodGen.mk (P := P) e₁ = CoprodGen.mk e₂ := eq_of_heq he
  cases hmk
  rfl

theorem coprod_pre_map_injective (i : ι) {x y : GenObj (P i).Gen} :
    Function.Injective fun g : x ⟶ y => (coprodι P i).pre.map g := fun g g' h =>
  eq_of_heq (Sigma.mk.inj_iff.mp (coprod_star_injective P i x
    (show (coprodι P i).pre.star x ⟨y, g⟩ = (coprodι P i).pre.star x ⟨y, g'⟩ from
      Sigma.ext rfl (heq_of_eq h)))).2

instance coprod_pathsFunctor_faithful (i : ι) :
    (coprodι P i).pre.pathsFunctor.Faithful :=
  Prefunctor.pathsFunctor_faithful _ (coprod_star_injective P i)

theorem coprod_pathsFunctor_full (i : ι) : (coprodι P i).pre.pathsFunctor.Full :=
  Prefunctor.pathsFunctor_full _ (coprod_star_surjective P i) (coprod_pre_obj_injective P i)

theorem coprodFibre_eq_of_hom {A B : GenObj (coprod P).Gen} (e : A ⟶ B) :
    coprodFibre P A = coprodFibre P B := by
  obtain ⟨A⟩ := A
  obtain ⟨B⟩ := B
  cases e
  rfl

/-- **A word of a coproduct stays in the leg it starts in.** -/
theorem coprodFibre_eq_of_path {A B : GenObj (coprod P).Gen} (u : Quiver.Path A B) :
    coprodFibre P A = coprodFibre P B := by
  induction u with
  | nil => rfl
  | cons _ e ih => exact ih.trans (coprodFibre_eq_of_hom P e)

/-- **Every word of a coproduct is a leg's**, up to the transport its endpoints carry. -/
theorem exists_coprod_mapPath {A B : GenObj (coprod P).Gen} (u : Quiver.Path A B) :
    ∃ (i : ι) (x y : GenObj (P i).Gen)
      (hx : (coprodι P i).pre.obj x = A) (hy : (coprodι P i).pre.obj y = B)
      (u' : Quiver.Path x y),
      cellCongr Quiver.Path hx hy ((coprodι P i).pre.mapPath u') = u := by
  obtain ⟨i, x, rfl⟩ := exists_coprod_obj P A
  obtain ⟨j, y, rfl⟩ := exists_coprod_obj P B
  obtain rfl : i = j := coprodFibre_eq_of_path P u
  obtain ⟨u', hu'⟩ := (coprod_pathsFunctor_full P i).map_surjective (X := x) (Y := y) u
  exact ⟨i, x, y, rfl, rfl, u', hu'⟩

/-! ## The 2-cells -/

/-- **Every 2-cell of a coproduct is a leg's**, up to the transport its boundary carries. -/
theorem exists_coprod_two {A B : GenObj (coprod P).Gen} (α : (coprod P).Rel A B) :
    ∃ (i : ι) (x y : GenObj (P i).Gen)
      (hx : (coprodι P i).pre.obj x = A) (hy : (coprodι P i).pre.obj y = B)
      (β : (P i).Rel x y),
      cellCongr (coprod P).Rel hx hy ((coprodι P i).two β) = α := by
  cases α with
  | mk β => exact ⟨_, _, _, rfl, rfl, β, rfl⟩

/-- **A 2-cell over one leg's 0-cells is that leg's.** -/
theorem coprod_two_surjective (i : ι) {x y : GenObj (P i).Gen}
    (α : (coprod P).Rel ((coprodι P i).pre.obj x) ((coprodι P i).pre.obj y)) :
    ∃ β : (P i).Rel x y, (coprodι P i).two β = α := by
  obtain ⟨j, x', y', hx, hy, β, hβ⟩ := exists_coprod_two P α
  obtain rfl : i = j := (coprod_index_eq P hx).symm
  obtain rfl : x' = x := coprod_pre_obj_injective P i hx
  obtain rfl : y' = y := coprod_pre_obj_injective P i hy
  exact ⟨β, by simpa using hβ⟩

/-- **A 2-cell of the coproduct is its leg's boundary**: a leg is a covering, so words determine
themselves, and a leg's own 2-cells are pinned by theirs. -/
theorem boundaryDetermined_coprod (hP : ∀ i, (P i).BoundaryDetermined) :
    (coprod P).BoundaryDetermined := by
  intro A B α β hs ht
  obtain ⟨i, x, y, rfl, rfl, α', rfl⟩ := exists_coprod_two P α
  obtain ⟨β', rfl⟩ := coprod_two_surjective P i β
  refine congrArg (coprodι P i).two (hP i α' β' ?_ ?_)
  · exact (coprod_pathsFunctor_faithful P i).map_injective
      (((coprodι P i).src_two α').symm.trans (hs.trans ((coprodι P i).src_two β')))
  · exact (coprod_pathsFunctor_faithful P i).map_injective
      (((coprodι P i).tgt_two α').symm.trans (ht.trans ((coprodι P i).tgt_two β')))

end Polygraph

/-! ## What it presents

A family of presentations presents the disjoint union of the categories.  The interpretation of a
leg's cells is that leg's own, included — and definitionally so, which is why nothing below
transports. -/

namespace Presents

open Polygraph

variable {ι : Type u} {P : ι → Polygraph.{u, u, u}} {C : ι → Type u} [∀ i, Category.{u} (C i)]
  (p : ∀ i, Presents (P i) (C i))

/-- The cells of the coproduct, interpreted in the disjoint union of the categories. -/
def coproductEval : GenObj (coprod P).Gen ⥤q (Σ i, C i) :=
  Polygraph.coprodDesc P fun i => (p i).evalPre ⋙q (CategoryTheory.Sigma.incl i).toPrefunctor

/-- **A leg's 0-cell names its own object, included.** -/
theorem coproduct_at (i : ι) (x : GenObj (P i).Gen) :
    (coproductEval p).obj ((coprodι P i).pre.obj x) = ⟨i, (p i).at' x⟩ := rfl

/-- **A leg's word, evaluated in the coproduct** — that leg's own evaluation, included. -/
theorem lift_coproductEval_mapPath (i : ι) {x y : GenObj (P i).Gen} (u : Quiver.Path x y) :
    (Paths.lift (coproductEval p)).map ((coprodι P i).pre.mapPath u)
      = (CategoryTheory.Sigma.incl i).map ((p i).eval.map u) := by
  rw [Paths.lift_mapPath]
  exact (p i).lift_evalPre_comp (CategoryTheory.Sigma.incl i) u

theorem coproduct_sound {A B : GenObj (coprod P).Gen} (α : (coprod P).Rel A B) :
    (Paths.lift (coproductEval p)).map ((coprod P).src α)
      = (Paths.lift (coproductEval p)).map ((coprod P).tgt α) := by
  obtain ⟨i, x, y, rfl, rfl, β, rfl⟩ := Polygraph.exists_coprod_two P α
  simp only [cellCongr_self]
  rw [(coprodι P i).src_two, (coprodι P i).tgt_two,
    lift_coproductEval_mapPath, lift_coproductEval_mapPath]
  exact congrArg (fun t : (p i).at' x ⟶ (p i).at' y => (CategoryTheory.Sigma.incl i).map t)
    ((p i).sound β)

theorem coproduct_complete {A B : GenObj (coprod P).Gen} {u v : Quiver.Path A B}
    (h : (Paths.lift (coproductEval p)).map u = (Paths.lift (coproductEval p)).map v) :
    (coprod P).quot.map u = (coprod P).quot.map v := by
  obtain ⟨i, x, y, rfl, rfl, u', rfl⟩ := Polygraph.exists_coprod_mapPath P u
  obtain ⟨v', rfl⟩ := (Polygraph.coprod_pathsFunctor_full P i).map_surjective (X := x) (Y := y) v
  simp only [cellCongr_self, Prefunctor.pathsFunctor_map] at h ⊢
  rw [lift_coproductEval_mapPath, lift_coproductEval_mapPath] at h
  exact (coprodι P i).quot_map_congr
    ((p i).E.map_injective ((CategoryTheory.Sigma.incl i).map_injective h))

theorem coproduct_full : (Paths.lift (coproductEval p)).Full where
  map_surjective := by
    intro A B f
    obtain ⟨i, x, rfl⟩ := Polygraph.exists_coprod_obj P A
    obtain ⟨j, y, rfl⟩ := Polygraph.exists_coprod_obj P B
    obtain ⟨k, a, b, g, hxa, hyb, rfl⟩ := CategoryTheory.Sigma.exists_incl_map f
    obtain rfl : i = k := (Sigma.mk.inj_iff.mp (hxa.trans (coproduct_at p i x))).1.symm
    obtain rfl : i = j := (Sigma.mk.inj_iff.mp (hyb.trans (coproduct_at p j y))).1
    obtain rfl : a = (p i).at' x :=
      eq_of_heq (Sigma.mk.inj_iff.mp (hxa.trans (coproduct_at p i x))).2
    obtain rfl : b = (p i).at' y :=
      eq_of_heq (Sigma.mk.inj_iff.mp (hyb.trans (coproduct_at p i y))).2
    obtain ⟨w, rfl⟩ := (p i).eval.map_surjective g
    exact ⟨(coprodι P i).pre.mapPath w, lift_coproductEval_mapPath p i w⟩

theorem coproduct_essSurj : (Paths.lift (coproductEval p)).EssSurj where
  mem_essImage := by
    rintro ⟨i, c⟩
    obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := (p i).eval) c
    exact ⟨(coprodι P i).pre.obj x, ⟨(CategoryTheory.Sigma.incl i).mapIso e⟩⟩

/-- **A family of presentations presents the disjoint union.** -/
def coproduct : Presents (coprod P) (Σ i, C i) :=
  Presents.ofDesc (coproductEval p) (coproduct_sound p) (coproduct_complete p) (coproduct_full p)
    (coproduct_essSurj p)

/-- **A leg's 1-cell names its own arrow, included.** -/
theorem coproduct_arrow (i : ι) {x y : GenObj (P i).Gen} (g : x ⟶ y) :
    (Presents.coproduct p).arrow ((coprodι P i).pre.map g)
      = (CategoryTheory.Sigma.incl i).map ((p i).arrow g) :=
  Presents.ofDesc_arrow _ (coproduct_sound p) _

end Presents

end CategoryTheory
