import CubeChains.Foundations.Grading
import Mathlib.CategoryTheory.Category.Factorisation
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Quotient
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Foundations/CutGradedPresentation — a category presented by its one-cut generators

A **cut grading** gives every morphism a finite set of *heights* (`cuts`), additive along
composition, with `codim` its cardinality.  `presentation`: the free category on the one-cut
morphisms, modulo "two two-step factorisations of one morphism agree", *is* `D`, identity on
objects.

Two axioms past the grading: `isId_of_codim_eq_zero`, and `factor_last` — a morphism splits off a
generator at the back at each height it cuts, in exactly one way.  Existence gives `exists_swap`,
uniqueness `gen_ext`, and the proof is then a selection sort (`exists_min_last`), minimality
carried as a bound so that no nonemptiness witness is threaded through.
-/

universe v u

open CategoryTheory

/-- Two factorisations that agree, compared field by field. -/
theorem CategoryTheory.Factorisation.congr {C : Type u} [Category.{v} C] {X Y : C} {f : X ⟶ Y}
    {p q : Factorisation f} (h : p = q) :
    ∃ hm : p.mid = q.mid, p.ι ≫ eqToHom hm = q.ι ∧ eqToHom hm ≫ q.π = p.π := by
  subst h
  exact ⟨rfl, by simp, by simp⟩

/-- **Factorisations in the opposite category are factorisations read backwards.** -/
def CategoryTheory.factorisationOpEquiv {C : Type u} [Category.{v} C] {X Y : Cᵒᵖ} (F : X ⟶ Y) :
    Factorisation F ≃ Factorisation F.unop where
  toFun p := ⟨p.mid.unop, p.π.unop, p.ι.unop, by rw [← unop_comp, p.ι_π]⟩
  invFun q := ⟨Opposite.op q.mid, q.π.op, q.ι.op, by rw [← op_comp, q.ι_π]; rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace CutGraded

variable {D : Type u} [Category.{v} D]

/-- **A category graded by junction heights** — a `Grading` whose codimension counts a finite set
of heights (`cuts`).  The two non-formal axioms are rigidity in codimension zero and `factor_last`:
at every height it cuts, a morphism splits off a generator at the back in exactly one way. -/
structure Data (D : Type u) [Category.{v} D] extends Grading D where
  /-- The heights a morphism removes. -/
  cuts : ∀ {a b : D}, (a ⟶ b) → Finset ℕ
  /-- **Codimension counts heights.** -/
  card_cuts : ∀ {a b : D} (f : a ⟶ b), (cuts f).card = codim f
  /-- Heights add along composites. -/
  cuts_comp : ∀ {a b c : D} (f : a ⟶ b) (g : b ⟶ c), cuts (f ≫ g) = cuts f ∪ cuts g
  /-- **Rigidity**: codimension zero leaves nothing to say. -/
  isId_of_codim_eq_zero : ∀ {a b : D} (f : a ⟶ b), codim f = 0 → ∃ h : a = b, f = eqToHom h
  /-- **A generator splits off at the back at any height, in exactly one way.** -/
  factor_last : ∀ {a b : D} (f : a ⟶ b) {t : ℕ}, t ∈ cuts f →
    ∃! p : Factorisation f, cuts p.π = {t}

namespace Data

variable (G : Data D)

/-- `e` removes exactly the height `t`. -/
def CutsAt {a b : D} (e : a ⟶ b) (t : ℕ) : Prop := G.cuts e = {t}

variable {G}

theorem CutsAt.cuts_eq {a b : D} {e : a ⟶ b} {t : ℕ} (h : G.CutsAt e t) : G.cuts e = {t} := h

theorem CutsAt.codim_eq {a b : D} {e : a ⟶ b} {t : ℕ} (h : G.CutsAt e t) : G.codim e = 1 := by
  rw [← G.card_cuts, h.cuts_eq, Finset.card_singleton]

theorem CutsAt.mem_cuts {a b : D} {e : a ⟶ b} {t : ℕ} (h : G.CutsAt e t) : t ∈ G.cuts e := by
  rw [h.cuts_eq]; exact Finset.mem_singleton_self t

/-- A generator removes no height but its own. -/
theorem CutsAt.eq_of_mem {a b : D} {e : a ⟶ b} {t s : ℕ} (h : G.CutsAt e t)
    (hs : s ∈ G.cuts e) : s = t := by
  rw [h.cuts_eq] at hs
  exact Finset.mem_singleton.mp hs

theorem exists_cutsAt {a b : D} (e : a ⟶ b) (he : G.codim e = 1) : ∃ t, G.CutsAt e t :=
  Finset.card_eq_one.mp ((G.card_cuts e).trans he)

variable (G)

/-- **Consecutive factors cut at disjoint heights** — their two cardinalities already add up. -/
theorem disjoint_cuts {a b c : D} (f : a ⟶ b) (g : b ⟶ c) : Disjoint (G.cuts f) (G.cuts g) := by
  have hcard : (G.cuts f ∪ G.cuts g).card = (G.cuts f).card + (G.cuts g).card := by
    rw [← G.cuts_comp, G.card_cuts, G.card_cuts, G.card_cuts, G.codim_comp]
  have hint := Finset.card_union_add_card_inter (G.cuts f) (G.cuts g)
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
  omega

/-- **A factorisation is pinned by the height its last step cuts at** — the uniqueness half of
`factor_last`, with the two factorisations spelled out. -/
theorem gen_ext {a b : D} {f : a ⟶ b} {c c' : D} {g : a ⟶ c} {e : c ⟶ b} {g' : a ⟶ c'}
    {e' : c' ⟶ b} (hge : g ≫ e = f) (hge' : g' ≫ e' = f) {t : ℕ}
    (ht : G.cuts e = {t}) (ht' : G.cuts e' = {t}) :
    ∃ h : c = c', g ≫ eqToHom h = g' ∧ eqToHom h ≫ e' = e := by
  have hmem : t ∈ G.cuts f := by
    rw [← hge, G.cuts_comp, ht]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self t)
  obtain ⟨r, -, huniq⟩ := G.factor_last f hmem
  exact Factorisation.congr
    ((huniq ⟨c, g, e, hge⟩ ht).trans (huniq ⟨c', g', e', hge'⟩ ht').symm)

/-- **Two consecutive generators re-factor with their heights exchanged** — split the *first*
one's height off the back of the composite; disjointness leaves the second's in front. -/
theorem exists_swap {a c b : D} {e₀ : a ⟶ c} {e₁ : c ⟶ b} {t₀ t₁ : ℕ}
    (h₀ : G.cuts e₀ = {t₀}) (h₁ : G.cuts e₁ = {t₁}) :
    ∃ (c' : D) (u : a ⟶ c') (v : c' ⟶ b),
      G.cuts u = {t₁} ∧ G.cuts v = {t₀} ∧ u ≫ v = e₀ ≫ e₁ := by
  have hne : t₀ ≠ t₁ := fun h =>
    Finset.disjoint_left.mp (G.disjoint_cuts e₀ e₁) (h₀ ▸ Finset.mem_singleton_self t₀)
      (h₁ ▸ h ▸ Finset.mem_singleton_self t₁)
  have hcuts : G.cuts (e₀ ≫ e₁) = {t₀} ∪ {t₁} := by rw [G.cuts_comp, h₀, h₁]
  obtain ⟨p, hp, -⟩ := G.factor_last (e₀ ≫ e₁)
    (by rw [hcuts]; exact Finset.mem_union_left _ (Finset.mem_singleton_self t₀))
  have hmem : ∀ s, s ∈ G.cuts p.ι ∨ s ∈ G.cuts p.π ↔ s = t₀ ∨ s = t₁ := fun s => by
    have h : s ∈ G.cuts p.ι ∪ G.cuts p.π ↔ s ∈ ({t₀} : Finset ℕ) ∪ {t₁} := by
      rw [← G.cuts_comp, p.ι_π, hcuts]
    simpa only [Finset.mem_union, Finset.mem_singleton] using h
  refine ⟨p.mid, p.ι, p.π, Finset.ext fun s => ?_, hp, p.ι_π⟩
  rw [Finset.mem_singleton]
  constructor
  · intro hs
    have h₂ : s ∉ G.cuts p.π := Finset.disjoint_left.mp (G.disjoint_cuts p.ι p.π) hs
    refine ((hmem s).mp (Or.inl hs)).resolve_left fun h => h₂ ?_
    rw [hp, h]; exact Finset.mem_singleton_self t₀
  · rintro rfl
    refine ((hmem s).mpr (Or.inr rfl)).resolve_right fun h => hne ?_
    rw [hp, Finset.mem_singleton] at h
    exact h.symm

/-- **A morphism of positive codimension splits off a generator at the back.** -/
theorem exists_last {a b : D} (f : a ⟶ b) (hf : G.codim f ≠ 0) :
    ∃ (c : D) (g : a ⟶ c) (e : c ⟶ b), G.codim e = 1 ∧ g ≫ e = f := by
  obtain ⟨t, ht⟩ : ∃ t, t ∈ G.cuts f :=
    Finset.card_pos.mp (by rw [G.card_cuts]; omega)
  obtain ⟨p, hp, -⟩ := G.factor_last f ht
  exact ⟨p.mid, p.ι, p.π, CutsAt.codim_eq (G := G) hp, p.ι_π⟩

end Data

/-! ### The generating quiver -/

/-- The objects of `D`, as the vertices of the generating quiver. -/
def Vert (_G : Data D) : Type u := D

/-- The object a vertex names. -/
def Vert.as {G : Data D} (a : Vert G) : D := a

/-- The vertex an object names. -/
def Vert.mk {G : Data D} (a : D) : Vert G := a

/-- A generating edge — a morphism removing a single height. -/
def Gen (G : Data D) (a b : D) : Type v := {f : a ⟶ b // G.codim f = 1}

instance (G : Data D) : Quiver.{v} (Vert G) := ⟨fun a b => Gen G a.as b.as⟩

/-- The generator named by a one-cut morphism.  `show … from` is what crosses the type synonym:
the quiver instance does not unfold at anonymous-constructor transparency. -/
def gen {G : Data D} {a b : Vert G} (f : a.as ⟶ b.as) (hf : G.codim f = 1) : a ⟶ b :=
  show Gen G a.as b.as from ⟨f, hf⟩

/-- The morphism a generator names. -/
def genHom {G : Data D} {a b : Vert G} (e : a ⟶ b) : a.as ⟶ b.as :=
  (show Gen G a.as b.as from e).1

theorem codim_genHom {G : Data D} {a b : Vert G} (e : a ⟶ b) : G.codim (genHom e) = 1 :=
  (show Gen G a.as b.as from e).2

/-- Every generator is named, with its codimension split off. -/
theorem exists_gen {G : Data D} {a b : Vert G} (e : a ⟶ b) :
    ∃ (f : a.as ⟶ b.as) (hf : G.codim f = 1), e = gen f hf := ⟨genHom e, codim_genHom e, rfl⟩

/-- The generating quiver's inclusion into `D`. -/
def evalPre (G : Data D) : Vert G ⥤q D where
  obj a := a.as
  map {_ _} e := genHom e

/-- Evaluation of a generating path — identity on objects. -/
def eval (G : Data D) : CategoryTheory.Paths (Vert G) ⥤ D := Paths.lift (evalPre G)

theorem codim_eval {G : Data D} {a b : Vert G} (P : Quiver.Path a b) :
    G.codim ((eval G).map P) = P.length := by
  induction P with
  | nil => exact G.codim_id _
  | cons P e ih =>
      have h : G.codim ((eval G).map (P.cons e))
          = G.codim ((eval G).map P) + G.codim (genHom e) := G.codim_comp _ _
      rw [h, ih, codim_genHom]
      rfl

/-- **The one-cut generators generate.**  Peel a generator off the back and induct on the
codimension; rigidity closes the base. -/
theorem exists_path {G : Data D} : ∀ (n : ℕ) {a b : D} (f : a ⟶ b), G.codim f ≤ n →
    ∃ P : Quiver.Path (Vert.mk a : Vert G) (Vert.mk b), (eval G).map P = f := by
  intro n
  induction n with
  | zero =>
      intro a b f hf
      obtain ⟨rfl, rfl⟩ := G.isId_of_codim_eq_zero f (Nat.le_zero.mp hf)
      exact ⟨Quiver.Path.nil, (eqToHom_refl a rfl).symm⟩
  | succ n ih =>
      intro a b f hf
      rcases Nat.eq_zero_or_pos (G.codim f) with h0 | hpos
      · obtain ⟨rfl, rfl⟩ := G.isId_of_codim_eq_zero f h0
        exact ⟨Quiver.Path.nil, (eqToHom_refl a rfl).symm⟩
      · obtain ⟨c, g, e, he, hge⟩ := G.exists_last f (by omega)
        have hc : G.codim g ≤ n := by
          have := G.codim_comp g e
          rw [hge, he] at this
          omega
        obtain ⟨P, hP⟩ := ih g hc
        exact ⟨P.cons (gen (a := Vert.mk c) (b := Vert.mk b) e he), by
          rw [show (eval G).map (P.cons (gen (a := Vert.mk c) (b := Vert.mk b) e he))
            = (eval G).map P ≫ e from rfl, hP]
          exact hge⟩

/-! ### The relation -/

/-- The one-cut generators of a two-step factorisation, as a two-edge path. -/
def twoStep {G : Data D} {a b : Vert G} {c : D} {e₀ : a.as ⟶ c} {e₁ : c ⟶ b.as}
    (h₀ : G.codim e₀ = 1) (h₁ : G.codim e₁ = 1) : Quiver.Path a b :=
  (Quiver.Path.nil.cons (gen (b := Vert.mk c) e₀ h₀)).cons (gen e₁ h₁)

@[simp] theorem eval_twoStep {G : Data D} {a b : Vert G} {c : D} {e₀ : a.as ⟶ c} {e₁ : c ⟶ b.as}
    (h₀ : G.codim e₀ = 1) (h₁ : G.codim e₁ = 1) :
    (eval G).map (twoStep h₀ h₁) = e₀ ≫ e₁ :=
  congrArg (fun m => m ≫ e₁) (Category.id_comp e₀)

/-- **The codimension-two relation**: the two-step factorisations of one morphism agree. -/
def rel (G : Data D) : HomRel (CategoryTheory.Paths (Vert G)) := fun a b P Q =>
  ∃ (c c' : D) (e₀ : a.as ⟶ c) (e₁ : c ⟶ b.as) (u : a.as ⟶ c') (v : c' ⟶ b.as)
    (h₀ : G.codim e₀ = 1) (h₁ : G.codim e₁ = 1) (hu : G.codim u = 1) (hv : G.codim v = 1),
    e₀ ≫ e₁ = u ≫ v ∧ P = twoStep h₀ h₁ ∧ Q = twoStep hu hv

theorem eval_map_eq_of_rel {G : Data D} {a b : Vert G} {P Q : Quiver.Path a b}
    (h : rel G P Q) : (eval G).map P = (eval G).map Q := by
  obtain ⟨c, c', e₀, e₁, u, v, h₀, h₁, hu, hv, hcomp, rfl, rfl⟩ := h
  rw [eval_twoStep, eval_twoStep, hcomp]

/-- The passage to the quotient. -/
noncomputable abbrev quotF (G : Data D) :
    CategoryTheory.Paths (Vert G) ⥤ CategoryTheory.Quotient (rel G) :=
  Quotient.functor (rel G)

theorem quot_cons {G : Data D} {x y z : Vert G} (P : Quiver.Path x y) (e : y ⟶ z) :
    (quotF G).map (P.cons e) = (quotF G).map P ≫ (quotF G).map e.toPath :=
  (quotF G).map_comp P e.toPath

/-- The relation, as an identity between two-step composites in the quotient. -/
theorem quot_swap {G : Data D} {x z : Vert G} {y w : D} {e₀ : x.as ⟶ y} {e₁ : y ⟶ z.as}
    {u : x.as ⟶ w} {v : w ⟶ z.as} (h₀ : G.codim e₀ = 1) (h₁ : G.codim e₁ = 1)
    (hu : G.codim u = 1) (hv : G.codim v = 1) (h : e₀ ≫ e₁ = u ≫ v) :
    (quotF G).map (gen (b := Vert.mk y) e₀ h₀).toPath ≫ (quotF G).map (gen e₁ h₁).toPath
      = (quotF G).map (gen (b := Vert.mk w) u hu).toPath ≫ (quotF G).map (gen v hv).toPath := by
  rw [← (quotF G).map_comp, ← (quotF G).map_comp]
  exact CategoryTheory.Quotient.sound _ ⟨y, w, e₀, e₁, u, v, h₀, h₁, hu, hv, h, rfl, rfl⟩

/-! ### Sorting a generating path -/

/-- **The lowest cut can be made last** — the last step cuts at a height no cut of the path is
below. -/
theorem exists_min_last {G : Data D} : ∀ (n : ℕ) {a b : Vert G} (P : Quiver.Path a b),
    P.length = n + 1 →
    ∃ (c : Vert G) (R : Quiver.Path a c) (e : c.as ⟶ b.as) (he : G.codim e = 1) (t : ℕ),
      G.CutsAt e t ∧ (∀ s ∈ G.cuts ((eval G).map P), t ≤ s) ∧ R.length + 1 = P.length ∧
        (eval G).map R ≫ e = (eval G).map P ∧
        (quotF G).map P = (quotF G).map (R.cons (gen e he)) := by
  intro n
  induction n with
  | zero =>
      intro a b P hP
      cases P with
      | nil => simp at hP
      | cons P' e =>
          cases P' with
          | cons P'' d => simp at hP
          | nil =>
              obtain ⟨e₁, he₁, rfl⟩ := exists_gen e
              obtain ⟨t, ht⟩ := Data.exists_cutsAt e₁ he₁
              have hev : (eval G).map (Quiver.Path.nil.cons (gen e₁ he₁)) = e₁ :=
                Category.id_comp e₁
              refine ⟨a, Quiver.Path.nil, e₁, he₁, t, ht, fun s hs => ?_, rfl, rfl, rfl⟩
              rw [hev] at hs
              exact (ht.eq_of_mem hs).ge
  | succ n ih =>
      intro a b P hP
      cases P with
      | nil => simp at hP
      | cons P' e =>
          obtain ⟨e₁, he₁, rfl⟩ := exists_gen e
          have hP' : P'.length = n + 1 := by simpa using hP
          obtain ⟨c₀, R', e₀, he₀, t₀, hcut₀, hmin₀, hlen₀, hcomp₀, hquot₀⟩ := ih P' hP'
          obtain ⟨t₁, ht₁⟩ := Data.exists_cutsAt e₁ he₁
          have hcuts : G.cuts ((eval G).map (P'.cons (gen e₁ he₁)))
              = G.cuts ((eval G).map P') ∪ G.cuts e₁ := G.cuts_comp ((eval G).map P') e₁
          have hbound : ∀ (t : ℕ), (∀ u ∈ G.cuts ((eval G).map P'), t ≤ u) → t ≤ t₁ →
              ∀ s ∈ G.cuts ((eval G).map (P'.cons (gen e₁ he₁))), t ≤ s := by
            intro t hP₀ ht₁' s hs
            rw [hcuts, Finset.mem_union, ht₁.cuts_eq, Finset.mem_singleton] at hs
            rcases hs with hs | rfl
            · exact hP₀ s hs
            · exact ht₁'
          rcases le_total t₁ t₀ with hle | hle
          · exact ⟨_, P', e₁, he₁, t₁, ht₁,
              hbound t₁ (fun u hu => hle.trans (hmin₀ u hu)) le_rfl, rfl, rfl, rfl⟩
          obtain ⟨c', u, v, hu, hv, huv⟩ := G.exists_swap hcut₀.cuts_eq ht₁.cuts_eq
          have hu' : G.codim u = 1 := Data.CutsAt.codim_eq hu
          have hv' : G.codim v = 1 := Data.CutsAt.codim_eq hv
          refine ⟨Vert.mk c', R'.cons (gen u hu'), v, hv', t₀, hv,
            hbound t₀ hmin₀ hle, by simpa using hlen₀, ?_, ?_⟩
          · calc (eval G).map (R'.cons (gen u hu')) ≫ v
                = ((eval G).map R' ≫ u) ≫ v := rfl
              _ = (eval G).map R' ≫ u ≫ v := Category.assoc _ _ _
              _ = (eval G).map R' ≫ e₀ ≫ e₁ :=
                  congrArg (fun m => (eval G).map R' ≫ m) huv
              _ = ((eval G).map R' ≫ e₀) ≫ e₁ := (Category.assoc _ _ _).symm
              _ = (eval G).map (P'.cons (gen e₁ he₁)) :=
                  congrArg (fun m => m ≫ e₁) hcomp₀
          · calc (quotF G).map (P'.cons (gen e₁ he₁))
                = (quotF G).map (R'.cons (gen e₀ he₀)) ≫ (quotF G).map (gen e₁ he₁).toPath := by
                  rw [quot_cons, hquot₀]
              _ = (quotF G).map R' ≫ ((quotF G).map (gen e₀ he₀).toPath
                    ≫ (quotF G).map (gen e₁ he₁).toPath) := by
                  rw [quot_cons, Category.assoc]
              -- `congrArg`, not `rw`: the middle vertex is spelled `Vert.mk c'` in `quot_swap`
              -- and `c'` here, which are defeq but not syntactically equal
              _ = (quotF G).map R' ≫ ((quotF G).map (gen u hu').toPath
                    ≫ (quotF G).map (gen v hv').toPath) :=
                  congrArg (fun m => (quotF G).map R' ≫ m)
                    (quot_swap he₀ he₁ hu' hv' huv.symm)
              _ = (quotF G).map ((R'.cons (gen u hu')).cons (gen v hv')) := by
                  rw [quot_cons (R'.cons (gen u hu')) (gen v hv'), quot_cons R' (gen u hu'),
                    Category.assoc]

/-- **Two generating paths with the same value agree in the quotient.**  Sort both; the two last
steps then cut at the same height, so they — and everything before them — coincide. -/
theorem quot_eq_of_eval_eq {G : Data D} : ∀ (n : ℕ) {a b : Vert G} (P Q : Quiver.Path a b),
    P.length = n → (eval G).map P = (eval G).map Q →
    (quotF G).map P = (quotF G).map Q := by
  intro n
  induction n with
  | zero =>
      intro a b P Q hP h
      cases P with
      | cons P' e => simp at hP
      | nil =>
          cases Q with
          | nil => rfl
          | cons Q' d =>
              exfalso
              have h₀ : G.codim ((eval G).map (Quiver.Path.nil (a := a))) = 0 := G.codim_id _
              rw [h, codim_eval] at h₀
              simp at h₀
  | succ n ih =>
      intro a b P Q hP h
      have hQ : Q.length = n + 1 := by
        have h₁ := codim_eval P
        have h₂ := codim_eval Q
        rw [h] at h₁
        omega
      obtain ⟨c, R, e, he, t, hcut, hmin, hlenR, hcompR, hquotP⟩ := exists_min_last n P hP
      obtain ⟨c', S, d, hd, t', hcut', hmin', -, hcompS, hquotQ⟩ := exists_min_last n Q hQ
      have hcompS' : (eval G).map S ≫ d = (eval G).map P := hcompS.trans h.symm
      have hcP : G.cuts ((eval G).map P) = G.cuts ((eval G).map R) ∪ G.cuts e := by
        rw [← hcompR]; exact G.cuts_comp ((eval G).map R) e
      have hcQ : G.cuts ((eval G).map Q) = G.cuts ((eval G).map S) ∪ G.cuts d := by
        rw [← hcompS]; exact G.cuts_comp ((eval G).map S) d
      have htmem : t ∈ G.cuts ((eval G).map P) := by
        rw [hcP]; exact Finset.mem_union_right _ hcut.mem_cuts
      have ht'mem : t' ∈ G.cuts ((eval G).map Q) := by
        rw [hcQ]; exact Finset.mem_union_right _ hcut'.mem_cuts
      obtain rfl : t = t' :=
        Nat.le_antisymm (hmin t' (by rw [h]; exact ht'mem)) (hmin' t (by rw [← h]; exact htmem))
      obtain ⟨hcc, hgg, hee⟩ := G.gen_ext hcompR hcompS' hcut.cuts_eq hcut'.cuts_eq
      obtain rfl : c = c' := hcc
      rw [eqToHom_refl, Category.comp_id] at hgg
      rw [eqToHom_refl, Category.id_comp] at hee
      subst hee
      have hRS := ih R S (by omega) hgg
      rw [hquotP, hquotQ, quot_cons, quot_cons, hRS]

/-! ### The presentation -/

/-- **The presentation functor**: evaluate a generating path, on the quotient. -/
noncomputable def presentationFunctor (G : Data D) :
    CategoryTheory.Quotient (rel G) ⥤ D :=
  CategoryTheory.Quotient.lift (rel G) (eval G) (fun _ _ _ _ h => eval_map_eq_of_rel h)

instance (G : Data D) : (presentationFunctor G).Full where
  map_surjective := by
    rintro ⟨X⟩ ⟨Y⟩ f
    obtain ⟨P, rfl⟩ := exists_path (G := G) (G.codim f) f le_rfl
    exact ⟨(quotF G).map P, rfl⟩

instance (G : Data D) : (presentationFunctor G).Faithful where
  map_injective := by
    rintro ⟨X⟩ ⟨Y⟩ f g hfg
    obtain ⟨P, rfl⟩ := (quotF G).map_surjective f
    obtain ⟨Q, rfl⟩ := (quotF G).map_surjective g
    have h' : (eval G).map P = (eval G).map Q := hfg
    exact quot_eq_of_eval_eq _ P Q rfl h'

instance (G : Data D) : (presentationFunctor G).EssSurj where
  mem_essImage X := ⟨{ as := Vert.mk X }, ⟨Iso.refl X⟩⟩

instance (G : Data D) : (presentationFunctor G).IsEquivalence where

/-- **`D` is presented by its one-cut generators modulo its two-step relations** — identity on
objects. -/
noncomputable def presentation (G : Data D) : CategoryTheory.Quotient (rel G) ≌ D :=
  (presentationFunctor G).asEquivalence

@[simp] theorem presentation_obj (G : Data D) (a : D) :
    (presentation G).functor.obj { as := Vert.mk a } = a := rfl

end CutGraded
