import CubeChains.Concurrency.Grading.Coarser
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Concurrency/Presentation/CutPresentation — `Ch Zbp` presented by its bead cuts

Generators the codimension-one refinements, relations the codimension-two ones, read in the
opposite category — the form `Concurrency/Presentation/LiftPresentation` transports to `Ch K`.

Everything rests on **factorisation** (`Concurrency/Grading/Coarser`), and on nothing else: unique
factorisation through an intermediate shape (`exists_factor`, `factor_ext`), additivity of `codim`,
splitting a codimension-one step off the front (`exists_first`), and the diamond closing two of
them (`exists_diamond`).  How a shape is modelled does not reach this file.
-/

open CategoryTheory Equiv Opposite BPSet CubeChain CubeChains

namespace ChainCat

open CubeChains

variable {a m b : Ch Zbp}

/-! ## The generating quiver

An edge runs the way a *path* does — from the coarse shape to the fine one — so that
`eval` lands in `(Ch Zbp)ᵒᵖ`, the form the transport to `Ch K` consumes. -/

namespace Cut

/-- The shapes, as the vertices of the generating quiver. -/
def Vert : Type := Ch Zbp

/-- The shape a vertex names. -/
def Vert.as (x : Vert) : Ch Zbp := x

/-- The vertex a shape names. -/
def Vert.mk (x : Ch Zbp) : Vert := x

/-- A generating edge — a refinement removing a single boundary, pointing at its fine end. -/
def Gen (x y : Vert) := {f : y.as ⟶ x.as // codim f = 1}

instance : Quiver Vert := ⟨Gen⟩

/-- The generator named by a one-cut refinement.  `show … from` is what crosses the type synonym:
the quiver instance does not unfold at anonymous-constructor transparency. -/
def gen {x y : Vert} (f : y.as ⟶ x.as) (hf : codim f = 1) : x ⟶ y :=
  show Gen x y from ⟨f, hf⟩

/-- The refinement a generator names. -/
def genHom {x y : Vert} (e : x ⟶ y) : y.as ⟶ x.as := (show Gen x y from e).1

theorem codim_genHom {x y : Vert} (e : x ⟶ y) : codim (genHom e) = 1 :=
  (show Gen x y from e).2

/-- Every generator is named, with its codimension split off. -/
theorem exists_gen {x y : Vert} (e : x ⟶ y) :
    ∃ (f : y.as ⟶ x.as) (hf : codim f = 1), e = gen f hf := ⟨genHom e, codim_genHom e, rfl⟩

/-- The generating quiver's inclusion. -/
def evalPre : Vert ⥤q (Ch Zbp)ᵒᵖ where
  obj x := op x.as
  map {_ _} e := (genHom e).op

/-- Evaluation of a generating path — identity on objects. -/
def eval : CategoryTheory.Paths Vert ⥤ (Ch Zbp)ᵒᵖ := Paths.lift evalPre

/-- The refinement a generating path performs: consing an edge *pre*composes. -/
def ev {x y : Vert} (P : Quiver.Path x y) : y.as ⟶ x.as := (eval.map P).unop

@[simp] theorem ev_nil {x : Vert} : ev (Quiver.Path.nil : Quiver.Path x x) = 𝟙 x.as := rfl

@[simp] theorem ev_cons {x y z : Vert} (P : Quiver.Path x y) (e : y ⟶ z) :
    ev (P.cons e) = genHom e ≫ ev P := rfl

theorem eval_map_eq_iff {x y : Vert} {P Q : Quiver.Path x y} :
    eval.map P = eval.map Q ↔ ev P = ev Q :=
  ⟨congrArg Quiver.Hom.unop, fun h => Quiver.Hom.unop_inj h⟩

theorem codim_ev {x y : Vert} (P : Quiver.Path x y) : codim (ev P) = P.length := by
  induction P with
  | nil => exact codim_id _
  | cons P e ih =>
      rw [ev_cons, codim_comp, codim_genHom, ih]
      exact Nat.add_comm _ _

theorem length_eq_of_ev_eq {x y : Vert} {P Q : Quiver.Path x y} (h : ev P = ev Q) :
    P.length = Q.length := by rw [← codim_ev, ← codim_ev, h]

/-- **The one-cut refinements generate.**  Peel a generator off the front and induct on the
codimension; a codimension-zero refinement is an identity. -/
theorem exists_path : ∀ (n : ℕ) {a b : Ch Zbp} (f : a ⟶ b), codim f ≤ n →
    ∃ P : Quiver.Path (Vert.mk b) (Vert.mk a), ev P = f := by
  intro n
  induction n with
  | zero =>
      intro a b f hf
      obtain rfl : a = b := (codim_eq_zero_iff f).mp (Nat.le_zero.mp hf)
      exact ⟨Quiver.Path.nil, (endo_eq_id f).symm⟩
  | succ n ih =>
      intro a b f hf
      rcases Nat.eq_zero_or_pos (codim f) with h0 | hpos
      · exact ih f (by omega)
      · obtain ⟨c, e, g, he, heg⟩ := exists_first f (by omega)
        have hc : codim g ≤ n := by
          have := codim_comp e g
          rw [heg, he] at this
          omega
        obtain ⟨P, hP⟩ := ih g hc
        exact ⟨P.cons (gen (x := Vert.mk c) (y := Vert.mk a) e he), by rw [ev_cons, hP]; exact heg⟩

/-! ### The relation -/

/-- **The codimension-two relation**: two two-step factorisations of one refinement.  A path of
length two *is* a two-step factorisation, so nothing more need be said. -/
def rel : HomRel (CategoryTheory.Paths Vert) := fun _ _ P Q =>
  P.length = 2 ∧ Q.length = 2 ∧ ev P = ev Q

/-- The passage to the quotient. -/
noncomputable abbrev quotF : CategoryTheory.Paths Vert ⥤ CategoryTheory.Quotient rel :=
  Quotient.functor rel

theorem quot_cons {x y z : Vert} (P : Quiver.Path x y) (e : y ⟶ z) :
    quotF.map (P.cons e) = quotF.map P ≫ quotF.map e.toPath :=
  quotF.map_comp P e.toPath

/-- The relation, as an identity between two-step composites in the quotient. -/
theorem quot_swap {x y : Vert} {c c' : Ch Zbp} {e₀ : c ⟶ x.as} {e₁ : y.as ⟶ c}
    {u : c' ⟶ x.as} {v : y.as ⟶ c'} (h₀ : codim e₀ = 1) (h₁ : codim e₁ = 1)
    (hu : codim u = 1) (hv : codim v = 1) (h : e₁ ≫ e₀ = v ≫ u) :
    quotF.map (gen (x := x) (y := Vert.mk c) e₀ h₀).toPath
        ≫ quotF.map (gen (x := Vert.mk c) (y := y) e₁ h₁).toPath
      = quotF.map (gen (x := x) (y := Vert.mk c') u hu).toPath
        ≫ quotF.map (gen (x := Vert.mk c') (y := y) v hv).toPath := by
  rw [← quotF.map_comp, ← quotF.map_comp]
  refine CategoryTheory.Quotient.sound _ ⟨rfl, rfl, ?_⟩
  change e₁ ≫ e₀ ≫ 𝟙 x.as = v ≫ u ≫ 𝟙 x.as
  rw [Category.comp_id, Category.comp_id, h]

/-! ## Confluence -/

/-- **A generating path can be re-cut to start at any factorisation of its value.**  Induct down
the path: either the first step already *is* the one wanted, or the diamond replaces the pair by
the other two sides, and `quot_swap` says the quotient does not see the exchange. -/
theorem exists_front : ∀ (n : ℕ) {x y : Vert} (P : Quiver.Path x y), P.length = n →
    ∀ {c : Ch Zbp} {e : y.as ⟶ c} (he : codim e = 1) {g : c ⟶ x.as}, e ≫ g = ev P →
      ∃ R : Quiver.Path x (Vert.mk c), ev R = g ∧
        quotF.map P = quotF.map (R.cons (gen e he)) := by
  intro n
  induction n with
  | zero =>
      intro x y P hP c e he g hg
      cases P with
      | cons P' d => simp at hP
      | nil =>
          have h := codim_comp e g
          rw [hg, ev_nil, codim_id, he] at h
          exact absurd h (by omega)
  | succ n ih =>
      intro x y P hP c e he g hg
      cases P with
      | nil => simp at hP
      | @cons z _ P' d =>
          obtain ⟨e₁, he₁, rfl⟩ := exists_gen d
          have hP' : P'.length = n := by simpa using hP
          have hval : e ≫ g = e₁ ≫ ev P' := hg
          by_cases hcz : c = z.as
          · subst hcz
            obtain ⟨rfl, rfl⟩ := factor_ext hval rfl
            exact ⟨P', rfl, rfl⟩
          obtain ⟨w, u, u', k, hu, hu', hsq, huk, hu'k⟩ :=
            exists_diamond he he₁ hval hcz
          obtain ⟨R', hR', hquot'⟩ := ih P' hP' hu' hu'k
          refine ⟨R'.cons (gen u hu), by rw [ev_cons, hR']; exact huk, ?_⟩
          calc quotF.map (P'.cons (gen e₁ he₁))
              = quotF.map R' ≫ (quotF.map (gen u' hu').toPath
                  ≫ quotF.map (gen e₁ he₁).toPath) := by
                rw [quot_cons, hquot', quot_cons, Category.assoc]; rfl
            -- `congrArg`, not `rw`: the middle vertex is spelled `Vert.mk c` in `quot_swap`
            -- and `c` here, which are defeq but not syntactically equal
            _ = quotF.map R' ≫ (quotF.map (gen u hu).toPath ≫ quotF.map (gen e he).toPath) :=
                congrArg (fun m => quotF.map R' ≫ m) (quot_swap hu' he₁ hu he hsq.symm)
            _ = quotF.map ((R'.cons (gen u hu)).cons (gen e he)) := by
                rw [quot_cons (R'.cons (gen u hu)) (gen e he), quot_cons R' (gen u hu),
                  Category.assoc]
                rfl

/-- **Two generating paths with the same value agree in the quotient.**  Split one generator off
the common value and bring it to the front of both; what is left is shorter and still equal. -/
theorem quot_eq_of_ev_eq : ∀ (n : ℕ) {x y : Vert} (P Q : Quiver.Path x y),
    P.length = n → ev P = ev Q → quotF.map P = quotF.map Q := by
  intro n
  induction n with
  | zero =>
      intro x y P Q hP h
      have hQ : Q.length = 0 := (length_eq_of_ev_eq h).symm.trans hP
      cases P with
      | cons P' e => simp at hP
      | nil =>
          cases Q with
          | cons Q' d => simp at hQ
          | nil => rfl
  | succ n ih =>
      intro x y P Q hP h
      have hQ : Q.length = n + 1 := (length_eq_of_ev_eq h).symm.trans hP
      obtain ⟨c, e, g, he, heg⟩ := exists_first (ev P) (by rw [codim_ev, hP]; omega)
      have hg : codim g = n := by
        have hc := codim_comp e g
        rw [heg, codim_ev, hP, he] at hc
        omega
      obtain ⟨R, hR, hquotP⟩ := exists_front _ P hP he heg
      obtain ⟨S, hS, hquotQ⟩ := exists_front _ Q hQ he (heg.trans h)
      rw [hquotP, hquotQ, quot_cons, quot_cons,
        ih R S (by rw [← codim_ev, hR]; exact hg) (hR.trans hS.symm)]

/-! ## The presentation -/

/-- **The presentation functor**: evaluate a generating path, on the quotient. -/
noncomputable def presentationFunctor : CategoryTheory.Quotient rel ⥤ (Ch Zbp)ᵒᵖ :=
  CategoryTheory.Quotient.lift rel eval fun _ _ _ _ h => eval_map_eq_iff.mpr h.2.2

instance : presentationFunctor.Full where
  map_surjective := by
    rintro ⟨X⟩ ⟨Y⟩ f
    obtain ⟨P, hP⟩ := exists_path (codim f.unop) f.unop le_rfl
    exact ⟨quotF.map P, Quiver.Hom.unop_inj hP⟩

instance : presentationFunctor.Faithful where
  map_injective := by
    rintro ⟨X⟩ ⟨Y⟩ f g hfg
    obtain ⟨P, rfl⟩ := quotF.map_surjective f
    obtain ⟨Q, rfl⟩ := quotF.map_surjective g
    exact quot_eq_of_ev_eq _ P Q rfl (eval_map_eq_iff.mp hfg)

instance : presentationFunctor.EssSurj where
  mem_essImage X := ⟨{ as := Vert.mk X.unop }, ⟨Iso.refl X⟩⟩

instance : presentationFunctor.IsEquivalence where

end Cut

/-- **`Ch Zbp` is presented by its bead cuts** — generators the codimension-one refinements,
relations the codimension-two ones, identity on objects.  It is the *opposite* that a path
presents: a path spells its steps in refinement order only there. -/
noncomputable def zPresentationOp : CategoryTheory.Quotient Cut.rel ≌ (Ch Zbp)ᵒᵖ :=
  Cut.presentationFunctor.asEquivalence

@[simp] theorem zPresentationOp_obj (a : Ch Zbp) :
    zPresentationOp.functor.obj { as := Cut.Vert.mk a } = op a := rfl

end ChainCat
