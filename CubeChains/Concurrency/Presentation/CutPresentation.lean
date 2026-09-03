import CubeChains.Concurrency.Grading.Coarser
import CubeChains.Machinery.Presentation.Basic

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

An edge runs the way a *path* does — from the coarse shape to the fine one — so that the
generators are arrows of `(Ch Zbp)ᵒᵖ`, the form the transport to `Ch K` consumes. -/

namespace Cut

/-- **The one-cut refinements**, as a generating family for `(Ch Zbp)ᵒᵖ`. -/
abbrev Refine (x y : Ch Zbp) : Type := {f : y ⟶ x // codim f = 1}

/-- The vertex a shape names. -/
abbrev vert (a : Ch Zbp) : GenObj Refine := ⟨a⟩

/-- The generator named by a one-cut refinement. -/
def gen {a b : Ch Zbp} (f : b ⟶ a) (hf : codim f = 1) : vert a ⟶ vert b := ⟨f, hf⟩

/-- The refinement a generator names. -/
def genHom {x y : GenObj Refine} (e : x ⟶ y) : y.as ⟶ x.as := e.1

theorem codim_genHom {x y : GenObj Refine} (e : x ⟶ y) : codim (genHom e) = 1 := e.2

/-- A one-cut refinement, read as an arrow of `(Ch Zbp)ᵒᵖ`. -/
def interp : GenObj Refine ⥤q (Ch Zbp)ᵒᵖ where
  obj x := op x.as
  map e := e.1.op

/-- The refinement a generating word performs: consing an edge *pre*composes. -/
def ev {x y : GenObj Refine} (P : Quiver.Path x y) : y.as ⟶ x.as :=
  ((Paths.lift interp).map P).unop

@[simp] theorem ev_nil {x : GenObj Refine} :
    ev (Quiver.Path.nil : Quiver.Path x x) = 𝟙 x.as := rfl

@[simp] theorem ev_cons {x y z : GenObj Refine} (P : Quiver.Path x y) (e : y ⟶ z) :
    ev (P.cons e) = genHom e ≫ ev P := rfl

theorem eval_map_eq_iff {x y : GenObj Refine} {P Q : Quiver.Path x y} :
    (Paths.lift interp).map P = (Paths.lift interp).map Q ↔ ev P = ev Q :=
  ⟨congrArg Quiver.Hom.unop, fun h => Quiver.Hom.unop_inj h⟩

theorem codim_ev {x y : GenObj Refine} (P : Quiver.Path x y) : codim (ev P) = P.length := by
  induction P with
  | nil => exact codim_id _
  | cons P e ih =>
      rw [ev_cons, codim_comp, codim_genHom, ih]
      exact Nat.add_comm _ _

theorem length_eq_of_ev_eq {x y : GenObj Refine} {P Q : Quiver.Path x y} (h : ev P = ev Q) :
    P.length = Q.length := by rw [← codim_ev, ← codim_ev, h]

/-- **The one-cut refinements generate.**  Peel a generator off the front and induct on the
codimension; a codimension-zero refinement is an identity. -/
theorem exists_path : ∀ (n : ℕ) {a b : Ch Zbp} (f : a ⟶ b), codim f ≤ n →
    ∃ P : Quiver.Path (vert b) (vert a), ev P = f := by
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
        exact ⟨P.cons (gen e he), by rw [ev_cons, hP]; exact heg⟩

/-! ### The relation -/

/-- **The 2-polygraph of the bead cuts** — 0-cells the shapes, 1-cells the codimension-one
refinements, 2-cells the codimension-two ones: two two-step factorisations of one refinement.  A
word of length two *is* a two-step factorisation, so nothing more need be said. -/
def poly : Polygraph where
  V := Ch Zbp
  Gen := Refine
  rel := fun _ _ P Q => P.length = 2 ∧ Q.length = 2 ∧ ev P = ev Q

/-- The passage to the quotient. -/
noncomputable abbrev quotF : CategoryTheory.Paths (GenObj Refine) ⥤ poly.presented := poly.quot

theorem quot_cons {x y z : GenObj Refine} (P : Quiver.Path x y) (e : y ⟶ z) :
    quotF.map (P.cons e) = quotF.map P ≫ quotF.map e.toPath :=
  quotF.map_comp P e.toPath

/-- The relation, as an identity between two-step composites in the quotient. -/
theorem quot_swap {a b c c' : Ch Zbp} {e₀ : c ⟶ a} {e₁ : b ⟶ c} {u : c' ⟶ a} {v : b ⟶ c'}
    (h₀ : codim e₀ = 1) (h₁ : codim e₁ = 1) (hu : codim u = 1) (hv : codim v = 1)
    (h : e₁ ≫ e₀ = v ≫ u) :
    quotF.map (gen e₀ h₀).toPath ≫ quotF.map (gen e₁ h₁).toPath
      = quotF.map (gen u hu).toPath ≫ quotF.map (gen v hv).toPath := by
  rw [← quotF.map_comp, ← quotF.map_comp]
  refine CategoryTheory.Quotient.sound _ ⟨rfl, rfl, ?_⟩
  change e₁ ≫ e₀ ≫ 𝟙 a = v ≫ u ≫ 𝟙 a
  rw [Category.comp_id, Category.comp_id, h]

/-! ## Confluence -/

/-- **A generating word can be re-cut to start at any factorisation of its value.**  Induct down
the word: either the first step already *is* the one wanted, or the diamond replaces the pair by
the other two sides, and `quot_swap` says the quotient does not see the exchange. -/
theorem exists_front : ∀ (n : ℕ) {x y : GenObj Refine} (P : Quiver.Path x y), P.length = n →
    ∀ {c : Ch Zbp} {e : y.as ⟶ c} (he : codim e = 1) {g : c ⟶ x.as}, e ≫ g = ev P →
      ∃ R : Quiver.Path x (vert c), ev R = g ∧
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
          obtain ⟨e₁, he₁⟩ := d
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
                rw [quot_cons, hquot', quot_cons, Category.assoc]
            _ = quotF.map R' ≫ (quotF.map (gen u hu).toPath ≫ quotF.map (gen e he).toPath) :=
                congrArg (fun m => quotF.map R' ≫ m) (quot_swap hu' he₁ hu he hsq.symm)
            _ = quotF.map ((R'.cons (gen u hu)).cons (gen e he)) := by
                rw [quot_cons (R'.cons (gen u hu)) (gen e he), quot_cons R' (gen u hu),
                  Category.assoc]

/-- **Two generating words with the same value agree in the quotient.**  Split one generator off
the common value and bring it to the front of both; what is left is shorter and still equal. -/
theorem quot_eq_of_ev_eq : ∀ (n : ℕ) {x y : GenObj Refine} (P Q : Quiver.Path x y),
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

end Cut

/-- **`Ch Zbp` is presented by its bead cuts.**  It is the *opposite* that words present: a word
spells its steps in refinement order only there. -/
def zCutPresentation : Presents Cut.poly ((Ch Zbp)ᵒᵖ) :=
  Presents.ofDesc Cut.interp
    (fun h => Quiver.Hom.unop_inj h.2.2)
    (fun h => Cut.quot_eq_of_ev_eq _ _ _ rfl (Cut.eval_map_eq_iff.mp h))
    { map_surjective := fun {_ _} f => by
        obtain ⟨P, hP⟩ := Cut.exists_path (codim f.unop) f.unop le_rfl
        exact ⟨P, Quiver.Hom.unop_inj hP⟩ }
    { mem_essImage := fun c => ⟨Cut.vert c.unop, ⟨Iso.refl c⟩⟩ }

end ChainCat
