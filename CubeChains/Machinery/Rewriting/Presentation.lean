import CubeChains.Machinery.Presentation.Basic
import CubeChains.Machinery.Rewriting.Newman

/-!
# Machinery/Rewriting/Presentation — a convergent orientation presents

An `Orientation` of a polygraph is a rule set on words whose contextual closure converts exactly
what the 2-cells identify.  Convergence then decides the word problem (`quot_eq_iff_normal_eq`), and
that discharges `Presents.ofDesc`'s completeness obligation once the interpretation separates
normal words (`Orientation.complete`) — separation holds the content, the rewriting does the rest.

Termination is not built in as a length: `ofShortening` is the length-graded entry point, and
`ofCells` takes any `Relation.Convergent`, so a length-preserving rule set measured by a
lexicographic refinement is equally admissible.
-/

universe w u' v u w₂

namespace CategoryTheory

namespace Polygraph

variable {P : Polygraph.{w, u', w₂}}

/-- **One rewriting step** between two fixed 0-cells: a rule, inside a context. -/
abbrev step (R : HomRel P.Word) (x y : GenObj P.Gen) :
    Quiver.Path x y → Quiver.Path x y → Prop :=
  fun u v => HomRel.CompClosure R u v

/-- **Termination by word length**: a shortening rule set terminates, contexts and all, because
`Quiver.Path.length` is additive.  The length-graded case — a rule set oriented "two letters to
one" — lands here; `Relation.terminating_of_measure` covers the rest. -/
theorem terminating_of_length (R : HomRel P.Word)
    (h : ∀ {x y : GenObj P.Gen} {u v : Quiver.Path x y}, R u v → v.length < u.length)
    (x y : GenObj P.Gen) : Relation.Terminating (step R x y) :=
  Relation.terminating_of_natMeasure Quiver.Path.length fun {_ _} hst => by
    obtain ⟨_, _, f, m₁, m₂, g, hr⟩ := hst
    have := h hr
    change (f.comp (m₂.comp g)).length < (f.comp (m₁.comp g)).length
    simp only [Quiver.Path.length_comp]
    omega

/-- **A convergent orientation of the 2-cells**: rules that the 2-cells imply, that imply the
2-cells back, and that converge. -/
structure Orientation (P : Polygraph.{w, u', w₂}) where
  /-- the rules, oriented -/
  rule : HomRel P.Word
  /-- a rule is a consequence of the 2-cells -/
  rule_sound : ∀ {x y : GenObj P.Gen} {u v : Quiver.Path x y},
    rule u v → P.quot.map u = P.quot.map v
  /-- the two sides of a 2-cell have a common reduct -/
  cell_join : ∀ {x y : GenObj P.Gen} (α : P.Rel x y),
    Relation.Join (Relation.ReflTransGen (step rule x y)) (P.src α) (P.tgt α)
  /-- the rewriting terminates and is locally confluent -/
  convergent : ∀ x y : GenObj P.Gen, Relation.Convergent (step rule x y)

namespace Orientation

variable (o : P.Orientation)

/-- **The 2-cells, oriented source to target** — soundness and spanning are then free, so a consumer
supplies exactly termination and local confluence. -/
def ofCells (P : Polygraph.{w, u', w₂})
    (convergent : ∀ x y : GenObj P.Gen, Relation.Convergent (step P.homRel x y)) :
    P.Orientation where
  rule := P.homRel
  rule_sound h := Quotient.sound _ h
  cell_join α := ⟨P.tgt α, .single (HomRel.CompClosure.of ⟨α, rfl, rfl⟩), .refl⟩
  convergent := convergent

/-- **The 2-cells oriented source to target and shortening** — then the consumer is left with local
confluence alone, which is the length-graded entry point. -/
def ofShortening (P : Polygraph.{w, u', w₂})
    (shorter : ∀ {x y : GenObj P.Gen} (α : P.Rel x y), (P.tgt α).length < (P.src α).length)
    (loc : ∀ x y : GenObj P.Gen, Relation.LocallyConfluent (step P.homRel x y)) :
    P.Orientation :=
  ofCells P fun x y =>
    ⟨terminating_of_length P.homRel
      (fun {_ _ _ _} h => by obtain ⟨α, rfl, rfl⟩ := h; exact shorter α) x y, loc x y⟩

/-! ## Soundness: a reduction is an equality of arrows -/

/-- **A step is an equality in `P.presented`** — a rule is, and `quot` is a functor. -/
theorem quot_eq_of_step {x y : GenObj P.Gen} {u v : Quiver.Path x y} (h : step o.rule x y u v) :
    P.quot.map u = P.quot.map v := by
  obtain ⟨_, _, f, m₁, m₂, g, hr⟩ := h
  simp only [Functor.map_comp, o.rule_sound hr]

theorem quot_eq_of_reflTransGen {x y : GenObj P.Gen} {u v : Quiver.Path x y}
    (h : Relation.ReflTransGen (step o.rule x y) u v) : P.quot.map u = P.quot.map v := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (o.quot_eq_of_step hbc)

theorem quot_eq_of_eqvGen {x y : GenObj P.Gen} {u v : Quiver.Path x y}
    (h : Relation.EqvGen (step o.rule x y) u v) : P.quot.map u = P.quot.map v := by
  induction h with
  | rel _ _ hab => exact o.quot_eq_of_step hab
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## Completeness: the rules convert everything the 2-cells identify

`Quotient.functor o.rule` is the category the *rules* present; the two quotients agree because each
2-cell is a conversion (`cell_join`) and each rule is an equality (`rule_sound`). -/

/-- **A 2-cell is an equality modulo the rules.** -/
theorem ruleQuot_cell {x y : GenObj P.Gen} (α : P.Rel x y) :
    (Quotient.functor o.rule).map (P.src α) = (Quotient.functor o.rule).map (P.tgt α) :=
  (Quotient.functor_homRel_eq_compClosure_eqvGen o.rule _ _).mpr (o.cell_join α).toEqvGen

/-- **…hence so is every equality of `P.presented`**, by induction on the conversion the quotient
records: context is functoriality of `Quotient.functor`. -/
theorem ruleQuot_eq_of_quot_eq {x y : GenObj P.Gen} {u v : Quiver.Path x y}
    (h : P.quot.map u = P.quot.map v) :
    (Quotient.functor o.rule).map u = (Quotient.functor o.rule).map v := by
  have h1 := (Quotient.functor_homRel_eq_compClosure_eqvGen P.homRel u v).mp h
  clear h
  induction h1 with
  | rel _ _ hab =>
    obtain ⟨_, _, f, m₁, m₂, g, α, rfl, rfl⟩ := hab
    simp only [Functor.map_comp]
    rw [o.ruleQuot_cell α]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The word problem, solved**: two parallel words name one arrow of `P.presented` exactly when
the rewriting converts them. -/
theorem quot_eq_iff_eqvGen {x y : GenObj P.Gen} (u v : Quiver.Path x y) :
    P.quot.map u = P.quot.map v ↔ Relation.EqvGen (step o.rule x y) u v :=
  ⟨fun h => (Quotient.functor_homRel_eq_compClosure_eqvGen o.rule u v).mp
    (o.ruleQuot_eq_of_quot_eq h), o.quot_eq_of_eqvGen⟩

/-- **…read at normal forms**: any two reductions to normal words decide it. -/
theorem quot_eq_iff_normal_eq {x y : GenObj P.Gen} {u v n m : Quiver.Path x y}
    (hun : Relation.ReflTransGen (step o.rule x y) u n) (hn : Relation.Normal (step o.rule x y) n)
    (hvm : Relation.ReflTransGen (step o.rule x y) v m) (hm : Relation.Normal (step o.rule x y) m) :
    P.quot.map u = P.quot.map v ↔ n = m :=
  (o.quot_eq_iff_eqvGen u v).trans ((o.convergent x y).eq_iff_eqvGen hun hn hvm hm).symm

/-! ## The bridge to `Presents.ofDesc` -/

section Desc

variable {C : Type u} [Category.{v} C] (φ : GenObj P.Gen ⥤q C)
  (sound : ∀ {x y : GenObj P.Gen} (α : P.Rel x y),
    (Paths.lift φ).map (P.src α) = (Paths.lift φ).map (P.tgt α))

include sound in
/-- **`ofDesc`'s completeness obligation, discharged**: reduce both words and appeal to separation.
Only termination is used from convergence here — local confluence is what makes the separation
hypothesis a check on *one* normal word per arrow rather than on a set nobody can enumerate, and
what `quot_eq_iff_normal_eq` needs. -/
theorem complete
    (sep : ∀ {x y : GenObj P.Gen} {u v : Quiver.Path x y},
      Relation.Normal (step o.rule x y) u → Relation.Normal (step o.rule x y) v →
      (Paths.lift φ).map u = (Paths.lift φ).map v → u = v)
    {x y : GenObj P.Gen} {u v : Quiver.Path x y}
    (h : (Paths.lift φ).map u = (Paths.lift φ).map v) : P.quot.map u = P.quot.map v := by
  obtain ⟨n, hun, hn⟩ := (o.convergent x y).exists_normal u
  obtain ⟨m, hvm, hm⟩ := (o.convergent x y).exists_normal v
  have hu := Polygraph.lift_map_eq_of_quot_eq φ sound (o.quot_eq_of_reflTransGen hun)
  have hv := Polygraph.lift_map_eq_of_quot_eq φ sound (o.quot_eq_of_reflTransGen hvm)
  exact (o.quot_eq_iff_normal_eq hun hn hvm hm).mpr (sep hn hm (hu.symm.trans (h.trans hv)))

end Desc

end Orientation

end Polygraph

/-- **A convergent orientation presents**: `Presents.ofDesc` with completeness supplied by the
rewriting, leaving the consumer only the obligations about `C` itself. -/
def Presents.ofOrientation {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C]
    (o : P.Orientation) (φ : GenObj P.Gen ⥤q C)
    (sound : ∀ {x y : GenObj P.Gen} (α : P.Rel x y),
      (Paths.lift φ).map (P.src α) = (Paths.lift φ).map (P.tgt α))
    (sep : ∀ {x y : GenObj P.Gen} {u v : Quiver.Path x y},
      Relation.Normal (Polygraph.step o.rule x y) u →
      Relation.Normal (Polygraph.step o.rule x y) v →
      (Paths.lift φ).map u = (Paths.lift φ).map v → u = v)
    (full : (Paths.lift φ).Full) (essSurj : (Paths.lift φ).EssSurj) : Presents P C :=
  Presents.ofDesc φ sound (o.complete φ sound sep) full essSurj

end CategoryTheory
