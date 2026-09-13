import Mathlib.Logic.Relation
import Mathlib.Order.RelClasses

/-!
# Machinery/Rewriting/Newman — abstract rewriting, at the `Relation` level

Mathlib stops at `Relation.church_rosser`, which wants *strong* confluence (one of the two reducts a
single step).  Newman's lemma (Newman 1942) — terminating + locally confluent ⇒ confluent — unique
normal forms, and Hindley–Rosen for unions are not there.  Said in mathlib's vocabulary
(`ReflTransGen`, `Join`) and in no other: nothing below names a category, a word or a presentation.
Prior art in Lean 4: arXiv:2512.09280.

Termination is a *parameter*: `terminating_of_measure` takes any well-founded `q` on any `β`, so a
lexicographic refinement of a length is as admissible as a length.
-/

universe u v

namespace Relation

variable {α : Type u} {r : α → α → Prop} {a b c : α}

/-! ## Confluence -/

/-- **Locally confluent**: two one-step reducts of a common source have a common reduct. -/
def LocallyConfluent (r : α → α → Prop) : Prop :=
  ∀ ⦃a b c⦄, r a b → r a c → Join (ReflTransGen r) b c

/-- **Confluent**: two reducts of a common source have a common reduct. -/
def Confluent (r : α → α → Prop) : Prop :=
  ∀ ⦃a b c⦄, ReflTransGen r a b → ReflTransGen r a c → Join (ReflTransGen r) b c

/-- **Terminating**: no infinite forward chain, i.e. the step relation read backwards is
well-founded. -/
def Terminating (r : α → α → Prop) : Prop :=
  WellFounded fun a b => r b a

/-- **Termination from a measure** — the measure's target and order are arbitrary, so a
lexicographic or product order serves as well as `ℕ`. -/
theorem terminating_of_measure {β : Type v} {q : β → β → Prop} (hq : WellFounded q) (m : α → β)
    (hm : ∀ ⦃a b⦄, r a b → q (m b) (m a)) : Terminating r :=
  Subrelation.wf (fun {_ _} h => hm h) (InvImage.wf m hq)

/-- **…and by a counter**, the case a length-graded rule set lands in. -/
theorem terminating_of_natMeasure (m : α → ℕ) (hm : ∀ ⦃a b⦄, r a b → m b < m a) : Terminating r :=
  terminating_of_measure Nat.lt_wfRel.wf m hm

/-- **Newman's lemma**: a terminating, locally confluent relation is confluent. -/
theorem LocallyConfluent.confluent (hwf : Terminating r) (h : LocallyConfluent r) :
    Confluent r := by
  have key : ∀ a b c, ReflTransGen r a b → ReflTransGen r a c → Join (ReflTransGen r) b c := by
    intro a
    induction a using hwf.induction with
    | _ a ih =>
      intro b c hab hac
      rcases hab.cases_head with rfl | ⟨b₁, hab₁, hb₁b⟩
      · exact ⟨c, hac, .refl⟩
      · rcases hac.cases_head with rfl | ⟨c₁, hac₁, hc₁c⟩
        · exact ⟨b, .refl, hb₁b.head hab₁⟩
        · obtain ⟨d, hb₁d, hc₁d⟩ := h hab₁ hac₁
          obtain ⟨e, hbe, hde⟩ := ih b₁ hab₁ b d hb₁b hb₁d
          obtain ⟨f, hcf, hef⟩ := ih c₁ hac₁ c e hc₁c (hc₁d.trans hde)
          exact ⟨f, hbe.trans hef, hcf⟩
  exact fun {_ _ _} hab hac => key _ _ _ hab hac

/-- **Joinability is an equivalence** on a confluent relation. -/
theorem Confluent.equivalence_join (hc : Confluent r) : Equivalence (Join (ReflTransGen r)) :=
  Relation.equivalence_join fun _ _ _ hab hac => hc hab hac

/-- **A reduction is a conversion.** -/
theorem ReflTransGen.toEqvGen (h : ReflTransGen r a b) : EqvGen r a b := by
  induction h with
  | refl => exact .refl _
  | tail _ hbc ih => exact ih.trans _ _ _ (.rel _ _ hbc)

/-- **A common reduct is a conversion.** -/
theorem Join.toEqvGen (h : Join (ReflTransGen r) a b) : EqvGen r a b := by
  obtain ⟨_, had, hbd⟩ := h
  exact had.toEqvGen.trans _ _ _ (hbd.toEqvGen.symm _ _)

/-- **Church–Rosser**: on a confluent relation, conversion *is* joinability. -/
theorem Confluent.join_iff_eqvGen (hc : Confluent r) : Join (ReflTransGen r) a b ↔ EqvGen r a b :=
  ⟨Join.toEqvGen, fun h => (hc.equivalence_join.eqvGen_iff).mp
    (EqvGen.mono (fun _ _ hxy => ⟨_, .single hxy, .refl⟩) h)⟩

/-! ## Unions

A rewriting system assembled from several rule families is confluent as soon as each family is and
the families commute — no critical pairs across families to check. -/

/-- **`r` and `s` commute**: a fork of an `r`-reduction and an `s`-reduction closes, with the
relations exchanged. -/
def Commutes (r s : α → α → Prop) : Prop :=
  ∀ ⦃a b c⦄, ReflTransGen r a b → ReflTransGen s a c →
    ∃ d, ReflTransGen s b d ∧ ReflTransGen r c d

theorem Commutes.symm {s : α → α → Prop} (h : Commutes r s) : Commutes s r := by
  intro _ _ _ hab hac
  obtain ⟨d, h₁, h₂⟩ := h hac hab
  exact ⟨d, h₂, h₁⟩

/-- **Confluence from a coarser relation with the one-step diamond**: `B` sandwiched between `u` and
its reductions, closing every fork in one step each, is `church_rosser`'s hypothesis read at `B`. -/
theorem confluent_of_diamond {u B : α → α → Prop} (hle : ∀ ⦃a b⦄, u a b → B a b)
    (hge : ∀ ⦃a b⦄, B a b → ReflTransGen u a b)
    (hd : ∀ a b c, B a b → B a c → ∃ d, ReflGen B b d ∧ ReflTransGen B c d) : Confluent u := by
  have toU : ∀ {a b}, ReflTransGen B a b → ReflTransGen u a b := by
    intro a b hab
    induction hab with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.trans (hge hbc)
  intro a b c hab hac
  obtain ⟨d, k₁, k₂⟩ :=
    church_rosser hd (hab.mono fun _ _ h => hle h) (hac.mono fun _ _ h => hle h)
  exact ⟨d, toU k₁, toU k₂⟩

/-- **Hindley–Rosen**: confluent relations that commute have a confluent union.  The two closures
close every fork between them in *one* step each, so no Newman induction enters. -/
theorem Confluent.union {s : α → α → Prop} (hr : Confluent r) (hs : Confluent s)
    (hc : Commutes r s) : Confluent fun a b => r a b ∨ s a b :=
  confluent_of_diamond (B := fun a b => ReflTransGen r a b ∨ ReflTransGen s a b)
    (fun {_ _} hxy => hxy.imp .single .single)
    (fun {_ _} hxy =>
      hxy.elim (fun h => h.mono fun _ _ => Or.inl) fun h => h.mono fun _ _ => Or.inr)
    (by
      rintro a b c (hab | hab) (hac | hac)
      · obtain ⟨d, h₁, h₂⟩ := hr hab hac; exact ⟨d, .single (Or.inl h₁), .single (Or.inl h₂)⟩
      · obtain ⟨d, h₁, h₂⟩ := hc hab hac; exact ⟨d, .single (Or.inr h₁), .single (Or.inl h₂)⟩
      · obtain ⟨d, h₁, h₂⟩ := hc hac hab; exact ⟨d, .single (Or.inl h₂), .single (Or.inr h₁)⟩
      · obtain ⟨d, h₁, h₂⟩ := hs hab hac; exact ⟨d, .single (Or.inr h₁), .single (Or.inr h₂)⟩)

/-! ## Normal forms -/

/-- **Normal**: nothing reduces it. -/
def Normal (r : α → α → Prop) (a : α) : Prop := ∀ b, ¬ r a b

/-- **A normal element reduces only to itself.** -/
theorem Normal.eq_of_reflTransGen (h : Normal r a) (hab : ReflTransGen r a b) : a = b := by
  rcases hab.cases_head with rfl | ⟨c, hac, _⟩
  · rfl
  · exact absurd hac (h c)

/-- **Every element has a normal form**, by induction along the steps out of it. -/
theorem exists_normal (hwf : Terminating r) (a : α) : ∃ b, ReflTransGen r a b ∧ Normal r b := by
  induction a using hwf.induction with
  | _ a ih =>
    by_cases h : Normal r a
    · exact ⟨a, .refl, h⟩
    · obtain ⟨b, hab⟩ := not_forall_not.mp h
      obtain ⟨c, hbc, hc⟩ := ih b hab
      exact ⟨c, hbc.head hab, hc⟩

/-- **Normal forms of a common source agree** — the statement a consumer wants out of confluence. -/
theorem Confluent.normal_eq (hc : Confluent r) (hb : Normal r b) (hc' : Normal r c)
    (hab : ReflTransGen r a b) (hac : ReflTransGen r a c) : b = c := by
  obtain ⟨d, hbd, hcd⟩ := hc hab hac
  exact (hb.eq_of_reflTransGen hbd).trans (hc'.eq_of_reflTransGen hcd).symm

/-- **Convertible normal elements are equal.** -/
theorem Confluent.eq_of_eqvGen (hc : Confluent r) (ha : Normal r a) (hb : Normal r b)
    (h : EqvGen r a b) : a = b := by
  obtain ⟨d, had, hbd⟩ := hc.join_iff_eqvGen.mpr h
  exact (ha.eq_of_reflTransGen had).trans (hb.eq_of_reflTransGen hbd).symm

/-- **The unique normal form.** -/
theorem Confluent.existsUnique_normal (hc : Confluent r) (hwf : Terminating r) (a : α) :
    ∃! b, ReflTransGen r a b ∧ Normal r b := by
  obtain ⟨b, hab, hb⟩ := exists_normal hwf a
  exact ⟨b, ⟨hab, hb⟩, fun _ h => hc.normal_eq h.2 hb h.1 hab⟩

/-! ## Convergence

The two halves travel together: `Convergent` is the hypothesis a rewriting system is designed to
meet, and `eq_iff_eqvGen` is what meeting it buys — a decision procedure for the conversion
relation. -/

/-- **Convergent**: terminating and locally confluent, hence (Newman) confluent with unique normal
forms. -/
structure Convergent (r : α → α → Prop) : Prop where
  /-- no infinite forward chain -/
  terminating : Terminating r
  /-- one-step reducts join -/
  locallyConfluent : LocallyConfluent r

namespace Convergent

theorem confluent (hr : Convergent r) : Confluent r :=
  hr.locallyConfluent.confluent hr.terminating

theorem exists_normal (hr : Convergent r) (a : α) : ∃ b, ReflTransGen r a b ∧ Normal r b :=
  Relation.exists_normal hr.terminating a

theorem existsUnique_normal (hr : Convergent r) (a : α) :
    ∃! b, ReflTransGen r a b ∧ Normal r b :=
  hr.confluent.existsUnique_normal hr.terminating a

/-- **Conversion is decided by the normal forms**: any two reductions to normal elements answer the
question for their sources. -/
theorem eq_iff_eqvGen (hr : Convergent r) {u v n m : α} (hun : ReflTransGen r u n) (hn : Normal r n)
    (hvm : ReflTransGen r v m) (hm : Normal r m) : n = m ↔ EqvGen r u v :=
  ⟨fun h => hun.toEqvGen.trans _ _ _ (h ▸ hvm.toEqvGen.symm _ _),
   fun h => hr.confluent.eq_of_eqvGen hn hm
     (((hun.toEqvGen.symm _ _).trans _ _ _ h).trans _ _ _ hvm.toEqvGen)⟩

end Convergent

end Relation
