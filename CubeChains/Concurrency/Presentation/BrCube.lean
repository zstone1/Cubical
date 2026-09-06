import CubeChains.Concurrency.Presentation.SliceInherit
import CubeChains.Concurrency.Merge.CubeWeakEquiv
import CubeChains.Concurrency.Presentation.HAction
import CubeChains.Concurrency.Presentation.GlueRun

/-!
# Concurrency/Presentation/BrCube — `Br p` at the cube and at its decoration

`Br p K` presents `Ch(K)[W⁻¹]`, so wherever that category has already been identified the
presentation transports onto the identification: the weak Bruhat order at `□ⁿ`, the positive braid
action at `Hbp □ⁿ`.  The polygraph never moves — only the category it is read in.

The action reads *covariantly* here, where the fibration route (`hLocActionPresentation`) reads it
on the opposite; `presentsBrActionOp` is the shape a comparison of the two consumes.

What comes *out* is what went *in*: the generators of `Br germBP K` are the Garside simples acting
on the runs, those of `Br artinBP K` the atoms.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph

namespace ChainCat

namespace BraidPresentation

variable (p : BraidPresentation)

/-- **`Br p (□n)` presents the right weak Bruhat order on `Sₙ`, read backwards.** -/
noncomputable def presentsBrCube (n : ℕ) : Presents (p.Br (□n)) ((WeakOrder n)ᵒᵖ) :=
  (p.presentsBr (□n)).transport (locCubeWeakOrder n)

/-- **`Br p (Hbp □ⁿ)` presents the positive braid action on the orderings of the axes.** -/
noncomputable def presentsBrAction (n : ℕ) :
    Presents (p.Br (Hbp.obj (□n))) (PosBraidAction n) :=
  (p.presentsBr (Hbp.obj (□n))).transport (hLocEquiv n)

/-- …in the Artin spelling of the acting monoid. -/
noncomputable def presentsBrArtinAction (n : ℕ) :
    Presents (p.Br (Hbp.obj (□n))) (ActionCategory (ArtinPosBraid n) (Equiv.Perm (Fin n))) :=
  (p.presentsBr (Hbp.obj (□n))).transport (hLocArtinEquiv n)

/-- **…and reversed**, where the fibration route's `hLocActionPresentation` also lives: the glue
route's words compose the other way round, so only after `Presents.op` are the two comparable. -/
noncomputable def presentsBrActionOp (n : ℕ) :
    Presents ((p.Br (Hbp.obj (□n))).op) ((PosBraidAction n)ᵒᵖ) :=
  (p.presentsBrAction n).op

/-- **The loops at every 0-cell are the positive pure braids** — `PosPureBraid n` is the kernel of
`posPermHom n`, so the stabilizer of a chamber does not depend on the chamber.  The presentation
does *not* present that monoid: its own loops are only the identity
(`end_not_generated_by_simples`), so the pure braids are read off the presented category rather
than off the polygraph. -/
noncomputable def endBrAction (n : ℕ) (x : GenObj (p.Br (Hbp.obj (□n))).Gen) :
    @End (PosBraidAction n) _ ((p.presentsBrAction n).at' x) ≃* PosPureBraid n :=
  endEquivPosPure _

end BraidPresentation

/-! ## The generators are what went in

A 1-cell of `Br p K` is `p`'s own generator crossed above a run (`exists_runGen`) — no word is
chosen — and a 0-cell is a run's (`exists_glueRunV`).  At `K = Hbp □ⁿ` the runs *are* the chambers
(`presentsBrAction`), so the two spellings read as follows. -/

/-- **Garside in ⟹ Garside out**: a 1-cell of `Br germBP K` is a **Garside simple acting** on a
run.  The generator *is* its simple — `germBP.S N` is `Perm (Fin N)` and `germBP_braid` is `rfl` —
and it takes the run's crossing `u.perm` to `u.perm * σ`, length-additively.  At `Hbp □ⁿ` these
runs are the chambers. -/
theorem germBr_gen (K : BPSet) {A B : GenObj (germBP.Br K).Gen} (e : A ⟶ B) :
    ∃ (c : ((wedgeHoms K).Elements)ᵒᵖ) (N : ℕ) (σ : Equiv.Perm (Fin N))
      (u v : RunAt (eltBase (wedgeHoms K) c) N)
      (hact : (sliceActionAt (eltBase (wedgeHoms K) c) N (posPerm σ)).unop.val (some u) = some v)
      (hA : glueV K germBP.fam c (germBP.runPt v) = A)
      (hB : glueV K germBP.fam c (germBP.runPt u) = B),
      v.perm = u.perm * σ ∧ permLen u.perm + permLen σ = permLen v.perm ∧
        Quiver.homOfEq (glueE K germBP.fam c (germBP.runGen σ hact)) hA hB = e := by
  obtain ⟨c, N, s, u, v, hact, hA, hB, he⟩ := germBP.exists_runGen K e
  exact ⟨c, N, s, u, v, hact, hA, hB, ((sliceActionAt_posPerm_iff s u v).mp hact).1,
    ((sliceActionAt_posPerm_iff s u v).mp hact).2, he⟩

/-- **Artin in ⟹ the generators are the codimension-one chains**: a 1-cell of `Br artinBP K` is an
**atom** acting on a run.  The generator *is* its atom — `artinBP.S N` is `Fin (N-1)` and
`artinBP_braid` is `rfl` — and it gains exactly one crossing. -/
theorem artinBr_gen (K : BPSet) {A B : GenObj (artinBP.Br K).Gen} (e : A ⟶ B) :
    ∃ (c : ((wedgeHoms K).Elements)ᵒᵖ) (N : ℕ) (k : Fin (N - 1))
      (u v : RunAt (eltBase (wedgeHoms K) c) N)
      (hact : (sliceActionAt (eltBase (wedgeHoms K) c) N (posPerm (adjT k))).unop.val (some u)
        = some v)
      (hA : glueV K artinBP.fam c (artinBP.runPt v) = A)
      (hB : glueV K artinBP.fam c (artinBP.runPt u) = B),
      v.perm = u.perm * adjT k ∧ permLen u.perm + 1 = permLen v.perm ∧
        Quiver.homOfEq (glueE K artinBP.fam c (artinBP.runGen k hact)) hA hB = e := by
  obtain ⟨c, N, s, u, v, hact, hA, hB, he⟩ := artinBP.exists_runGen K e
  exact ⟨c, N, s, u, v, hact, hA, hB, ((sliceActionAt_adjT_iff s u v).mp hact).1,
    ((sliceActionAt_adjT_iff s u v).mp hact).2, he⟩

end ChainCat
