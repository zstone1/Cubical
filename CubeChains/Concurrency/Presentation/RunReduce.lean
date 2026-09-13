import CubeChains.Concurrency.Presentation.RunContract
import CubeChains.Concurrency.Presentation.Retraction
import CubeChains.Machinery.Presentation.Reduce

/-!
# Concurrency/Presentation/RunReduce — naming the localized cut polygraph

    ⟨bead cuts | codim-2 cells⟩ ──invert merges──▸ cutLocPoly K

The vocabulary the contraction is read in: a 0-cell is its **shape** (`shOf`), a 1-cell that is not
inverted is its **bead cut** (`chFwdOf`), and a 2-cell is a pair of two-step factorisations of one
codimension-two refinement (`pairCell`) — a word of length two *being* a two-step factorisation.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains

namespace ChainCat

/-- The shape a 0-cell of the lifted polygraph names.  `Cut.poly.V` does not unfold at instance
transparency, so the projection is wrapped at the type callers see. -/
abbrev shOf {K : BPSet} (z : (chCutPoly K).V) : Ch Zbp := z.1

/-- The merges among the lifted bead cuts. -/
noncomputable abbrev chCutPicked (K : BPSet) :
    ∀ {a b : (chCutPoly K).V}, (chCutPoly K).Gen a b → Prop :=
  chPicked zCutPresentation Cut.mergeGen K

/-- The lifted bead cuts with a formal inverse adjoined to each merge. -/
noncomputable abbrev cutLocPoly (K : BPSet) : Polygraph := chCutLocFunctor.obj K

/-- The bead cut an unmerged 1-cell of the extension is. -/
def chFwdOf {K : BPSet} {a b : (chCutPoly K).V} :
    ∀ g : InvGen (chCutPoly K) (chCutPicked K) a b, ¬ Cut.merged g → (chCutPoly K).Gen a b
  | .inl e, _ => e
  | .inr _, h => absurd trivial h

/-- A renaming does not change the codimension — `codim` sees only the two shapes. -/
theorem codim_eqToHom_comp {K : BPSet} {a a' b : Ch K} (h : a = a') (f : a' ⟶ b) :
    codim (eqToHom h ≫ f) = codim f := by subst h; rfl

/-- A leg out of an atom's cell into a degree-two chain cuts once. -/
theorem codim_leg {d : Ch Zbp} (hdeg : degree d = 2) {N : ℕ} {k : Fin (N - 1)}
    (w : zObj (atomComp N k) ⟶ d) : codim w = 1 := by rw [codim, hdeg, degree_atomComp]

/-- **Two two-step factorisations of one codimension-two refinement, as a 2-cell** — a word of
length two *is* a two-step factorisation, so the 2-cell carries no more data than its value. -/
noncomputable def pairCell {K : BPSet} {z zm zm' zd : (chCutPoly K).V}
    (e₁ : (chCutPoly K).Gen zd zm) (e₂ : (chCutPoly K).Gen zm z)
    (e₁' : (chCutPoly K).Gen zd zm') (e₂' : (chCutPoly K).Gen zm' z)
    (hev : Cut.genHom e₂.1 ≫ Cut.genHom e₁.1 = Cut.genHom e₂'.1 ≫ Cut.genHom e₁'.1) :
    (chCutPoly K).Rel ⟨zd⟩ ⟨z⟩ where
  src := (Quiver.Path.nil.cons (Polygraph.cell e₁)).cons (Polygraph.cell e₂)
  tgt := (Quiver.Path.nil.cons (Polygraph.cell e₁')).cons (Polygraph.cell e₂')
  cell :=
    { src := (Quiver.Path.nil.cons e₁.1).cons e₂.1
      tgt := (Quiver.Path.nil.cons e₁'.1).cons e₂'.1
      src_length := rfl
      tgt_length := rfl
      ev_eq := by simpa using hev }
  src_eq := rfl
  tgt_eq := rfl

end ChainCat
