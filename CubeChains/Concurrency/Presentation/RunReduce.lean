import CubeChains.Concurrency.Presentation.RunContract
import CubeChains.Machinery.Presentation.Reduce

/-!
# Concurrency/Presentation/RunReduce — naming the lifted cut polygraph

The vocabulary the collapse is read in: a 0-cell is its **shape** (`shOf`), a 1-cell is its **bead
cut**, the merges among them are `chCutPicked`, and a 2-cell is a pair of two-step factorisations of
one codimension-two refinement (`pairCell`) — a word of length two *being* a two-step
factorisation.
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

/-- **The element a bead cut restricts** — the lift carries no data beyond its base map. -/
theorem map_cutHom {K : BPSet} {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    (wedgeHoms K).map (Cut.genHom e.1).op a.2 = b.2 :=
  (congrArg (fun q => (wedgeHoms K).map q a.2) (zCutPresentation_arrow e.1)).symm.trans e.2

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
