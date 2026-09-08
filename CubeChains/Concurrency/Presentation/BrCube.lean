import CubeChains.Concurrency.Presentation.SliceInherit
import CubeChains.Concurrency.Merge.CubeWeakEquiv
import CubeChains.Concurrency.Presentation.HAction
import CubeChains.Concurrency.Presentation.RunCells
import CubeChains.Concurrency.Presentation.ChainAction

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

/-- **`Br p (Hbp □ⁿ)` presents the positive braid action on the orderings of the axes.**  The
identification is `chainActionEquiv`, read off the hand-written Artin presentation — not off the
discrete fibration. -/
noncomputable def presentsBrAction (n : ℕ) :
    Presents (p.Br (Hbp.obj (□n))) (PosBraidAction n) :=
  (p.presentsBr (Hbp.obj (□n))).transport (chainActionEquiv n)

/-- …in the Artin spelling of the acting monoid. -/
noncomputable def presentsBrArtinAction (n : ℕ) :
    Presents (p.Br (Hbp.obj (□n))) (ActionCategory (ArtinPosBraid n) (Equiv.Perm (Fin n))) :=
  (p.presentsBr (Hbp.obj (□n))).transport
    ((chainActionEquiv n).trans
      (actionCategoryCongr (posBraid_equiv_artinPos n) fun m a => by
        change posPermHom n m * a
          = posPermHom n (posOfArtinPos n (posBraid_equiv_artinPos n m)) * a
        rw [show posOfArtinPos n (posBraid_equiv_artinPos n m) = m from
          (posBraid_equiv_artinPos n).symm_apply_apply m]))

/-- **…and reversed**, where the fibration route's `hLocActionPresentation` also lives: the colimit
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
chosen — and a 0-cell is a run's (`exists_ιRun`).  At `K = Hbp □ⁿ` the runs *are* the chambers
(`presentsBrAction`), so the two spellings read as follows. -/

/-- **Garside in ⟹ Garside out**: a 1-cell of `Br germBP K` is a **Garside simple acting** on a
run.  The generator *is* its simple — `germBP.S N` is `Perm (Fin N)` and `germBP_braid` is `rfl` —
and it takes the run's crossing `u.perm` to `u.perm * σ`, length-additively.  At `Hbp □ⁿ` these
runs are the chambers. -/
theorem germBr_gen (K : BPSet) {A B : GenObj (germBP.Br K).Gen} (e : A ⟶ B) :
    ∃ (c : ((wedgeHoms K).Elements)ᵒᵖ) (N : ℕ) (σ : Equiv.Perm (Fin N))
      (u v : RunAt (eltBase (wedgeHoms K) c) N)
      (hact : (sliceActionAt (eltBase (wedgeHoms K) c) N (posPerm σ)).unop.val (some u) = some v)
      (hA : ιV K germBP.fam c (germBP.runPt v) = A)
      (hB : ιV K germBP.fam c (germBP.runPt u) = B),
      v.perm = u.perm * σ ∧ permLen u.perm + permLen σ = permLen v.perm ∧
        Quiver.homOfEq (ιE K germBP.fam c (germBP.runGen σ hact)) hA hB = e := by
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
      (hA : ιV K artinBP.fam c (artinBP.runPt v) = A)
      (hB : ιV K artinBP.fam c (artinBP.runPt u) = B),
      v.perm = u.perm * adjT k ∧ permLen u.perm + 1 = permLen v.perm ∧
        Quiver.homOfEq (ιE K artinBP.fam c (artinBP.runGen k hact)) hA hB = e := by
  obtain ⟨c, N, s, u, v, hact, hA, hB, he⟩ := artinBP.exists_runGen K e
  exact ⟨c, N, s, u, v, hact, hA, hB, ((sliceActionAt_adjT_iff s u v).mp hact).1,
    ((sliceActionAt_adjT_iff s u v).mp hact).2, he⟩

/-! ## …read at the cube

`Ch(□ⁿ)[W⁻¹]` is the weak Bruhat order (`locCubeWeakOrder`), and there a 0-cell of `Br p (□ⁿ)` is a
run — its own crossing permutation, `weakClass`.  So the base's generators come out unchanged: a
Garside simple gives every length-additive pair `x ≤ y`, an atom only a covering. -/

/-- **A chart of the cube has `n` strands.** -/
theorem cubeStrands {n : ℕ} (c : ((wedgeHoms (□n)).Elements)ᵒᵖ) :
    dimSum (eltBase (wedgeHoms (□n)) c).dims = n :=
  dimSum_dims_cube ⟨(eltBase (wedgeHoms (□n)) c).dims, c.unop.2⟩

/-- **The leg of a chart of the cube along a run's arrow** — the run's arrow, read at `□n`.  The
endpoints of `Hom.φ` are given explicitly: they are not read off the expected type. -/
def chartLeg {n : ℕ} {d : Ch Zbp} (W : ⋁d.dims ⟶ □n) (t : zObj (𝟙^n) ⟶ d) :
    (runCh (Hom.φ t ≫ W) : Ch (□n)) ⟶ (⟨d.dims, W⟩ : Ch (□n)) :=
  ⟨Hom.φ (a := zObj (𝟙^n)) (b := d) t, rfl⟩

@[simp] theorem chartLeg_φ {n : ℕ} {d : Ch Zbp} (W : ⋁d.dims ⟶ □n) (t : zObj (𝟙^n) ⟶ d) :
    Hom.φ (chartLeg W t) = Hom.φ t := rfl

/-- **A run's weak-order class over a chart** — the chart's own, crossed by the run's arrow. -/
theorem cross_runCh_chart {n : ℕ} {d : Ch Zbp} (W : ⋁d.dims ⟶ □n) (t : zObj (𝟙^n) ⟶ d) :
    cross (runCh (Hom.φ t ≫ W))
      = cross (⟨d.dims, W⟩ : Ch (□n)) * crossPerm (dimSum_replicate n) t :=
  (cross_eq_mul (chartLeg W t)).trans
    (congrArg (fun σ => cross (⟨d.dims, W⟩ : Ch (□n)) * σ)
      (crossPerm_eq_of_φ (dimSum_replicate n) (g := chartLeg W t) (g' := t) (chartLeg_φ W t)))

/-- …and the crossings add. -/
theorem permLen_cross_runCh_chart {n : ℕ} {d : Ch Zbp} (W : ⋁d.dims ⟶ □n)
    (t : zObj (𝟙^n) ⟶ d) :
    permLen (crossPerm (dimSum_replicate n) t) + permLen (cross (⟨d.dims, W⟩ : Ch (□n)))
      = permLen (cross (runCh (Hom.φ t ≫ W))) :=
  (congrArg (fun σ => permLen σ + crossLen (⟨d.dims, W⟩ : Ch (□n)))
      (crossPerm_eq_of_φ (dimSum_replicate n) (g := chartLeg W t) (g' := t)
        (chartLeg_φ W t))).symm.trans
    (crossLen_eq_add (chartLeg W t)).symm

/-- **The 0-cell a run names, read in the weak order** — the run's own crossing permutation. -/
theorem at_ιRun_cube (p : BraidPresentation) {n : ℕ} (z : ⋁(𝟙^n) ⟶ □n) :
    (p.presentsBrCube n).at' (p.ιRun (□n) z) = op (weakClass (runCh z)) :=
  Opposite.unop_injective
    (WeakOrder.eq_of_iso ((locCubeWeakOrder n).functor.mapIso (p.ιRunIso (□n) z)).unop).symm

/-- **The 0-cells over one chart, read in the weak order**: the chart contributes a fixed
permutation `τ`, and each run over it multiplies `τ` on the right by its own crossing,
length-additively. -/
theorem brCube_chart (p : BraidPresentation) {n : ℕ} (c : ((wedgeHoms (□n)).Elements)ᵒᵖ) :
    ∃ τ : Equiv.Perm (Fin n), ∀ (u : RunAt (eltBase (wedgeHoms (□n)) c) n)
      {A : GenObj (p.Br (□n)).Gen}, ιV (□n) p.fam c (p.runPt u) = A →
        (p.presentsBrCube n).at' A = op (WeakOrder.of (τ * u.perm)) ∧
          permLen u.perm + permLen τ = permLen (τ * u.perm) := by
  obtain ⟨⟨⟨d⟩, W⟩⟩ := c
  refine ⟨cross (⟨d.dims, W⟩ : Ch (□n)), fun u {A} hA => ?_⟩
  obtain ⟨t, rfl⟩ := exists_runPush (cubeStrands (op ⟨op d, W⟩)) u
  have hperm : (RunAt.push t (runAtSelf n)).perm = crossPerm (dimSum_replicate n) t := by
    rw [RunAt.push_perm t (dimSum_replicate n), perm_runAtSelf, mul_one]
  refine ⟨?_, ?_⟩
  · rw [← hA, ιV_runPush p (□n) W t, at_ιRun_cube, weakClass, cross_runCh_chart W t, hperm]
    rfl
  · rw [hperm]
    exact (permLen_cross_runCh_chart W t).trans (congrArg permLen (cross_runCh_chart W t))

/-- **Garside in ⟹ the whole order comes out**: a 1-cell of `Br germBP (□ⁿ)` is a simple acting on
a run, so its two 0-cells are a **length-additive pair** — the full weak order relation, covering
or not. -/
theorem germBrCube_gen (n : ℕ) {A B : GenObj (germBP.Br (□n)).Gen} (e : A ⟶ B) :
    ∃ σ : Equiv.Perm (Fin n),
      WeakOrder.perm ((germBP.presentsBrCube n).at' A).unop
          = WeakOrder.perm ((germBP.presentsBrCube n).at' B).unop * σ ∧
        permLen (WeakOrder.perm ((germBP.presentsBrCube n).at' B).unop) + permLen σ
          = permLen (WeakOrder.perm ((germBP.presentsBrCube n).at' A).unop) := by
  obtain ⟨c, N, σ, u, v, _, hA, hB, hperm, hlen, _⟩ := germBr_gen (□n) e
  obtain rfl : N = n := u.strands.symm.trans (cubeStrands c)
  obtain ⟨τ, hτ⟩ := brCube_chart germBP c
  obtain ⟨hAeq, hAlen⟩ := hτ v hA
  obtain ⟨hBeq, hBlen⟩ := hτ u hB
  refine ⟨σ, ?_, ?_⟩
  · rw [hAeq, hBeq]
    exact (congrArg (fun ρ => τ * ρ) hperm).trans (mul_assoc τ u.perm σ).symm
  · rw [hAeq, hBeq]
    change permLen (τ * u.perm) + permLen σ = permLen (τ * v.perm)
    omega

/-- **Artin in ⟹ only the covering relations come out**: a 1-cell of `Br artinBP (□ⁿ)` is an atom
acting on a run, so it raises the crossing length by exactly one — a Hasse edge of the weak
order. -/
theorem artinBrCube_gen (n : ℕ) {A B : GenObj (artinBP.Br (□n)).Gen} (e : A ⟶ B) :
    ((artinBP.presentsBrCube n).at' B).unop ⋖ ((artinBP.presentsBrCube n).at' A).unop := by
  obtain ⟨c, N, k, u, v, _, hA, hB, hperm, hlen, _⟩ := artinBr_gen (□n) e
  obtain rfl : N = n := u.strands.symm.trans (cubeStrands c)
  obtain ⟨τ, hτ⟩ := brCube_chart artinBP c
  obtain ⟨hAeq, hAlen⟩ := hτ v hA
  obtain ⟨hBeq, hBlen⟩ := hτ u hB
  have hmul : τ * v.perm = τ * u.perm * adjT k :=
    (congrArg (fun ρ => τ * ρ) hperm).trans (mul_assoc τ u.perm (adjT k)).symm
  have hstep : permLen (τ * u.perm) + 1 = permLen (τ * v.perm) := by omega
  rw [hAeq, hBeq]
  change WeakOrder.of (τ * u.perm) ⋖ WeakOrder.of (τ * v.perm)
  refine WeakOrder.covBy_of_permLen_succ ?_ hstep
  rw [hmul]
  exact WeakOrder.le_of_mul (by rw [permLen_adjT, ← hmul]; omega)

end ChainCat
