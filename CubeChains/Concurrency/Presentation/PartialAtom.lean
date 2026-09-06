import CubeChains.Concurrency.Presentation.ElementsFibration
import CubeChains.Concurrency.Presentation.LocPresentation

/-!
# Concurrency/Presentation/PartialAtom — the atoms acting partially on the runs

`atomComp N k` carries one bead of size two, so a chart of it is a path with a **square** at the
`k`-th cut, `mergeLift` along `mergeOnes N k` finds that square, and `atomOnes N k` reads its other
staircase.  So `atomAct` is "flip the square at `k`, if `K` has one" — total exactly when `K` has
every square, which the bare cube does not.

`exists_square_of_atomAct` is the fact a braid relation turns on: the square refines *both* its
staircases, so a step leaves two codimension-one refinements at the chart it lands on, and that is
where `HasDiamonds` applies — not at the chart it started from.

The two legs need different things.  Separation is used only for the **merge** leg, to make the
square unique; the **atom** leg is a cartesian lift and asks nothing of `K`, which is why this route
survives where descent does not.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain

namespace ChainCat

variable {K : BPSet} (h : SeparatesMerges K) {N : ℕ}

/-- **The atom at the `k`-th cut, acting partially on the charts over the run**: lift along the
merge — the square at that cut, if `K` has one — then read the square's other staircase. -/
noncomputable def atomAct (k : Fin (N - 1)) :
    (wedgeHoms K).obj (op (zObj (𝟙^N))) → Option ((wedgeHoms K).obj (op (zObj (𝟙^N)))) :=
  fun x => (mergeLift (h _ (W_mergeOnes N k)) x).map ((wedgeHoms K).map (atomOnes N k).op)

/-- **The square refines both its staircases** — the two codimension-one refinements a step leaves
behind, and the reason `HasDiamonds` has purchase after a step rather than before one. -/
theorem exists_square_of_atomAct {k : Fin (N - 1)} {x y : (wedgeHoms K).obj (op (zObj (𝟙^N)))}
    (hp : atomAct h k x = some y) :
    ∃ (z : (wedgeHoms K).obj (op (zObj (atomComp N k))))
      (u : chartChain (𝟙^N) x ⟶ chartChain (atomComp N k) z)
      (v : chartChain (𝟙^N) y ⟶ chartChain (atomComp N k) z),
      codim u = 1 ∧ codim v = 1 := by
  rw [atomAct, Option.map_eq_some_iff] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  exact ⟨z, homOfRestrict (mergeOnes N k) ((mergeLift_eq_some_iff _ x z).mp hz),
    homOfRestrict (atomOnes N k) rfl, codim_mergeOnes N k, codim_atomOnes N k⟩

end ChainCat
