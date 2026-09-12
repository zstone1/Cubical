import CubeChains.Concurrency.Presentation.PaperPoly
import CubeChains.Machinery.Presentation.Bijective

/-!
# Concurrency/Presentation/PaperPresents — the paper's polygraph presents `Ch(K)[W⁻¹]`

`chCellPresentation` presents `Ch(K)[W⁻¹]` on the runs, the kept cuts and the greatest
codimension-two cuts out of a run.  `Paper.poly` presents it on the runs and the **objects** of
degree one and two.  The comparison is one bijection per dimension below two:

    kept cut out of a run ◂───────▸ degree-one object        `genOfRunCut` / its greatest refinement

and in dimension two derivability both ways, the kept cells being ordered pairs of the two
factorisations where a degree-two object carries the pair itself.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat.Paper

variable {K : BPSet}

/-! ## The 1-cells are the kept cuts

A kept cut is the degree-one object it lands on, and that object's greatest refinement is the cut
again — at degree one there is no other crossing refinement (`hom_eq_of_not_W_deg_one`). -/

/-- Renaming a cell's endpoints leaves its object alone. -/
theorem obj_cellCongr {n : ℕ} {X X' Y Y' : Run K} (hx : X = X') (hy : Y = Y') (α : Cell n X Y) :
    (cellCongr (Cell n) hx hy α).obj = α.obj := by subst hx; subst hy; rfl

/-- …and renaming a 1-cell of the contraction leaves its source alone. -/
theorem dom_cellCongr {U U' V V' : (chContraction K).V} (hu : U = U') (hv : V = V')
    (g : (chContraction K).Gen U V) :
    (cellCongr (chContraction K).Gen hu hv g).dom = g.dom := by subst hu; subst hv; rfl

/-- …and its target. -/
theorem cod_cellCongr {U U' V V' : (chContraction K).V} (hu : U = U') (hv : V = V')
    (g : (chContraction K).Gen U V) :
    (cellCongr (chContraction K).Gen hu hv g).cod = g.cod := by subst hu; subst hv; rfl

@[simp] theorem obj_genOfRunCut {U V : (chContraction K).V} (g : (chContraction K).Gen U V)
    (hg : RunCut g) : (genOfRunCut g hg).obj = vChain g.dom :=
  obj_cellCongr _ _ _

/-- **A kept cut lands on its target run** — `RunCut` says the target is its own representative. -/
theorem cod_eq_of_runCut {U V : (chContraction K).V} (g : (chContraction K).Gen U V)
    (hg : RunCut g) : g.cod = V.1 := hg.symm.trans g.rep_cod

/-- **A kept cut crosses** — it is not one of the merges the contraction inverts. -/
theorem not_W_genHom_of_not_merged {a b : (chCutPoly K).V} (c : (chCutPoly K).Gen a b)
    (hc : ¬ Cut.merged (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) c)) :
    ¬ W Zbp (Cut.genHom c.1) := fun hW =>
  hc ((merge_iff (Cut.genHom c.1)).mpr ⟨hW, Cut.codim_genHom c.1⟩)

/-- **A kept cut is pinned by the object it lands on** — the cut itself is then forced, there being
only one crossing refinement at degree one. -/
theorem genOfRunCut_injective {U V : (chContraction K).V} :
    Function.Injective
      (fun e : {g : (chContraction K).Gen U V // RunCut g} => genOfRunCut e.1 e.2) := by
  rintro ⟨⟨dom, cod, gen, nm, rd, rc⟩, hg⟩ ⟨⟨dom', cod', gen', nm', rd', rc'⟩, hg'⟩ h
  obtain rfl : cod = V.1 := hg.symm.trans rc
  obtain rfl : cod' = V.1 := hg'.symm.trans rc'
  obtain rfl : dom = dom' := by
    have hobj : vChain dom = vChain dom' :=
      (obj_genOfRunCut _ hg).symm.trans ((congrArg Cell.obj h).trans (obj_genOfRunCut _ hg'))
    exact (chV_vChain dom).symm.trans ((congrArg chV hobj).trans (chV_vChain dom'))
  obtain ⟨c, rfl⟩ : ∃ c, gen = Sum.inl c := by
    rcases gen with c | ⟨c, hc⟩
    · exact ⟨c, rfl⟩
    · exact absurd trivial nm
  obtain ⟨c', rfl⟩ : ∃ c', gen' = Sum.inl c' := by
    rcases gen' with c' | ⟨c', hc'⟩
    · exact ⟨c', rfl⟩
    · exact absurd trivial nm'
  have hrun : ∀ x ∈ (shOf V.1).dims, x = 1 := fun x hx =>
    List.eq_of_mem_replicate
      (congrArg ChainCat.Obj.dims (shOf_eq_ones_of_eltRep hg rfl) ▸ hx)
  have hdeg : degree (shOf dom) = 1 := by
    have h1 := degree_eq_add_codim (Cut.genHom c.1)
    rw [(degree_eq_zero_iff (shOf V.1)).mpr hrun, Cut.codim_genHom c.1] at h1
    simpa using h1
  have hcut : Cut.genHom c.1 = Cut.genHom c'.1 :=
    eq_of_not_W_deg_one hrun hdeg (not_W_genHom_of_not_merged c nm)
      (not_W_genHom_of_not_merged c' nm')
  obtain rfl : c = c' := Subtype.ext (Subtype.ext hcut)
  rfl

/-- **The kept cut a degree-one object is** — its greatest refinement. -/
noncomputable def runCutOfGen {U V : (chContraction K).V} (α : Gen (runOfV U) (runOfV V)) :
    (chContraction K).Gen U V :=
  cellCongr (chContraction K).Gen
    (((runEquiv K).right_inv _).symm.trans
      ((congrArg vOfRun α.below).trans ((runEquiv K).right_inv U)))
    (Subtype.ext ((congrArg eltRep (chV_vChain V.1)).trans V.2))
    (chGenOf α.hom α.codim_hom (α.not_W_hom one_ne_zero))

@[simp] theorem dom_runCutOfGen {U V : (chContraction K).V} (α : Gen (runOfV U) (runOfV V)) :
    (runCutOfGen α).dom = chV α.obj := dom_cellCongr _ _ _

@[simp] theorem cod_runCutOfGen {U V : (chContraction K).V} (α : Gen (runOfV U) (runOfV V)) :
    (runCutOfGen α).cod = chV (runOfV V).chain := cod_cellCongr _ _ _

theorem runCut_runCutOfGen {U V : (chContraction K).V} (α : Gen (runOfV U) (runOfV V)) :
    RunCut (runCutOfGen α) := by
  change eltRep (runCutOfGen α).cod = (runCutOfGen α).cod
  rw [cod_runCutOfGen]
  exact eltRep_chV (runOfV V)

/-- **…and it lands on that object again**, so the kept cuts and the degree-one objects biject. -/
theorem genOfRunCut_runCutOfGen {U V : (chContraction K).V} (α : Gen (runOfV U) (runOfV V)) :
    genOfRunCut (runCutOfGen α) (runCut_runCutOfGen α) = α :=
  Cell.ext (by rw [obj_genOfRunCut, dom_runCutOfGen, vChain_chV])

theorem genOfRunCut_surjective {U V : (chContraction K).V} :
    Function.Surjective
      (fun e : {g : (chContraction K).Gen U V // RunCut g} => genOfRunCut e.1 e.2) :=
  fun α => ⟨⟨runCutOfGen α, runCut_runCutOfGen α⟩, genOfRunCut_runCutOfGen α⟩

/-- **The kept cuts out of a run are the degree-one objects.** -/
noncomputable def genEquiv (U V : (chContraction K).V) :
    {g : (chContraction K).Gen U V // RunCut g} ≃ Gen (runOfV U) (runOfV V) :=
  Equiv.ofBijective _ ⟨genOfRunCut_injective, genOfRunCut_surjective⟩

@[simp] theorem genEquiv_apply {U V : (chContraction K).V}
    (e : {g : (chContraction K).Gen U V // RunCut g}) :
    genEquiv U V e = genOfRunCut e.1 e.2 := rfl

end ChainCat.Paper
