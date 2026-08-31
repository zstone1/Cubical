import CubeChains.Concurrency.Complexification.HPresentation
import CubeChains.Concurrency.Complexification.HPosAction

/-!
# Concurrency/Complexification/WallPresentation — the codimension filtration, as a presentation

Objects the runs, generators the codimension-one cells, relations the codimension-two ones.  A
generator is a span (`Wall`), because a codimension-one chain lies *below* both runs it separates;
`Wall.act` is that span read in the positive braid action, where the merge leg acts trivially.

⚠ Relations are indexed by the codimension-two **cell**, not by path length: commutation is a
length-two coincidence but the braid relation is length-three, so `Cut.rel`'s "two factorisations
of one refinement" has to be read as "two paths under one cell" here.

Soundness needs no rank-two classification: `Ch (Hbp □ⁿ)` is a poset, so a path under `d`
telescopes against the unique arrows to `d` (`act_comp_toAction`), and the length bookkeeping in
`PosBraid n` pins the value down (`eq_posPerm_of_posLen`).
-/

open CategoryTheory Equiv Opposite BPSet ChainCat

namespace CubeChains

variable {n : ℕ}

/-! ## The wall graph

The vertices are the runs themselves; only the edges differ, so this is a `Quiver` instance
looking for a carrier, not a new encoding of anything. -/

/-- The runs of `K`, carrying the **wall graph** rather than their own refinements. -/
def WallGraph (K : BPSet) : Type := Run K

instance {K : BPSet} : Quiver (WallGraph K) where
  Hom a b := Wall (a : Run K) (b : Run K)

/-- **A path of wall crossings lies under `d`** when every cell it crosses does — the source
included, so the whole zigzag sits in the closed star of `d`. -/
def Under {K : BPSet} {a : WallGraph K} (d : Ch K) :
    ∀ {b : WallGraph K}, Quiver.Path a b → Prop
  | _, .nil => Nonempty ((a : Run K).chain ⟶ d)
  | _, .cons P u => Under d P ∧ Nonempty (u.cell ⟶ d)

theorem Under.src {K : BPSet} {a : WallGraph K} {d : Ch K} :
    ∀ {b : WallGraph K} {P : Quiver.Path a b}, Under d P → Nonempty ((a : Run K).chain ⟶ d)
  | _, .nil, h => h
  | _, .cons _ _, h => Under.src h.1

theorem Under.tgt {K : BPSet} {a : WallGraph K} {d : Ch K} :
    ∀ {b : WallGraph K} {P : Quiver.Path a b}, Under d P → Nonempty ((b : Run K).chain ⟶ d)
  | _, .nil, h => h
  | _, .cons _ u, h => ⟨u.merge ≫ h.2.some⟩

/-- **The codimension-two relation**: two paths of wall crossings under one codimension-two
chain. -/
def WallRel (K : BPSet) : HomRel (Paths (WallGraph K)) := fun _ _ P Q =>
  ∃ d : Ch K, ChainCat.degree d = 2 ∧ Under d P ∧ Under d Q

/-! ## The wall graph, acting on the orderings -/

/-- **Crossing a wall, read in the positive braid action** — the merge leg acts trivially, so only
the crossing leg is left. -/
noncomputable def Wall.act {a b : Run (Hbp.obj (□n))} (u : Wall a b) :
    (chToAction n).obj a.chain ⟶ (chToAction n).obj b.chain :=
  ⟨posPerm (chainCross u.cross), by
    change posPermHom n (posPerm (chainCross u.cross)) * chainPerm a.chain = chainPerm b.chain
    rw [posPermHom_posPerm, chainCross_smul, chToAction_map_of_W u.merge_mem]⟩

/-- The wall graph, acting on the orderings: a run to the order it performs the axes in, a wall
crossing to the atom it crosses. -/
noncomputable def wallFunctor (n : ℕ) : Paths (WallGraph (Hbp.obj (□n))) ⥤ PosBraidAction n :=
  Paths.lift { obj := fun a => (chToAction n).obj (a : Run (Hbp.obj (□n))).chain
               map := fun {_ _} u => Wall.act u }

theorem wallFunctor_map_cons {a b c : WallGraph (Hbp.obj (□n))}
    (P : Quiver.Path a b) (u : b ⟶ c) :
    (wallFunctor n).map (P.cons u) = (wallFunctor n).map P ≫ Wall.act u := rfl

/-! ## Soundness: a path under a cell is pinned by that cell

`Ch (Hbp □ⁿ)` is a poset, so the arrows `a ⟶ d` and `b ⟶ d` are unique; the path telescopes
against them, and the germ relation reads off the value. -/

/-- **The telescope.**  Crossing walls under `d` and then landing on `d` is landing on `d`. -/
theorem act_comp_toAction {a : WallGraph (Hbp.obj (□n))} (d : Ch (Hbp.obj (□n)))
    (fa : (a : Run (Hbp.obj (□n))).chain ⟶ d) :
    ∀ {b : WallGraph (Hbp.obj (□n))} (P : Quiver.Path a b), Under d P →
      ∀ fb : (b : Run (Hbp.obj (□n))).chain ⟶ d,
        (wallFunctor n).map P ≫ (chToAction n).map fb = (chToAction n).map fa
  | _, .nil, _, fb => by
      rw [show fb = fa from Subsingleton.elim _ _]
      exact Category.id_comp _
  | _, .cons P u, h, fb => by
      have hstep : Wall.act u ≫ (chToAction n).map fb
          = (chToAction n).map (u.cross ≫ h.2.some) := by
        refine Subtype.ext ?_
        rw [ActionCategory.comp_val, show fb = u.merge ≫ h.2.some from Subsingleton.elim _ _]
        change posPerm (chainCross (u.merge ≫ h.2.some)) * posPerm (chainCross u.cross)
          = posPerm (chainCross (u.cross ≫ h.2.some))
        rw [chainCross_comp, chainCross_eq_one_of_W u.merge_mem, mul_one,
          posPerm_mul_chainCross]
      rw [wallFunctor_map_cons]
      refine (Category.assoc _ _ _).trans ?_
      exact (congrArg (fun g => (wallFunctor n).map P ≫ g) hstep).trans
        (act_comp_toAction d fa P h.1 _)

/-- **A path under a codimension-two cell is reduced**, hence is the simple of its permutation:
the crossings it makes are exactly the inversions its endpoints differ by. -/
theorem val_wallFunctor_eq {a b : WallGraph (Hbp.obj (□n))} {P : Quiver.Path a b}
    {d : Ch (Hbp.obj (□n))} (fa : (a : Run (Hbp.obj (□n))).chain ⟶ d)
    (fb : (b : Run (Hbp.obj (□n))).chain ⟶ d) (h : Under d P) :
    ((wallFunctor n).map P).val = posPerm ((chainCross fb)⁻¹ * chainCross fa) := by
  have key : posPerm (chainCross fb) * ((wallFunctor n).map P).val
      = posPerm (chainCross fa) := by
    rw [← chToAction_map_val, ← chToAction_map_val, ← ActionCategory.comp_val]
    exact congrArg Subtype.val (act_comp_toAction d fa P h fb)
  set β := ((wallFunctor n).map P).val with hβ
  have hlen := congrArg (fun c => Multiplicative.toAdd (posLen n c)) key
  have hperm := congrArg (posPermHom n) key
  simp only [map_mul, toAdd_mul, posLen_posPerm, toAdd_ofAdd, posPermHom_posPerm] at hlen hperm
  have hsub : permLen (chainCross fb * posPermHom n β)
      ≤ permLen (chainCross fb) + permLen (posPermHom n β) := permLen_mul_le _ _
  rw [hperm] at hsub
  have hle := permLen_posPermHom_le β
  have hred : Multiplicative.toAdd (posLen n β) = permLen (posPermHom n β) := by omega
  have hπ : posPermHom n β = (chainCross fb)⁻¹ * chainCross fa := by
    rw [← hperm, inv_mul_cancel_left]
  rw [eq_posPerm_of_posLen hred, hπ]

/-- **The codimension-two relation is sound**: two paths under one cell have one value. -/
theorem wallFunctor_congr {a b : Paths (WallGraph (Hbp.obj (□n)))} {P Q : a ⟶ b}
    (h : WallRel (Hbp.obj (□n)) P Q) :
    (wallFunctor n).map P = (wallFunctor n).map Q := by
  obtain ⟨d, -, hP, hQ⟩ := h
  refine Subtype.ext ?_
  rw [val_wallFunctor_eq hP.src.some hP.tgt.some hP,
    val_wallFunctor_eq hP.src.some hP.tgt.some hQ]

/-- **The wall graph, modulo the codimension-two cells, acts on the orderings.** -/
noncomputable def wallQuotientFunctor (n : ℕ) :
    Quotient (WallRel (Hbp.obj (□n))) ⥤ PosBraidAction n :=
  CategoryTheory.Quotient.lift _ (wallFunctor n) fun _ _ _ _ h => wallFunctor_congr h

/-! ## The runs exhaust the orderings

Every ordering is performed by some run: the fibre over the all-edges chain is the orderings
(`bijective_fibrePerm`), and an all-edges chain *is* a run. -/

/-- **Every ordering is a run's.** -/
theorem chainPerm_surjective (n : ℕ) :
    Function.Surjective fun r : Run (Hbp.obj (□n)) => chainPerm r.chain := by
  intro σ
  obtain ⟨β, hβ⟩ :=
    (bijective_fibrePerm (⟨ChainCat.zObj (𝟙^n), dimSum_replicate n⟩ : ChainCat.ChStrands Zbp n)).2 σ
  exact ⟨⟨⟨𝟙^n, β⟩, fun _ hd => List.eq_of_mem_replicate hd⟩, hβ⟩

instance (n : ℕ) : (wallQuotientFunctor n).EssSurj where
  mem_essImage x := by
    obtain ⟨r, hr⟩ := chainPerm_surjective n x.back
    have hr' : chainPerm r.chain = x.back := hr
    refine ⟨⟨(r : WallGraph (Hbp.obj (□n)))⟩, ⟨eqToIso ?_⟩⟩
    change ((chainPerm r.chain : Equiv.Perm (Fin n)) : PosBraidAction n) = x
    rw [hr']
    exact ActionCategory.back_coe x

end CubeChains
