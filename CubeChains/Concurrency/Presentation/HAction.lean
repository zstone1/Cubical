import CubeChains.Concurrency.Presentation.BaseComponent
import CubeChains.Concurrency.Presentation.ElementsFibration
import CubeChains.Machinery.Localization.ActionPresentation
import CubeChains.Machinery.Localization.PathPresentation
import CubeChains.Machinery.Localization.ElementsPresentation
import CubeChains.Concurrency.Complexification.HPosAction
import CubeChains.Concurrency.Complexification.HSegal

/-!
# Concurrency/Presentation/HAction — the localized chains, lifted from the presentation

Generic in `K`: localizing only localizes the base (`isLocalization_chDescent`), and the localized
base is `PosBraid N` at the run (`Concurrency/Presentation/Retraction`), so `chLocEquivElements`
reads `Ch K[W⁻¹]` as the elements of `K`'s fibre over the run, a `PosBraid N`-set.  Then for the
decorated cube: the fibre is `Sₙ` by the **run classifier**, and the action is `posPermHom`,
checked on the `n−1` atoms.

This presents the **category**, never its vertex monoids (`end_not_generated_by_simples`).
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain ChainCat

namespace CubeChains

variable {n : ℕ}

/-! ## Generic in `K`: the localized chains are the fibre over the run

Nothing below mentions a cube, a crossing permutation or a decoration. -/

section Generic

variable (K : BPSet) (N : ℕ) (hS : IsSegal K.toPsh)

/-- **Every object carrying a chain of `K` is the run**, when `K` puts all its chains at one
strand count. -/
theorem cover_of_strands (hK : ∀ {d : List ℕ+}, (⋁d ⟶ K) → dimSum d = N)
    (c : ((W Zbp).op).Localization) (x : (wedgeHomsDescend K hS).obj c) :
    ∃ d, Nonempty ((runBase N).obj d ≅ c) := by
  obtain ⟨⟨⟨a⟩⟩⟩ := c
  exact ⟨op (SingleObj.star (PosBraid N)), ⟨(runIso a (hK x)).symm⟩⟩

/-- **`Ch K` with the bead merges inverted is the category of elements of `K`'s fibre over the
run**, read as a `PosBraid N`-set.  The presentation of the base does all the work: `runIso` sees
every chain as its run, and `homEquivPosBraid` is the hom-sets. -/
noncomputable def chLocEquivElements (hK : ∀ {d : List ℕ+}, (⋁d ⟶ K) → dimSum d = N) :
    (W K).Localization ≌ ((runBase N ⋙ wedgeHomsDescend K hS).Elements)ᵒᵖ :=
  haveI : (chDescent K hS).IsLocalization (W K) := isLocalization_chDescent _ _
  haveI : (CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N)).IsEquivalence :=
    CategoryOfElements.isEquivalence_pre _ _ (cover_of_strands K N hS hK)
  (Localization.equivalenceFromModel (chDescent K hS) (W K)).trans
    ((CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N)).asEquivalence.symm.op)

end Generic

/-! ## The decorated cube: the fibre is `Sₙ`

The run classifier, not a crossing permutation. -/

/-- The decorated cube's fibre, descended through the merges. -/
noncomputable abbrev hFibre (n : ℕ) : ((W Zbp).op).Localization ⥤ Type :=
  wedgeHomsDescend (Hbp.obj (□n)) (isSegal_H_cube n)

/-- **The fibre over the run is the orderings** — a map out of the `n` edges is a run of the
decorated cube, and a run of the decorated cube is an ordering of its axes. -/
noncomputable def runFibreEquiv (n : ℕ) :
    (⋁(𝟙^n) ⟶ Hbp.obj (□n)) ≃ Equiv.Perm (Fin n) :=
  (onesHomEquivRunHbp n).trans (runHbpCubeEquivPerm n)

/-! ## The decorated cube: the action is `posPermHom`, checked on the atoms -/

theorem hFibre_map_Q {x y : (Ch Zbp)ᵒᵖ} (f : x ⟶ y) :
    (hFibre n).map (((W Zbp).op).Q.map f) = (wedgeHoms (Hbp.obj (□n))).map f :=
  Category.id_comp _

theorem wedgeHoms_map_op {a b : Ch Zbp} (h : a ⟶ b) (z : ⋁b.dims ⟶ Hbp.obj (□n)) :
    (wedgeHoms (Hbp.obj (□n))).map h.op z = h.φ ≫ z := rfl

/-- **The `k`-th atom exchanges the `k`-th and `(k+1)`-st steps of a run** — one of the `n−1`
facts the whole action rests on.  `crossPerm` appears only to name the atom's transposition. -/
theorem runFibreEquiv_atomLoop (k : Fin (n - 1)) (z : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) :
    runFibreEquiv n ((hFibre n).map (atomLoop n k) z)
      = (adjT k)⁻¹ * runFibreEquiv n z := by
  haveI := isIso_Q_op_of_W (W_mergeOnes n k)
  have hconj : atomLoop n k
      = inv (((W Zbp).op).Q.map (mergeOnes n k).op)
          ≫ ((W Zbp).op).Q.map (atomOnes n k).op := by
    rw [atomLoop, conj,
      show runMerge (ChainCat.zObj (𝟙^n)) (dimSum_replicate n) = 𝟙 _ from endo_eq_id _,
      op_id, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  obtain ⟨y, hy⟩ : ∃ y, (hFibre n).map
      (inv (((W Zbp).op).Q.map (mergeOnes n k).op)) z = y := ⟨_, rfl⟩
  have hmy : (mergeOnes n k).φ ≫ y = z := by
    have h1 : (hFibre n).map (((W Zbp).op).Q.map (mergeOnes n k).op) y = z := by
      rw [← hy, ← (hFibre n).map_comp_apply, IsIso.inv_hom_id, (hFibre n).map_id_apply]
    rw [hFibre_map_Q] at h1
    exact h1
  have hval : (hFibre n).map (atomLoop n k) z = (atomOnes n k).φ ≫ y := by
    rw [hconj, (hFibre n).map_comp_apply, hy, hFibre_map_Q]
    rfl
  rw [show runFibreEquiv n ((hFibre n).map (atomLoop n k) z)
      = fibrePerm (A := ChainCat.zObj (𝟙^n)) (dimSum_replicate n)
          ((hFibre n).map (atomLoop n k) z) from (fibrePerm_ones _).symm,
    show runFibreEquiv n z
      = fibrePerm (A := ChainCat.zObj (𝟙^n)) (dimSum_replicate n) z from (fibrePerm_ones _).symm,
    hval, fibrePerm_comp (dimSum_replicate n) (dimSum_atomComp n k) (atomOnes n k) y,
    crossPerm_atomOnes,
    ← hmy, fibrePerm_comp (dimSum_replicate n) (dimSum_atomComp n k) (mergeOnes n k) y,
    crossPerm_eq_one_of_W (dimSum_replicate n) (W_mergeOnes n k), inv_one, one_mul]

/-- **Two maps out of `PosBraid n` agreeing on the atoms agree** — peel an adjacent descent and
induct on the length; no Matsumoto. -/
theorem posPerm_adjT_ext {M : Type*} [Monoid M] {φ ψ : PosBraid n →* M}
    (h : ∀ k : Fin (n - 1), φ (posPerm (adjT k)) = ψ (posPerm (adjT k))) : φ = ψ := by
  refine posPerm_ext ?_
  suffices key : ∀ (m : ℕ) (σ : Equiv.Perm (Fin n)), permLen σ ≤ m →
      φ (posPerm σ) = ψ (posPerm σ) from fun σ => key (permLen σ) σ le_rfl
  intro m
  induction m with
  | zero =>
      intro σ hσ
      obtain rfl : σ = 1 := eq_one_of_permLen_eq_zero σ (Nat.le_zero.mp hσ)
      rw [posPerm_one, map_one, map_one]
  | succ m ih =>
      intro σ hσ
      rcases Nat.eq_zero_or_pos (permLen σ) with h0 | hpos
      · obtain rfl : σ = 1 := eq_one_of_permLen_eq_zero σ h0
        rw [posPerm_one, map_one, map_one]
      obtain ⟨i, hdesc⟩ := exists_adjacent_descent σ hpos
      have hlen : permLen σ = permLen (σ * adjT i) + 1 := permLen_mul_adjT_of_descent hdesc
      have hsplit : posPerm (σ * adjT i) * posPerm (adjT i) = posPerm σ := by
        rw [posPerm_mul_adjT (adjT_ascent_of_descent hdesc), mul_adjT_adjT]
      rw [← hsplit, map_mul, map_mul, ih (σ * adjT i) (by omega), h i]

/-- Restriction along a braid, read on the orderings. -/
noncomputable def fibreAction (n : ℕ) :
    PosBraid n →* (Function.End (Equiv.Perm (Fin n)))ᵐᵒᵖ where
  toFun β := MulOpposite.op fun x =>
    runFibreEquiv n ((hFibre n).map ((runBraid n β).unop) ((runFibreEquiv n).symm x))
  map_one' := by
    refine congrArg MulOpposite.op (funext fun x => ?_)
    rw [show ((runBraid n (1 : PosBraid n)).unop) = 𝟙 _ from
        congrArg MulOpposite.unop (map_one (runBraid n)),
      (hFibre n).map_id_apply, Equiv.apply_symm_apply]
    rfl
  map_mul' a b := by
    refine congrArg MulOpposite.op (funext fun x => ?_)
    rw [show ((runBraid n (a * b)).unop) = (runBraid n a).unop ≫ (runBraid n b).unop from
        congrArg MulOpposite.unop (map_mul (runBraid n) a b),
      (hFibre n).map_comp_apply]
    change _ = runFibreEquiv n ((hFibre n).map ((runBraid n b).unop)
      ((runFibreEquiv n).symm (runFibreEquiv n
        ((hFibre n).map ((runBraid n a).unop) ((runFibreEquiv n).symm x)))))
    rw [Equiv.symm_apply_apply]

/-- The orderings, acted on through `posPermHom` — what `permPresheaf` is. -/
noncomputable def permAction (n : ℕ) :
    PosBraid n →* (Function.End (Equiv.Perm (Fin n)))ᵐᵒᵖ where
  toFun β := MulOpposite.op fun x => (posPermHom n β)⁻¹ * x
  map_one' := by
    refine congrArg MulOpposite.op (funext fun x => ?_)
    rw [map_one, inv_one, one_mul]
    rfl
  map_mul' a b := by
    refine congrArg MulOpposite.op (funext fun x => ?_)
    change (posPermHom n (a * b))⁻¹ * x = (posPermHom n b)⁻¹ * ((posPermHom n a)⁻¹ * x)
    rw [map_mul, mul_inv_rev, mul_assoc]

/-- **A positive braid acts on the runs through its own permutation** — the atoms determine it. -/
theorem fibreAction_eq (n : ℕ) : fibreAction n = permAction n :=
  posPerm_adjT_ext fun k => by
    refine congrArg MulOpposite.op (funext fun x => ?_)
    change runFibreEquiv n
      ((hFibre n).map ((runBraid n (posPerm (adjT k))).unop) ((runFibreEquiv n).symm x))
        = (posPermHom n (posPerm (adjT k)))⁻¹ * x
    have hb : ((runBraid n (posPerm (adjT k))).unop) = atomLoop n k := by
      rw [runBraid_posPerm]
      exact runLoop_adjT n k
    rw [hb, runFibreEquiv_atomLoop, posPermHom_posPerm, Equiv.apply_symm_apply]

/-- **The braid's action on the fibre is left multiplication by its permutation.** -/
theorem runFibreEquiv_runBraid (β : PosBraid n) (z : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) :
    runFibreEquiv n ((hFibre n).map ((runBraid n β).unop) z)
      = (posPermHom n β)⁻¹ * runFibreEquiv n z := by
  have h2 : (fun x => runFibreEquiv n
        ((hFibre n).map ((runBraid n β).unop) ((runFibreEquiv n).symm x)))
      = fun x => (posPermHom n β)⁻¹ * x :=
    MulOpposite.op_injective (DFunLike.congr_fun (fibreAction_eq n) β)
  have h3 := congrFun h2 (runFibreEquiv n z)
  rw [Equiv.symm_apply_apply] at h3
  exact h3

/-- **The fibre over the run is `Sₙ`, equivariantly.** -/
noncomputable def fibreIso (n : ℕ) : runBase n ⋙ hFibre n ≅ permPresheaf n :=
  NatIso.ofComponents (fun _ => (runFibreEquiv n).toIso) (by
    intro x y f
    ext z
    exact runFibreEquiv_runBraid f.unop z)

/-! ## The lift -/

/-- **The decorated chains of `□ⁿ` with the bead merges inverted are the positive braid action** —
`PosBraid n` on the `n!` orderings of the axes, the runs. -/
noncomputable def hLocEquiv (n : ℕ) :
    (W (Hbp.obj (□n))).Localization ≌ PosBraidAction n :=
  (chLocEquivElements (Hbp.obj (□n)) n (isSegal_H_cube n) (fun {_} α => hbpCubeStrands α)).trans
    (((CategoryOfElements.mapEquivalence (fibreIso n)).op).trans permPresheafElementsEquiv)

/-! ## The presentation, read off

`ArtinPosBraid n` is `PresentedMonoid (ArtinRel n)` by definition, so naming it is naming the
generators and the relations. -/

/-- The Artin monoid acts on the orderings through its comparison with the positive braids. -/
instance : MulAction (ArtinPosBraid n) (Equiv.Perm (Fin n)) :=
  MulAction.compHom _ (posOfArtinPos n)

/-- **The decorated chains of `□ⁿ` with the bead merges inverted are the Artin monoid on `n−1`
generators acting on the `n!` orderings** — the `Ch Zbp[W⁻¹]` presentation, one copy per run. -/
noncomputable def hLocArtinEquiv (n : ℕ) :
    (W (Hbp.obj (□n))).Localization ≌ ActionCategory (ArtinPosBraid n) (Equiv.Perm (Fin n)) :=
  (hLocEquiv n).trans
    (actionCategoryCongr (posBraid_equiv_artinPos n) fun m a => by
      change posPermHom n m * a
        = posPermHom n (posOfArtinPos n (posBraid_equiv_artinPos n m)) * a
      rw [show posOfArtinPos n (posBraid_equiv_artinPos n m) = m from
        (posBraid_equiv_artinPos n).symm_apply_apply m])

/-! ## The presentation, lifted

`PosBraid n` is `PresentedMonoid (PosGermRel n)` — generators the simples, relations the germ
relations — so `pathQuotientEquiv` puts it in the `Quotient`-of-`Paths` form that
`elementsPresentation` consumes.  Lifting it along the fibration gives generators the simples
acting on an ordering and relations the germ relations on projected paths;
`val_elementsPresentation_map` says which generator a morphism is. -/

/-- The germ presentation of `PosBraid n`, as a quotient of a path category. -/
noncomputable def germQuotientEquiv (n : ℕ) :
    Quotient (pathRel (PosGermRel n)) ≌ (SingleObj (PosBraid n))ᵒᵖ :=
  pathQuotientEquiv (PosGermRel n)

/-- The orderings of the axes, read on the germ presentation. -/
noncomputable abbrev germFibre (n : ℕ) : Quotient (pathRel (PosGermRel n)) ⥤ Type :=
  (germQuotientEquiv n).functor ⋙ runBase n ⋙ hFibre n

/-! ### Off the cube

Representability of `symFree K` supplies the Segal condition but *not* the strand count: it
constrains `K.toPsh` alone, while the strand count is a fact about `K`'s two base points, which
`Hbp` reads off `K.init`/`K.final`.  So both are carried; the fibre is left as the hom-set. -/

/-- The fibre of a `K` whose symmetrization is representable. -/
noncomputable abbrev hFibreOf (K : BPSet) {n : ℕ}
    (e : symFree.obj K.toPsh ≅ yoneda.obj ▪n) : ((W Zbp).op).Localization ⥤ Type :=
  wedgeHomsDescend (Hbp.obj K) (isSegal_H_of_symFree_repr e)

/-- …read on the germ presentation. -/
noncomputable abbrev germFibreOf (K : BPSet) {n : ℕ}
    (e : symFree.obj K.toPsh ≅ yoneda.obj ▪n) :
    Quotient (pathRel (PosGermRel n)) ⥤ Type :=
  (germQuotientEquiv n).functor ⋙ runBase n ⋙ hFibreOf K e

/-- **The decorated chains of any `K` with representable symmetrization, presented** — generators
the Garside simples acting on the fibre, relations the germ relations on projected paths. -/
noncomputable def hLocPresentationOf (K : BPSet) {n : ℕ}
    (e : symFree.obj K.toPsh ≅ yoneda.obj ▪n)
    (hK : ∀ {d : List ℕ+}, (⋁d ⟶ Hbp.obj K) → dimSum d = n) :
    (W (Hbp.obj K)).Localization
      ≌ (Quotient (totalRel (pathRel (PosGermRel n)) (germFibreOf K e)))ᵒᵖ :=
  (chLocEquivElements (Hbp.obj K) n (isSegal_H_of_symFree_repr e) (fun {_} α => hK α)).trans
    (((CategoryOfElements.preEquivalenceComp (runBase n ⋙ hFibreOf K e)
        (germQuotientEquiv n)).symm.op).trans
      ((elementsPresentation (pathRel (PosGermRel n)) (germFibreOf K e)).symm.op))

/-- **The decorated chains of `□ⁿ` with the bead merges inverted, presented** — the cube instance,
where `symFreeCube` supplies the representability and `hbpCubeStrands` the strand count. -/
noncomputable def hLocPresentation (n : ℕ) :
    (W (Hbp.obj (□n))).Localization
      ≌ (Quotient (totalRel (pathRel (PosGermRel n)) (germFibre n)))ᵒᵖ :=
  hLocPresentationOf (□n) (symFreeCube n) (fun {_} α => hbpCubeStrands α)

end CubeChains
