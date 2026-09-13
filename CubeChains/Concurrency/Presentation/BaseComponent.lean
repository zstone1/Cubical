import CubeChains.Concurrency.Presentation.Retraction

/-!
# Concurrency/Presentation/BaseComponent — the run, as a one-object piece of the localized base

`runBase N` is the run of `N` events with `PosBraid N` for endomorphisms.  Full faithfulness *is*
bijectivity of `runBraid N` — nothing else — and it is what `CategoryOfElements.isEquivalence_pre`
asks of the functor a fibre is pulled back along.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain ChainCat

namespace ChainCat

/-- The run of `N` events, as a one-object piece of the localized base. -/
noncomputable def runBase (N : ℕ) :
    (SingleObj (PosBraid N))ᵒᵖ ⥤ ((W Zbp).op).Localization where
  obj _ := ((W Zbp).op).Q.obj (op (zObj (𝟙^N)))
  map {_ _} f := (runBraid N (f.unop : PosBraid N)).unop
  map_id x := by
    have h := SingleObj.id_as_one (M := PosBraid N) x.unop
    change (runBraid N (𝟙 x).unop).unop = _
    rw [unop_id, h, map_one]
    rfl
  map_comp {_ _ _} f g := by
    have h := SingleObj.comp_as_mul (M := PosBraid N) g.unop f.unop
    change (runBraid N (f ≫ g).unop).unop = _
    rw [unop_comp, h, map_mul]
    rfl

instance (N : ℕ) : (runBase N).Faithful where
  map_injective {_ _ _ _} h :=
    Quiver.Hom.unop_inj (runBraid_injective N (MulOpposite.unop_inj.mp h))

instance (N : ℕ) : (runBase N).Full where
  map_surjective {_ _} t :=
    ⟨Quiver.Hom.op (runGrade N (MulOpposite.op t)),
      congrArg MulOpposite.unop (runBraid_runGrade N (MulOpposite.op t))⟩

end ChainCat
