import CubeChains.Braid.GermPresentation
import CubeChains.Braid.Matsumoto
import CubeChains.Chains.LiftPresentation

/-!
# Chains/ArtinPresentation — the transported presentation is the Artin one, letter for letter

`Braid/GermPresentation` presents the base by *all* permutations and the length-additive products;
Matsumoto replaces that by the `n-1` adjacent transpositions and the two Artin families.  Feeding
the second into `chLocPresentation` presents `Ch K[W⁻¹]` with generators `(chain, adjacent
index)` and relations `ArtinRel`, read on the spelled words (`Sigma.totalRel_word_iff`).
-/

open CategoryTheory Equiv Opposite CubeChains BPSet

universe v u

namespace CubeChains

/-- The Artin quiver: one vertex per strand count, a loop for each adjacent transposition. -/
abbrev ArtinQuiver : Type := Sigma.WordQuiver fun n : ℕ => Fin (n - 1)

/-- The Artin relations, read on paths. -/
def artinPathRel : HomRel (Paths ArtinQuiver) := Sigma.wordPathRel ArtinRel

/-- **The positive braid monoids are presented by the Artin relations** — `germPresentation` with
Matsumoto's theorem substituted degreewise.

    Quotient artinPathRel ≌ Σₙ Quotient (pathRel (ArtinRel n))    -- Sigma.presentation
                          ≌ Σₙ (SingleObj (ArtinPosBraid n))ᵒᵖ    -- presentedMonoidPresentation
                          ≌ (Graded ArtinPosBraid)ᵒᵖ              -- Sigma.opEquiv, sigmaEquivalence
                          ≌ FullPosBraidᵒᵖ                        -- posBraid_equiv_artinPos
-/
noncomputable def artinPresentation : Quotient artinPathRel ≌ FullPosBraidᵒᵖ :=
  (Sigma.presentation _).trans <|
    (((Sigma.Functor.sigma' fun n =>
          (SingleObj.presentedMonoidPresentation (ArtinRel n)).functor).asEquivalence.trans
        Sigma.opEquiv).trans
      ((Graded.sigmaEquivalence (M := ArtinPosBraid)).trans
        (Graded.congr fun n => (posBraid_equiv_artinPos n).symm)).op)

/-- **The generator is the simple of an adjacent transposition** — the identification the
presentation is for. -/
@[simp] theorem artinPresentation_map_gen (m : ℕ) (i : Fin (m - 1)) :
    artinPresentation.functor.map
        ((Quotient.functor artinPathRel).map (Sigma.wordPath (FreeMonoid.of i)))
      = Quiver.Hom.op (Graded.ofVal (posPerm (adjT i))) :=
  rfl

/-! ## The two relations, between the transported generators

`Sigma.totalRel_word_iff` says the imposed relation is `ArtinRel` on the spelled word; these two
are that relation read forwards, on the paths that spell the four words. -/

section Relations

universe w

variable {Pd : Quotient artinPathRel ⥤ Type w} {m : ℕ}
variable {c c' : Sigma.wordFibre Pd m} {i j : Fin (m - 1)}

/-- **A generator's crossing permutation is `adjT i`** — the arrow of `∫Pd` it names lies over the
`i`-th atom of the base. -/
theorem artinPresentation_val_gen (h : Sigma.wordAct Pd (FreeMonoid.of i) c = c') :
    artinPresentation.functor.map
        (((elementsPresentation artinPathRel Pd).functor.map
          ((Quotient.functor (totalRel artinPathRel Pd)).map (Sigma.totalPath _ h))).val)
      = Quiver.Hom.op (Graded.ofVal (posPerm (adjT i))) := by
  refine Eq.trans ?_ (artinPresentation_map_gen m i)
  exact congrArg (fun g => artinPresentation.functor.map g)
    (Sigma.val_elementsPresentation_totalPath (rel := ArtinRel) (Pd := Pd) (FreeMonoid.of i) h)

/-- **Far-apart generators commute**: `σᵢ` then `σⱼ` and `σⱼ` then `σᵢ` are one arrow. -/
theorem artin_comm (hij : (i : ℕ) + 1 < (j : ℕ))
    (h₁ : Sigma.wordAct Pd (FreeMonoid.of i * FreeMonoid.of j) c = c')
    (h₂ : Sigma.wordAct Pd (FreeMonoid.of j * FreeMonoid.of i) c = c') :
    (Quotient.functor (totalRel artinPathRel Pd)).map (Sigma.totalPath _ h₁)
      = (Quotient.functor (totalRel artinPathRel Pd)).map (Sigma.totalPath _ h₂) :=
  Sigma.quotient_map_totalPath (ArtinRel.comm i j hij) h₁ h₂

/-- **Consecutive generators braid**: `σᵢσⱼσᵢ` and `σⱼσᵢσⱼ` are one arrow. -/
theorem artin_braid (hij : (j : ℕ) = (i : ℕ) + 1)
    (h₁ : Sigma.wordAct Pd (FreeMonoid.of i * FreeMonoid.of j * FreeMonoid.of i) c = c')
    (h₂ : Sigma.wordAct Pd (FreeMonoid.of j * FreeMonoid.of i * FreeMonoid.of j) c = c') :
    (Quotient.functor (totalRel artinPathRel Pd)).map (Sigma.totalPath _ h₁)
      = (Quotient.functor (totalRel artinPathRel Pd)).map (Sigma.totalPath _ h₂) :=
  Sigma.quotient_map_totalPath (ArtinRel.braid i j hij) h₁ h₂

end Relations

end CubeChains

namespace ChainCat

open CubeChains

/-! ## The presentation of the localized base, and its transport -/

/-- **`Ch(Zbp)[W⁻¹]ᵒᵖ` is presented by the Artin relations**: one vertex per event count, `n-1`
generators on it, and the two Artin families. -/
noncomputable def locArtinPresentation :
    Quotient artinPathRel ≌ ((W Zbp).op).Localization :=
  artinPresentation.trans locFullOpEquiv.symm

/-- **`Ch K[W⁻¹]` is presented by the adjacent transpositions acting on a chain.**  A generator
is an adjacent pair of events of a chain of `K`; the relations are the Artin ones. -/
noncomputable def chLocArtinPresentation (K : BPSet) (hK : IsSegal K.toPsh) :
    (W K).Localization ≌
      (Quotient (totalRel artinPathRel
        (locArtinPresentation.functor ⋙ wedgeHomsDescend K hK)))ᵒᵖ :=
  chLocPresentation K artinPathRel hK locArtinPresentation

/-! ## The chain a generator sits at

`Construction.fac` is an *equality*, so the descended fibre over `Q(op a)` is literally the maps of
`⋁a` into `K`; and the base presentation's vertex at strand count `m` is isomorphic to `Q(op 1ᵐ)`
because `FullPosBraid` has no morphisms between degrees. -/

section Fibre

private theorem locFullOpEquiv_functor_inverse_obj (Y : FullPosBraidᵒᵖ) :
    locFullOpEquiv.functor.obj (locFullOpEquiv.inverse.obj Y) = Y :=
  Opposite.unop_injective (locFullOpEquiv.counitIso.app Y).hom.unop.deg.symm

/-- The localized base at strand count `m`, named by the run of `m` edges. -/
theorem locFullOpEquiv_obj_Q_ones (m : ℕ) :
    locFullOpEquiv.functor.obj ((W Zbp).op.Q.obj (op (zObj (𝟙^m))))
      = op (m : FullPosBraid) :=
  (Functor.congr_obj (Localization.Construction.fac ((chPosBraid Zbp).op)
    (Localization.inverts ((chPosBraid Zbp).op) ((W Zbp).op))) (op (zObj (𝟙^m)))).trans
    (congrArg op (dimSum_replicate m))

variable (K : BPSet) (hK : IsSegal K.toPsh)

/-- **The descended fibre over a chain is the maps of that wedge into `K`.** -/
theorem wedgeHomsDescend_obj_Q (a : Ch Zbp) :
    (wedgeHomsDescend K hK).obj ((W Zbp).op.Q.obj (op a)) = (wedgeHoms K).obj (op a) :=
  Functor.congr_obj (Localization.Construction.fac (wedgeHoms K) (invertsMerges_of_isSegal K hK))
    (op a)

/-- **A vertex the base presentation puts over strand count `m` carries the chains of `K` with `m`
unit beads.** -/
noncomputable def locFibreEquiv {C : Type u} [Category.{v} C]
    (F : C ⥤ ((W Zbp).op).Localization) (Z : C) (m : ℕ)
    (h : locFullOpEquiv.functor.obj (F.obj Z) = op (m : FullPosBraid)) :
    (F ⋙ wedgeHomsDescend K hK).obj Z ≃ (wedgeHoms K).obj (op (zObj (𝟙^m))) :=
  ((wedgeHomsDescend K hK).mapIso (locFullOpEquiv.functor.preimageIso
    (eqToIso (h.trans (locFullOpEquiv_obj_Q_ones m).symm)))).toEquiv.trans
      (Equiv.cast (wedgeHomsDescend_obj_Q K hK (zObj (𝟙^m))))

theorem locArtinPresentation_obj (m : ℕ) :
    locFullOpEquiv.functor.obj (locArtinPresentation.functor.obj
        ((Quotient.functor artinPathRel).obj (Sigma.wordVtx m)))
      = op (m : FullPosBraid) :=
  locFullOpEquiv_functor_inverse_obj (op m)

theorem locGermPresentation_obj (m : ℕ) :
    locFullOpEquiv.functor.obj (locGermPresentation.functor.obj
        ((Quotient.functor germRel).obj (Sigma.wordVtx m)))
      = op (m : FullPosBraid) :=
  locFullOpEquiv_functor_inverse_obj (op m)

/-- **The Artin generators at strand count `m` sit at the chains of `K` with `m` unit beads.** -/
noncomputable def artinFibreEquiv (m : ℕ) :
    Sigma.wordFibre (locArtinPresentation.functor ⋙ wedgeHomsDescend K hK) m
      ≃ (wedgeHoms K).obj (op (zObj (𝟙^m))) :=
  locFibreEquiv K hK _ _ m (locArtinPresentation_obj m)

/-- …and so do the germ generators. -/
noncomputable def germFibreEquiv (m : ℕ) :
    Sigma.wordFibre (locGermPresentation.functor ⋙ wedgeHomsDescend K hK) m
      ≃ (wedgeHoms K).obj (op (zObj (𝟙^m))) :=
  locFibreEquiv K hK _ _ m (locGermPresentation_obj m)

end Fibre

end ChainCat
