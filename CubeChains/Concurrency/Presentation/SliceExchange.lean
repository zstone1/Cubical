import CubeChains.Concurrency.Presentation.SlicePresentation
import CubeChains.Machinery.Presentation.SliceColimit

/-!
# Concurrency/Presentation/SliceExchange — the localized slice *is* the weak order

`SliceRuns` has the runs over `d` and the arrows between them; here they are assembled into an
equivalence, which needs faithfulness — i.e. `locOver_isThin` — and so lives above it.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv Polygraph

namespace ChainCat

variable {d : Ch Zbp} {N : ℕ}

/-! ### …as an equivalence

Fullness is `nonempty_locOver_hom_of_le` read between the two objects' own runs; faithfulness is
`locOver_isThin`; essential surjectivity asks that every permutation be realised, which pins down
the shapes for which the slice is the *whole* weak order. -/

/-- **The weak-order class, on the localized slice** — `degLoc` at a degree valued in the weak
order rather than in `ℕ`. -/
noncomputable def weakOverLoc (hd : dimSum d.dims = N) :
    ((W Zbp).over (X := d)).Localization ⥤ (WeakOrder N)ᵒᵖ :=
  degLoc (weakOver hd) (weakOver_le hd) ((W Zbp).over (X := d))
    (fun hm => le_of_eq (weakOver_eq_of_W hd hm))

instance weakOverLoc_faithful (hd : dimSum d.dims = N) : (weakOverLoc hd).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance weakOverLoc_full (hd : dimSum d.dims = N) : (weakOverLoc hd).Full where
  map_surjective {X Y} h := by
    obtain ⟨y, rfl⟩ := Localization.Construction.exists_Q_obj _ X
    obtain ⟨y', rfl⟩ := Localization.Construction.exists_Q_obj _ Y
    obtain ⟨g⟩ := nonempty_locOver_hom hd (leOfHom h.unop)
    exact ⟨g, Subsingleton.elim _ _⟩

/-- **Every permutation `d` realises is an object of the localized slice** — the run that spells
it. -/
theorem weakOverLoc_essSurj (hd : dimSum d.dims = N)
    (hall : ∀ σ : Perm (Fin N), ∃ a : RunOver d, RunOver.perm hd a = σ) :
    (weakOverLoc hd).EssSurj where
  mem_essImage σ := by
    obtain ⟨a, ha⟩ := hall (WeakOrder.perm σ.unop)
    refine ⟨((W Zbp).over (X := d)).Q.obj a.1, ⟨eqToIso ?_⟩⟩
    change op (weakOver hd a.1) = σ
    rw [show weakOver hd a.1 = WeakOrder.of (RunOver.perm hd a) from rfl, ha]
    rfl

/-- **The localized slice over `d` is the right weak order on the permutations `d` realises**,
read backwards. -/
noncomputable def locOverWeakOrder (hd : dimSum d.dims = N)
    (hall : ∀ σ : Perm (Fin N), ∃ a : RunOver d, RunOver.perm hd a = σ) :
    ((W Zbp).over (X := d)).Localization ≌ (WeakOrder N)ᵒᵖ :=
  haveI := weakOverLoc_essSurj hd hall
  haveI : (weakOverLoc hd).IsEquivalence := { }
  (weakOverLoc hd).asEquivalence

/-- **The runs are never all of the slice**: `Over (zObj [2])` has an object that is not a run —
`𝟙` on the one-bead chain of length `2`.  So the slice family is not a levelwise *isomorphism* of
categories, and the retraction of `Machinery/Presentation/SliceColimit` cannot be traded for one. -/
theorem exists_not_isRun_over :
    ∃ y : Over (zObj ([2] : List ℕ+)), ¬ IsRun Zbp y.left :=
  ⟨Over.mk (𝟙 _), fun h => absurd (h 2 (List.mem_singleton_self 2)) (by decide)⟩

/-- **A colimit on both sides, for every `K`**: the colimit of the slice presentations presents the
colimit of the localized slices of `Ch K`. -/
noncomputable def presentsChainsColimitLoc (K : BPSet) {P : Ch Zbp ⥤ Polygraph.{0, 0, 0}}
    (p : ∀ d : Ch Zbp, Presents (P.obj d) (((W Zbp).over (X := d)).Localization))
    (hP : ∀ {d' d : Ch Zbp} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc (W Zbp) f) :
    Presents (Limits.colimit (elementsPoly (wedgeHoms K) P))
      ↥(Limits.colimit (overLocFunctor (W K))) :=
  (presentsChainsColimit K p hP).transport
    (Cat.equivOfIso
      ((isColimitOverLocCocone (W K)).coconePointUniqueUpToIso (Limits.colimit.isColimit _)))

end ChainCat
