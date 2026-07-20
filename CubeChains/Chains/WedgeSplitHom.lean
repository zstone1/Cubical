import CubeChains.Chains.SegalProd

/-!
# Chains/WedgeSplitHom — the Segal split at the level of a single wedge map

`splitObj` splits a chain *object* of `X ∨ Y`; `splitWedgeMorphism` says the same thing about a
bare map `⋁as ⟶ X ∨ Y`, which is the form the run-level constructions consume.  Both round trips
of `splitObj` hold on the nose, so this is a reading of `chConcat_obj_splitObj`, not new content.
-/

open CategoryTheory BPSet MonoidalCategory

namespace ChainCat

variable {X Y : BPSet}

/-- Converse of `Obj.mk_eq_mk`: read a chain-object equality back as a dims equality plus a
transported map equality. -/
theorem Obj.eq_mk_iff {K : BPSet} {d d' : List ℕ+} {m : ⋁d ⟶ K} {m' : ⋁d' ⟶ K}
    (e : (⟨d, m⟩ : Obj K) = ⟨d', m'⟩) :
    ∃ h : d = d', m = eqToHom (congrArg BPSet.serialWedge h) ≫ m' := by
  injection e with hd hm
  subst hd
  exact ⟨rfl, by simpa using eq_of_heq hm⟩

/-- **Every wedge map into a `wedge2` splits**, uniquely and computably: `as` is an append and `f`
is the corresponding `concatChainMap`.  The altitude hypothesis is what rules out a map that
re-crosses the junction; for serial wedges it is discharged by `serialWedge_admitsAltitude`. -/
def splitWedgeMorphism (h : (wedge2 X Y).AdmitsAltitude) (as : List ℕ+)
    (f : ⋁as ⟶ wedge2 X Y) :
    Σ' (l : Ch X) (r : Ch Y) (heq : as = l.dims ++ r.dims),
      f = eqToHom (congrArg BPSet.serialWedge heq) ≫ concatChainMap X Y l r :=
  ⟨(splitObj h ⟨as, f⟩).1, (splitObj h ⟨as, f⟩).2,
    (congrArg Obj.dims (chConcat_obj_splitObj h (⟨as, f⟩ : Ch (wedge2 X Y)))).symm,
    by
      obtain ⟨_, hmap⟩ :=
        Obj.eq_mk_iff (chConcat_obj_splitObj h (⟨as, f⟩ : Ch (wedge2 X Y))).symm
      exact hmap⟩

end ChainCat
