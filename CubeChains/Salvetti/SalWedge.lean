import CubeChains.Arrangements.COMSum
import CubeChains.Salvetti.LinesWedge
import CubeChains.Salvetti.BraidIso

/-!
# Salvetti/SalWedge — `Sal (L₁ ⊕ L₂) ≌ Int(Lines(P ∨ Q))`

The **monoidal** companion of the headline theorem `braidSalEquiv`
(`Sal (braidCOM n) ≌ Int(Lines(□ⁿ))`, `BraidIso.lean`): the comparison between Salvetti posets and
the retraction model of directed lines is compatible with taking direct sums of COMs on one side
and serial wedges of bi-pointed precubical sets on the other.  Both operations become the
categorical product, so the theorem is a two-line assembly of

```
Sal (L₁ ⊕ L₂)  ≌  Sal L₁ × Sal L₂                       -- salSumEquiv    (COMSum)
               ≌  Int(Lines P) × Int(Lines Q)           -- e₁.prod e₂     (hypotheses)
               ≌  Int(Lines (P ∨ Q))                    -- linesWedgeEquiv.symm (LinesWedge)
```

Neither summand need be an oriented matroid: `COM.compClosed` (from face symmetry alone) supplies
the only cross-summand ingredient of the direct sum's strong-elimination axiom.

`braidSumSalEquiv` specialises `P`, `Q` to standard cubes, where the hypotheses are `braidSalEquiv`.
Iterating it along a list of dimensions (a serial wedge is an iterated `wedge2`) identifies the
Salvetti complex of a direct sum of braid arrangements with `Int(Lines)` of the corresponding
cube chain.

All theorems here are **sorry-free** (`#print axioms braidSerialSalEquiv` is clean):
`linesWedgeEquiv` routes through `ChainCat.chSegal` (`Chains/SegalProd.lean`), itself proved from
the sorry-free Segal splitting of `Chains/SegalSplit.lean`.
-/

open CategoryTheory CubeChain BPSet

namespace FinalBraid

variable {E₁ E₂ : Type*}

/-- **The wedge theorem for Salvetti posets.**  If the Salvetti poset of `L₁` is the line model of
`P` and that of `L₂` is the line model of `Q`, then the Salvetti poset of the direct sum `L₁ ⊕ L₂`
is the line model of the wedge `P ∨ Q`.

The COM side splits by `COM.salSumEquiv`, the precubical side by `linesWedgeEquiv`, and the two
splittings are matched by the hypothesised equivalences. -/
noncomputable def salWedgeEquiv (L₁ : COM E₁) (L₂ : COM E₂) {P Q : BPSet}
    (hP : P.AdmitsAltitude) (hQ : Q.AdmitsAltitude)
    (e₁ : Sal L₁ ≌ (Lines P).Elements) (e₂ : Sal L₂ ≌ (Lines Q).Elements) :
    Sal (L₁.directSum L₂) ≌ (Lines (wedge2 P Q)).Elements :=
  (COM.salSumEquiv L₁ L₂).trans ((e₁.prod e₂).trans (linesWedgeEquiv P Q hP hQ).symm)

/-- **The braid case.**  The Salvetti complex of the direct sum of two braid arrangements is
`Int(Lines)` of the wedge of the two cubes: `Sal (A_{m−1} ⊕ A_{n−1}) ≌ Int(Lines(□ᵐ ∨ □ⁿ))`. -/
noncomputable def braidSumSalEquiv (m n : ℕ) :
    Sal ((braidCOM m).directSum (braidCOM n)) ≌
      (Lines (wedge2 (BPSet.cube m) (BPSet.cube n))).Elements :=
  salWedgeEquiv (braidCOM m) (braidCOM n)
    (BPSet.cube_admitsAltitude m) (BPSet.cube_admitsAltitude n)
    (braidSalEquiv m) (braidSalEquiv n)

/-! ## The n-ary serial wedge

Iterating `salWedgeEquiv` along a dimension sequence: the serial wedge `□^∨(dims)` is a
right-folded iterate of `wedge2` (`BPSet.serialWedge_cons`), and the matching COM is the
right-folded iterate of `directSum` of the braid arrangements of the beads.  This is the
`Int(Lines)`-side companion of the n-ary Segal decomposition `ChainCat.chSegalProd`. -/

/-- The ground set of the iterated direct sum `braidSumProd dims`. -/
def braidSumGround : List ℕ+ → Type
  | [] => BraidGround 0
  | n :: rest => BraidGround (n : ℕ) ⊕ braidSumGround rest

/-- **The iterated direct sum of braid arrangements** along a dimension sequence: `⊕ᵢ A_{dᵢ−1}`,
right-folded to match `serialWedge`.  The empty list gives the (empty) braid arrangement of the
point `□⁰`. -/
def braidSumProd : (dims : List ℕ+) → COM (braidSumGround dims)
  | [] => braidCOM 0
  | n :: rest => (braidCOM (n : ℕ)).directSum (braidSumProd rest)

/-- **The n-ary serial-wedge theorem.**  The Salvetti complex of the iterated direct sum of braid
arrangements `⊕ᵢ A_{dᵢ−1}` is `Int(Lines)` of the serial wedge `□^∨(dims)`:

> `braidSerialSalEquiv dims : Sal (braidSumProd dims) ≌ Int(Lines(□^∨(dims)))`.

By recursion on `dims`: `[]` is `braidSalEquiv 0` (as `serialWedge [] = □⁰`), and `n :: rest`
glues the head cube via `salWedgeEquiv`, using `braidSalEquiv n` on the head and the recursive
equivalence on the tail (both `wedge2`/`directSum` steps hold definitionally). -/
noncomputable def braidSerialSalEquiv : (dims : List ℕ+) →
    Sal (braidSumProd dims) ≌ (Lines (BPSet.serialWedge dims)).Elements
  | [] => braidSalEquiv 0
  | n :: rest =>
      salWedgeEquiv (braidCOM (n : ℕ)) (braidSumProd rest)
        (BPSet.cube_admitsAltitude (n : ℕ)) (BPSet.serialWedge_admitsAltitude rest)
        (braidSalEquiv (n : ℕ)) (braidSerialSalEquiv rest)

end FinalBraid
