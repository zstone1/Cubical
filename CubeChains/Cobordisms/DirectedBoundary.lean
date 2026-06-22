import CubeChains.Foundations.Reachability

/-!
# Cobordisms/DirectedBoundary

The **directed-boundary** theory of a precubical set, milestone **M1-core** of the
directed-cobordism build: sieves/cosieves and the loop-barrier lemmas.

Sub-cell-sets of a precubical set `W` are modelled as predicates
`P : W.TotalCell → Prop` on its total cell type (a cobordism leg's image will be
such a predicate later).  Over the directed-reachability preorder `Reaches W`
(`Foundations/Reachability.lean`) we develop:

* `IsSieve W P` — *past-closed* sub-cell-sets (down-closed under `Reaches`) and
  `IsCosieve W P` — *future-closed* ones (up-closed); each with the cell-level
  characterization through `vertex₁`/`vertex₀` (`IsSieve.terminal`,
  `IsCosieve.initial`).
* `StronglyConnected W` — the symmetric core of `Reaches` (mutual reachability),
  an `Equivalence`/`Setoid` (`stronglyConnectedSetoid`).
* The **loop-barrier lemmas** `IsSieve.sc_iff`, `IsCosieve.sc_iff` (a directed loop
  meeting a sieve/cosieve lies entirely inside it) and `no_straddle` (no loop
  straddles a disjoint sieve and cosieve) — the reachability heart of why gluing
  cobordisms along disjoint directed boundaries creates no spurious loops.

**Layer:** Cobordisms.  **Imports:** `Foundations/Reachability`.
-/

namespace Precubical.Cobordism

open PrecubicalSet

variable {W : PrecubicalSet}

/-! ### Sieves and cosieves -/

/-- A **sieve** (past-closed sub-cell-set): if a later cell `y` (reached from `x`)
is in `P`, then so is the earlier cell `x`.  Down-closed under `Reaches`. -/
def IsSieve (W : PrecubicalSet) (P : W.TotalCell → Prop) : Prop :=
  ∀ x y, Reaches W x y → P y → P x

/-- A **cosieve** (future-closed sub-cell-set): if an earlier cell `x` is in `P`,
then so is every cell `y` reached from it.  Up-closed under `Reaches`. -/
def IsCosieve (W : PrecubicalSet) (P : W.TotalCell → Prop) : Prop :=
  ∀ x y, Reaches W x y → P x → P y

namespace IsSieve

variable {P : W.TotalCell → Prop}

/-- A sieve containing a cell's **terminal vertex** `τc` contains the whole cell:
since `c` reaches `⟨0, W.vertex₁ c⟩`, past-closure pulls membership back. -/
theorem terminal (hP : IsSieve W P) {n : ℕ} {c : W.cells n}
    (h : P ⟨0, W.vertex₁ c⟩) : P ⟨n, c⟩ :=
  hP _ _ (reaches_vertex₁ c) h

end IsSieve

namespace IsCosieve

variable {P : W.TotalCell → Prop}

/-- A cosieve containing a cell's **initial vertex** `ιc` contains the whole cell:
since `⟨0, W.vertex₀ c⟩` reaches `c`, future-closure pushes membership forward. -/
theorem initial (hP : IsCosieve W P) {n : ℕ} {c : W.cells n}
    (h : P ⟨0, W.vertex₀ c⟩) : P ⟨n, c⟩ :=
  hP _ _ (reaches_vertex₀ c) h

end IsCosieve

/-! ### Strong connectivity -/

/-- Two cells are **strongly connected** when they are mutually reachable.  This is
the symmetric core of the directed reachability preorder — a directed loop. -/
def StronglyConnected (W : PrecubicalSet) (x y : W.TotalCell) : Prop :=
  Reaches W x y ∧ Reaches W y x

namespace StronglyConnected

@[refl]
theorem refl (x : W.TotalCell) : StronglyConnected W x x :=
  ⟨Reaches.refl x, Reaches.refl x⟩

@[symm]
theorem symm {x y : W.TotalCell} (h : StronglyConnected W x y) :
    StronglyConnected W y x :=
  ⟨h.2, h.1⟩

theorem trans {x y z : W.TotalCell} (hxy : StronglyConnected W x y)
    (hyz : StronglyConnected W y z) : StronglyConnected W x z :=
  ⟨hxy.1.trans hyz.1, hyz.2.trans hxy.2⟩

/-- The forward reachability half of a strong connection. -/
theorem reaches {x y : W.TotalCell} (h : StronglyConnected W x y) :
    Reaches W x y := h.1

/-- The backward reachability half of a strong connection. -/
theorem reaches_symm {x y : W.TotalCell} (h : StronglyConnected W x y) :
    Reaches W y x := h.2

end StronglyConnected

/-- Strong connectivity is an equivalence relation on the total cell type. -/
theorem stronglyConnected_equivalence (W : PrecubicalSet) :
    Equivalence (StronglyConnected W) where
  refl := StronglyConnected.refl
  symm := StronglyConnected.symm
  trans := StronglyConnected.trans

/-- Strong connectivity as a `Setoid` on the total cell type — its classes are the
strongly-connected components (the directed loops) of `W`. -/
def stronglyConnectedSetoid (W : PrecubicalSet) : Setoid W.TotalCell where
  r := StronglyConnected W
  iseqv := stronglyConnected_equivalence W

/-! ### Loop-barrier lemmas

The content of M1-core: a directed loop cannot cross the boundary between a sieve
and the rest, nor between a cosieve and the rest, and in particular cannot straddle
a disjoint sieve/cosieve pair.  These are exactly the facts that prevent gluing two
cobordisms along disjoint directed boundaries from manufacturing a spurious loop. -/

variable {x y : W.TotalCell}

/-- **Sieve loop-barrier.**  If `x` and `y` are strongly connected, a sieve contains
`x` iff it contains `y`: a directed loop meeting a sieve lies entirely inside it. -/
theorem IsSieve.sc_iff {P : W.TotalCell → Prop} (hP : IsSieve W P)
    (h : StronglyConnected W x y) : P x ↔ P y :=
  ⟨fun hx => hP _ _ h.2 hx, fun hy => hP _ _ h.1 hy⟩

/-- **Cosieve loop-barrier.**  If `x` and `y` are strongly connected, a cosieve
contains `x` iff it contains `y`: a directed loop meeting a cosieve lies entirely
inside it. -/
theorem IsCosieve.sc_iff {Q : W.TotalCell → Prop} (hQ : IsCosieve W Q)
    (h : StronglyConnected W x y) : Q x ↔ Q y :=
  ⟨fun hx => hQ _ _ h.1 hx, fun hy => hQ _ _ h.2 hy⟩

/-- **No straddling loop.**  A directed loop cannot straddle a *disjoint* sieve `P`
and cosieve `Q`: if `x` lies in the sieve, `y` lies in the cosieve, and `x`, `y` are
strongly connected, then since the loop forces both endpoints into `P` and into `Q`
the disjointness is contradicted. -/
theorem no_straddle {P Q : W.TotalCell → Prop} (hP : IsSieve W P)
    (_hQ : IsCosieve W Q) (hdisj : ∀ z, ¬ (P z ∧ Q z))
    (h : StronglyConnected W x y) (hPx : P x) (hQy : Q y) : False := by
  -- The loop forces both endpoints into `P` (sieve barrier): push `P x` forward to
  -- `P y`, which with the given `Q y` contradicts disjointness at `y`.  (The cosieve
  -- hypothesis `_hQ` is part of the symmetric contract but the sieve barrier alone
  -- suffices; dually one could pull `Q y` back to `Q x` via `_hQ`.)
  have hPy : P y := (hP.sc_iff h).1 hPx
  exact hdisj y ⟨hPy, hQy⟩

end Precubical.Cobordism
